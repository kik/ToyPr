module Prover.Goal where

import Kernel (assertType, Binding (Decl, Def), convertible, gbindings, Global (Global), Kernel, pattern, pushSubst, reduceFull, shift, Term (TmAbs, TmApp, TmConst, TmEq, TmEqInd, TmHole, TmProd, TmRefl, TmUniv, TmVar), termEqSyntactically, typeof, ubindings, UnivExpr, unKernel)
import Prover.ProofState (GlobalState (GlobalState), Goal (Goal), goals, lemmaName, mainGoal, nextHoleId, printProofState, proof, ProofState (ProofState))
import Parser.TypedTerm (showsTerm)
import Parser.PreTypedTerm
import Data.Maybe (isNothing)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Control.Monad.Reader (ask, lift, liftIO, ReaderT, runReader, unless)
import Control.Monad.State (execStateT, get, put, StateT)
import Control.Monad.Error (runErrorT)
import Control.Exception (catch, IOException)
import Text.Parsec

initGlobal :: IO (IORef GlobalState)
initGlobal = newIORef $ GlobalState Global { gbindings = [], ubindings = [] } Nothing

type ProverCommand a = ReaderT (IORef GlobalState) IO a
type CommandImpl a = StateT GlobalState IO a

runTermHandler :: Kernel a -> CommandImpl a
runTermHandler h = do GlobalState g _ <- get
                      case runReader (runErrorT (unKernel h)) g of
                        Right v -> return v
                        Left e -> undefined -- fail $ show e

command :: CommandImpl () -> ProverCommand ()
command body = do
  gs <- ask
  lift $ catch (go gs) err
  where
    go s = readIORef s >>= execStateT body >>= writeIORef s
    err :: IOException -> IO ()
    err e = do
      putStrLn $ "Error: " ++ show e
      return ()

parsePTTerm :: String -> ProverCommand PTTerm
parsePTTerm s =
  case runParser termParser () "" s of
    Right t -> return t
    Left err -> fail $ show err

parseTerm :: PTTerm -> CommandImpl Term
parseTerm s = do GlobalState _ mps <- get
                 let e = case mps of
                       Just (ProofState { goals = Goal _ _ e' :_ }) -> e'
                       _ -> []
                 case toKernelTerm (map fst e) s of
                   Just t -> return t
                   Nothing -> fail ""

uvar :: String -> UnivExpr -> ProverCommand ()
uvar n u = command f
  where f = do GlobalState g mps <- get
               -- TODO: need check
               let g' = g { ubindings = (n, u):ubindings g }
               put $ GlobalState g' mps

lemma :: String -> PTTerm -> ProverCommand ()
lemma n props = command f
  where f = do prop <- parseTerm props
               GlobalState g mps <- get
               unless (isNothing mps) $ fail "proof not complete"
               runTermHandler $ assertType [] prop
               liftIO $ printProofState (ps prop)
               put $ GlobalState g (Just (ps prop))
        ps prop = ProofState { goals = [Goal 0 prop []]
                             , proof = TmHole 0
                             , mainGoal = prop
                             , lemmaName = n
                             , nextHoleId = 1
                             }

qed :: ProverCommand ()
qed = command f
  where f = do GlobalState g mps <- get
               case mps of
                 Nothing -> fail "not in proof mode"
                 Just ps -> do
                   unless (null $ goals ps) $ fail "proof not complete"
                   ty <- runTermHandler $ typeof [] (proof ps)
                   b  <- runTermHandler $ convertible [] ty (mainGoal ps)
                   unless b $ fail "invalid proof"
                   liftIO $ putStrLn $ lemmaName ps ++ " is defined."
                   put $ GlobalState (g { gbindings = (lemmaName ps, Def (mainGoal ps) (proof ps)):gbindings g }) Nothing

substHole :: Int -> Term -> Term -> Term
substHole i = subst
  where
    subst s = go
      where
        go t@(TmUniv _) = t
        go t@(TmVar _) = t
        go t@(TmConst _) = t
        go t@(TmHole j) | i == j = s
                        | otherwise = t
        go (TmProd n t1 t2) = TmProd n (go t1) (go t2)
        go (TmAbs  n t1 t2) = TmAbs  n (go t1) (go t2)
        go (TmApp t1 t2) = TmApp (go t1) (go t2)
        go (TmEq t1 t2 t3) = TmEq (go t1) (go t2) (go t3)
        go (TmRefl t1 t2) = TmRefl (go t1) (go t2)
        go (TmEqInd ct a x y p) =
          TmEqInd (go ct) (go a) (go x) (go y) (go p)

type TacImpl a = CommandImpl a

curGoal :: TacImpl Goal
curGoal = do
  GlobalState _ s <- get
  case s of
    Just (ProofState { goals = g:_ }) -> return g
    _ -> fail "no more goal"

updateGoal :: Int -> Term -> [Goal] -> TacImpl ()
updateGoal i pf ss = do
  GlobalState g ps <- get
  case ps of
    Just s@(ProofState { goals = _:gs }) ->
      put $ GlobalState g $ Just $ s { goals = ss ++ gs
                                     , proof = substHole i pf (proof s)
                                     }
    _ -> fail "no more goal"

allocId :: TacImpl Int
allocId = do
  GlobalState g ps <- get
  case ps of
    Just s -> do
      let i = nextHoleId s
      put $ GlobalState g $ Just $ s { nextHoleId = i + 1 }
      return i
    _ -> fail "not in proof mode"

tac :: TacImpl () -> ProverCommand ()
tac f = command body
  where
    body = do
      f
      GlobalState _ ps <- get
      case ps of
        Just s -> lift $ printProofState s
        Nothing -> return ()

exact :: PTTerm -> ProverCommand ()
exact ts = tac f
  where
    f = do
      t <- parseTerm ts
      Goal i g e <- curGoal
      ty <- runTermHandler $ typeof e t
      b  <- runTermHandler $ convertible e ty g
      unless b $ fail "invalid proof"
      updateGoal i t []

assert :: PTTerm -> ProverCommand ()
assert ts = tac f
  where
    f = do
      t <- parseTerm ts
      Goal i g e <- curGoal
      holeId1 <- allocId
      holeId2 <- allocId
      let goal1 = Goal holeId1 (TmProd Nothing t (shift 1 g)) e
          goal2 = Goal holeId2 t e
      updateGoal i (TmApp (TmHole holeId1) (TmHole holeId2)) [goal1, goal2]

intros :: [String] -> ProverCommand ()
intros names = tac (f names)
  where
    f [] = return ()
    f (name:ns) = do
      Goal i g e <- curGoal
      case g of
        TmProd _ ty body -> do
          holeId <- allocId
          updateGoal i (TmAbs (Just name) ty (TmHole holeId)) [Goal holeId body ((Just name, Decl ty):e)]
          f ns
        _ -> fail "not product type"

introsw :: String -> ProverCommand ()
introsw names = intros $ words names

intro :: String -> ProverCommand ()
intro name = intros [name]

{-# ANN elim_eq "HLint: ignore" #-}
elim_eq :: String -> PTTerm -> ProverCommand ()
elim_eq name ts = tac f
  where
    f = do
      p <- parseTerm ts
      Goal i g e <- curGoal
      ty <- runTermHandler $ reduceFull e =<< typeof e p
      case ty of
        TmEq a x y -> do
          --liftIO $ putStrLn $ "eliminating: " ++ show p ++ " : " ++ show x ++ " = " ++ show y ++ " <: " ++ show a
          let ct = pattern (shift 2 p) $ pattern (shift 1 y) $ pattern x g
          --liftIO $ putStrLn $ "pattern: " ++ show ct
          let cz = pattern (TmVar 0) $ pushSubst (TmVar 0) $ pushSubst (TmVar 1) $ pushSubst (TmRefl (shift 2 a) (TmVar 2)) ct
          holeId <- allocId
          updateGoal i (TmEqInd (TmAbs Nothing a (TmAbs Nothing (shift 1 a) (TmAbs Nothing (TmEq (shift 2 a) (TmVar 1) (TmVar 0)) ct)))
            (TmAbs (Just name) a (TmHole holeId)) x y p) [Goal holeId cz ((Just name, Decl a):e)]
        _ ->
          fail "not eq type"

trans :: PTTerm -> ProverCommand ()
trans s = tac f
  where
    f = do
      t <- parseTerm s
      Goal i g e <- curGoal
      case g of
        TmEq a x y -> do
          h1 <- allocId
          h2 <- allocId
          let g1 = TmEq a x t
              g2 = TmEq a t y
          updateGoal i (foldl1 TmApp [TmConst "eq_trans", a, x, t, y, TmHole h1, TmHole h2])
            [Goal h1 g1 e, Goal h2 g2 e]
        _ -> fail "not identity type"

sym :: ProverCommand ()
sym = tac f
  where
    f = do
      Goal i g e <- curGoal
      case g of
        TmEq a x y -> do
          h1 <- allocId
          let g1 = TmEq a y x
          updateGoal i (foldl1 TmApp [TmConst "eq_sym", a, y, x, TmHole h1])
            [Goal h1 g1 e]
        _ -> fail "not identity type"

{-# ANN f_equal_1 "HLint: ignore" #-}
f_equal_1 :: ProverCommand ()
f_equal_1 = tac f
  where
    f = do
      Goal i g e <- curGoal
      case g of
        TmEq _ (TmApp fn x) (TmApp gn y) | termEqSyntactically x y -> do
          h1 <- allocId
          a <- runTermHandler $ typeof e fn
          b <- runTermHandler $ typeof e (TmApp fn x)
          let g1 = TmEq a fn gn
              ct = TmAbs Nothing a (TmAbs Nothing (shift 1 a) (TmAbs Nothing (TmEq (shift 2 a) (TmVar 1) (TmVar 0))
                                                                   (TmEq (shift 3 b)
                                                                    (TmApp (TmVar 2) (shift 3 x))
                                                                    (TmApp (TmVar 1) (shift 3 x)))))
              c = TmAbs Nothing a (TmRefl (shift 1 b) (TmApp (TmVar 0) (shift 1 x)))
          updateGoal i (TmEqInd ct c fn gn (TmHole h1)) [Goal h1 g1 e]
        _ -> fail "not identity type"
          
{-# ANN f_equal_2 "HLint: ignore" #-}
f_equal_2 :: ProverCommand ()
f_equal_2 = tac f
  where
    f = do
      Goal i g e <- curGoal
      case g of
        TmEq _ (TmApp fn x) (TmApp gn y) | termEqSyntactically fn gn -> do
          h1 <- allocId
          a <- runTermHandler $ typeof e x
          b <- runTermHandler $ typeof e (TmApp fn x)
          let g1 = TmEq a x y
              ct = TmAbs Nothing a (TmAbs Nothing (shift 1 a) (TmAbs Nothing (TmEq (shift 2 a) (TmVar 1) (TmVar 0))
                                                                   (TmEq (shift 3 b)
                                                                    (TmApp (shift 3 fn) (TmVar 2))
                                                                    (TmApp (shift 3 fn) (TmVar 1)))))
              c = TmAbs Nothing a (TmRefl (shift 1 b) (TmApp (shift 1 fn) (TmVar 0)))
          updateGoal i (TmEqInd ct c x y (TmHole h1)) [Goal h1 g1 e]
        _ -> fail "not identity type"
          

compute :: PTTerm -> ProverCommand ()
compute s = command f
  where
    f = do t <- parseTerm s
           GlobalState _ mps <- get
           case mps of
             Nothing -> do
               v <- runTermHandler $ reduceFull [] t -- TODO: type check
               liftIO $ putStrLn $ "Value: " ++ showsTerm [] v ""
             Just (ProofState { goals = Goal _ _ e:_ }) -> do
               v <- runTermHandler $ reduceFull e t -- TODO: type check
               liftIO $ putStrLn $ "Value: " ++ showsTerm e v ""
             _ -> undefined


