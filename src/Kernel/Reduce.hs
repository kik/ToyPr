module Kernel.Reduce where

import Kernel.Term
import Kernel.Env
import Kernel.KernelMonad
import Control.Applicative

reduceFull :: LocalEnv -> Term -> Kernel Term
reduceFull = rd
  where
    rd e t = case t of
      TmUniv _ -> return t
      TmVar i ->
        case lookupVar e i of
          Nothing -> fatalError "unbound variable"
          Just (Decl _) -> return t
          Just (Def _ t') -> return $ shift (i+1) t'
      TmConst name -> do
        g <- getGlobalBindings
        case lookupConst g name of
          Nothing -> fatalError "unbound variable"
          Just (Decl _) -> return t
          Just (Def _ t') -> return t'
      TmHole _ -> fatalError "reducing Hole"
      TmProd n ty body -> TmProd n <$> rd e ty <*> rd ((n, Decl ty):e) body
      TmAbs  n ty body -> TmAbs  n <$> rd e ty <*> rd ((n, Decl ty):e) body
      TmApp t1 t2 -> do
        t1' <- rd e t1
        t2' <- rd e t2
        case t1' of
          TmAbs n ty body ->
            shift (-1) <$> rd ((n, Def ty t2'):e) body
          _ -> return $ TmApp t1' t2'
      TmEq   a x y -> TmEq   <$> rd e a <*> rd e x <*> rd e y
      TmRefl a x   -> TmRefl <$> rd e a <*> rd e x
      TmEqInd ct c x y p -> do
        p' <- rd e p
        case p' of
          TmRefl _ z -> rd e (TmApp c z)
          _ -> TmEqInd <$> rd e ct <*> rd e c <*> rd e x <*> rd e y <*> pure p'
