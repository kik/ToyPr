module Prover.ProofState where

import Kernel
import Parser.TypedTerm
import Data.List

data Goal = Goal Int Type LocalEnv

data ProofState = ProofState { goals :: [Goal]
                             , proof :: Term
                             , lemmaName :: String
                             , mainGoal :: Term
                             , nextHoleId :: Int
                             }

data GlobalState = GlobalState Global (Maybe ProofState)

printProofState :: ProofState -> IO ()
printProofState s = do mapM_ runGoal $ zip [1..] $ goals s
                       --runProof $ proof s
  where
    runGoal (i, (Goal _ ty e)) = do
      putStrLn $ "---- Goal " ++ show i ++ " ----"
      mapM_ runBinding $ zip [0..] $ tails e
      putStrLn "===="
      putStrLn $ showsTerm e ty ""
    runProof p = do
      putStrLn $ "---- Proof ----"
      putStrLn $ showsTerm [] p ""
    runBinding (i, ((n, Decl ty):e)) = do
      putStrLn $ "[" ++ show i ++ "] " ++ name n ++ " : " ++ showsTerm e ty ""
    runBinding (i, ((n, Def t ty):e)) = do
      putStrLn $ "[" ++ show i ++ "] " ++ name n ++ " := " ++ showsTerm e t "" ++ " : " ++ showsTerm e ty ""
    runBinding (_, []) = return ()
    name (Just n) = n
    name Nothing = "_"

