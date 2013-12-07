module Main where

import Kernel
import Prover.ProofState
import Prover.Goal
import Parser.Token
import Parser.PreTypedTerm
import Parser.InputLine
import Parser.Command
import Data.IORef
import Control.Monad.Reader
import System.Console.Haskeline
import Control.Applicative hiding (many)
import Text.Parsec hiding ((<|>))
import System.Console.GetOpt
import System.Environment

commands :: [Parsec String () (ProverCommand Bool)]
commands = [ command "Quit" quit True
           , c "Qed" $ return qed
           , c "Lemma" (lemma <$> pIdent <*> pTerm)
           , c "UVar" (uvar <$> pIdent <*> pUniv)
           , c "intro" (intro <$> pIdent)
           , c "intros" (intros <$> many1 pIdent)
           , c "elim_eq" (elim_eq <$> pIdent <*> pTerm)
           , c "exact" (exact <$> pTerm)
           , c "trans" (trans <$> pTerm)
           , c "sym" $ return sym
           , c "f_equal_1" $ return f_equal_1
           , c "f_equal_2" $ return f_equal_2
           ]
  where
    command :: String -> Parsec String () (ProverCommand ()) -> Bool -> Parsec String () (ProverCommand Bool)
    command name f isQuit = try $ do spaces >> string name >> whiteSpace
                                     cmd <- f
                                     eof
                                     return $ cmd >> return isQuit
    c :: String -> Parsec String () (ProverCommand ()) -> Parsec String () (ProverCommand Bool)
    c name f = command name f False
    quit :: Parsec String () (ProverCommand ())
    quit = return $ do
      lift $ putStrLn "Quiting."
      return ()

main :: IO ()
main = do
  g <- initGlobal
  args <- getArgs
  let inputs = case args of
                 [] -> [defaultBehavior]
                 files -> map useFile files
  forM_ inputs (\b -> runInputTBehavior b defaultSettings (mainLoop g))
          
mainLoop :: IORef GlobalState -> InputT IO ()
mainLoop gs = loop gs "" 
  where
    loop :: IORef GlobalState -> String -> InputT IO ()
    loop g rest = do
      minput <- getInputLine "ToyPr> "
      case minput of
        Nothing -> return ()
        Just input  -> do outputStrLn $ "Input was: " ++ input
                          let (cmds, rest') = splitInput (rest ++ input)
                          outputStrLn $ "Input was: " ++ show cmds ++ rest'
                          isquit <- lift $ runCmds g cmds
                          unless isquit $ loop g rest' 
    runCmds _ [] = return False
    runCmds g (c:cs) = do
      isquit <- runCmd g c
      if isquit then return True else runCmds g cs
    runCmd g cmd = case runParser p () "" cmd of
      Left err -> do
        putStrLn $ "Unknown command: " ++ show err
        return True
      Right c ->
        runReaderT c g
    p = choice commands

