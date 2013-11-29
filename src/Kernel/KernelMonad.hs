module Kernel.KernelMonad where

import Kernel.Term
import Kernel.Env
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error

data KernelError = TypeError String [(LocalEnv, Term)]
                 | FatalError String

instance Error KernelError where
  strMsg = FatalError

{-
instance Show KernelError where
  show (TypeError s ts) = "type error: " ++ s ++ " " ++ show (map (uncurry LocalTerm) ts)
  show (FatalError s) = "fatal error: " ++ s
-}

newtype Kernel a = Kernel { unKernel :: ErrorT KernelError (Reader Global) a }

instance Functor Kernel where
  fmap = liftM

instance Applicative Kernel where
  pure = return
  (<*>) = ap

instance Monad Kernel where
  return = Kernel . return
  (Kernel m) >>= k = Kernel $ m >>= \x -> unKernel (k x)

getGlobalBindings :: Kernel GlobalBindings
getGlobalBindings = Kernel $ gbindings <$> ask

getUniverseBindings :: Kernel UnivBindings
getUniverseBindings = Kernel $ ubindings <$> ask

typeError :: String -> [(LocalEnv, Term)] -> Kernel a
typeError s ts = Kernel $ throwError $ TypeError s ts

fatalError :: String -> Kernel a
fatalError s = Kernel $ throwError $ FatalError s

