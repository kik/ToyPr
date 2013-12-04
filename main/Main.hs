module Main where

import Kernel
import Prover.ProofState
import Prover.Goal
import Parser.PreTypedTerm
import Parser.InputLine
import Data.IORef
import Control.Monad.Reader
import System.Console.Haskeline
import Control.Applicative hiding (many)
import Text.Parsec hiding ((<|>))

type InputParser a = Parsec String () a


        

main :: IO ()
main = do g <- initGlobal
          --mod_eq g
          runInputT defaultSettings (loop g)
  where
    loop :: IORef GlobalState -> InputT IO ()
    loop g = do
      minput <- getInputLine "ToyPr> "
      case minput of
        Nothing -> return ()
        Just "quit" -> return ()
        Just input -> do outputStrLn $ "Input was: " ++ input
                         let input' = splitInput input
                         outputStrLn $ "Input was: " ++ show input'
                         loop g

{-# ANN mod_eq "HLint: ignore" #-}
mod_eq :: IORef GlobalState -> IO ()
mod_eq g = flip runReaderT g $ do
  uvar "eq" UnivExpr0
  
  lemma "eq_sym" `p` "forall (A : Type eq) (x y : A), x = y :> A -> y = x :> A"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl A x'"
  qed

  --compute "fun A : Type eq => fun x : A => eq_sym A x x (eq_refl A x)"

  lemma "eq_trans" `p` "forall (A : Type eq) (x y z : A), x = y :> A -> y = z :> A -> x = z :> A"
  introsw "A x y z p"
  elim_eq "x'" `p` "p"
  intro "q"
  elim_eq "y'" `p` "q"
  exact `p` "eq_refl A y'"
  qed

  --compute "fun A : Type eq => fun x : A => eq_trans A x x x (eq_refl A x) (eq_refl A x)"

  lemma "path_o_refl" `p` "forall (A : Type eq) (x y : A) (p : x = y :> A), p = eq_trans A x y y p (eq_refl A y) :> (x = y :> A)"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl (x' = x' :> A) (eq_refl A x')"
  qed

  lemma "refl_o_path" `p` "forall (A : Type eq) (x y : A) (p : x = y :> A), p = eq_trans A x x y (eq_refl A x) p :> (x = y :> A)"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl (x' = x' :> A) (eq_refl A x')"
  qed

  lemma "inv_o_path" `p` "forall (A : Type eq) (x y : A) (p : x = y :> A), eq_trans A y x y (eq_sym A x y p) p = eq_refl A y :> (y = y :> A)"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl (x' = x' :> A) (eq_refl A x')"
  qed

  lemma "path_o_inv" `p` "forall (A : Type eq) (x y : A) (p : x = y :> A), eq_trans A x y x p (eq_sym A x y p) = eq_refl A x :> (x = x :> A)"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl (x' = x' :> A) (eq_refl A x')"
  qed

  lemma "inv_inv" `p` "forall (A : Type eq) (x y : A) (p : x = y :> A), eq_sym A y x (eq_sym A x y p) = p :> (x = y :> A)"
  introsw "A x y p"
  elim_eq "x'" `p` "p"
  exact `p` "eq_refl (x' = x' :> A) (eq_refl A x')"
  qed

  lemma "o_assoc" `p` "forall (A : Type eq) (x y z w : A) (p : x = y :> A) (q : y = z :> A) (r : z = w :> A), eq_trans A x y w p (eq_trans A y z w q r) = eq_trans A x z w (eq_trans A x y z p q) r :> (x = w :> A)"
  introsw "A x y z w p"
  elim_eq "x'" `p` "p"
  intro "q"
  elim_eq "y'" `p` "q"
  intro "r"
  elim_eq "z'" `p` "r"
  exact `p` "eq_refl (z' = z' :> A) (eq_refl A z')"
  qed

  lemma
    "whisker_r" `p` 
    ("forall (A : Type eq) (a b c : A) (r : b = c :> A) (p q : a = b :> A) (alpha : p = q :> a = b :> A), "
     ++ "eq_trans A a b c p r = eq_trans A a b c q r :> a = c :> A")
  introsw "A a b c r"
  elim_eq "x" `p` "r"
  introsw "p q alpha"

  trans `p` "q"
  trans `p` "p"
  sym
  exact `p` "path_o_refl A a x p"
  exact `p` "alpha"
  exact `p` "path_o_refl A a x q"
  qed

  lemma
    "whisker_l" `p` 
    ("forall (A : Type eq) (a b c : A) (q : a = b :> A) (r s : b = c :> A) (beta : r = s :> b = c :> A), "
     ++ "eq_trans A a b c q r = eq_trans A a b c q s :> a = c :> A")
  introsw "A a b c q"
  elim_eq "x" `p` "q"
  introsw "r s beta"

  trans `p` "s"
  trans `p` "r"
  sym
  exact `p` "refl_o_path A x c r"
  exact `p` "beta"
  exact `p` "refl_o_path A x c s"
  qed

  lemma
    "whisker_r_refl" `p` 
    ("forall (A : Type eq) (a : A) (alpha : eq_refl A a = eq_refl A a :> a = a :> A), "
     ++ "alpha = whisker_r A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) alpha :> eq_refl A a = eq_refl A a :> a = a :> A")
  introsw "A a alpha"

  trans `p` "eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) (eq_refl (a = a :> A) (eq_refl A a)) alpha"
  exact `p` "refl_o_path (a = a :> A) (eq_refl A a) (eq_refl A a) alpha"
  exact `p` "path_o_refl (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) (eq_refl (a = a :> A) (eq_refl A a)) alpha)"
  qed

  lemma
    "whisker_l_refl" `p` 
    ("forall (A : Type eq) (a : A) (beta : eq_refl A a = eq_refl A a :> a = a :> A), "
     ++ "beta = whisker_l A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) beta :> eq_refl A a = eq_refl A a :> a = a :> A")
  introsw "A a beta"

  trans `p` "eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) (eq_refl (a = a :> A) (eq_refl A a)) beta"
  exact `p` "refl_o_path (a = a :> A) (eq_refl A a) (eq_refl A a) beta"
  exact `p` "path_o_refl (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) (eq_refl (a = a :> A) (eq_refl A a)) beta)"
  qed

  lemma
    "whisker_rl_lr" `p` 
    ("forall (A : Type eq) (a b c : A) (p q : a = b :> A) (alpha : p = q :> a = b :> A) "
     ++ "(r s : b = c :> A) (beta : r = s :> b = c :> A), "
     ++ "eq_trans (a = c :> A) "
     ++   "(eq_trans A a b c p r) "
     ++   "(eq_trans A a b c q r) "
     ++   "(eq_trans A a b c q s) "
     ++   "(whisker_r A a b c r p q alpha) (whisker_l A a b c q r s beta) ="
     ++ "eq_trans (a = c :> A) "
     ++   "(eq_trans A a b c p r) "
     ++   "(eq_trans A a b c p s) "
     ++   "(eq_trans A a b c q s) "
     ++   "(whisker_l A a b c p r s beta)  (whisker_r A a b c s p q alpha) "
     ++ ":> eq_trans A a b c p r = eq_trans A a b c q s :> a = c :> A")
  introsw "A a b c p q alpha"
  elim_eq "p'" `p` "alpha"
  elim_eq "a'" `p` "p'"
  introsw "r s beta"
  elim_eq "r'" `p` "beta"
  elim_eq "b'" `p` "r'"
  exact `p` "eq_refl (eq_refl A b' = eq_refl A b' :> b' = b' :> A) (eq_refl (b' = b' :> A) (eq_refl A b'))"
  qed

  lemma "Eckmann_Hilton" `p` 
    ("forall (A : Type eq) (a : A) "
     ++ "(alpha : eq_refl A a = eq_refl A a :> a = a :> A)"
     ++ "(beta  : eq_refl A a = eq_refl A a :> a = a :> A), "
     ++ "eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) alpha beta = "
     ++ "eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) beta alpha :> eq_refl A a = eq_refl A a :> a = a :> A")
  introsw "A a alpha beta"

  trans `p` ("eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) alpha "
         ++ "(whisker_l A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) beta)")
  f_equal_2
  exact `p` "whisker_l_refl A a beta"
  trans `p` ("eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) "
         ++ "(whisker_r A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) alpha) "
         ++ "(whisker_l A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) beta)")
  f_equal_1
  f_equal_2
  exact `p` "whisker_r_refl A a alpha"

  trans `p` ("eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) "
         ++ "(whisker_l A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) beta) "
         ++ "(whisker_r A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) alpha)")
  exact `p` "whisker_rl_lr A a a a (eq_refl A a) (eq_refl A a) alpha (eq_refl A a) (eq_refl A a) beta"

  trans `p` ("eq_trans (a = a :> A) (eq_refl A a) (eq_refl A a) (eq_refl A a) "
         ++ "(whisker_l A a a a (eq_refl A a) (eq_refl A a) (eq_refl A a) beta) "
         ++ "alpha")
  f_equal_2
  sym
  exact `p` "whisker_r_refl A a alpha"
  f_equal_1
  f_equal_2
  sym
  exact `p` "whisker_l_refl A a beta"
  qed
  where
    p :: (PTTerm -> ProverCommand ()) -> String -> ProverCommand ()
    p f s = do
      t <- parsePTTerm s
      f t

