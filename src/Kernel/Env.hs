module Kernel.Env where

import Kernel.Universe
import Kernel.Term

data Binding = Decl Type
             | Def  Type Term

type UnivBindings = [(String, UnivExpr)]

type LocalEnv = [(Maybe String, Binding)]
type GlobalBindings = [(String, Binding)]
data Global = Global { gbindings :: GlobalBindings
                     , ubindings :: UnivBindings
                     }

lookupVar :: LocalEnv -> Int -> Maybe Binding
lookupVar e i = if 0 <= i && i < l then Just (snd (e!!i)) else Nothing
  where l = length e

lookupConst :: GlobalBindings -> String -> Maybe Binding
lookupConst g name = lookup name g

{-
showsLocalTerm :: LocalEnv -> Term -> ShowS
showsLocalTerm l = walk (10 :: Int) $ env l
  where
    env l' = foldr (\(n, _) e -> alpha e n:e) [] l'
    alpha e n = newName e $ maybe "t" id n
    newName e n = if elem n e then newName e $ n ++ "'" else n
    walk pr e t = case t of
      TmUniv i -> showString "Type " . shows i
      TmVar i | i < length e -> showString $ e!!i
              | otherwise -> showString "_var_" . shows i
      TmConst n -> showString "$" . showString n
      TmHole i -> showString "_" . shows i
      TmProd _ ty body | not (use 0 body) ->
        paren 4 $ walk 3 e ty . showString " -> " . walk 4 ("_":e) body
      TmProd _ _ _ ->
        paren 2 $ showString "forall " . prod e t
        where
          prod e' (TmProd n ty t'@(TmProd _ ty' body))
            | use 0 body && termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . prod (n':e') t'
            where n' = alpha e' n
          prod e' (TmProd n ty body) =
            showString n' . showString " : " . walk 10 e' ty . showString ", " . walk 10 (n':e') body
            where n' = alpha e' n
          prod _ _ = undefined
      TmAbs  _ _ _ ->
        paren 2 $ showString "fun " . abst e t
        where
          abst e' (TmAbs n ty t'@(TmAbs _ ty' _))
            | termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . abst (n':e') t'
            where n' = if use 0 t' then alpha e' n else "_"
          abst e' (TmAbs n ty body) =
            showString n' . showString " : " . walk 10 e' ty . showString " => " . walk 10 (n':e') body
            where n' = if use 0 body then alpha e' n else "_"
          abst _ _ = undefined
      TmApp t1 t2 -> paren 2 $ list [w 2 t1, w 1 t2]
      TmRefl a x -> paren 2 $ list [showString "eq_refl", w 1 a, w 1 x]
      TmEqInd ct c x y p -> paren 2 $ list $ showString "eq_ind" : map (w 1) [ct, c, x, y, p]
      TmEq a x y -> paren 3 $ list[w 2 x, showString "=", w 2 y, showString ":>", w 3 a]
      where
        w pr' = walk pr' e
        paren n s = showParen (pr < n) s
        list = foldr (.) id . intersperse (showChar ' ')

-}

data LocalTerm = LocalTerm LocalEnv Term

--instance Show LocalTerm where
--  showsPrec _ (LocalTerm e t) = showsLocalTerm e t
