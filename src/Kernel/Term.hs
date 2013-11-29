module Kernel.Term where

import Kernel.Universe

data Term = TmUniv UnivExpr
          | TmVar Int
          | TmConst String
          | TmHole Int
          | TmProd (Maybe String) Type Term
          | TmAbs (Maybe String) Type Term
          | TmApp Term Term
          | TmEq Type Term Term
          | TmRefl Type Term
          | TmEqInd Type Term Term Term Term

type Type = Term

mapTerm :: (Term -> Int -> Term -> Term) -> Term -> Term
mapTerm f = go 0
  where
    go c t = f (dflt c t) c t
    dflt c (TmProd n ty body) = TmProd n (go c ty) (go (c+1) body)
    dflt c (TmAbs  n ty body) = TmAbs  n (go c ty) (go (c+1) body)
    dflt c (TmApp t1 t2) = TmApp (go c t1) (go c t2)
    dflt c (TmEq t1 t2 t3) = TmEq (go c t1) (go c t2) (go c t3)
    dflt c (TmRefl t1 t2) = TmRefl  (go c t1) (go c t2)
    dflt c (TmEqInd t1 t2 t3 t4 t5) = TmEqInd  (go c t1) (go c t2) (go c t3) (go c t4) (go c t5)
    dflt _ t = t

foldTerm :: r -> (r -> Int -> r -> Term -> r) -> Term -> r
foldTerm v f = go 0 v
  where
    go c a t = f (dflt c a t) c a t
    dflt c a (TmProd _ ty body) = go (c+1) (go c a ty) body
    dflt c a (TmAbs  _ ty body) = go (c+1) (go c a ty) body
    dflt c a (TmApp t1 t2) = go c (go c a t1) t2
    dflt c a (TmEq t1 t2 t3) = go c (go c (go c a t1) t2) t3
    dflt c a (TmRefl t1 t2) = go c (go c a t1) t2
    dflt c a (TmEqInd t1 t2 t3 t4 t5) = go c (go c (go c (go c (go c a t1) t2) t3) t4) t5
    dflt _ a _ = a

shift :: Int -> Term -> Term
shift d = mapTerm f
  where
    f _ c (TmVar i) | i >= c = TmVar (i + d)
    f _ _ (TmHole _) = error "unable to shift hole"
    f dflt _ _ = dflt

subst :: Int -> Term -> Term -> Term
subst j s = mapTerm f
  where
    f _ c (TmVar i) | i == j + c = shift c s
    f _ _ (TmHole _) = error "unable to subst hole"
    f dflt _ _ = dflt

pushSubst :: Term -> Term -> Term
pushSubst s t = shift (-1) $ subst 0 (shift 1 s) t

use :: Int -> Term -> Bool
use j = foldTerm False f
  where
    f _ _ True _ = True
    f _ c _ (TmVar i) | i == j + c = True
    f _ _ _ (TmHole _) = error "uname to test use hole"
    f dflt _ _ _ = dflt

termEqSyntactically :: Term -> Term -> Bool
termEqSyntactically t s = t === s
  where
    TmUniv i  === TmUniv j  = i == j
    TmVar i   === TmVar j   = i == j
    TmConst i === TmConst j = i == j
    TmHole  i === TmHole j  = i == j
    TmProd _ t1 t2 === TmProd _ s1 s2 = t1 === s1 && t2 === s2
    TmAbs  _ t1 t2 === TmAbs  _ s1 s2 = t1 === s1 && t2 === s2
    TmApp t1 t2 === TmApp s1 s2       = t1 === s1 && t2 === s2
    TmEq t1 t2 t3 === TmEq s1 s2 s3   = t1 === s1 && t2 === s2 && t3 === s3
    TmRefl t1 t2 === TmRefl s1 s2     = t1 === s1 && t2 === s2
    TmEqInd t1 t2 t3 t4 t5 === TmEqInd s1 s2 s3 s4 s5 =
      t1 === s1 && t2 === s2 && t3 === s3 && t4 === s4 && t5 === s5
    _ === _ = False

termPattern :: Int -> Term -> Term -> Term
termPattern i = walk 0
  where
    walk c s t | termEqSyntactically s t = TmVar $ i + c
    walk c s t = case t of
      TmProd n ty body -> TmProd n (w id ty) (w (+1) body)
      TmAbs  n ty body -> TmAbs  n (w id ty) (w (+1) body)      
      TmApp  t1 t2 -> TmApp (w id t1) (w id t2)
      TmEq t1 t2 t3 -> TmEq (w id t1) (w id t2) (w id t3)
      TmRefl t1 t2 -> TmRefl (w id t1) (w id t2)
      TmEqInd ct a x y p ->
        TmEqInd (w id ct) (w id a) (w id x) (w id y) (w id p)
      _ -> t
      where
        w f = walk (f c) (shift (f 0) s)

-- pattern s t = t' where [s/0]t' = t
pattern :: Term -> Term -> Term
pattern s t = termPattern 0 (shift 1 s) (shift 1 t)
