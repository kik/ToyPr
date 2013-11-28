{-# LANGUAGE TupleSections #-}
module Kernel.TypeCheck where

import Kernel.Universe
import Kernel.Term
import Kernel.Env
import Kernel.KernelMonad
import Kernel.Reduce
import Kernel.Conversion
import Control.Applicative
import Control.Monad.Reader

typeofBinding :: Binding -> Type
typeofBinding (Decl ty)  = ty
typeofBinding (Def ty _) = ty

reduceToUniverse :: LocalEnv -> Term -> Kernel UnivExpr
reduceToUniverse e t = reduceFull e t >>= go
  where go (TmUniv i) = return i
        go t' = typeError "not universe" [(e, t')]

assertUniverse :: LocalEnv -> Term -> Kernel ()
assertUniverse e t = void $ reduceToUniverse e t

typeofType :: LocalEnv -> Term -> Kernel UnivExpr
typeofType e t = reduceToUniverse e =<< typeof e t

assertType :: LocalEnv -> Term -> Kernel ()
assertType e t = void $ typeofType e t

univOfProd :: UnivExpr -> UnivExpr -> Kernel UnivExpr
univOfProd u1 u2 = return $ UnivExprMax u1 u2

univSucc :: UnivExpr -> UnivExpr
univSucc (UnivExprLift u i) = UnivExprLift u (i + 1)
univSucc (UnivExprMax u1 u2) = UnivExprMax (univSucc u1) (univSucc u2)
univSucc u = UnivExprLift u 1

-- e |- t : ty
typeCheck :: LocalEnv -> Term -> Term -> Kernel ()
typeCheck e t ty = do tty <- typeof e t
                      b <- convertible e tty ty
                      unless b $ typeError "typecheck error" [(e, t), (e, ty)]

typeof :: LocalEnv -> Term -> Kernel Type
typeof e = to
  where
    to (TmUniv u) = return $ TmUniv $ univSucc u
    to (TmVar i) =
      case lookupVar e i of
          Nothing -> fatalError "unbound variable"
          Just b -> return $ shift (i+1) $ typeofBinding b
    to (TmConst name) = do
      g <- getGlobalBindings
      case lookupConst g name of
          Nothing -> fatalError "unbound variable"
          Just b -> return $ typeofBinding b
    to (TmHole _) = fatalError "typeof Hole"
    to (TmProd n ty body) = do uty   <- typeofType e ty
                               ubody <- typeofType ((n, Decl ty):e) body
                               TmUniv <$> (univOfProd uty ubody)
    to (TmAbs n ty body)  = do assertType e ty
                               tbody <- typeof ((n, Decl ty):e) body
                               return $ TmProd n ty tbody
    to (TmApp t1 t2) = do tt1 <- to t1
                          case tt1 of
                            TmProd _ ty body -> do
                              typeCheck e t2 ty
                              return $ pushSubst t2 body
                            _ -> typeError "not applicative" [(e, t1)]
    to (TmEq a x y) = do ta <- to a
                         ua <- reduceToUniverse e ta
                         typeCheck e x a
                         typeCheck e y a
                         return $ TmUniv ua
    to (TmRefl a x) = do assertType e a
                         typeCheck e x a
                         return $ TmEq a x x
    to (TmEqInd ct c x y p) = do
      a  <- to x
      typeCheck e x a
      typeCheck e y a
      typeCheck e p $ TmEq a x y
      -- e, x:A, y:A, p:A |- ct x y p : U
      let e' = map (Nothing,) [Decl (TmEq (shift 2 a) (TmVar 1) (TmVar 0)), Decl (shift 1 a), Decl (shift 0 a)] ++ e
      assertType e' (TmApp (TmApp (TmApp (shift 3 ct) (TmVar 2)) (TmVar 1)) (TmVar 0))
      -- e, z:A |- c z : ct z z (refl z)
      let e'' = (Nothing, Decl a):e
      let cz = TmApp (TmApp (TmApp (shift 1 ct) (TmVar 0)) (TmVar 0)) (TmRefl (shift 1 a) (TmVar 0))
      typeCheck e'' (TmApp (shift 1 c) (TmVar 0)) cz
      -- ct x y p
      return $ TmApp (TmApp (TmApp ct x) y) p


