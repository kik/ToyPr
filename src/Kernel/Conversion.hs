module Kernel.Conversion where

import Kernel.Universe
import Kernel.Term
import Kernel.Env
import Kernel.KernelMonad
import Kernel.Reduce
import Control.Applicative

universeLe :: UnivExpr -> UnivExpr -> Kernel Bool
universeLe = go 0
  where
    go n UnivExpr0 UnivExpr0 | n >= 0 = return True
    go n (UnivExprVar v1) (UnivExprVar v2) | n >= 0 && v1 == v2 = return True
    go n (UnivExprMax u v) w =
      (&&) <$> go n u w <*> go n v w
    go n (UnivExprLift u i) v = go (n - i) u v
    go n u (UnivExprLift v i) = go (n + i) u v
    go n u (UnivExprVar v) = do ub <- getUniverseBindings
                                case lookup v ub of
                                  Nothing -> fatalError $ "not declared universe: " ++ v
                                  Just w -> go n u w
    go n u (UnivExprMax v w) =
      (||) <$> go n u v <*> go n u w
    go _ _ _ = return False

universeEq :: UnivExpr -> UnivExpr -> Kernel Bool
universeEq u1 u2 = (&&) <$> universeLe u1 u2 <*> universeLe u2 u1

-- e |- t1 <: t2
convertible :: LocalEnv -> Term -> Term -> Kernel Bool
convertible e t1 t2 = do t1' <- reduceFull e t1
                         t2' <- reduceFull e t2
                         go False t1' t2'
  where
    go True  (TmUniv u1) (TmUniv u2) = u1 `universeEq` u2
    go False (TmUniv u1) (TmUniv u2) = u1 `universeLe` u2
    go _ (TmVar v1) (TmVar v2) = return $ v1 == v2
    go _ (TmConst v1) (TmConst v2) = return $ v1 == v2
    go eq (TmProd _ ty1 body1) (TmProd _ ty2 body2) =
      ands [go True ty1 ty2, go eq body1 body2]
    go eq (TmAbs _ ty1 body1) (TmAbs _ ty2 body2) =
      ands [go True ty1 ty2, go eq body1 body2]
    go eq (TmApp f1 a1) (TmApp f2 a2) =
      ands [go eq f1 f2, go True a1 a2]
    go _ (TmEq a1 x1 y1) (TmEq a2 x2 y2) =
      ands [go True a1 a2, go True x1 x2, go True y1 y2]
    go _ (TmRefl a1 x1) (TmRefl a2 x2) =
      ands [go True a1 a2, go True x1 x2]
    go _ (TmEqInd ct1 c1 x1 y1 p1) (TmEqInd ct2 c2 x2 y2 p2) =
      ands [go True ct1 ct2, go True c1 c2, go True x1 x2, go True y1 y2, go True p1 p2]
    go _ _ _ = return False
    ands = fmap and . sequence

