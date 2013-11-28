module Kernel.Universe where

data UnivExpr = UnivExpr0
              | UnivExprLift UnivExpr Int
              | UnivExprMax UnivExpr UnivExpr
              | UnivExprVar String
              deriving (Eq, Show)
