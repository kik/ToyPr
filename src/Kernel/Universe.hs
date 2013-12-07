module Kernel.Universe where

data UnivExpr = UnivExpr0
              | UnivExprLift UnivExpr Integer
              | UnivExprMax UnivExpr UnivExpr
              | UnivExprVar String
              deriving (Eq, Show)
