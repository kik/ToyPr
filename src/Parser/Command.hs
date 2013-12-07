module Parser.Command where

import Kernel
import Parser.Token
import Parser.PreTypedTerm
import Text.Parsec


pIdent :: Parsec String () String
pIdent = identifier

pTerm :: Parsec String () PTTerm
pTerm = termParser

pUniv :: Parsec String () UnivExpr
pUniv = univParser
