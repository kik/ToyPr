module Parser.Token where

import Text.Parsec
import Text.Parsec.Token as P
import Control.Monad

toyprLang :: P.LanguageDef ()
toyprLang = P.LanguageDef
        { P.commentStart = "(*"
        , P.commentEnd = "*)"
        , P.commentLine = ""
        , P.nestedComments = True
        , P.identStart = letter <|> char '_'
        , P.identLetter = alphaNum <|> oneOf "_'"
        , P.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , P.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , P.reservedNames = words "Type forall fun eq_refl eq_ind"
        , P.reservedOpNames = words "-> => :> ="
        , P.caseSensitive = True
        }

toyprToken :: TokenParser ()        
toyprToken = makeTokenParser toyprLang

identifier :: Parsec String () String
identifier = P.identifier toyprToken

kType :: Parsec String () ()
kType = P.reserved toyprToken "Type"

kForall :: Parsec String () ()
kForall = P.reserved toyprToken "forall"

kFun :: Parsec String () ()
kFun = P.reserved toyprToken "fun"

kEqRefl :: Parsec String () ()
kEqRefl = P.reserved toyprToken "eq_refl"

kEqInd :: Parsec String () ()
kEqInd = P.reserved toyprToken "eq_ind"

opArrow :: Parsec String () ()
opArrow = P.reservedOp toyprToken "->"

opMapsTo :: Parsec String () ()
opMapsTo = P.reservedOp toyprToken "=>"

opEqCoarse :: Parsec String () ()
opEqCoarse = P.reservedOp toyprToken ":>"

opEq :: Parsec String () ()
opEq = P.reservedOp toyprToken "="

symbol :: String -> Parsec String () ()
symbol s = void $ P.symbol toyprToken s

parens :: Parsec String () a -> Parsec String () a
parens = P.parens toyprToken

whiteSpace :: Parsec String () ()
whiteSpace = P.whiteSpace toyprToken


