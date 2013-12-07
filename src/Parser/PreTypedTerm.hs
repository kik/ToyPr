module Parser.PreTypedTerm where

import           Control.Applicative
import           Kernel.Term
import           Kernel.Universe
import           Parser.Token
import           Text.Parsec         hiding ((<|>), many)
import Data.List (elemIndex)
import Text.Parsec.Error (Message)

data PTTerm = PTUniv UnivExpr
            | PTVar String
            | PTHole (Maybe Int)
            | PTArrow PTTerm PTTerm
            | PTProd PTBinders PTTerm
            | PTAbs  PTBinders PTTerm
            | PTApp PTTerm PTTerm
            | PTEq PTTerm PTTerm PTTerm
            | PTRefl PTTerm PTTerm
            | PTEqInd PTTerm PTTerm PTTerm PTTerm PTTerm
            | PTImplicit

type PTBinders = [PTBinder]
data PTBinder  = PTBinder [String] PTTerm

univParser :: Parsec String () UnivExpr
univParser = whiteSpace >> goMax
  where
    goMax = goLift `chainl1` do { opOr; return UnivExprMax }
    goLift = do { x <- goVar
                ; xs <- many $ try $ do
                  { symbol "+"
                  ; decimal
                  }
                ; return $ foldl UnivExprLift x xs
                }
    goVar =  UnivExpr0 <$ symbol "0"
         <|> UnivExprVar <$> identifier
         <|> parens goMax

termParser :: Parsec String () PTTerm
termParser = whiteSpace >> goExpr
  where
    binder = binders <|>  fmap (:[]) binder1
    binder1 = PTBinder <$> many1 identifier <* symbol ":" <*> goExpr
    binders = many1 $ try $ parens binder1
    goExpr = go10
      where
        go10 = go4
        go4 = go3 `chainr1` do { opArrow; return PTArrow }
        go3 = do { x <- go2
                 ; option x (eq x <$ opEq <*> go2 <* opEqCoarse <*> go3)
                 }
          where eq x y a = PTEq a x y
        go2 = fmap (foldl1 PTApp) (many1 (try go1))
        go1 = goType
           <|> goForall
           <|> goFun
           <|> goEqRefl
           <|> goEqInd
           <|> goIdent
           <|> parens go10
        goType   = PTUniv . UnivExprVar <$ kType <*> identifier
        goForall = PTProd <$ kForall <*> binder <* symbol "," <*> go10
        goFun    = PTAbs <$ kFun <*> binder <* opMapsTo <*> go10
        goEqRefl = PTRefl <$ kEqRefl <*> go1 <*> go1
        goEqInd  = PTEqInd <$ kEqInd <*> go1 <*> go1 <*> go1 <*> go1 <*> go1
        goIdent  = do
          name <- identifier
          return $ if name == "_" then PTImplicit else PTVar name

toKernelTerm :: [Maybe String] -> PTTerm -> Maybe Term
toKernelTerm _ (PTUniv u) = Just $ TmUniv u
toKernelTerm e (PTVar s) =
  case elemIndex (Just s) e of
    Just i -> Just $ TmVar i
    Nothing -> Just $ TmConst s
toKernelTerm _ (PTHole (Just i)) = Just $ TmHole i
toKernelTerm e (PTArrow a b) = do
  a' <- toKernelTerm e a
  b' <- toKernelTerm e b
  Just $ TmProd Nothing a' (shift 1 b')
toKernelTerm e (PTProd [] body) = toKernelTerm e body
toKernelTerm e (PTProd (PTBinder [] _:bs) body) =
  toKernelTerm e (PTProd bs body)
toKernelTerm e (PTProd (PTBinder (name:names) ty:bs) body) = do
  ty' <- toKernelTerm e ty
  body' <- toKernelTerm (Just name:e) (PTProd (PTBinder names ty:bs) body)
  Just $ TmProd (Just name) ty' body'
toKernelTerm e (PTAbs [] body) = toKernelTerm e body
toKernelTerm e (PTAbs (PTBinder [] _:bs) body) =
  toKernelTerm e (PTAbs bs body)
toKernelTerm e (PTAbs (PTBinder (name:names) ty:bs) body) = do
  ty' <- toKernelTerm e ty
  body' <- toKernelTerm (Just name:e) (PTAbs (PTBinder names ty:bs) body)
  Just $ TmAbs (Just name) ty' body'
toKernelTerm e (PTApp f a) = do
  f' <- toKernelTerm e f
  a' <- toKernelTerm e a
  Just $ TmApp f' a'
toKernelTerm e (PTEq a x y) = do
  a' <- toKernelTerm e a
  x' <- toKernelTerm e x
  y' <- toKernelTerm e y
  Just $ TmEq a' x' y'
toKernelTerm e (PTRefl a x) = do
  a' <- toKernelTerm e a
  x' <- toKernelTerm e x
  Just $ TmRefl a' x'
toKernelTerm e (PTEqInd ct c x y p) = do
  ct' <- toKernelTerm e ct
  c' <- toKernelTerm e c
  x' <- toKernelTerm e x
  y' <- toKernelTerm e y
  p' <- toKernelTerm e p
  Just $ TmEqInd ct' c' x' y' p'
toKernelTerm _ _ = Nothing

 
runTypedTermParser :: String -> String -> [Maybe String] -> Either ParseError (Maybe Term)
runTypedTermParser fname input e = do
  t <- runParser parse () fname input
  return $ toKernelTerm e t
  where
    parse = do t <- termParser
               eof
               return t
 

