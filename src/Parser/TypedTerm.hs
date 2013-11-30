module Parser.TypedTerm where

import Kernel.Universe (UnivExpr (UnivExprVar))
import Kernel.Term (shift, Term (TmAbs, TmApp, TmConst, TmEq, TmEqInd, TmHole, TmProd, TmRefl, TmUniv, TmVar), termEqSyntactically, use)
import Kernel.Env (LocalEnv)
import Parser.Token (identifier, kEqInd, kEqRefl, kForall, kFun, kType, opArrow, opEq, opEqCoarse, opMapsTo, parens, symbol, whiteSpace)
import Data.List (elemIndex, intersperse)
import Control.Applicative ((<$), (<*), (<*>), (<|>))
import Control.Monad (liftM, mzero, unless)
import Text.Parsec (alphaNum, between, chainr1, char, choice, eof, letter, lookAhead, many1, oneOf, option, Parsec, ParseError, runParser, spaces, string, try)
import Data.Maybe (fromMaybe)

type TermParser a = Parsec String () a

termParser :: [Maybe String] -> TermParser Term
termParser env = whiteSpace >> goExpr env
  where
    binder e body = binders [] e body <|> binder1 e body
    binder1 e body = do { names <- many1 identifier
                        ; symbol ":"
                        ; ty <- goExpr e
                        ; let bs = [(name, shift i ty) | (i, name) <- zip [0..] names]
                              e' = foldl (\x y -> Just y : x) e names
                        ; body bs e'
                        }
    binders bs e body = do { symbol "("
                           ; binder1 e $ \bs' e' -> do { symbol ")"
                                                       ; binders (bs++bs') e' body
                                                         <|> body (bs++bs') e'
                                                       }
                           }
    goExpr e = go10
      where
        go10 = go4
        go4 = go3 `chainr1` do { opArrow; return arr }
          where arr x y = TmProd Nothing x (shift 1 y)
        go3 = do { x <- go2
                 ; option x (eq x <$ opEq <*> go2 <* opEqCoarse <*> go3)
                 }
          where eq x y a = TmEq a x y
        go2 = liftM (foldl1 TmApp) (many1 (try go1))
        go1 = goType
           <|> goForall
           <|> goFun
           <|> goEqRefl
           <|> goEqInd
           <|> goIdent
           <|> parens go10
        goType = TmUniv . UnivExprVar <$ kType <*> identifier
        goForall = do
          kForall
          binder e $ \bs e' -> do { symbol ","
                                  ; body <- goExpr e'
                                  ; return $ foldr (\(name, ty) b -> TmProd (Just name) ty b) body bs
                                  }
        goFun = do
          kFun
          binder e $ \bs e' -> do { opMapsTo
                                  ; body <- goExpr e'
                                  ; return $ foldr (\(name, ty) b -> TmAbs (Just name) ty b) body bs
                                  }
        goEqRefl = TmRefl <$ kEqRefl <*> go1 <*> go1
        goEqInd = TmEqInd <$ kEqInd <*> go1 <*> go1 <*> go1 <*> go1 <*> go1
        goIdent = do
          n <- identifier
          case elemIndex (Just n) e of
            Just i -> return $ TmVar i
            Nothing -> return $ TmConst n

showsTerm :: LocalEnv -> Term -> ShowS
showsTerm l = walk (10 :: Int) $ env l
  where
    env = foldr (\ (n, _) e -> alpha e n : e) []
    alpha e n = newName e $ fromMaybe "t" n
    newName e n = if n `elem` e then newName e $ n ++ "'" else n
    walk pr e t = case t of
      TmUniv i -> showString "Type " . shows i
      TmVar i | i < length e -> showString $ e!!i
              | otherwise -> showString "_var_" . shows i
      TmConst n -> showString "$" . showString n
      TmHole i -> showString "_" . shows i
      TmProd _ ty body | not (use 0 body) ->
        paren 4 $ walk 3 e ty . showString " -> " . walk 4 ("_":e) body
      TmProd {} ->
        paren 2 $ showString "forall " . prod e t
        where
          prod e' (TmProd n ty tb@(TmProd _ ty' body))
            | use 0 body && termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . prod (n':e') tb
            where n' = alpha e' n
          prod e' (TmProd n ty body) =
            showString n' . showString " : " . walk 10 e' ty . showString ", " . walk 10 (n':e') body
            where n' = alpha e' n
          prod _ _ = undefined
      TmAbs {} ->
        paren 2 $ showString "fun " . abst e t
        where
          abst e' (TmAbs n ty tb@(TmAbs _ ty' _))
            | termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . abst (n':e') tb
            where n' = if use 0 tb then alpha e' n else "_"
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
        paren n = showParen (pr < n)
        list = foldr (.) id . intersperse (showChar ' ')

runTypedTermParser :: String -> String -> [Maybe String] -> Either ParseError Term
runTypedTermParser fname input e = runParser parse () fname input
  where
    parse = do t <- termParser e
               eof
               return t


