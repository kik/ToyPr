module Parser.TypedTerm where

import Kernel.Universe
import Kernel.Term
import Kernel.Env
import Data.List
import Control.Applicative
import Control.Monad
import Text.Parsec hiding ((<|>))

type TermParser a = Parsec String () a

termParser :: [Maybe String] -> TermParser Term
termParser env = do { t <- goExpr env; eof; return t }
  where
    ident = try $ do { spaces
                     ; lookAhead $ letter <|> char '_'
                     ; many1 $ alphaNum <|> oneOf "_'"
                     }
    op s = try $ ops >>= \x -> if s == x then return () else mzero
    ops = do { spaces
             ; choice $ map (try . string) ["->", "=>", ":>", "(", ")", ",", ":", "="]
             }

    binder e body = binders [] e body <|> binder1 e body
    binder1 e body = do { names <- many1 ident
                        ; op ":"
                        ; ty <- goExpr e
                        ; let bs = [(name, shift i ty) | (i, name) <- zip [0..] names]
                              e' = foldl (\x y -> Just y : x) e names
                        ; body bs e'
                        }
    binders bs e body = do { op "("
                           ; binder1 e $ \bs' e' -> do { op ")"
                                                       ; binders (bs++bs') e' body
                                                         <|> body (bs++bs') e'
                                                       }
                           }
    goExpr e = go10
      where
        go10 = go4
        go4 = go3 `chainr1` do { op "->"; return $ \x y -> TmProd Nothing x (shift 1 y) }
        go3 = do { x <- go2
                 ; option x $ do { op "="
                                 ; y <- go2
                                 ; op ":>"
                                 ; a <- go3
                                 ; return $ TmEq a x y
                                 }
                 }
        go2 = many1 (try go1) >>= return . foldl1 TmApp
        go1 = do { v <- ident; goIdent v  }
              <|> do { between (op "(") (op ")") go10 }
        goIdent "Type0" = return $ TmUniv UnivExpr0
        goIdent "Type"  = do { name <- ident; return $ TmUniv (UnivExprVar name) }
        goIdent "forall" = binder e $ \bs e' -> do { op ","
                                                   ; body <- goExpr e'
                                                   ; return $ foldr (\(name, ty) b -> TmProd (Just name) ty b) body bs
                                                   }
        goIdent "fun"    = binder e $ \bs e' -> do { op "=>"
                                                   ; body <- goExpr e'
                                                   ; return $ foldr (\(name, ty) b -> TmAbs (Just name) ty b) body bs
                                                   }
        goIdent "eq_refl" = TmRefl <$> go1 <*> go1
        goIdent "eq_ind" = TmEqInd <$> go1 <*> go1 <*> go1 <*> go1 <*> go1
        goIdent n = case elemIndex (Just n) e of
          Just i -> return $ TmVar i
          Nothing -> return $ TmConst n

showsTerm :: LocalEnv -> Term -> ShowS
showsTerm l = walk 10 $ env l
  where
    env l = foldr (\(n, _) e -> alpha e n:e) [] l
    alpha e n = newName e $ maybe "t" id n
    newName e n = if elem n e then newName e $ n ++ "'" else n
    walk pr e t = case t of
      TmUniv i -> showString "Type " . shows i
      TmVar i | i < length e -> showString $ e!!i
              | otherwise -> showString "_var_" . shows i
      TmConst n -> showString "$" . showString n
      TmHole i -> showString "_" . shows i
      TmProd n ty body | not (use 0 body) ->
        paren 4 $ walk 3 e ty . showString " -> " . walk 4 ("_":e) body
      TmProd _ _ _ ->
        paren 2 $ showString "forall " . prod e t
        where
          prod e (TmProd n ty t@(TmProd _ ty' body))
            | use 0 body && termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . prod (n':e) t
            where n' = alpha e n
          prod e (TmProd n ty body) =
            showString n' . showString " : " . walk 10 e ty . showString ", " . walk 10 (n':e) body
            where n' = alpha e n
          prod _ _ = undefined
      TmAbs  _ _ _ ->
        paren 2 $ showString "fun " . abs e t
        where
          abs e (TmAbs n ty t@(TmAbs _ ty' body))
            | termEqSyntactically (shift 1 ty) ty' =
              showString n' . showString " " . abs (n':e) t
            where n' = if use 0 t then alpha e n else "_"
          abs e (TmAbs n ty body) =
            showString n' . showString " : " . walk 10 e ty . showString " => " . walk 10 (n':e) body
            where n' = if use 0 body then alpha e n else "_"
      TmApp t1 t2 -> paren 2 $ list [w 2 t1, w 1 t2]
      TmRefl a x -> paren 2 $ list [showString "eq_refl", w 1 a, w 1 x]
      TmEqInd ct c x y p -> paren 2 $ list $ showString "eq_ind" : map (w 1) [ct, c, x, y, p]
      TmEq a x y -> paren 3 $ list[w 2 x, showString "=", w 2 y, showString ":>", w 3 a]
      where
        w pr = walk pr e
        paren n s = showParen (pr < n) s
        list = foldr (.) id . intersperse (showChar ' ')

runTypedTermParser :: String -> String -> [Maybe String] -> Either ParseError Term
runTypedTermParser fname input e = runParser (termParser e) () fname input

