module Parser.InputLine where

import Control.Monad (void)
import Text.Parsec (anyChar, char, many, manyTill, runParser, space, try)

splitInput :: String -> ([String], String)
splitInput input = case runParser inp () "" (input ++ "\n") of
                     Left _ -> ([], input)
                     Right r -> r
  where
    inp = do cs <- many (try sentense)
             rest <- many anyChar
             return (cs, rest)
    sentense = manyTill anyChar fullstop
    fullstop = try $ do void $ char '.'
                        space
