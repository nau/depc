{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Data.List as List
import Data.Maybe
import Data.String
import Data.Void
import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text.Prettyprint.Doc
import Core
import Parser

pprint exp = show $ pretty (PExpr 0 exp)

prove t p = if typecheck p t
    then do
        putStrLn $ "Theorem " ++ pprint t
        putStrLn "Proof."
        putStrLn $ pprint p
        putStrLn "QED."
    else putStrLn "Error"

main :: IO ()
main = do
    let p s = do
            let exp = pp s
            putStrLn s
            print exp
            let ss = pprint exp
            putStrLn $ ss ++ " ==> " ++ show (pp ss == exp)
            putStrLn ""
    p "a (b (c (d e f))) g"
    p "a (λ b -> c c (d d))"
    p "A -> (B x -> U) -> D"
    p "(A : U) -> B"
    p "(A : U) -> (x : A) -> (P : A -> U) -> P x"
    p "λ A -> λ x -> λ y -> a (λ b -> c c (d d))"
    p " λ A x y -> x y"
    let proof = pp "λ A x y -> x y"
        theorem = pp "(A : U) -> (A -> A) -> A -> A"
    prove theorem proof