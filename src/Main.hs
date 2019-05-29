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
import Core
import Parser

(==>) = Pi "_"
infixr ==>

prove t p = if typecheck p t
    then putStrLn $ "Theorem " ++ show t ++ "\nQED."
    else putStrLn "Error"

main :: IO ()
main = do
    print $ pp "a"
    print $ pp "a (b c) d"
    print $ pp "a (λ b -> c c (d d))"
    print $ pp "A -> (B x -> U) -> D"
    print $ pp "(A : U) -> B"
    print $ pp "(A : U) -> (x : A) -> (P : A -> U) -> P x"
    print $ pp " λ A -> λ x -> λ y -> x y"
    print $ pp " λ A x y -> x y"
    let proof = pp "λ A x y -> x y"
        theorem = pp "(A : U) -> (A -> A) -> A -> A"
    prove theorem proof