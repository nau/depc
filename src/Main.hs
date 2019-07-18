{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
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
import Debug.Trace
import Core
import Parser

prove t p = case typecheck p t of
    Right _ -> do
        putStrLn $ "Theorem " ++ pprint t
        putStrLn $ pprint p
        putStrLn "QED."
    Left err -> putStrLn $ show $ "Error: " <+> pretty err <+> " in theorem " <+> pretty t

theorems = do
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
    p [s| λ A x y -> x y |]
    p [s| let a : U = U in let b : U -> U = λ x -> x in b a |]
    let proof = pp "λ A x y -> x y"
    let theorem = pp "(A : U) -> (A -> A) -> A -> A"
    prove theorem proof
    prove (pp "(A : U) -> (F : A -> U) -> U") (pp "λ A F -> A")
    prove (pp "(Int : U) -> Int -> Int") (pp "λ Int a -> a")
    prove (pp "(A : U) -> (List : U -> U) -> (single : A -> List A) -> A -> List A") (pp "λ a Ls cons l -> cons l")
    print $ pprint $ eval (V "Int" VType Empty) (pp [s| (λ x -> x) Int |])

showEval :: Constructors -> Rho -> Expr -> String
showEval cons rho expr = case runResolver (resolve expr) cons of
    Right e -> show $ pretty (eval rho e)
    Left  e -> e



main :: IO ()
main = do
    -- theorems
    r <- parseFile "Examples.depc"
    let defaultTEnv = do
            let decls = case r of
                    Left err -> error $ parseErrorPretty err
                    Right (Right expr) -> error "Want decls"
                    Right (Left decls) -> decls
            (ds, cons) <- runResolveDecls decls
            let tenv = initTEnv
            runTyping tenv $ checkDecls ds
            traceShowM "TYPING COMPLETE!"
            let env = addDecls ds tenv
            return (env, cons)
    case defaultTEnv of
        Right r@((_, rho, _), cons) -> do
            let ev = showEval cons rho
            putStrLn $ ev (pp "main")
        Left e -> putStrLn e
