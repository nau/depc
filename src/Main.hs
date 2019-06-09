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
    print $ pprint $ eval (Rho [("Int", VType)]) (pp [s| (λ x -> x) Int |])

main :: IO ()
main = do
    -- theorems
    -- let r = typecheckEnv (2, Rho [("Bool", VGen 1), ("Int", VGen 0)],
            -- Gamma [("Bool", VClosure (Rho []) Type), ("Int", VClosure (Rho []) Type)])
                -- (pp "λ a b -> a ") (pp "Int -> Bool -> Int")
    let defaultTEnv = do
            let decls = pd [s|
                                        data Bool = true : Bool | false : Bool;
                                        data Nat = Z : Nat | S : Nat -> Nat;
                                        id : (A : U) -> A -> A = \ A a -> a;
                                        asdf : Bool -> Bool = \ x -> false;
                                        one : Nat = S Z;
                                        two : Nat = S (S Z);
                                        plus : Nat -> Nat -> Nat = split (Nat -> Nat -> Nat) {
                                            Z -> \ n -> n ;
                                            S m -> \ n -> S (plus m n);
                                        };
                                        four : Nat = plus (S Z) Z;
                                        modusPonens : (A : U) -> (B : U) -> (A -> B) -> A -> B = λ A B f a -> f a;
                                    |]
            case runResolver $ resolveDecls decls of
                Left _ -> error "AAA"
                Right (ds, cons) -> Right (initTEnv cons) -- addDecls (initTEnv cons) ds
    -- putStrLn "Test"
    case defaultTEnv of
        Right r@(_, rho, _, _) -> do
            putStrLn $ pprint rho
            putStrLn $ pprint $ rho --eval rho $ pp "four"
        Left e -> putStrLn e
