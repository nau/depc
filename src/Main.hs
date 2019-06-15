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
    -- let r = typecheckEnv (2, Rho [("Bool", VGen 1), ("Int", VGen 0)],
            -- Gamma [("Bool", VClosure (Rho []) Type), ("Int", VClosure (Rho []) Type)])
                -- (pp "λ a b -> a ") (pp "Int -> Bool -> Int")
    let defaultTEnv = do
            let decls = pd [s|
                        data Void = ;
                        data Bool = true | false;
                        data Nat = Z | S (n : Nat);
                        data List (A : U) = Nil | Cons (n : Nat) (t : List A);
                        data Id (A : U) (a : A) = refl (b : A);
                        efq : (C : U) -> Void -> C = \CC -> split (Void -> CC) {};
                        neg : (A : U) -> U = \A -> A -> Void;
                        explosion : (A : U) -> A -> neg A -> (B : U) -> B =
                            \AA a na B -> efq B (na a);
                        id : (A : U) -> A -> A = λ A a -> a;
                        append : (A : U) -> List A -> List A -> List A = \ A -> split (List A -> List A -> List A) {
                            Nil -> id (List A);
                            Cons x xs -> \ ys -> Cons x (append A xs ys);
                        };

                        reverse : (A : U) -> List A -> List A = \A -> split (List A -> List A) {
                            Nil -> Nil;
                            Cons x xs -> append A (reverse A xs) (Cons x Nil);
                        };

                        map : (A:U)->(B:U)->(f:A->B)->List A->List B = \A B f -> split (List A->List B ) {
                            Nil -> Nil;
                            Cons x xs -> Cons (f x) (map A B f xs);
                        };

                        not : Bool -> Bool = split (Bool -> Bool) { true -> false; false -> true; };
                        one : Nat = S Z;
                        two : Nat = S (S Z);
                        plus : Nat -> Nat -> Nat = split (Nat -> Nat -> Nat) {
                            Z -> λ n -> n ;
                            S m -> λ n -> S (plus m n);
                        };
                        three : Nat = plus two one;
                        four : Nat = plus three one;
                        modusPonens : (A : U) -> (B : U) -> (A -> B) -> A -> B = λ A B f a -> f a;

                    |]
            (ds, cons) <- runResolveDecls decls
            let tenv = initTEnv cons
            env1 <- runTyping tenv $ checkDecls ds
            -- traceM $ "After typing " ++ show env1
            let env = addDecls ds tenv
            -- traceShowM env
            return env
    case defaultTEnv of
        Right r@(_, rho, _, cons) -> do
            let ev = showEval cons rho
            -- putStrLn $ pprint rho
            putStrLn $ ev (pp "efq Void ")
            -- putStrLn $ ev (pp "plus two one")
            -- putStrLn $ ev (pp "not false")
            -- putStrLn $ ev (pp [s|
                -- map Nat Nat (λ n -> S n) (reverse Nat (append Nat (Cons one Nil) (Cons two Nil)))
                -- |])
        Left e -> putStrLn e
