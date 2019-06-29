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
    theorems
    let defaultTEnv = do
            let decls = pd [s|
            data Void = ;
            data Unit = unit : Unit;
            data Bool = true : Bool | false : Bool;
            data Nat = Z : Nat | S (n : Nat) : Nat;
            zero : Nat = Z;
            one : Nat = S zero;
            data List (A : U) = Nil : List A | Cons (e : A) (t : List A) : List A;
            length (A : U) : List A -> Nat = split (List A -> Nat) {
                Nil -> Z;
                Cons e t -> S (length A t)
            };
            data Sigma (A : U) (B : A -> U) = Pair (x : A) (y : B x) : Sigma A B;
            data Vec (n : Nat) (A : U) =
                VNil : Vec Z A |
                VCons (elem : A) (k : Nat) (tail : Vec k A) : Vec (S k) A;
            data Id (A : U) (a : A) (b : A) = refl : Id A a a;
            empty : Vec Z Bool = VNil;
            single : Vec (S Z) Bool = VCons true (Z) empty;
            exists (A : U) (B : A -> U) : U = Sigma A B;
            ∃ : (A : U) -> (B : A -> U) -> U = exists;
            Tuple (A : U) (B : U) : U = Sigma A (\x -> B);
            gtZ : Nat -> U = split (Nat -> U) { Z -> Void ; S x -> Unit };
            existsNatGtZ : ∃ Nat gtZ = Pair (S Z) (unit);
            tuple : Tuple Bool Nat = Pair false (S Z);
            id (A : U) (a : A) : A = a;
            neg (A : U) : U = A -> Void;
            ¬ : (A : U) -> U = neg;
            efq (C : U) : Void -> C = split (Void -> C) {};
            natOrListBool : Nat -> U = split (Nat -> U) { Z -> Unit; S n -> List Bool };
            u : natOrListBool Z = unit;
            lb : natOrListBool (S Z) = Cons true Nil;
            explosion (A : U) (a : A) (na : ¬ A) (B : U) : B = efq B (na a);
            append (A : U) : List A -> List A -> List A = split (List A -> List A -> List A) {
                Nil -> id (List A);
                Cons x xs -> λ ys -> Cons x (append A xs ys);
            };

            reverse (A : U) : List A -> List A = split (List A -> List A) {
                Nil -> Nil;
                Cons x xs -> append A (reverse A xs) (Cons x Nil);
            };

            map (A : U) (B : U) (f : A -> B) : List A -> List B = split (List A -> List B) {
                Nil -> Nil;
                Cons x xs -> Cons (f x) (map A B f xs);
            };

            not : Bool -> Bool = split (Bool -> Bool) { true -> false; false -> true };
            one : Nat = S Z;
            two : Nat = S (S Z);
            plus : Nat -> Nat -> Nat = split (Nat -> Nat -> Nat) {
                Z -> λ n -> n ;
                S m -> λ n -> S (plus m n);
            };
            three : Nat = plus two one;
            four : Nat = plus three one;
            twoPlusTwoEqFour : Id Nat (plus two two) four = refl;
            modusPonens (A : U) (B : U) (f : A -> B) (a : A) : B = f a;
            vfill (A : U) (a : A) : (m : Nat) -> Vec m A = split ((m : Nat) -> Vec m A) {
                Z -> VNil;
                S k -> VCons a k (vfill A a k);
            };

                    |]
            (ds, cons) <- runResolveDecls decls
            let tenv = initTEnv
            runTyping tenv $ checkDecls ds
            traceShowM "TYPING COMPLETE!"
            let env = addDecls ds tenv
            return (env, cons)
    case defaultTEnv of
        Right r@((_, rho, _), cons) -> do
            let ev = showEval cons rho
            -- putStrLn $ pprint rho
            putStrLn $ ev (pp "vfill Bool true two")
            putStrLn $ ev (pp "not false")
            putStrLn $ ev (pp "existsNatGtZ")
            putStrLn $ ev (pp "tuple")
            putStrLn $ ev (pp [s|
                map Nat Nat (λ n -> S n) (reverse Nat (append Nat (Cons one Nil) (Cons two Nil)))
                |])
        Left e -> putStrLn e
