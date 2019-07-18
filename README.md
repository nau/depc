# Simple Dependent Type Checker

Normalization by Evaluation type checker implementation for simple dependent type system.

Based on paper by Thierry Coquand
[An algorithm for type-checking dependent types](https://doi.org/10.1016/0167-6423(95)00021-6)

Extended with inductive types and simple pattern matching, similar to
[cubicaltt](https://github.com/mortberg/cubicaltt).

There is basic macros support.

It's a type system prototype for [Lasca programming language](http://lasca-lang.org).

## Examples

[Examples.depc](https://github.com/nau/depc/blob/master/Examples.depc)

```agda
-- Bool stuff
data Bool = true : Bool | false : Bool;
boolToType (A : U) : Bool -> U = split {
    true -> A;
    false -> Void;
};

data Nat = Z : Nat | S (n : Nat) : Nat;
plus : Nat -> Nat -> Nat = split {
    Z -> λ n -> n ;
    S m -> λ n -> S (plus m n);
};

twoPlusTwoEqFour : Id Nat (plus 2 2) 4 = refl;

data Sigma (A : U) (B : A -> U) = Pair (x : A) (y : B x) : Sigma A B;
∃ : (A : U) -> (B : A -> U) -> U = Sigma A B;
-- Proove there exists a natural number greater than zero.
gtZ : Nat -> U = split { Z -> Void ; S x -> Unit };
existsNatGtZ : ∃ Nat gtZ = Pair (S Z) (unit);

```

## Build

    stack setup
    stack build

## VSCode Support

There is a [VSCode Extension](https://marketplace.visualstudio.com/items?itemName=lasca-lang.depc-vscode) for depc syntax highlighting.

## Bibliography

http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf
