{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Core where

import qualified Data.List as List
import Data.Maybe
import Data.String
import Data.Void
import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text.Prettyprint.Doc

type Id = String
type Env = [(Id, Val)]

data Expr
  = Var Id
  | App Expr Expr
  | Lam Id Expr
  | Let Id Expr Expr Expr
  | Pi Id Expr Expr
  | Type
  deriving (Show, Eq)

data Val
  = VGen Int
  | VApp Val Val
  | VType
  | VClosure Env Expr
  deriving (Show, Eq)

update env id v = (id, v) : env

lookupEnv id env = fromMaybe (error $ "Couldn't find in env " ++ id) $ lookup id env

app (VClosure env (Lam x e)) arg = eval (update env x arg) e
app e arg = VApp e arg

eval env e = case e of
    Var x         -> lookupEnv x env
    App e1 e2     -> app (eval env e1) (eval env e2)
    Let x e1 _ e3 -> eval (update env x (eval env e1)) e3
    Type          -> VType
    Lam{}         -> VClosure env e
    Pi{}          -> VClosure env e



whnf (VApp     e   v) = app (whnf e) (whnf v)
whnf (VClosure env v) = eval env v
whnf e                = e

checkType (k, rho, gamma) e = checkExpr (k, rho, gamma) e VType

checkExpr (k, rho, gamma) e v =
    case e of
        Lam x n -> case whnf v of
            VClosure env (Pi y a b) ->
                let v = VGen k
                in checkExpr (k + 1, update rho x v, update gamma x (VClosure env a)) n (VClosure (update env y v) b)
            wrong -> error $ "Expected Pi but got " ++ pprint wrong
        Pi x a b -> case whnf v of
            VType -> checkType (k, rho, gamma) a && checkType (k + 1, update rho x (VGen k), update gamma x (VClosure rho a)) b
            _ -> error $ "Expected Type but got" ++ pprint (whnf v)
        Let x e1 e2 e3 -> checkType (k, rho, gamma) e2
          && checkExpr (k, update rho x (eval rho e1), update gamma x (eval rho e2)) e3 v
        Var{} -> eqVal k (inferExpr (k, rho, gamma) e) v
        App{} -> eqVal k (inferExpr (k, rho, gamma) e) v
        Type  -> eqVal k (inferExpr (k, rho, gamma) e) v

eqVal k u1 u2 = case (whnf u1, whnf u2) of
    (VType     , VType     ) -> True
    (VApp f1 a1, VApp f2 a2) -> eqVal k f1 f2 && eqVal k a1 a2
    (VGen k1   , VGen k2   ) -> k1 == k2
    (VClosure env1 (Lam x1 e1), VClosure env2 (Lam x2 e2)) ->
        let v = VGen k
        in  eqVal (k + 1)
                  (VClosure (update env1 x1 v) e1)
                  (VClosure (update env2 x2 v) e2)
    (VClosure env1 (Pi x1 a1 b1), VClosure env2 (Pi x2 a2 b2)) ->
        let v = VGen k
        in  eqVal k (VClosure env1 a1) (VClosure env2 a2) && eqVal
                (k + 1)
                (VClosure (update env1 x1 v) b1)
                (VClosure (update env2 x2 v) b2)
    _ -> False


inferExpr :: (Int, Env, Env) -> Expr -> Val
inferExpr (k, rho, gamma) e = case e of
    Var id -> lookupEnv id gamma
    App e1 e2 -> do
        let infer = whnf $ inferExpr (k, rho, gamma) e1
        case infer of
            VClosure env (Pi x a b) -> if checkExpr (k, rho, gamma) e2 (VClosure env a)
                then VClosure (update env x (VClosure rho e2)) b
                else error $ "Can't infer type for App, expected Pi: " ++ pprint e ++ " inferred " ++ pprint infer
            _ -> error $ "Can't infer type for App, expected Pi: " ++ pprint e ++ " inferred " ++ pprint infer
    Type -> VType
    _ -> error $ "Couldn't infer type for " ++ show e

typecheck m a =
    checkType (0, [], []) a && checkExpr (0, [], []) m (VClosure [] a)

instance Pretty Expr where
    pretty e = case e of
        Var id -> pretty id
        App e1 e2 -> parens $ pretty e1 <+> pretty e2
        Lam id expr -> parens $ "λ" <+> pretty id <+> "->" <+> pretty expr
        Let id v t b -> parens $ "let" <+> pretty id <+> "=" <+> pretty v <+> pretty b
        Pi "_" tpe body -> parens $ pretty tpe <+> "->" <+> pretty body
        Pi id tpe body -> parens (pretty id <+> ":" <+> pretty tpe) <+> "->" <+> pretty body
        Type -> "U"

data PEnv a = PEnv Int a

instance Pretty (PEnv Expr) where
    pretty (PEnv prec e) = case e of
        Var id -> pretty id
        App e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <+> pretty (PEnv 11 e2)
        Lam id expr -> wrap 5 prec $ "λ" <+> pretty id <+> "->" <+> pretty (PEnv 5 expr)
        Let id v t b -> parens $ "let" <+> pretty id <+> "=" <+> pretty v <+> pretty b
        Pi "_" tpe body -> wrap 5 prec $ pretty (PEnv 6 tpe) <+> "->" <+> pretty (PEnv 5 body)
        Pi id tpe body ->  wrap 5 prec $ parens (pretty id <+> ":" <+> pretty (PEnv 5 tpe)) <+> "->" <+> pretty (PEnv 5 body)
        Type -> "U"

instance Pretty (PEnv Val) where
    pretty (PEnv prec e) = case e of
        VGen i -> pretty i
        VApp e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <+> pretty (PEnv 11 e2)
        VType -> "U"
        VClosure env expr -> pretty (PEnv prec expr)

wrap p p1 = if p < p1 then parens else id

pprint :: Pretty (PEnv a) => a -> String
pprint exp = show $ pretty (PEnv 0 exp)