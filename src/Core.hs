{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE UnicodeSyntax  #-}
module Core where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader

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

type Id = String
type Env = [(Id, Val)]
newtype Rho = Rho Env deriving (Show, Eq)
newtype Gamma = Gamma Env deriving (Show, Eq)

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
  | VClosure Rho Expr
  deriving (Show, Eq)

data Decl = Def Id Expr Expr deriving (Show)

-- Type checking monad
type TEnv = (Int, Rho, Gamma)

emptyTEnv :: TEnv
emptyTEnv = (0, Rho [], Gamma [])

type Typing a = ReaderT TEnv (Except String) a

-- runTyping :: TEnv -> Typing a -> Either String a
runTyping :: TEnv -> Typing a -> Either String a
runTyping env t = runIdentity $ runExceptT $ runReaderT t env

updateRho (Rho env) id v = Rho $ (id, v) : env
updateGamma (Gamma env) id v = Gamma $ (id, v) : env

perr = error . show

lookupRho :: Id -> Rho -> Val
lookupRho id (Rho env) = fromMaybe err $ lookup id env
  where err = perr $ "Couldn't find" <+> squotes (pretty id) <+> "in ρ" <+> prettyEnv env

lookupGamma :: Id -> Gamma -> Typing Val
lookupGamma id (Gamma env) = case lookup id env of
    Just v -> return v
    Nothing -> throwError $ show $ "Couldn't find" <+> squotes (pretty id) <+> "in Γ" <+> prettyEnv env


app :: Val -> Val -> Val
app (VClosure env (Lam x e)) arg = eval (updateRho env x arg) e
app e arg = VApp e arg

eval :: Rho -> Expr -> Val
eval env e = let
    res = case e of
        Var x         -> lookupRho x env
        App e1 e2     -> app (eval env e1) (eval env e2)
        Let x e1 _ e3 -> eval (updateRho env x (eval env e1)) e3
        Type          -> VType
        Lam{}         -> VClosure env e
        Pi{}          -> VClosure env e
    in traceShow (pretty e <+> "↦" <+> pretty res) res


whnf :: Val -> Val
whnf (VApp     e   v) = app (whnf e) (whnf v)
whnf (VClosure env v) = eval env v
whnf e                = e

checkType e = do
    checkExprHasType e VType
    -- traceShowM $ "Type" <+> pretty e <+> "is a type!"
    return ()

tr :: Pretty a => a -> b -> b
tr = traceShow . pretty

checkExprHasType expr typeVal = do
    (k, ρ, γ) <- ask
    let whTypeVal = whnf typeVal
    case (expr, whTypeVal) of
        (Lam x body, VClosure env (Pi y yType piBody)) -> do
            let vgen = VGen k
                ρ' = updateRho ρ x vgen
                γ' = updateGamma γ x (VClosure env yType)
            let txt = "ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            traceShowM txt
            local (const (k + 1, ρ', γ')) $
                checkExprHasType body (VClosure (updateRho env y vgen) piBody)
        (Lam{}, wrong) -> throwError $ "Expected Pi but got " ++ pprint wrong
        (Pi x xType body, VType) -> do
            checkType xType
            let ρ' = updateRho ρ x (VGen k)
                γ' = updateGamma γ x (VClosure ρ xType)
            let txt = "ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            -- traceShowM txt
            local (const (k + 1, ρ', γ')) $ checkType body
        (Pi x a b, _) -> throwError $ "Expected Type but got" ++ pprint whTypeVal ++ " for " ++ pprint expr
        (Let x e eType body, _) -> do
            checkType eType
            let ρ' = updateRho ρ x (eval ρ e)
                γ' = updateGamma γ x (eval ρ eType)
            local (const (k, ρ', γ')) $ checkExprHasType body typeVal
        _ -> do
            inferredTypeVal <- inferExprType expr
            if eqVal k inferredTypeVal typeVal
            then return ()
            else throwError $ show $ "Types aren't equal with k=" <> pretty k <+> colon <+> line <+>
                pretty inferredTypeVal <+> line <+> pretty typeVal
        -- App{} -> eqVal k (inferExpr e) v
        -- Type  -> eqVal k (inferExpr e) v

inferExprType :: Expr -> Typing Val
inferExprType e = do
    (k, ρ, γ) <- ask
    case e of
        Var id -> do
            typeVal <- lookupGamma id γ
            traceM $ show ("Infer" <+> pretty e <+> ":" <+> pretty typeVal)
            return typeVal
        App e1 e2 -> do
            inferred <- inferExprType e1
            let wh = whnf inferred
            case wh of
                VClosure env (Pi x xType piBody) -> do
                    checkExprHasType e2 (VClosure env xType)
                    let res = VClosure (updateRho env x (VClosure ρ e2)) piBody
                    traceShowM $ "App" <+> pretty e1 <+> colon <+> pretty wh <+> "⚈" <+>
                        pretty e2 <+> colon <+> pretty (VClosure env xType) <+> "≡" <+> pretty res
                    return res
                _ -> throwError $ "Can't infer type for App, expected Pi: " ++ pprint e ++ " inferred " ++ pprint inferred
        Type -> return VType
        _ -> throwError $ show $ "Couldn't infer type for" <+> pretty e

eqVal :: Int -> Val -> Val -> Bool
eqVal k u1 u2 = do
    let wh1 = whnf u1
        wh2 = whnf u2
    traceShow ("EQ" <+> pretty wh1 <+> "≟≟≟" <+> pretty wh2) $ case (wh1, wh2) of
        (VType     , VType     ) -> True
        (VApp f1 a1, VApp f2 a2) -> eqVal k f1 f2 && eqVal k a1 a2
        (VGen k1   , VGen k2   ) -> k1 == k2
        (VClosure env1 (Lam x1 e1), VClosure env2 (Lam x2 e2)) ->
            let v = VGen k
            in  eqVal (k + 1)
                        (VClosure (updateRho env1 x1 v) e1)
                        (VClosure (updateRho env2 x2 v) e2)
        -- It's a modification of original algorithm. I guess Type is Type in any context.
        (VClosure env1 Type, VType) -> True
        (VClosure env1 Type, VClosure env2 Type) -> True
        (VClosure env1 (Pi x1 xType1 b1), VClosure env2 (Pi x2 xType2 b2)) ->
            let v = VGen k
            in  eqVal k (VClosure env1 xType1) (VClosure env2 xType2) &&
                eqVal (k + 1) (VClosure (updateRho env1 x1 v) b1) (VClosure (updateRho env2 x2 v) b2)
        _ -> False


typecheck :: Expr -> Expr -> Either String ()
typecheck = typecheckEnv (0, Rho [], Gamma [])

typecheckEnv tenv@(_, ρ, _) m a = runTyping tenv $ do
    checkType a
    checkExprHasType m (VClosure ρ a)


addDecl1 (Def name tpe body) tenv@(k, r, g) =
    (k, updateRho r name (eval r body),
        updateGamma g name (eval r tpe))

addDecl :: TEnv -> Decl -> Either String TEnv
addDecl tenv decl = runTyping tenv $ do
    let Def name tpe body = decl
    checkType tpe
    addDecl1 decl <$> ask

addDecls tenv decls = foldM addDecl tenv decls

instance Pretty Decl where
    pretty (Def id tpe body) = pretty id <+> ":" <+> pretty (PEnv 0 tpe) <+> "=" <+> pretty (PEnv 0 body)

data PEnv a = PEnv Int a

foldLam :: Expr -> ([Id], Expr)
foldLam expr = go expr ([], expr) where
    go (Lam name e) result = let (args, body) = go e result in (name : args, body)
    go e (args, _) = (args, e)

instance Pretty (PEnv Expr) where
    pretty (PEnv prec e) = case e of
        Var id -> pretty id
        App e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <> "·" <> pretty (PEnv 11 e2)
        Lam id expr -> let
            (ids, expr) = foldLam e
            foldedIds = foldl (\a i -> a <+> pretty i) "λ" ids
            in wrap 5 prec $ foldedIds <+> "→" <+> pretty (PEnv 5 expr)
        Let id v t b -> parens $ "let" <+> pretty id <+> "=" <+> pretty v <+> pretty b
        Pi "_" tpe body -> wrap 5 prec $ pretty (PEnv 6 tpe) <+> "→" <+> pretty (PEnv 5 body)
        Pi id tpe body ->  wrap 5 prec $ parens (pretty id <+> ":" <+> pretty (PEnv 5 tpe)) <+> "→" <+> pretty (PEnv 5 body)
        Type -> "U"

instance Pretty (PEnv Val) where
    pretty (PEnv prec e) = case e of
        VGen i -> pretty i
        VApp e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <+> "·" <+> pretty (PEnv 11 e2)
        VType -> "Ú"
        VClosure (Rho env) expr -> prettyEnv env <+> "⊢" <+> pretty (PEnv prec expr)

instance Pretty Rho where pretty (Rho env) = prettyEnv env
instance Pretty Gamma where pretty (Gamma env) = prettyEnv env

prettyEnv [] = "∅"
prettyEnv ls = list $ fmap p ls
  where p (i, t) = pretty i <> "=" <> pretty t

instance Pretty Val where pretty val = pretty (PEnv 0 val)
instance Pretty Expr where pretty val = pretty (PEnv 0 val)


wrap p p1 = if p < p1 then parens else id

pprint :: Pretty a => a -> String
pprint exp = show $ pretty exp
