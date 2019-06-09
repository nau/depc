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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
  | Con Id [Expr]
  | App Expr Expr
  | Lam Id Expr
  | Let Id Expr Expr Expr
  | Pi Id Expr Expr
  | Sum Id [Id]
  | Split Expr [Case]
  | Type
  deriving (Show, Eq)

data Case = Case Id [Id] Expr deriving (Show, Eq)

data Val
  = VGen Int
  | VCon Id [Val]
  | VApp Val Val
--   | VPi Val Val
  | VType
  | VClosure Rho Expr
  deriving (Show, Eq)

data Decl = Def Id Expr Expr
          | Data Id [Constructor]
          deriving (Show)

data Constructor = Constructor Id Expr deriving (Show)

-- Type checking monad
type Constructors = Map Id Expr
type TEnv = (Int, Rho, Gamma, Constructors)

emptyTEnv :: TEnv
emptyTEnv = (0, Rho [], Gamma [], Map.empty)

initTEnv :: Constructors -> TEnv
initTEnv cons = (0, Rho [], Gamma [], cons)

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


type Resolver a = ReaderT Constructors (ExceptT String Identity) a

unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runExceptT $ runReaderT x Map.empty

resolveDecls :: [Decl] -> Resolver ([Decl], Constructors)
resolveDecls []     = return ([], Map.empty)
resolveDecls (d:ds) = do
  (decl, cons)  <- resolveDecl d
  (decls, cons') <- local (Map.union cons) $ resolveDecls ds
  return (decl : decls, Map.union cons' cons)


resolveDecl :: Decl -> Resolver (Decl, Constructors)
resolveDecl decl = case decl of
    Def id tpe body -> do
        t <- resolve tpe
        b <- resolve body
        return (Def id t b, Map.empty)
    Data id cons -> return (decl, foldl (\acc (Constructor nm _) -> Map.insert nm (Var id) acc) Map.empty cons)



resolve :: Expr -> Resolver Expr
resolve e = case e of
    Var x         -> do
        cons <- ask
        case Map.lookup x cons of
            Just _ -> return $ Con x []
            Nothing -> return e
    Con name ts   -> return e
    App e1 e2     -> let (head, spine) = unApps e1 [e2]
                     in mkApps <$> resolve head <*> mapM resolve spine
    Let x e1 e2 e3 -> Let x <$> resolve e1 <*> resolve e2 <*> resolve e3
    Type          -> return Type
    Pi id tpe body -> Pi id <$> resolve tpe <*> resolve body
    Lam x body         -> Lam x <$> resolve body
    Split tpe cases -> Split <$> resolve tpe <*> mapM (\(Case con args expr) -> Case con args <$> resolve expr) cases

mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts


lookupCase :: Id -> [Case] -> Maybe Case
lookupCase x cases = case cases of
    c@(Case con args expr) : cs | x == con    -> Just c
                                | otherwise -> lookupCase x cs


app :: Val -> Val -> Val
app (VClosure env (Lam x e)) arg = eval (updateRho env x arg) e
app (VClosure env (Split tpe cases)) (VCon id args) =
    case lookupCase id cases of
        Just (Case _ params body) | length params == length args -> let
            bindings = zip params args
            rho' = foldl (\rho (p, a) -> updateRho rho p a) env bindings
            in traceShow "Here" $ eval rho' body
        Just (Case _ params body) -> error $ show $
            "splitting on not fully applied constructor" <+> pretty id <+>
            "expected" <+> pretty (length params) <+> "but given" <+> pretty (length args)
        _     -> error $ "app: missing case in split for " ++ id
app e arg = {- trace (show $ pretty $ VApp e arg) $ -} VApp e arg


eval :: Rho -> Expr -> Val
eval rho e = let
    res = case e of
        Var x         -> lookupRho x rho
        Con name ts   -> VCon name (map (eval rho) ts)
        App e1 e2     -> app (eval rho e1) (eval rho e2)
        Let x e1 _ e3 -> eval (updateRho rho x (eval rho e1)) e3
        Type          -> VType
        -- Pi name tpe body -> VPi (eval rho tpe) (eval rho (Lam name body))
        Pi{}          -> VClosure rho e
        Lam{}         -> VClosure rho e
        Split{}       -> VClosure rho e
    in {- traceShow (pretty e <+> "↦" <+> pretty res) -} res


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

checkExprHasType :: Expr -> Val -> Typing ()
checkExprHasType expr typeVal = do
    (k, ρ, γ, datadecls) <- ask
    let whTypeVal = whnf typeVal
    case (expr, whTypeVal) of
        (Lam x body, VClosure env (Pi y yType piBody)) -> do
            let vgen = VGen k
                ρ' = updateRho ρ x vgen
                γ' = updateGamma γ x (VClosure env yType)
            let txt = "ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            traceShowM txt
            local (const (k + 1, ρ', γ', datadecls)) $
                checkExprHasType body (VClosure (updateRho env y vgen) piBody)
        (Lam{}, wrong) -> throwError $ "Expected Pi but got " ++ pprint wrong
        (Con id args, _) ->
            case Map.lookup id datadecls of
                Just ty -> return ()
                Nothing -> throwError $ show $ "Unknown constructor" <+> pretty id <+> pretty (show datadecls)

        (Split tpe cases, VClosure env (Pi y yType piBody)) -> do
            checkType tpe
            let splitTypeVal = eval ρ tpe
            if eqVal k splitTypeVal typeVal
            then return ()
            else throwError $ show $ "AAA:" <+> pretty splitTypeVal <+> "!=" <+> pretty typeVal
        (Pi x xType body, VType) -> do
            checkType xType
            let ρ' = updateRho ρ x (VGen k)
                γ' = updateGamma γ x (VClosure ρ xType)
            let txt = "ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            -- traceShowM txt
            local (const (k + 1, ρ', γ', datadecls)) $ checkType body
        (Pi x a b, _) -> throwError $ "Expected Type but got" ++ pprint whTypeVal ++ " for " ++ pprint expr
        (Let x e eType body, _) -> do
            checkType eType
            let ρ' = updateRho ρ x (eval ρ e)
                γ' = updateGamma γ x (eval ρ eType)
            local (const (k, ρ', γ', datadecls)) $ checkExprHasType body typeVal
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
    (k, ρ, γ, datadecls) <- ask
    case e of
        Var id -> do
            typeVal <- lookupGamma id γ
            -- traceM $ show ("Infer" <+> pretty e <+> ":" <+> pretty typeVal)
            return typeVal
        App e1 e2 -> do
            inferred <- inferExprType e1
            let wh = whnf inferred
            case wh of
                VClosure env (Pi x xType piBody) -> do
                    checkExprHasType e2 (VClosure env xType)
                    let res = VClosure (updateRho env x (VClosure ρ e2)) piBody
                    {- traceShowM $ "App" <+> pretty e1 <+> colon <+> pretty wh <+> "⚈" <+>
                        pretty e2 <+> colon <+> pretty (VClosure env xType) <+> "≡" <+> pretty res -}
                    return res
                _ -> throwError $ "Can't infer type for App, expected Pi: " ++ pprint e ++ " inferred " ++ pprint inferred
        Type -> return VType
        _ -> throwError $ show $ "Couldn't infer type for" <+> pretty e

eqVal :: Int -> Val -> Val -> Bool
eqVal k u1 u2 = do
    let wh1 = whnf u1
        wh2 = whnf u2
    -- traceShow ("EQ" <+> pretty wh1 <+> "≟≟≟" <+> pretty wh2) $
    case (wh1, wh2) of
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
typecheck = typecheckEnv emptyTEnv

typecheckEnv tenv@(_, ρ, _, _) m a = runTyping tenv $ do
    checkType a
    checkExprHasType m (VClosure ρ a)


addDecl :: Decl -> TEnv -> TEnv
addDecl (Def name tpe body) (k, rho, gamma, datadecls) =
    (k, updateRho rho name (eval rho body),
        updateGamma gamma name (eval rho tpe), datadecls)
addDecl (Data name cons) (k, rho, gamma, datadecls) = do
    let v = VGen k
    let r' = updateRho rho name v
    let g' = updateGamma gamma name (VClosure rho Type)
    -- let cs = foldl (\acc (Constructor nm _) -> Map.insert nm (Var name) acc) Map.empty cons
    foldl addCon (k + 1, r', g', datadecls) cons

  where addCon (k, rho, gamma, datadecls) (Constructor con tpe) = do
            let v = VGen k
            let r' = updateRho rho con v
            let g' = updateGamma gamma con (VClosure rho tpe)
            (k + 1, r', g', datadecls)

checkDecl :: TEnv -> Decl -> Either String TEnv
checkDecl tenv@(_, rho, _, _) decl = runTyping tenv $
    case decl of
        Def name tpe body -> do
            checkType tpe
            let vtpe  = eval rho tpe
            checkExprHasType body vtpe
            return tenv
        Data name cons -> return tenv



addDecls :: TEnv -> [Decl] -> Either String TEnv
addDecls tenv decls = do
    let env = foldr addDecl tenv decls
    traceM $ "AAAddDecls" ++ show env
    -- foldM checkDecl env decls
    return env

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
        Con id args -> wrap 10 prec $ pretty id <+> foldl (\a b -> a <+> pretty b) "" args
        App e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <+> pretty (PEnv 11 e2)
        Lam id expr -> let
            (ids, expr) = foldLam e
            foldedIds = foldl (\a i -> a <+> pretty i) "λ" ids
            in wrap 5 prec $ foldedIds <+> "->" <+> pretty (PEnv 5 expr)
        Split tpe cases -> wrap 3 prec $ "split" <+> parens (pretty tpe) <+> braces (pretty cases)
        Let id v t b -> wrap 3 prec $ "let" <+> pretty id <+> colon <+> pretty t <+> "=" <+> pretty v <+> "in" <+> pretty b
        Pi "_" tpe body -> wrap 5 prec $ pretty (PEnv 6 tpe) <+> "->" <+> pretty (PEnv 5 body)
        Pi id tpe body ->  wrap 5 prec $ parens (pretty id <+> ":" <+> pretty (PEnv 5 tpe)) <+> "->" <+> pretty (PEnv 5 body)
        Type -> "U"

instance Pretty Case where
    pretty (Case con ids e) = pretty con <+> list (map pretty ids) <+> "->" <+> pretty e <+> semi
instance Pretty (PEnv Val) where
    pretty (PEnv prec e) = case e of
        VGen i -> pretty i
        VCon id args -> parens $ pretty id <+> foldl (\a b -> a <+> pretty b) "" args
        VApp e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <> "·" <> pretty (PEnv 11 e2)
        -- VPi e1 e2 -> wrap 5 prec $ pretty e1 <+> "->>>" <+> pretty e2
        VType -> "Û"
        VClosure (Rho env) expr -> {- prettyEnv env <+> -} "⊢" <+> pretty (PEnv prec expr)

instance Pretty Rho where pretty (Rho env) = prettyEnv env
instance Pretty Gamma where pretty (Gamma env) = prettyEnv env

instance Pretty TEnv where
    pretty t@(k, rho, gamma, datadecls) = "TEnv"

-- prettyEnv _ = ""
prettyEnv [] = "∅"
prettyEnv ls = list $ fmap p ls
  where p (i, t) = pretty i <> "=" <> pretty t

instance Pretty Val where pretty val = pretty (PEnv 0 val)
instance Pretty Expr where pretty val = pretty (PEnv 0 val)


wrap p p1 = if p < p1 then parens else id

pprint :: Pretty a => a -> String
pprint exp = show $ pretty exp
