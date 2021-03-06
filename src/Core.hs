{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE UnicodeSyntax  #-}
module Core where

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
data Rho = D Decl Rho | V Id Val Rho | Empty deriving (Show, Eq)
newtype Gamma = Gamma Env deriving (Show, Eq)

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Id, Expr)]

data Expr
  = Var Id
  | Lit Id
  | Con Id [Expr]
  | App Expr Expr
  | Lam Id Expr
  | Let Id Expr Expr Expr
  | Pi Id Expr Expr
  | Sum Id Expr [Constructor]
  | Split (Maybe Expr) [Case]
  | Type
  | Quote Expr
  | Splice Expr
  deriving (Show, Eq)

data Case = Case Id [Id] Expr deriving (Show, Eq)

data Val
  = VGen Int
  | VLit Id
  | VCon Id [Val]
  | VApp Val Val
  | VType
  | VClosure Rho Expr
  deriving (Show, Eq)

data Decl = Def Id Expr Expr
          | Data Id Expr [Constructor]
          deriving (Show, Eq)

data Constructor = Constructor Id Expr deriving (Show, Eq)

-- Type checking monad
type Constructors = Map Id Expr
type TEnv = (Int, Rho, Gamma)

emptyTEnv :: TEnv
emptyTEnv = (0, Empty, Gamma [])

initTEnv :: TEnv
initTEnv = (0, Empty, Gamma [])

type Typing a = ReaderT TEnv (Except String) a

-- runTyping :: TEnv -> Typing a -> Either String a
runTyping :: TEnv -> Typing a -> Either String a
runTyping env t = runIdentity $ runExceptT $ runReaderT t env

updateRho ρ id v = V id v ρ
updateGamma (Gamma env) id v = Gamma $ (id, v) : env

perr = error . show

lookupRho :: Id -> Rho -> Val
lookupRho id ρ = {- trace ("lookupRho " ++ id) $ -}
  case ρ of
    V i v _| i == id -> v
    V _ _ r -> lookupRho id r
    D (Def name _ body) r -> if name == id
        then eval ρ body
        else lookupRho id r
    D (Data name dataType cons) r -> if name == id
        then let
            body = Sum name dataType cons
            lam = lamForPi dataType body
            in eval ρ lam
        else lookupRho id r
    _ -> perr $ "Couldn't find" <+> squotes (pretty id) <+> "in ρ" <+> pretty ρ

lookupCons id [] = Nothing
lookupCons id (Constructor name e : cons) = if id == name then  Just e else lookupCons id cons

lookupGamma :: Id -> Gamma -> Typing Val
lookupGamma id (Gamma env) = case lookup id env of
    Just v -> do
        {- traceShowM $ "lookupGamma" <+> pretty id <+> "=" <+> pretty (show v) <+> "in" <+> line
            <+> prettyEnv env -}
        return v
    Nothing -> throwError $ show $ "Couldn't find" <+> squotes (pretty id) <+> "in Γ" <+> prettyEnv env


type Resolver a = ReaderT Constructors (ExceptT String Identity) a

unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

runResolver :: Resolver a -> Constructors -> Either String a
runResolver x cons = runIdentity $ runExceptT $ runReaderT x cons

runResolveDecls :: [Decl] -> Either String ([Decl], Constructors)
runResolveDecls decls = runResolver (resolveDecls decls) Map.empty

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
    Data id tpe cons -> do
        t <- resolve tpe
        cs <- mapM (\(Constructor nm tpe) -> Constructor nm <$> resolve tpe) cons
        return (Data id t cs, foldl (\acc (Constructor nm _) -> Map.insert nm (Var id) acc) Map.empty cs)

resolveTele tele = forM tele $ \(id, expr) -> do
    e <- resolve expr
    return (id, e)

resolve :: Expr -> Resolver Expr
resolve e = case e of
    Var x         -> do
        cons <- ask
        case Map.lookup x cons of
            Just _ -> return $ Con x []
            Nothing -> return e
    Lit _         -> return e
    Con name ts   -> return e
    App e1 e2     -> let (head, spine) = unApps e1 [e2]
                     in mkApps <$> resolve head <*> mapM resolve spine
    Let x e1 e2 e3 -> Let x <$> resolve e1 <*> resolve e2 <*> resolve e3
    Type          -> return Type
    Pi id tpe body -> Pi id <$> resolve tpe <*> resolve body
    Lam x body         -> Lam x <$> resolve body
    Split tpe cases -> Split <$> mapM resolve tpe <*> mapM (\(Case con args expr) -> Case con args <$> resolve expr) cases
    Sum name tpe constrs -> Sum name <$> resolve tpe <*> mapM (\(Constructor con expr) -> Constructor con <$> resolve expr) constrs
    Quote e -> Quote <$> resolve e
    Splice e -> Splice <$> resolve e

mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts


lookupCase :: Id -> [Case] -> Maybe Case
lookupCase x cases = case cases of
    [] -> Nothing
    c@(Case con args expr) : cs | x == con    -> Just c
                                | otherwise -> lookupCase x cs


app :: Val -> Val -> Val
app (VApp (VLit "error") _) (VLit s) = error $ "Error: " ++ s
app (VClosure env (Lam x e)) arg = eval (updateRho env x arg) e
app (VClosure env (Split tpe cases)) (VCon id args) =
    case lookupCase id cases of
        Just (Case _ params body) | length params == length args -> let
            bindings = zip params args
            rho' = foldl (\rho (p, a) -> updateRho rho p a) env bindings
            in eval rho' body
        Just (Case _ params body) -> error $ show $
            "splitting on not fully applied constructor" <+> pretty id <+>
            "expected" <+> pretty (length params) <+> "but given" <+> pretty (length args)
        _     -> error $ "app: missing case in split for " ++ id
app e arg = {- trace (show $ pretty $ VApp e arg) $ -} VApp e arg


eval :: Rho -> Expr -> Val
eval rho e = let
    -- ee = traceShow ("eval" <+> pretty e <+> "in rho = " <+> pretty rho) e
    res = case e of
        Var "error"   -> VLit "error"
        Var x         -> lookupRho x rho
        Lit s         -> VLit s
        Con name ts   -> VCon name (map (eval rho) ts)
        App e1 e2     -> app (eval rho e1) (eval rho e2)
        Let x e1 _ e3 -> eval (updateRho rho x (eval rho e1)) e3
        Type          -> VType
        -- Pi name tpe body -> VPi (eval rho tpe) (eval rho (Lam name body))
        Sum{}         -> VClosure rho e
        Pi{}          -> VClosure rho e
        Lam{}         -> VClosure rho e
        Split{}       -> VClosure rho e
        Quote e       -> quote rho e
        Splice e      -> eval rho (unquote $ eval rho e)
    in {- traceShow (pretty e <+> "↦" <+> pretty res) -} res


whnf :: Val -> Val
whnf (VApp     e   v) = app (whnf e) (whnf v)
whnf (VClosure env v) = eval env v
whnf e                = e

checkType e = do
    checkExprHasType e VType
    -- traceShowM $ "Type" <+> pretty e <+> "is a type!"
    return ()


checkExprHasType :: Expr -> Val -> Typing ()
checkExprHasType expr typeVal = do
    (k, ρ, γ) <- ask
    let whTypeVal = whnf typeVal
    -- traceShowM $ "checkExprHasType" <+> pretty expr <+> colon <+> pretty whTypeVal
    -- traceM $ "checkExprHasType " <> show expr
    -- traceM $ "  has type " <> show whTypeVal
    case (expr, whTypeVal) of
        (Splice e, vt) -> checkExprHasType (unquote (eval ρ e)) vt
        (Quote e, VClosure rho (Sum "Expr" _ _)) -> return ()
        (Lit s, VClosure rho (Sum "String" _ _)) -> return ()
        (Lam x body, VClosure env (Pi y yType piBody)) -> do
            let vgen = VGen k
                ρ' = updateRho ρ x vgen
                γ' = updateGamma γ x (VClosure env yType)
            let txt = "Lam: Pi, ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            -- traceShowM txt
            local (const (k + 1, ρ', γ')) $
                checkExprHasType body (VClosure (updateRho env y vgen) piBody)
        (Lam{}, wrong) -> throwError $ "Expected Pi but got " ++ pprint wrong
        (Sum _ _ bs, VType) -> forM_ bs $ \(Constructor id tpe) -> do
            let (tele, t) = unTele tpe
            checkTele tele
        (Con id args, VClosure rho s@(Sum name dataType constructors)) -> let
            cons = map (\(Constructor id tpe) -> (id, tpe)) constructors
            in case lookup id cons of
                Just tpe -> do
                    let (tele, t) = unTele tpe
                    -- traceM $ "asdf " ++ id ++ show (tele) ++ show t
                    rho' <- checks tele rho args
                    let tt@(VClosure venv _) = eval rho' t
                    -- traceM $ "vv = " ++ show (pretty venv)
                    if eqVal k tt whTypeVal
                    then return ()
                    else throwError $ show $ "Expected" <+> line <+>
                        pretty whTypeVal <+> line <+>
                        "but got:" <+> line <+>
                        pretty tt
                Nothing -> throwError $ show $ "Unknown constructor" <+> pretty id <+> pretty s

        (Split tpe cases, VClosure env (Pi y yType piBody)) -> do
            splitTypeVal <- case tpe of
                    Just tpe -> do  checkType tpe
                                    return $ eval ρ tpe
                    Nothing -> return whTypeVal
            if eqVal k splitTypeVal whTypeVal
            then case eval env yType of
                    VClosure env2 (Sum _ _ constrs) ->
                        if map (\(Constructor id _) -> id) constrs == map (\(Case id _ _) -> id) cases
                            then sequence_ [ checkCase lbl env2 whTypeVal brc
                                           | (brc, lbl) <- zip cases constrs ]
                            else throwError "case branches does not match the data type"
                    _ -> throwError "AAAAAA"
            else throwError $ show $ "AAA:" <+> pretty splitTypeVal <+> "!=" <+> pretty whTypeVal
        (Pi x xType body, VType) -> do
            checkType xType
            let ρ' = updateRho ρ x (VGen k)
                γ' = updateGamma γ x (VClosure ρ xType)
            let txt = "Pi : Type, ρ:" <+> pretty ρ' <+> "Γ:" <+> pretty γ'
            -- traceShowM txt
            local (const (k + 1, ρ', γ')) $ checkType body
        (Pi x a b, _) -> throwError $ "Expected Type but got" ++ pprint whTypeVal ++ " for " ++ pprint expr
        (Let x e eType body, _) -> do
            checkType eType
            let ρ' = updateRho ρ x (eval ρ e)
                γ' = updateGamma γ x (eval ρ eType)
            local (const (k, ρ', γ')) $ checkExprHasType body whTypeVal
        _ -> do
            inferredTypeVal <- inferExprType expr
            if eqVal k inferredTypeVal whTypeVal
            then return ()
            else throwError $ show $ "Types aren't equal for " <> pretty expr <+> colon <+> line <+>
                pretty inferredTypeVal <+> line <+> line <+> pretty whTypeVal

checkCase :: Constructor -> Rho -> Val -> Case -> Typing ()
checkCase (Constructor con expr) nu (VClosure env (Pi x xType piBody)) (Case _ names e) = do
    (k, rho, gamma) <- ask
    let
        k' = k + length names
        vars = map VGen [k+1..k']
        rho' = foldl (\r (var, vgen) -> V var vgen r) rho (zip names vars)
        (tele, _) = unTele expr
        gamma' = foldl (\(Gamma g) ((_, tpe), var) -> Gamma $ (var, eval nu tpe) : g) gamma (zip tele names)
        vcon = VCon con vars
    local (const (k', rho', gamma')) $
        checkExprHasType e (VClosure (updateRho env x vcon) piBody)
checkCase c r v cs = error "checkCase"

inferExprType :: Expr -> Typing Val
inferExprType e = do
    (k, ρ, γ) <- ask
    case e of
        Var "error" -> return $ VClosure Empty (Pi "A" Type (Pi "_" (Sum "String" Type []) (Var "A")))
        Var id -> do
            typeVal <- lookupGamma id γ
            let evaled = whnf typeVal
            -- traceM $ show ("Infer" <+> pretty e <+> ":" <+> pretty evaled)
            return evaled
        Lit{} -> return $ VClosure Empty (Sum "String" Type [])
        App e1 e2 -> do
            inferred <- inferExprType e1
            let wh = whnf inferred
            case wh of
                VClosure env (Pi x xType piBody) -> do
                    -- traceM $ show ("Infer App" <+> pretty wh <+> pretty e2 <+> "in" <+> pretty ρ)
                    checkExprHasType e2 (VClosure env xType)
                    let res = VClosure (updateRho env x (eval ρ e2)) piBody
                    {- traceShowM $ "App" <+> pretty e1 <+> colon <+> pretty wh <+> "⚈" <+>
                        pretty e2 <+> colon <+> pretty (VClosure env xType) <+> "≡" <+> pretty res -}
                    return res
                _ -> throwError $ "Can't infer type for App, expected Pi: " ++ pprint e ++ " inferred " ++ pprint inferred
        Type -> return VType
        Split (Just tpe) cases -> do
            let vtpe = eval ρ tpe
            checkExprHasType e vtpe
            return vtpe
        _ -> throwError $ show $ "Couldn't infer type for" <+> pretty (show e)

eqVal :: Int -> Val -> Val -> Bool
eqVal k u1 u2 = do
    let wh1 = whnf u1
        wh2 = whnf u2
    -- traceShow ("EQ" <+> pretty wh1 <+> "≟≟≟" <+> pretty wh2) $
    case (wh1, wh2) of
        (VType     , VType     ) -> True
        (VApp f1 a1, VApp f2 a2) -> eqVal k f1 f2 && eqVal k a1 a2
        (VGen k1   , VGen k2   ) -> k1 == k2
        (VCon id1 args1, VCon id2 args2) -> id1 == id2 && all (\(a, b) -> eqVal k a b) (zip args1 args2)
        (VClosure env1 (Split t1 bs1), VClosure env2 (Split t2 bs2)) -> True -- todo FIXME
        (VClosure env1 (Lam x1 e1), VClosure env2 (Lam x2 e2)) ->
            let v = VGen k
            in  eqVal (k + 1)
                        (VClosure (updateRho env1 x1 v) e1)
                        (VClosure (updateRho env2 x2 v) e2)
        -- It's a modification of original algorithm. I guess Type is Type in any context.
        (VClosure env1 Type, VType) -> True
        (VClosure env1 (Sum id1 dataType cons1), VClosure env2 (Sum id2 _ cons2)) -> let
            tele = fst $ unTele dataType
            asdf ((x, _) : xs) (V n1 v1 rest1) (V n2 v2 rest2) = let
                r1 = x == n1
                r2 = n1 == n2
                r3 = eqVal k v1 v2
                in {- trace ("eq " ++ x ++ show r1 ++ show r2 ++ show r3 ++ show v1 ++ "\n" ++ show v2) $ -}
                    r1 && r2 && r3 && asdf xs rest1 rest2
            asdf _ _ _ = True
            r1 = id1 == id2
            r2 = asdf (reverse tele) env1 env2
            in -- traceShow ("eqVal = " <+> pretty dataType <+> pretty r2 <+> pretty id1 <+> pretty env1 <+> line <+> pretty env2 )
                (r1 && r2)

        (VClosure env1 Type, VClosure env2 Type) -> True
        (VClosure env1 (Pi x1 xType1 b1), VClosure env2 (Pi x2 xType2 b2)) ->
            let v = {- trace "HEre" $ -} VGen k
                eq1 = eqVal k (VClosure env1 xType1) (VClosure env2 xType2)
                eq2 = eqVal (k + 1) (VClosure (updateRho env1 x1 v) b1) (VClosure (updateRho env2 x2 v) b2)
                res = {- trace (show b1 ++ show b2) $ -} eq1 && eq2
            in  res

        _ -> False


typecheck :: Expr -> Expr -> Either String ()
typecheck = typecheckEnv emptyTEnv

typecheckEnv tenv@(_, ρ, _) m a = runTyping tenv $ do
    checkType a
    checkExprHasType m (VClosure ρ a)


checkDecls :: [Decl] -> Typing TEnv
checkDecls [] = ask
checkDecls decls@(decl:ds) = do
    let (tele, body) = extractTeleBodies decl ([], [])
    checkTele tele
    local (addDecls [decl]) $ do
        (k, rho, gamma) <- ask
        checks tele rho body
        checkDecls ds

checkMutualDecls :: [Decl] -> Typing TEnv
checkMutualDecls [] = ask
checkMutualDecls decls = do
    let (teles, bodies) = foldr extractTeleBodies ([], []) decls
    traceM $ "check types"
    checkTele teles
    traceM $ "addDecls"
    local (addDecls decls) $ do
        (k, rho, gamma) <- ask
        checks teles rho bodies
    ask

extractTeleBodies :: Decl -> (Tele, [Expr]) -> (Tele, [Expr])
extractTeleBodies (Def name tpe body) (teles, bodies) = ((name, tpe) : teles, body : bodies)
extractTeleBodies (Data name dataType cons) (teles, bodies) = let
    body = Sum name dataType cons
    lam = lamForPi dataType body
    in ((name, dataType) : teles, lam : bodies)

lamForPi :: Expr -> Expr -> Expr
lamForPi (Pi x xType body) a = Lam x (lamForPi body a)
lamForPi Type a = a
lamForPi e a = error $ show $ "Unexpected" <+> pretty e <+> "in lamForPi"

teleToExpr :: Tele -> Expr -> Expr -> (Expr, Expr)
teleToExpr tele tbody body =
    foldr (\(id, t) (tp, bd) -> (Pi id t tp, Lam id bd)) (tbody, body) tele

unTele :: Expr -> (Tele, Expr)
unTele (Pi x t b) = let (restT, res) = unTele b in ((x, t) : restT, res)
unTele r = ([], r)

checks :: Tele -> Rho -> [Expr] -> Typing Rho
checks [] rho []     = return rho
checks ((x, tpe) : xas) rho (expr : exprs) = do
    let vType = eval rho tpe
    -- traceShowM $ "Checking" <+> pretty x <+> "=" <+> pretty expr <+> colon <+> pretty vType
    -- traceShowM $ "Context" <+> pretty rho
    checkExprHasType expr vType
    (_, ρ, _) <- ask
    let v = eval ρ expr
    checks xas (V x v rho) exprs
checks tele rho exprs =
  throwError $ show $ "checks: incorrect number of arguments" <+> pretty tele <+> pretty exprs


-- Check a telescope
checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x, a) : xas) = do
    checkType a
    (k, ρ, γ) <- ask
    let ρ' = updateRho ρ x (VGen k)
        γ' = updateGamma γ x (eval ρ a)
    local (const (k + 1, ρ', γ')) $ checkTele xas


addDecl :: Decl -> TEnv -> TEnv
addDecl d@(Def name tpe body) (k, rho, gamma) = do
    let r' = D d rho
    let g' = {- traceShow ("Add def" <+> pretty name <+> pretty rho <+> pretty tpe) $ -}
                updateGamma gamma name (VClosure rho tpe)
    (k, r', g')
addDecl d@(Data name tpe cons) (k, rho, gamma) = do
    let r' = D d rho
    let g' = {- traceShow ("Add data" <+> pretty name <+> colon <+> pretty tpe <+> pretty rho) $ -}
                updateGamma gamma name (VClosure rho tpe)
    (k, r', g')


addDecls :: [Decl] -> TEnv -> TEnv
addDecls decls tenv = do
    let env = List.foldl (flip addDecl) tenv decls
    env


{- Macros -}

vnil = (VCon "Nil" [])

quote :: Rho -> Expr -> Val
quote rho e = case e of
    Var x         -> VCon "Var" [VLit x]
    Lit s         -> VCon "Lit" [VLit s]
    Con name ts   -> VCon "Con" [VLit name, foldr (\e a -> VCon "Cons" [quote rho e, a]) vnil ts ]
    App e1 e2     -> VCon "App" [quote rho e1, quote rho e2]
    Type          -> VCon "Type" []
    Lam x body    -> VCon "Lam" [VLit x, quote rho body]
    Let x expr tpe body -> VCon "Let" [VLit x, quote rho expr, quote rho tpe, quote rho body]
    Pi x tpe body -> VCon "Pi" [VLit x, quote rho tpe, quote rho body]
    Split (Just tpe) cases -> VCon "Split" [quote rho tpe, quoteCases cases]
    Splice e      -> eval rho e
    _ -> undefined
  where quoteCases cases = foldr (\e a -> VCon "Cons" [quoteCase e, a]) vnil cases
        quoteCase (Case con args body) = let
            vcases = foldr (\e a -> VCon "Cons" [VLit e, a] ) vnil args
            in VCon "Pair" [VLit con, VCon "Pair" [vcases, quote rho body]]

unquote :: Val -> Expr
unquote val = case val of
    VCon "Var" [VLit x] -> Var x
    VCon "Lit" [VLit s] -> Lit s
    VCon "Con" [VLit s, vlist] -> Con s $ unquoteList vlist
    VCon "App" [f, a] -> App (unquote f) (unquote a)
    VCon "Type" [] -> Type
    VCon "Lam" [VLit s, body] -> Lam s (unquote body)
    VCon "Let" [VLit s, expr, tpe, body] -> Let s (unquote expr) (unquote tpe) (unquote body)
    VCon "Pi"  [VLit s, tpe, body] -> Pi s (unquote tpe) (unquote body)
    VCon "Split"  [tpe, cases] -> Split (Just $ unquote tpe) (unquoteCases cases)
    _ -> error $ "Unsupported unquote: " ++ show val

unquoteCases :: Val -> [Case]
unquoteCases cases = case cases of
    VCon "Cons" [el, tl] -> unquoteCase el : unquoteCases tl
    VCon "Nil" [] -> []
    _  -> error "unquoteCases"

unquoteCase (VCon "Pair" [VLit con, VCon "Pair" [vcases, body]]) = Case con [] (unquote body)
unquoteCase e = error $ "unquoteCase " ++ show e

unquoteList ls = case ls of
    VCon "Cons" [el, tl] -> unquote el : unquoteList tl
    VCon "Nil" [] -> []
    _ -> error $ "This is not a List! " ++ show ls


instance Pretty Decl where
    pretty (Def id tpe body) = pretty id <+> ":" <+> pretty (PEnv 0 tpe) <+> "=" <+> pretty (PEnv 0 body)
    pretty (Data name tpe cons) = "data" <+> pretty name -- <+> colon <+> pretty tpe <+> "=" <+> pretty cons

instance Pretty Constructor where
    pretty (Constructor name params) = pretty name <+> pretty params

data PEnv a = PEnv Int a

foldLam :: Expr -> ([Id], Expr)
foldLam expr = go expr ([], expr) where
    go (Lam name e) result = let (args, body) = go e result in (name : args, body)
    go e (args, _) = (args, e)

instance Pretty (PEnv Expr) where
    pretty (PEnv prec e) = case e of
        Var id -> pretty id
        Lit s  -> dquotes $ pretty s
        Con id args -> wrap 10 prec $ pretty id <+> foldl (\a b -> a <+> pretty b) "" args
        Sum id _ cons -> "∑" <+> pretty id{- <+> list (map pretty cons) -}
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
        Splice e -> "${" <+> pretty e <+> "}"
        Quote e -> "[|" <+> pretty e <+> "|]"

instance Pretty Case where
    pretty (Case con ids e) = pretty con <+> list (map pretty ids) <+> "->" <+> pretty e <+> semi
instance Pretty (PEnv Val) where
    pretty (PEnv prec e) = case e of
        VGen i -> pretty i
        VLit s  -> dquotes $ pretty s
        VCon "Z" args -> "0"
        VCon "S" args -> let
            go :: Val -> Integer
            go (VCon "S" [a]) = 1 + go a
            go (VCon "Z" []) = 0
            go e = error ("Impossible " ++ show e)
            in pretty $ go e

        VCon id args -> parens $ pretty id <+> foldl (\a b -> a <+> pretty b) "" args
        VApp e1 e2 -> wrap 10 prec $ pretty (PEnv 10 e1) <> "·" <> pretty (PEnv 11 e2)
        -- VPi e1 e2 -> wrap 5 prec $ pretty e1 <+> "->>>" <+> pretty e2
        VType -> "Û"
        VClosure rho expr -> pretty rho <+> "⊢" <+> pretty (PEnv prec expr)

instance Pretty Rho where
    pretty ρ = list $ prettyRho ρ

prettyRho ρ = take 2 $ pr ρ
  where
    pr Empty = []
    pr (V id v r) = pretty id <> "=" <> pretty v : pr r
    pr (D d r) = pretty d : pr r

instance Pretty Gamma where pretty (Gamma env) = prettyEnv env

-- instance Pretty TEnv where
    -- pretty t@(k, rho, gamma) = "TEnv"

-- prettyEnv _ = ""
prettyEnv [] = "∅"
prettyEnv ls = list $ fmap p ls
  where p (i, t) = pretty i <> "=" <> pretty t

instance Pretty Val where pretty val = pretty (PEnv 0 val)
instance Pretty Expr where pretty val = pretty (PEnv 0 val)


wrap p p1 = if p < p1 then parens else id

pprint :: Pretty a => a -> String
pprint exp = show $ pretty exp
