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

type Id = String
type Env = [(Id, Val)]

data Expr
  = Var Id
  | App Expr Expr
  | Lam Id Expr
  | Let Id Expr Expr Expr
  | Pi Id Expr Expr
  | Type
  deriving (Show)

data Val
  = VGen Int
  | VApp Val Val
  | VType
  | VClosure Env Expr
  deriving (Show)


instance IsString Expr where
   fromString = Var

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
            wrong -> error $ "Expected Pi but got " ++ show wrong
        Pi x a b -> case whnf v of
            VType -> checkType (k, rho, gamma) a && checkType (k + 1, update rho x (VGen k), update gamma x (VClosure rho a)) b
            _ -> error $ "Expected Type but got" ++ show (whnf v)
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
                else error $ "Can't infer type for App, expected Pi: " ++ show e ++ ", " ++ show infer
            _ -> error $ "Can't infer type for App, expected Pi: " ++ show e ++ ", " ++ show infer
    Type -> VType
    _ -> error $ "Couldn't infer type for " ++ show e

typecheck m a =
    checkType (0, [], []) a && checkExpr (0, [], []) m (VClosure [] a)

type Parser = Parsec Void String
sc :: Parser () -- ‘sc’ stands for “space consumer”
sc = L.space (void space1) lineComment blockComment
  where lineComment = (string "--" <|> string "#") *> void (takeWhileP (Just "character") (/= '\n'))
        blockComment = L.skipBlockComment "{-" "-}"

lexeme = L.lexeme sc
symbol = L.symbol sc
parens = between (symbol "(") (symbol ")")
brackets  = between (symbol "[") (symbol "]")
braces  = between (symbol "{") (symbol "}")
comma = symbol ","
semi = symbol ";"
commaSep p  = p `sepBy` comma
trailCommaSep p  = p `sepEndBy` comma
semiSep  p  = p `sepBy` semi


identifier = lexeme $ try $ (:) <$> letterChar <*> many alphaNumChar


telescope = identifier

data PTele = PTele Id Expr

ptele = parens $ do
    e1 <- identifier
    symbol ":"
    e2 <- expr
    return $ PTele e1 e2

var :: Parser Expr
var = (lexeme $ try $ Var <$> identifier) <?> "var expected"

universe = symbol "U" >> return Type

lambda :: Parser Expr
lambda = do
    symbol "\\" <|> symbol "λ"
    teles <- some telescope
    symbol "->"
    e <- expr
    return $ foldr Lam e teles
    <?> "lambda expression"

expr = lambda <|> try fun <|> try piType <|> exp1
exp1 = apply <|> exp2
exp2 = universe <|> var <|> parens expr

fun = do
    e1 <- exp1
    symbol "->"
    e2 <- expr
    return $ Pi "_" e1 e2

piType = do
    PTele name e2 <- ptele
    symbol "->"
    e <- expr
    return $ Pi name e2 e

apply = try $ do
    f <- exp2
    args <- some exp2
    return (foldl App f args) <?> "apply"

toplevel = expr

contents p = between sc eof p

parseWith :: Parser Expr -> String -> Either (ParseError (Token String) Void) Expr
parseWith parser s = parse (contents parser) "<stdin>" s

pp :: String -> Expr
pp s = case parseWith toplevel s of
    Left err -> error $ parseErrorPretty err
    Right exprs -> exprs


(==>) = Pi "_"
infixr ==>

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
    let expr = pp "λ A x y -> x y"
        eTpe = pp "(A : U) -> (A -> A) -> A -> A"
    print $ typecheck expr eTpe