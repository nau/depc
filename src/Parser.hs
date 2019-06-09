{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Parser where
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.String
import Data.Void
import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Debug.Trace

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Core

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

keywords = ["let", "in", "data", "case", "of"]

identifier = lexeme $ do
    ident <- (:) <$> letterChar <*> many alphaNumChar
    when (ident `elem` keywords) $ unexpected . Label . NonEmpty.fromList $ "reserved " ++ ident
    return ident


telescope = identifier

data PTele = PTele Id Expr

ptele = parens $ do
    e1 <- identifier
    symbol ":"
    e2 <- expr
    return $ PTele e1 e2

var :: Parser Expr
var = lexeme (try $ Var <$> identifier) <?> "var expected"

universe = symbol "U" >> return Type

lambda :: Parser Expr
lambda = do
    symbol "\\" <|> symbol "λ"
    teles <- some telescope
    symbol "->"
    e <- expr
    return $ foldr Lam e teles
    <?> "lambda expression"

letins = do
    symbol "let"
    name <- identifier
    symbol ":"
    tpe <- expr
    traceM $ "let tpe = " ++ show tpe
    symbol "="
    e1 <- expr
    traceM $ "let e1 = " ++ show e1
    symbol "in"
    e2 <- expr
    return $ Let name e1 tpe e2

caseClause = do
    (con : params) <- some identifier
    symbol "->"
    e <- expr
    symbol ";"
    return $ Case con params e

split = do
    symbol "split"
    tpe <- parens expr
    cases <- braces $ many caseClause
    return $ Split tpe cases


expr = try split <|> try letins <|> lambda <|> try fun <|> try piType <|> exp1
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

datadecl = do
    symbol "data"
    name <- identifier
    symbol "="
    cons <- constructor `sepBy` symbol "|"
    symbol ";"
    return $ Data name cons


constructor = do
    name <- identifier
    symbol ":"
    tpe <- expr
    return $ Constructor name tpe

def = do
    name <- identifier
    symbol ":"
    tpe <- expr
    symbol "="
    e <- expr
    symbol ";"
    return $ Def name tpe e
    <?> "declaration"

decl = try datadecl <|> def

decls = some decl

toplevel = Left <$> try decls <|> Right <$> expr

contents p = between sc eof p

parseWith parser s = parse (contents parser) "<stdin>" s

pp :: String -> Expr
pp s = case parseWith toplevel s of
    Left err -> error $ parseErrorPretty err
    Right (Right expr) -> expr
    Right (Left _) -> error "Decls but want expr"

pd :: String -> [Decl]
pd s = case parseWith toplevel s of
    Left err -> error $ parseErrorPretty err
    Right (Right expr) -> error "Want decls"
    Right (Left decls) -> decls


s :: QuasiQuoter
s = QuasiQuoter {
    quoteExp  = return . LitE . StringL,

    quotePat  = \_ -> fail "illegal QuasiQuote \
                            \(allowed as expression only, used as a pattern)",
    quoteType = \_ -> fail "illegal QuasiQuote \
                            \(allowed as expression only, used as a type)",
    quoteDec  = \_ -> fail "illegal raw string QuasiQuote \
                            \(allowed as expression only, used as a declaration)"
}
