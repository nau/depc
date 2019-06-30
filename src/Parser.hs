{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Parser where
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Char
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

keywords = ["let", "in", "data", "split", "λ"]
reservedSymbols = ['|', '=', '\\', '-', ':', ';', '(', ')', '{', '}']

identifier = lexeme $ do
    first <- satisfy (\s -> (isLetter s || isSymbol s) && notElem s reservedSymbols)
    rest <- many alphaNumChar
    let ident = first : rest
    when (ident `elem` keywords) $ unexpected . Label . NonEmpty.fromList $ "reserved " ++ ident
    return ident


telescope = many ptele

ptele = parens $ do
    e1 <- identifier
    symbol ":"
    e2 <- expr
    return $ (e1, e2)

var :: Parser Expr
var = lexeme (try $ Var <$> identifier) <?> "var expected"

universe = try $ do
    symbol "U"
    notFollowedBy alphaNumChar
    return Type

lambda :: Parser Expr
lambda = do
    symbol "\\" <|> symbol "λ"
    idents <- some identifier
    symbol "->"
    e <- expr
    return $ foldr Lam e idents
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
    return $ Case con params e

split = do
    symbol "split"
    tpe <- optional $ parens expr
    cases <- braces $ caseClause `sepEndBy` semi
    return $ Split tpe cases

integer = lexeme L.decimal

nat = do
    i <- integer
    return $ foldr (\_ e -> Con "S" [e]) (Con "Z" []) [1..i]

literal = nat

expr = try split <|> try letins <|> lambda <|> try fun <|> try piType <|> exp1
exp1 = apply <|> exp2
exp2 = universe <|> var <|> literal <|> parens expr

fun = do
    e1 <- exp1
    symbol "->"
    e2 <- expr
    return $ Pi "_" e1 e2

piType = do
    (name, e2) <- ptele
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
    tele <- telescope
    symbol "="
    cons <- constructor `sepBy` symbol "|"
    let tpe = foldr (\(nm, t) a -> Pi nm t a) Type tele
    return $ Data name tpe cons


constructor = do
    name <- identifier
    tele <- telescope
    symbol ":"
    tpe <- expr
    let conType = foldr (\(id, t) acc -> Pi id t acc) tpe tele
    return $ Constructor name conType

def = do
    name <- identifier
    tele <- telescope
    symbol ":"
    tpe <- expr
    symbol "="
    e <- expr
    let (t, b) = teleToExpr tele tpe e
    return $ Def name t b
    <?> "declaration"

decl = try datadecl <|> def

decls = decl `sepEndBy1` semi

toplevel = Left <$> try decls <|> Right <$> expr

contents p = between sc eof p

parseFileNameWith filename parser s = parse (contents parser) filename s

parseWith parser s = parseFileNameWith "<stdin>" parser s

parseFileWith filename parser = do
    contents <- readFile filename
    return $ parseFileNameWith filename parser contents

parseFile filename = parseFileWith filename toplevel

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
