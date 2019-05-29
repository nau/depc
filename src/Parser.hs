module Parser where
import qualified Data.List as List
import Data.Maybe
import Data.String
import Data.Void
import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
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


identifier = lexeme $ try $ (:) <$> letterChar <*> many alphaNumChar


telescope = identifier

data Decl = Def Id Expr Expr
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

decl = do
    name <- identifier
    symbol ":"
    tpe <- expr
    symbol "="
    e <- expr
    symbol ";"
    return $ Def name tpe e
    <?> "declaration"

toplevel = expr

contents p = between sc eof p

parseWith :: Parser Expr -> String -> Either (ParseError (Token String) Void) Expr
parseWith parser s = parse (contents parser) "<stdin>" s

pp :: String -> Expr
pp s = case parseWith toplevel s of
    Left err -> error $ parseErrorPretty err
    Right exprs -> exprs