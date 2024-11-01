module Parser where

import AST

import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Expr hiding (Infix)
import Text.Parsec.Token
import qualified Text.Parsec.Expr as P

parser :: String -> Either ParseError Program
parser = parse programParser ""

parseFunDef :: String -> Either ParseError FunDef
parseFunDef = parse funcParser ""

parseExpr :: String -> Either ParseError Expr
parseExpr = parse exprparser ""

programParser = do
  m_whiteSpace
  funcs <- many funcParser
  return (Program funcs)

funcParser = do
  n <- m_identifier
  m_reserved "="
  e <- exprparser 
  return (FunDef n $ e ) 


def = haskellDef { reservedOpNames = "div" : reservedOpNames haskellDef }

TokenParser { parens = m_parens
            , identifier = m_identifier
            , symbol = m_symbol
            , reservedOp = m_reservedOp
            , reserved = m_reserved
            , commaSep = m_commaSep
            , whiteSpace = m_whiteSpace
            , natural = m_natural
            } = makeTokenParser def


idPlusEq = do _ <- exprparser
              m_reserved "="

plit =
     do t <- m_symbol "True"
        return (Lit (LitBool True))
 <|> do t <- m_symbol "False"
        return (Lit (LitBool False))
 <|> do t <- m_symbol "[]"
        return (Lit (LitNil))
 <|> try (fmap (Lit . LitInt) m_natural)

pterm
  =  m_parens exprparser 
 <|> plit
 <|> try (do v <- m_identifier
             notFollowedBy (m_reservedOp "=")
             return (Var v))
 <|> do m_reserved "case"
        e <- exprparser
        m_reservedOp "of"
        m_reserved "[]"
        m_reservedOp "->"
        e1 <- exprparser
        m_reserved ";"
        m_symbol "("
        x <- m_identifier
        m_reserved ":"
        xs <- m_identifier
        m_symbol ")"
        m_reserved "->"
        e2 <- exprparser
        return (Case e e1 (x, xs, e2))
 <|> do m_reserved "if"
        cnd <- exprparser
        m_reserved "then"
        e1 <- exprparser
        m_reserved "else"
        e2 <- exprparser
        return (If cnd e1 e2)
 <|> do m_symbol "\\"
        vn <- m_identifier
        m_reservedOp "->"
        e <- exprparser
        return (Lam vn e)
  

exprparser :: Parser Expr
exprparser = buildExpressionParser table pterm <?> "expression"


         
app = m_whiteSpace
            *> notFollowedBy (choice . map m_reservedOp $ (reservedOpNames def))
            *> return App
            
table =
  [ [ P.Infix app AssocLeft ]
  , [ P.Infix (m_reservedOp "."   >> return (Infix Comp)) AssocLeft]
  , [ P.Infix (m_reservedOp "*"   >> return (Infix Mult)) AssocLeft
    , P.Infix (m_reservedOp "div" >> return (Infix Div))  AssocLeft
    ]
  , [ P.Infix (m_reservedOp "-"   >> return (Infix Sub))  AssocLeft
    , P.Infix (m_reservedOp "+"   >> return (Infix Add))  AssocLeft
    ]
  , [ P.Infix (m_reservedOp ":"   >> return (Infix Cons))  AssocLeft
    , P.Infix (m_reservedOp "++" >> return (Infix Append))  AssocLeft]
  , [ P.Infix (m_reservedOp "=="  >> return (Infix Eq))   AssocLeft
    , P.Infix (m_reservedOp ">"   >> return (Infix GTh))  AssocLeft
    , P.Infix (m_reservedOp "<"   >> return (Infix LTh))  AssocLeft
    ]
  , [P.Infix (m_reservedOp "&&" >> return (Infix And))  AssocLeft]
  , [P.Infix (m_reservedOp "||" >> return (Infix Or))  AssocLeft]
  ]
