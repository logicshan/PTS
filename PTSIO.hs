module PTSIO(parseExpr) where
import Char(isAlphaNum, isAlpha)

import Text.ParserCombinators.ReadP(ReadP, (+++), char, munch, munch1, many1, string, pfail, sepBy1,
	 optional, many, skipSpaces, readP_to_S, look)

import PTS

parseExpr :: String -> (PTSVariant, Expr)
parseExpr s =
    let ess = readP_to_S pTop (removeComments s)
    in  case filter (null . snd) ess of
        [(e, "")] -> e
        _ -> error ("bad parse: " ++ show ess)

removeComments :: String -> String
removeComments "" = ""
--removeComments ('#':cs) = skip cs
removeComments ('-':'-':cs) = skip cs
  where skip "" = ""
	skip s@('\n':_) = removeComments s
	skip (_:s) = skip s
removeComments (c:cs) = c : removeComments cs

pTop :: ReadP (PTSVariant, Expr)
pTop = do
    v <- pPTSVariant +++ return pts_Fw
    e <- pExpr
    skipSpaces
    return (v, e)

pPTSVariant :: ReadP PTSVariant
pPTSVariant = do
    skeyword "PTS"
    r <- many (do s <- pKSym; schar ':'; k <- pKind; return (s, k))
    v <- many (pParen (do k1 <- pKind; schar ','; k2 <- pKind; schar ','; k3 <- pKind; return ((k1, k2), k3)))
    schar ';'
    return $ PTSVariant r v

pExpr :: ReadP Expr
pExpr = pAExpr +++ pPi +++ pLam +++ pLet

pAExpr :: ReadP Expr
pAExpr = pAtomExpr +++ pApply

pType :: ReadP Expr
pType = pExpr

pAtomExpr :: ReadP Expr
pAtomExpr = pVar +++ pKind +++ pParen pExpr

pParen :: ReadP a -> ReadP a
pParen p = do
    schar '('
    e <- p
    schar ')'
    return e

pApply :: ReadP Expr
pApply = do
    f <- pAtomExpr
    as <- many1 pAtomExpr
    return $ foldl Apply f as

pLet :: ReadP Expr
pLet = do
    skeyword "let"
    stes <- sepBy1 pBind (schar ';')
    optional (schar ';')
    skeyword "in"
    b <- pExpr
    return $ eLets' stes b

pBind :: ReadP (Sym, Type, Maybe Expr)
pBind = do
    let addT (s, t) r = ePi s t r
	addE (s, t) e = Lam s t e
    sy <- pSym
    args <- many pArg
    schar ':'
    rt <- pType
    (do
        schar '='
        be <- pExpr
        return (sy, foldr addT rt args, Just $ foldr addE be args)
     ) +++
       (return (sy, foldr addT rt args, Nothing))

eLet' :: (Sym, Type, Maybe Expr) -> Expr -> Expr
eLet' (s, t, Nothing) b = Lam s t b
eLet' (s, t, Just e) b = Apply (Lam s t b) e

eLets' :: [(Sym, Type, Maybe Expr)] -> Expr -> Expr
eLets' stes b = foldr eLet' b stes

pPi :: ReadP Expr
pPi = pPiQuant +++ pPiArrow

pPiQuant :: ReadP Expr
pPiQuant = do
    sstring "\\/" +++ sstring "|~|"
    (s, t) <- pVarType +++ pParen pVarType
    schar '.'
    e <- pExpr
    return $ Pi s t e

pPiArrow :: ReadP Expr
pPiArrow = do
    ts <- many1 (do e <- pPiArg; sstring "->"; return e)
    rt <- pAExpr
    return $ foldr (\ (s, t) r -> Pi s t r) rt ts
  where pPiArg = pPiNoDep +++ pArg
	pPiNoDep = do
	    t <- pAExpr
	    return (dummySym, t)

pArg :: ReadP (Sym, Type)
pArg = pParen pVarType

pVarType :: ReadP (Sym, Type)
pVarType = do
    s <- pSym
    schar ':'
    t <- pType
    return (s, t)
    
pLam :: ReadP Expr
pLam = do
    schar '\\' +++ sstring "/\\"
    (s, t) <- pVarType +++ pParen pVarType
    schar '.'
    e <- pExpr
    return $ Lam s t e

pVar :: ReadP Expr
pVar = do
    s <- pSym
    return $ Var s

pKind :: ReadP (ExprA a)
pKind = do
    s <- pKSym
    return $ Kind $ s

pKSym :: ReadP Sym
pKSym = do
    schar '*'
    cs <- munch isSym
    return $ Sym $ '*':cs

pSym :: ReadP Sym
pSym = do
    skipSpaces
    cs <- munch1 isSym
    if cs `elem` ["let", "in"] then
	pfail
     else
        return $ Sym cs

schar :: Char -> ReadP ()
schar c = do
    skipSpaces
    char c
    return ()

sstring :: String -> ReadP ()
sstring s = do
    skipSpaces
    string s
    return ()

skeyword :: String -> ReadP ()
skeyword s = do
    sstring s
    cs <- look
    case cs of
     c:_ | isAlpha c -> pfail
     _ -> return ()

isSym :: Char -> Bool
isSym c = isAlphaNum c || c `elem` "_'#"
