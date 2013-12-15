module PTS(Sym(..), dummySym,
	ExprA(..), Expr, Type, eLets, ePi,
	ppsExpr,
	freeVars,
	subst,
	nf, alphaEq, typeCheck,
	pts_Fw, PTSVariant(..), checkPTS
	) where
import List(union, (\\), nub)
import Control.Monad.Error

import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text, (<>), parens, ($$), vcat, punctuate, sep, nest)

--import Debug.Trace

data Sym = Sym { unSym :: String }
	deriving (Eq, Ord)

instance Show Sym where
    show (Sym s) = show s

dummySym :: Sym
dummySym = Sym "_"

data ExprA a
	= Pi Sym (ExprA a) (ExprA a)
        | Lam Sym (ExprA a) (ExprA a)
	| Apply (ExprA a) (ExprA a)
	| Var Sym
        | Kind Sym
	| Con Sym a			-- Only used in PTSEval
	deriving (Eq)

instance Show (ExprA a) where
    show e = ppsExpr e

type Expr = ExprA ()	-- () is just some type
type Type = Expr
--type Kind = Expr

type ExprT = ExprA ((),()) -- ((),()) is just some type /= ()
type TypeT = ExprT
type KindT = ExprT

eLet :: (Sym, Type, Expr) -> Expr -> Expr
eLet (s, t, e) b = Apply (Lam s t b) e

eLets :: [(Sym, Type, Expr)] -> Expr -> Expr
eLets stes b = foldr eLet b stes

ePi :: Sym -> ExprA a -> ExprA a -> ExprA a
ePi s t r = if s `elem` freeVars r then Pi s t r else Pi dummySym t r

star, box :: KindT
star = Kind $ Sym "*"
box = Kind $ Sym "*BOX"

data PTSVariant = PTSVariant [(Sym, KindT)] [((KindT, KindT), KindT)]
    deriving (Show, Eq)

pts_Fw :: PTSVariant
pts_Fw = PTSVariant [(Sym "*", box)] [((star, star), star), ((box, star), star), ((box, box), box)]


-----------------------------

-- Make sure all bound variables in scope are unique.
-- The type checker wants this.
rename :: ExprA a -> ExprA a
rename = ren [] []
  where	ren m s (Pi  v t e) = let (m', v') = uniq m s v in Pi  v' (ren m s t) (ren m' (v':s) e)
	ren m s (Lam v t e) = let (m', v') = uniq m s v in Lam v' (ren m s t) (ren m' (v':s) e)
	ren m s (Apply f a) = Apply (ren m s f) (ren m s a)
	ren m _ (Var v) = maybe (Var v) Var (lookup v m)
	ren _ _ e = e
	uniq m s v =
	    if v `elem` s then
		let v' = cloneSym s v
		in  ((v,v'):m, v')
	    else
		(m, v)

-----------------------------

ppsExpr :: ExprA a -> String
ppsExpr e = renderStyle style $ ppExpr 0 e

ppExpr :: Int -> ExprA a -> Doc
ppExpr p (Pi s t e) | s == dummySym = pparens (p > 0) $ ppExpr 1 t <> text "->" <> ppExpr 0 e
ppExpr p (Pi s t e) = pparens (p > 0) $ (parens $ ppSym s <> text ":" <> ppExpr 0 t) <> text "->" <> ppExpr 0 e
ppExpr p (Lam s t e) = pparens (p > 0) $ sep [text "\\" <> ppSym s <> text ":" <> ppExpr 0 t <> text ".",
					      ppExpr 0 e]
ppExpr p ee@(Apply (Lam _ _ _) _) = 
    let (stes, body) = collectBinds [] ee
	ppBind (s, t, Just e) = sep [ppSym s <> text ":" <> ppExpr 0 t <> text " =", nest 4 $ ppExpr 0 e]
	ppBind (s, t, Nothing) = ppSym s <> text ":" <> ppExpr 0 t
	ppBinds xs = vcat $ punctuate (text ";") (map ppBind xs)
	collectBinds bs (Apply (Lam s t b) e) = collectBinds (bs ++ [(s, t, Just e)]) b
	collectBinds bs (Lam s t b) = collectBinds (bs ++ [(s, t, Nothing)]) b
	collectBinds bs b = (bs, b)
    in  pparens (p > 0) $
        (text "let " <> ppBinds stes) $$ (text "in  " <> ppExpr 0 body)
ppExpr p (Apply f a) = pparens (p > 9) $ ppExpr 9 f <> text " " <> ppExpr 10 a
ppExpr _p (Var s) = ppSym s
ppExpr _p (Kind k) = ppSym k
ppExpr _p (Con s _) = ppSym s

ppSym :: Sym -> Doc
ppSym (Sym s) = text s

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

-------------------------------

freeVars :: ExprA a -> [Sym]
freeVars (Pi i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Apply f a) = freeVars f `union` freeVars a
freeVars (Var s) = [s]
freeVars (Kind _) = []
freeVars (Con _ _) = []

allVars :: ExprA a -> [Sym]
allVars (Pi _i k t) = allVars k `union` allVars t
allVars (Lam _i t e) = allVars t `union` allVars e
allVars (Apply f a) = allVars f `union` allVars a
allVars (Var s) = [s]
allVars (Kind _) = []
allVars (Con _ _) = []

cloneSym :: [Sym] -> Sym -> Sym
cloneSym is (Sym sy) = Sym news
  where news =
	    let n = maximum (map getNumSuf ss) :: Integer
		getNumSuf s = if '#' `elem` s then read (tail (dropWhile (/= '#') s)) else 0
	    in  sy ++ "#" ++ show (n+1)
	ss = map unSym is

subst :: Sym -> ExprA a -> ExprA a -> ExprA a
subst v _ e | v == dummySym = e
subst v (Var s) e | v == s = e
subst v x e = sub e
  where	sub (Pi i k t) =
	    if v == i then
		Pi i (sub k) t
	    else if i `elem` fvx then
		let i' = cloneSym vs i
		    t' = subst i (Var i') t
		in  Pi i' (sub k) (sub t')
	    else
		Pi i (sub k) (sub t)
	sub (Lam i k t) =
	    if v == i then
		Lam i (sub k) t
	    else if i `elem` fvx then
		let i' = cloneSym vs i
		    t' = subst i (Var i') t
		in  Lam i' (sub k) (sub t')
	    else
		Lam i (sub k) (sub t)
	sub (Apply f a) = Apply (sub f) (sub a)
	sub ee@(Var i) = if i == v then x else ee
	sub ee@(Kind _) = ee
	sub ee@(Con _ _) = ee
	fvx = freeVars x
	vs = fvx `union` allVars e

whnf :: ExprT -> ExprT
whnf ee = spine ee []
  where spine (Apply f a) as = spine f (a:as)
	spine (Lam s _ e) (a:as) = spine (subst s a e) as
	spine f as = foldl Apply f as

nf :: ExprT -> ExprT
nf ee = spine ee []
  where spine (Apply f a) as = spine f (a:as)
	spine (Lam s t e) [] = Lam s (nf t) (nf e)
	spine (Lam s _ e) (a:as) = spine (subst s a e) as
	spine f as = castApply (nf' f) (map nf as)
	nf' (Pi s k t) = ePi s (nf k) (nf t)
	nf' e = e
	-- An ugly hack for "type conversion".  Note that the
	-- from and to type must be identical for the CAST to
	-- be removed.
	castApply (Var (Sym "CAST")) (t1:t2:a:as) | alphaEq t1 t2 = spine a as
	castApply f as = foldl Apply f as

substVar :: Sym -> Sym -> ExprA a -> ExprA a
substVar _s s' e | s' == dummySym = e
substVar s s' e = subst s (Var s') e

alphaEq :: (Eq a) => ExprA a -> ExprA a -> Bool
alphaEq e1 e2 | e1 == e2 = True
alphaEq (Pi s k t) (Pi s' k' t') = alphaEq k k' && alphaEq t (substVar s' s t')
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq t t' && alphaEq e (substVar s' s e')
alphaEq (Apply f a) (Apply f' a') = alphaEq f f' && alphaEq a a'
alphaEq _ _ = False

betaEq :: ExprT -> ExprT -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

-------------------------------

type ErrorMsg = String

data Env = Env { kinds :: [KindT],
	         axioms :: [(Sym, KindT)],
	         rules :: [((KindT, KindT), KindT)],
	         gamma :: [(Sym, TypeT)]
		}
		deriving (Show)

initalEnv :: PTSVariant -> Env
initalEnv (PTSVariant as rs) = Env ks as rs []
  where ks = nub $ [ k | (s, a) <- as, k <- [ Kind s, a ] ] ++ [ k | ((r1,r2),r3) <- rs, k <- [ r1,r2,r3] ]

extend :: Sym -> TypeT -> Env -> Env
extend s _t r | s == dummySym = r
extend s t r = r { gamma = (s, t) : gamma r }

findVar :: Env -> Sym -> TC TypeT
findVar r s =
    case lookup s (gamma r) of
    Just t -> return t
    Nothing -> throwError ("Cannot find variable " ++ unSym s)

findKind :: Env -> Sym -> TC KindT
findKind r s =
    case lookup s (axioms r) of
    Just t -> return t
    Nothing -> throwError ("Cannot find kind " ++ unSym s)

hasKind :: Env -> KindT -> TC ()
hasKind r s =
    if elem s (kinds r) then
        return ()
    else
        throwError ("No kind " ++ show s)

type TC a = Either ErrorMsg a

tCheck :: String -> Env -> Expr -> TC ExprType
tCheck _msg r e = do
--     () <- ctrace (isAp e) ("Enter: " ++ msg ++ " " ++ show (e, r)) $ return ()
     et <- tCheck' r e
--     () <- ctrace (isAp e) ("Exit: " ++ msg ++ " " ++ show (e, t)) $ return ()
     return et

{-
ctrace True s x = trace s x
ctrace False _ x = x
isAp (Apply (Lam _ _ _) _) = False
isAp (Apply _ _) = True
isAp _ = False
-}

unUp :: String -> UKind -> TC KindT
unUp msg Up = throwError $ "unUp " ++ msg
unUp _ (A s) = return s

data ExprType = ExprT ::: TypeT

tCheck' :: Env -> Expr -> TC ExprType
tCheck' r ee@(Pi x k t) = do
    s <- sort r (A (convert k))
    (k', r') <- extendChk x k r
    t' ::: kt <- tCheckRed "Pi2" r' t
    k'' <- unUp ("Pi " ++ show (ee, k, s, kt, r)) $ rho r s (A kt)
    return $ Pi x k' t' ::: k''
tCheck' r ee@(Lam s t e) = do
    elmt r (A (convert ee)) >>= unUp "Lam"
    (t', r') <- extendChk s t r
    e' ::: te <- tCheck "Lam2" r' e
    return $ Lam s t' e' ::: ePi s t' te
-- XXX Type check let by substitution
-- XXX Should add it to the environment
tCheck' r (Apply f@(Lam s t e) a) = do
    t' ::: _kt <- tCheck "Let1" r t
    _a' ::: ta <- tCheck "Let2" r a
    if betaEq ta t' then do
        tCheck "Let3" r (subst s a e)
     else
	throwError $ "Bad (let) argument " ++ show a ++ "\nof function " ++ show f ++ "\nhas type    " ++
		      show ta ++ "\nshould have " ++ show t ++ "\n" ++ show (nf ta) ++ "\n" ++ show (nf t')
tCheck' r (Apply f a) = do
    f' ::: tf <- tCheckRed "Ap1" r f
    a' ::: ta <- tCheck "Ap2" r a
    case tf of
     Pi x at rt ->
	if betaEq ta at then
	    return $ Apply f' a' ::: subst x a' rt
	else
	throwError $ "Bad argument " ++ show a ++ "\nof function " ++ show f ++ "\nhas type    " ++
		      show ta ++ "\nshould have " ++ show at ++ "\n" ++ show (nf ta) ++ "\n" ++ show (nf at)
     t -> throwError $ "Not a function " ++ show (f, t)
tCheck' r (Var s)  = do t <- findVar  r s; return $ Var  s ::: t
tCheck' r (Kind s) = do t <- findKind r s; return $ Kind s ::: t
tCheck' _r (Con _ _) = error "tCheck Con"

tCheckRed :: String -> Env -> Expr -> TC ExprType
tCheckRed msg r e = do
    e' ::: t <- tCheck msg r e
    return $ e' ::: whnf t

typeCheck :: PTSVariant -> Expr -> (ExprT, TypeT)
typeCheck v e =
    case tCheck "Top" (initalEnv v) (rename e) of
    Left msg -> error ("Type error:\n" ++ msg)
    Right (e' ::: t) -> (e', t)

extendChk :: Sym -> Type -> Env -> TC (TypeT, Env)
extendChk x t r = do
    t' ::: k <- tCheckRed "extendChk" r t
    hasKind r k
    return (t', extend x t' r)

convert :: Expr -> ExprT
convert (Pi s t e) = Pi s (convert t) (convert e)
convert (Lam s t e) = Lam s (convert t) (convert e)
convert (Apply f a) = Apply (convert f) (convert a)
convert (Var s) = Var s
convert (Kind s) = Kind s
convert (Con _ _) = error "convert"

-------------------------------

-- Check that the PTS is functional and injective
checkPTS :: PTSVariant -> PTSVariant
checkPTS v =
    if isFunctional v then
	if isInjective v then
	    v
	else
	    error "The PTS is not injective"
    else
	error "The PTS is not functional"

isFunctional :: PTSVariant -> Bool
isFunctional (PTSVariant as rs) = all isAxiom1Func as && all isRule1Func rs
  where isAxiom1Func (a, _) = length (nub [ b | (a', b) <- as, a == a' ]) == 1
	isRule1Func ((a,b),_) = length (nub [ c | ((a', b'), c) <- rs, a == a' && b == b' ]) == 1

isInjective :: PTSVariant -> Bool
isInjective (PTSVariant as rs) = all isAxiom1Inj as && all isRule1Inj rs
  where isAxiom1Inj (_, b) = length (nub [ a | (a, b') <- as, b == b' ]) == 1
	isRule1Inj ((a,_),c) = length (nub [ b | ((a', b), c') <- rs, a == a' && c == c' ]) == 1

-------------------------------

rlookup :: (Eq b) => b -> [(a, b)] -> Maybe a
rlookup _b [] = Nothing
rlookup b ((a,b'):_) | b == b' = Just a
rlookup b (_:xs) = rlookup b xs

-------------------------------

-- Represent the up arrow
data Up a = A a | Up
	deriving (Eq, Show)

type UKind = Up KindT

plus :: Env -> UKind -> UKind
plus r (A (Kind s)) =
    case lookup s (axioms r) of
	Just s' -> A s'
	Nothing -> Up
plus _ _ = Up

minus :: Env -> UKind -> UKind
minus r (A s@(Kind _)) =
    case rlookup s (axioms r) of
	Just s' -> A (Kind s')
	Nothing -> Up
minus _ _ = Up

rho :: Env -> UKind -> UKind -> UKind
rho r (A s1@(Kind _)) (A s2@(Kind _)) =
    case lookup (s1, s2) (rules r) of
	Just s3 -> A s3
	Nothing -> Up
rho _ _ _ = Up

mu :: Env -> UKind -> UKind -> UKind
mu r (A s1@(Kind _)) (A s2@(Kind _)) =
    case [ s3' | ((s1', s3'), s2') <- rules r, s1==s1', s2==s2' ] of
	(s3 : _) -> A s3
	_ -> Up
mu _ _ _ = Up

findVarGamma :: Env -> Sym -> TC (Env, TypeT)
findVarGamma (Env k a r sts) x = loop sts
  where loop [] = throwError ("findVarGamma: " ++ show x)
	loop ((s, t):sts') =
		if x == s then return (Env k a r sts', t) else loop sts'

sort :: Env -> Up ExprT -> TC UKind
sort _r Up = return Up
sort r s@(A (Kind _)) = return $ plus r s
sort r (A (Pi x a b)) = liftM2 (rho r) (sort r (A a)) (sort (extend x a r) (A b))
sort r e = liftM (minus r) (elmt r e)

elmt :: Env -> Up ExprT -> TC UKind
elmt _r Up = return Up
elmt r (A (Var x)) = do (r0, a) <- findVarGamma r x; sort r0 (A a)
elmt r (A (Apply m n)) = liftM2 (mu r) (elmt r (A n)) (elmt r (A m))
elmt r (A (Lam x a m)) = liftM2 (rho r) (sort r (A a)) (elmt (extend x a r) (A m))
elmt r e = liftM (plus r) (sort r e)
