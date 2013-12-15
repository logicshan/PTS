module PTSEval(eval) where
import Char(isDigit)
import Monad(mplus)

import PTS

--
-- Evaluate an expression with primitives.
-- This is pretty ugly.  It locates primitives which have
-- been lambda bound by looking at the name of the bound variable.
-- It's a quick hack, but it works for now.

--import Debug.Trace

eApply :: ExprC -> [ExprC] -> ExprC
eApply f as = foldl Apply f as

type ExprC = ExprA Const

data Const
	= Delta ([ExprC] -> ExprC)
	| CInt Integer
	| CChar Char
--	deriving (Show, Eq)

eval :: Expr -> ExprC
eval e = hnfd (applyConstants e)

hnfd :: ExprC -> ExprC
hnfd ee = {-trace (show ee) $ -} spine ee []
  where spine (Apply f a) as = spine f (a:as)
	spine (Lam s t e) [] = Lam s (hnfd t) (hnfd e)
	spine (Lam s _ e) (a:as) = spine (subst s a e) as
	spine f@(Con _ (Delta d)) as = d (f:as)
	spine f as = eApply f as

applyConstants :: Expr -> ExprC
applyConstants (Lam s t e) =
    case findConst s of
    Nothing -> Lam s (idExpr t) (applyConstants e)
    Just c -> Apply (Lam s (idExpr t) (applyConstants e)) (Con s c)
applyConstants (Apply (Lam s t e) b) = Apply (Lam s (idExpr t) (applyConstants e)) (idExpr b)
applyConstants e = idExpr e

idExpr :: Expr -> ExprC
idExpr (Lam s t e) = Lam s (idExpr t) (idExpr e)
idExpr (Pi s t e) = Pi s (idExpr t) (idExpr e)
idExpr (Apply f a) = Apply (idExpr f) (idExpr a)
idExpr (Var s) = Var s
idExpr (Kind s) = Kind s
idExpr (Con _ _) = error "idExpr Con"

findConst :: Sym -> Maybe Const
findConst (Sym s) = lookup s constants `mplus` integer s `mplus` char s

integer :: String -> Maybe Const
integer s | all isDigit s = Just (CInt (read s))
integer _ = Nothing

char :: String -> Maybe Const
char ['\'',c,'\''] = Just (CChar c)
char _ = Nothing

constants :: [(String, Const)]
constants = [
    ("Integer", cType "Integer"),
    ("Char", cType "Char"),
    ("primIntegerAdd", binop (+)),
    ("primIntegerSub", binop (-)),
    ("primIntegerMul", binop (*)),
    ("primIntegerDiv", binop div),
    ("primIntegerEq", binopbool (==)),
    ("fix", Delta fix),
    ("CAST", Delta cast)
    ]

fix :: [ExprC] -> ExprC
fix (cfix : t : f : as) = hnfd $ eApply (Apply f (Apply (Apply cfix t) f)) as
fix (cfix : as) = eApply cfix as
fix xs = error ("impossible " ++ show xs)

cast :: [ExprC] -> ExprC
cast (_f:_t1:_t2:f:es) = hnfd (eApply f es)
cast xs = error ("impossible " ++ show xs)

binop :: (Integer -> Integer -> Integer) -> Const
binop op = Delta (fun . map hnfd)
  where fun [_, Con _ (CInt x), Con _ (CInt y)] = Con (Sym (show s)) (CInt s) where s = x `op` y
	fun (f:as) = eApply f as
	fun xs = error ("impossible " ++ show xs)

binopbool :: (Integer -> Integer -> Bool) -> Const
binopbool op = Delta (fun . map hnfd)
  where fun [_, Con _ (CInt x), Con _ (CInt y), _, true, false] = if x `op` y then true else false
	fun (f:as) = eApply f as	
	fun xs = error ("impossible " ++ show xs)

cType :: String -> Const
cType s = Delta $ \ as -> eApply (Var (Sym s)) (tail as)
