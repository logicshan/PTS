module Main(main) where
import IO(hGetContents, stdin)

import PTS(ExprA, ppsExpr, nf, typeCheck, checkPTS)
import PTSIO(parseExpr)
import PTSEval(eval)

prExpr :: ExprA a -> IO ()
prExpr = putStrLn . ppsExpr

main :: IO ()
main = do
    inp <- hGetContents stdin
    let (v, e) = parseExpr inp
	v' = checkPTS v
	(e', t) = typeCheck v' e
	e'' = nf e'
    prExpr e
    putStrLn ""
    putStrLn $ " : " ++ ppsExpr (nf t)
    putStrLn " = "
    prExpr $ e''
    putStrLn " === "
    prExpr $ eval e
