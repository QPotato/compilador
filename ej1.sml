open tigerabs

fun max (x, y) = if x > y then x else y
fun maxL xs = foldl max 0 xs

fun maxargsv (SubscriptVar (_, e)) = maxargs e
 |  maxargsv _ = 0

and maxargsd (FunctionDec xs) = let val elist = map (fn ({body, ...}, _) => body) xs
                                in maxL (map maxargs elist) end
 |  maxargsd (VarDec ({init, ...}, _)) = maxargs init
 |  maxargsd _ = 0

and maxargs (CallExp ({func, args}, _)) = let val mArgs = maxL (map maxargs args)
                                          in if func = "print"
                                             then max ((length args), mArgs)
                                             else mArgs end
 |  maxargs (OpExp ({left, right, ...}, _)) = max (maxargs left, maxargs right)
 |  maxargs (RecordExp ({fields, ...}, _)) = let val exps = map (fn (x, y) => y) fields
                                             in maxL (map maxargs exps) end
 |  maxargs (SeqExp (exps, _)) = maxL (map maxargs exps)
 |  maxargs (AssignExp ({var, exp}, _)) = max (maxargsv var, maxargs exp)
 |  maxargs (IfExp ({test, then', else' = NONE}, _)) = max (maxargs test, maxargs then')
 |  maxargs (IfExp ({test, then', else' = SOME e}, _)) = maxL (map maxargs [test, then', e])
 |  maxargs (WhileExp ({test, body}, _)) = max (maxargs test, maxargs body)
 |  maxargs (ForExp ({lo, hi, body, ...}, _)) = maxL (map maxargs [lo, hi, body])
 |  maxargs (LetExp ({decs, body}, _)) = max (maxL (map maxargsd decs), maxargs body)
 |  maxargs (ArrayExp ({size, init, ...}, _)) = max (maxargs size, maxargs init)
 |  maxargs _ = 0

fun cantplusv (SubscriptVar (_, e)) = cantplus e
 |  cantplusv _ = 0

and cantplusd (FunctionDec xs) = let val elist = map (fn ({body, ...}, _) => body) xs
                                 in foldl op+ 0 (map cantplus elist) end
 |  cantplusd (VarDec ({init, ...}, _)) = cantplus init
 |  cantplusd _ = 0

and cantplus (CallExp ({func, args}, _)) = foldl op+ 0 (map cantplus args)
 |  cantplus (OpExp ({left, oper = PlusOp, right}, _)) = 1 + cantplus left + cantplus right
 |  cantplus (OpExp ({left, right, ...}, _)) = cantplus left + cantplus right
 |  cantplus (RecordExp ({fields, ...}, _)) = let val exps = map (fn (x, y) => y) fields
                                              in foldl op+ 0 (map cantplus exps) end
 |  cantplus (SeqExp (exps, _)) = foldl op+ 0 (map cantplus exps)
 |  cantplus (AssignExp ({var, exp}, _)) = cantplusv var + cantplus exp
 |  cantplus (IfExp ({test, then', else' = NONE}, _)) = cantplus test + cantplus then'
 |  cantplus (IfExp ({test, then', else' = SOME e}, _)) = cantplus test + cantplus then' + cantplus e
 |  cantplus (WhileExp ({test, body}, _)) = cantplus test + cantplus body
 |  cantplus (ForExp ({lo, hi, body, ...}, _)) = cantplus lo + cantplus hi + cantplus body
 |  cantplus (LetExp ({decs, body}, _)) = (foldl op+ 0 (map cantplusd decs)) + cantplus body
 |  cantplus (ArrayExp ({size, init, ...}, _)) = cantplus size + cantplus init
 |  cantplus _ = 0


