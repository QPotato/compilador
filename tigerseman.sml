structure tigerseman :> tigerseman =
struct

open tigerabs
open tigerpp
open tigersres
open tigertab
open tigertopsort
open tigertrans

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=topLevel(), label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=topLevel(), label="ord",
		formals=[TString], result=TInt RW, extern=true}),
	("chr", Func{level=topLevel(), label="chr",
		formals=[TInt RW], result=TString, extern=true}),
	("size", Func{level=topLevel(), label="size",
		formals=[TString], result=TInt RW, extern=true}),
	("substring", Func{level=topLevel(), label="substring",
		formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
	("concat", Func{level=topLevel(), label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=topLevel(), label="not",
		formals=[TInt RW], result=TInt RW, extern=true}),
	("exit", Func{level=topLevel(), label="exit",
		formals=[TInt RW], result=TUnit, extern=true})
	])

fun esInt t = case t of
                    TInt _     => true
                    | _        => false

fun tipoReal (TTipo s, (env : tenv)) : Tipo =
    (case tabBusca(s , env) of
         NONE => raise Fail "tipoReal Ttipo"
       | SOME t => t)
  | tipoReal (t, _) = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo _) b =
		(*let
			val a = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (1)"
		in
			tiposIguales a b
		end *)
        raise Fail "No deberia pasar! (compara TTipo en tiposiguales)"
  | tiposIguales a (TTipo _) =
	    (*let
			val b = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (2)"
		in
			tiposIguales a b
		end *)
        raise Fail "No deberia pasar! (compara TTipo en tiposiguales)"
  | tiposIguales a b = (a=b)



fun transExp(venv : (string, EnvEntry) Tabla, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
		| trexp(NilExp _)= {exp=nilExp(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt RW}
		| trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
		| trexp(CallExp({func, args}, nl)) =
            let
                val {level = lev, label = name, formals = tformals, result = tresult, extern = ext}  = case tabBusca(func, venv) of
                                  SOME (Func f) => f
                                | SOME _ => error(func ^ " no es una funcion", nl)
                                | _ => error("no hay nada llamado" ^ func, nl)
                val trexargs = List.map trexp args
                val targs = List.map #ty trexargs
                val ls = List.map #exp trexargs

                fun argsCorrectos [] [] = ()
                  | argsCorrectos fs [] = error("faltan argumentos al llamar a "^func, nl)
                  | argsCorrectos [] ars = error("sobran argumentos al llamar a "^func, nl)
                  | argsCorrectos (f::fs) (a::ars) = if tiposIguales f a
                                                    then argsCorrectos fs ars
                                                    else error(func^" esperaba argumento de tipo "^ppTipo f^" pero recibio un "^ppTipo a, nl)
                val _ = argsCorrectos tformals targs

                val isproc = tiposIguales tresult TUnit

            in {exp=callExp(name, ext, isproc, lev, ls), ty=tresult} end
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit 
                then {exp=binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt RW}
		        else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit 
                then {exp=binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt RW}
				else error("Tipos no comparables", nl)
			end
        | trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr 
                then case oper of
						PlusOp => if esInt(tipoReal (tyl, tenv)) 
                                  then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} 
                                  else error("Error de tipos", nl)
						| MinusOp => if esInt(tipoReal (tyl, tenv))
                                     then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} 
                                     else error("Error de tipos", nl)
						| TimesOp => if esInt(tipoReal (tyl, tenv)) 
                                     then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} 
                                     else error("Error de tipos", nl)
						| DivideOp => if esInt(tipoReal (tyl, tenv)) 
                                      then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} 
                                      else error("Error de tipos", nl)
						| LtOp => if esInt(tipoReal (tyl, tenv)) orelse tipoReal (tyl, tenv)=TString 
                                  then {exp=if esInt(tipoReal (tyl, tenv)) 
                                            then binOpIntRelExp {left=expl,oper=oper,right=expr} 
                                            else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							      else error("Error de tipos", nl)
						| LeOp => if esInt(tipoReal (tyl, tenv)) orelse tipoReal (tyl, tenv)=TString 
                                  then {exp=if esInt(tipoReal (tyl, tenv)) 
                                            then binOpIntRelExp {left=expl,oper=oper,right=expr} 
                                            else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							      else error("Error de tipos", nl)
						| GtOp => if esInt(tipoReal (tyl, tenv)) orelse tipoReal (tyl, tenv)=TString 
                                  then {exp=if esInt(tipoReal (tyl, tenv)) 
                                            then binOpIntRelExp {left=expl,oper=oper,right=expr} 
                                            else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							      else error("Error de tipos", nl)
						| GeOp => if esInt(tipoReal (tyl, tenv)) orelse tipoReal (tyl, tenv)=TString 
                                  then {exp=if esInt(tipoReal (tyl, tenv)) 
                                            then binOpIntRelExp {left=expl,oper=oper,right=expr} 
                                            else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							      else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal(t,tenv) of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
                
                (* en cs tenemos una lista de (symbol * tipo ref * int) que corresponde a cómo se definió el tipo *)
                (* en tfields tenemos una lista de (symbol, {exp=e, ty=t}) *)
                
                fun verif (syt, r) [] l = error("No hay un campo "^syt, nl)
                  | verif (syt, r) ((syr, tref, index)::cs) l = if syt = syr
                                                                then if tiposIguales (#ty r) (!tref)
                                                                     then (cs, ((#exp r), index)::l)
                                                                     else error("el campo "^syt^" no es del tipo correcto", nl)
                                                                else let val (cs, nnl) = verif (syt, r) cs l
                                                                     in ((syr, tref, index)::cs, nnl) end

                fun verifica [] [] l = l
                  | verifica (t::ts) [] l = error("Sobran campos!", nl)
                  | verifica [] (c::cs) l = error("Faltan campos!", nl)
                  | verifica (t::ts) cs l = let val (ncs, nnl) = verif t cs l in verifica ts ncs nnl end

				val l = verifica tfields cs []

			in
				{exp=recordExp l, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=(seqExp exprs), ty=tipo } end

		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let val (tvar, acc, lev) = case tabBusca(s, venv) of SOME (Var {ty = TInt RO, ...}) => error("variable read only", nl)
                                                               | SOME (Var {ty = t, access = acc, level = lev}) => (t, acc, lev)
                                                               | SOME _ => error(s ^ " no es una variable", nl)
                                                               | NONE => error("no existe la variable " ^ s, nl)
                val {ty = texp, exp = e} = trexp exp
                val _ = (case tvar of
                             TRecord _ => ()
                           | _ => if texp = TNil
                                  then error("no podes asignar nil a algo que no es un record", nl)
                                  else ())

                val _    = if tiposIguales tvar texp
                           then ()
                           else error("esperaba tipo " ^ ppTipo tvar ^ " pero la expresion es de tipo " ^ ppTipo texp, nl)
                val v = simpleVar(acc, lev)
            in {exp=assignExp {var = v, exp = e}, ty=TUnit} end
		| trexp(AssignExp({var, exp}, nl)) =
            let val {ty = tvar, exp = expvar} = trvar (var, nl)
                val {ty = texp, exp = expexp} = trexp exp
                val _    = if tiposIguales tvar texp
                           then ()
                           else error("esperaba tipo " ^ ppTipo tvar ^ " pero la expresion es de tipo " ^ ppTipo texp, nl)
            in {exp=assignExp {var = expvar, exp = expexp}, ty=TUnit} end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
                val e = if tiposIguales tythen TUnit
                        then ifThenElseExpUnit {test = testexp, then' = thenexp, else' = elseexp}
                        else ifThenElseExp {test = testexp, then' = thenexp, else' = elseexp}
			in
				if esInt (tipoReal(tytest,tenv)) andalso tiposIguales tythen tyelse then {exp=e, ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if esInt (tipoReal(tytest,tenv)) andalso tythen=TUnit then {exp=ifThenExp {test = exptest, then' = expthen}, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val {exp = exptest, ty = tytest} = trexp test
				val {exp = expbody, ty = tybody} = trexp body
                val _ = preWhileForExp()
                val exp = whileExp{test = exptest, body = expbody}
                val _ = postWhileForExp() 
			in
				if esInt (tipoReal(tytest, tenv)) andalso tybody = TUnit then {exp=exp, ty=TUnit}
				else if not (esInt (tipoReal(tytest, tenv))) then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
			 let val {exp = explo,ty = tylo} = trexp lo
                 val _ = if esInt tylo then () else error("la cota de for no es entera", nl)
                 val {exp = exphi, ty = tyhi} = trexp hi
                 val _ = if esInt tyhi then () else error("la cota de for no es entera", nl)

                 val lvl = topLevel ()
                 val acc = allocLocal lvl (!escape)
                 val venv' = tabRInserta(var, Var {ty = TInt RO, access = acc, level = getActualLev()}, venv)

                 val forVar = varDec(acc)

                 val {exp=expbody, ty=tybody} = transExp (venv', tenv) body
                 val _ = if tybody = TUnit then () else error("el body no puede devolver un valor", nl)

             in {exp = forExp {lo = explo, hi = exphi, var = forVar, body = expbody}, ty = TUnit} end
		| trexp(LetExp({decs, body}, _)) =
			let
			    (* Este fold como devuelve en el tercer valor las traducciones de todas las declaraciones *)
				val (venv', tenv', decs') = List.foldl (fn (d, (v, t, l)) =>
                                                           let val (nvenv, ntenv, ndecs) = trdec(v, t) d
                                                           in (nvenv, ntenv,
                                                           ndecs @ l) end)
                                                       (venv, tenv, [])
                                                       decs
				val {exp=expbody, ty=tybody} = transExp (venv', tenv') body
			in
				{exp=letExp(decs', expbody), ty=tybody}
			end
		| trexp(BreakExp nl) = 
			{exp=breakExp(), ty=TUnit}
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let
                val (tarray, u) = case tabBusca(typ, tenv) of
                                     SOME (TArray (t, u)) => (t, u)
                                   | SOME t => error(ppTipo t ^ "no es un array", nl)
                                   | NONE => error("Arreglo de tipo inexistente", nl)
                val {ty = tsize, exp = expsize} = trexp size
                val {ty = tinit, exp = expinit} = trexp init
                val _ = if esInt tsize then () else error("El tamaño del arreglo no es un entero", nl)
                val _ = if tiposIguales (!tarray) tinit then () else
                  error("arreglo de tipo " ^ ppTipo (!tarray) ^ " inicializado con tipo " ^ ppTipo tinit, nl)
			in {exp=arrayExp{size = expsize, init = expinit} , ty = TArray (tarray, u)} end
        and trvar(SimpleVar s, nl) =
            (case tabBusca(s, venv) of
                SOME (Var {ty, access, level}) => {exp = simpleVar(access, level), ty = ty}
              | SOME _ => error(s^" no es una variable", nl)
              | _   => error("no se encontro la variable " ^ s, nl))	
		| trvar(FieldVar(v, s), nl) =
            let fun getRTipoIndex [] x = NONE
                 |  getRTipoIndex ((s, tr, i) :: xs) x = if s = x then SOME ((!tr), i) else getRTipoIndex xs x

                val (tipo, exp, i) = case trvar (v, nl) of
                    {ty = TRecord (l, _), exp} => (case getRTipoIndex l s of
                                                      SOME (t, i) => (t, exp, i)
                                                    | NONE   => error(s ^ " no es un campo del record", nl))
                    | _ => error("la expresion no es un record", nl)
            in {exp = fieldVar(exp, i), ty = tipo} end
		| trvar(SubscriptVar(v, e), nl) =
            let val {ty, exp = expindex} = trexp e
                val _ = if esInt ty then () else error("la expresion no evalua a un entero", nl)
                val (tipo, exparr) = case trvar (v, nl) of
                           {ty = TArray (tr, _), exp} => (!tr, exp)
                         | _ => error("la expresion no es un arreglo", nl)
			in {exp=subscriptVar(exparr, expindex), ty=tipo} end

		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
		    let
		        val {exp = expinit, ty = tinit} = transExp (venv, tenv) init
                val _ = if tinit = TNil
                        then error("no podes asignar nil a una variable que no es un record", pos)
                        else ()
                val tinit' = if esInt tinit
                             then TInt RW
                             else tinit

                val lvl = topLevel ()
                val acc = allocLocal lvl (!escape)
                val venv' = tabRInserta(name, Var {ty = tinit', access = acc, level = getActualLev()}, venv)

		    in (venv', tenv, [assignExp {var = varDec(acc), exp = expinit}]) end
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
		    let
		        val {exp = expinit, ty = tinit} = transExp (venv, tenv) init
		        val typ = case tabBusca(s, tenv) of
		                    SOME t => t
		                    | NONE => error("No se encontro el tipo " ^ s, pos)
                val _ = if tiposIguales tinit typ then () else error("La variable se declaro con tipo " ^ s ^ " pero la trataste de inicializar a algo de tipo " ^ ppTipo tinit, pos)
                
                val lvl = topLevel ()
                val acc = allocLocal lvl (!escape)
                val venv' = tabRInserta(name, Var {ty = typ, access = acc, level = getActualLev()}, venv)
                
		    in (venv', tenv, [assignExp {var = varDec(acc), exp = expinit}]) end
		| trdec (venv,tenv) (FunctionDec fs) =
		    let
                (* Esto se fija que las funciones se tengan nombres distintos*)
                fun funcsDistintas [] = true
                  | funcsDistintas (h :: t) = 
                        let val m = List.map (fn e => (#name h) = (#name e)) t
                            val va = List.foldr (fn (x, y) => x orelse y) false m
                        in funcsDistintas t andalso (not va) end
                val (frecs', ps') = ListPair.unzip fs
                val _ = if funcsDistintas frecs'
                        then ()
                        else error("definiste dos funciones con el mismo nombre en el mismo batch, pavo", List.hd ps')
                (* Esto genera un venv con los prototipos*)
                fun field2tipo pos {typ = NameTy s, ...} = (case tabBusca(s, tenv) of
                                                          SOME t => t
                                                          | NONE => error("No existe el tipo "^s, pos))
                |   field2tipo pos _ = error("Error interno field2tipo", pos)
		        fun insDecls (({name, params, result, ...}, pos), venvIn) = 
		            let 
		                val params' = List.map (field2tipo pos) params
		                val result' = case result of
		                                SOME s => (case tabBusca(s, tenv) of
		                                            SOME t => t
		                                            | NONE => error("No eixste el tipo "^s, pos))
		                                | NONE => TUnit
                        
                        val venv' = tabRInserta(name, Func {level = topLevel(), label = name, formals = params', result = result', extern = false}, venvIn)

                    in venv' end
                val venvDecs = List.foldr insDecls venv fs
                (* Crea un venv que tiene los parametros y se fija que el body tipe *)
                fun trfun ({name, params, result, body}, pos) =
                    let        
                        fun field2tupla {typ = NameTy s, name = n, escape = e} = (case tabBusca(s, tenv) of
                                                                              SOME t => (n, t, e)
                                                                              | NONE => error("Error Interno", pos))
                         |  field2tupla _ = error("Error Interno field2tupla", pos)

                        val params' = List.map field2tupla params

                        fun paramsDistintos [] = true
                          | paramsDistintos (h :: t) = 
                            let val m = List.map (fn e => (#1 h) = (#1 e)) t
                                val va = List.foldr (fn (x, y) => x orelse y) false m
                            in paramsDistintos t andalso (not va) end

                        val _ = if paramsDistintos params'
                                then ()
                                else error("funcion con dos argumentos iguales", pos)

		                val result' = case result of
		                                SOME s => (case tabBusca(s, tenv) of
		                                            SOME t => t
		                                            | NONE => error("Error interno", pos))
		                                | NONE => TUnit
                        val venv' = foldr (fn ((nom, tipo, escape), e) =>
                                                let
                                                    val lvl = topLevel ()
                                                    val acc = allocLocal lvl (!escape)
                                                in tabRInserta(nom, Var {ty = tipo, access = acc, level = getActualLev()}, e)end)
                                          venvDecs
                                          params'
                        val {ty = tbody, exp = e} = transExp (venv', tenv) body
                        val _ = if tiposIguales tbody result' then () else error("La funcion " ^ name ^ " no tipa", pos)
                    in functionDec(e, topLevel(), tiposIguales result' TUnit) end

                val _ = preFunctionDec()
                val exps = List.map trfun fs
                val _ = postFunctionDec()

            in (venvDecs, tenv, exps) end

		| trdec (venv,tenv) (TypeDec ts) =
		    let
                val (ts', ps') = ListPair.unzip ts
                
                fun tiposDistintos [] = true
                  | tiposDistintos (h :: t) = 
                       let val m = List.map (fn e => (#name h) = (#name e)) t
                           val va = List.foldr (fn (x, y) => x orelse y) false m
                       in tiposDistintos t andalso (not va) end

                val _ = if tiposDistintos ts'
                        then ()
                        else error("definiste dos tipos con el mismo nombre en un batch, pavo", List.hd ps')

                val tenv' = fijaTipos ts' tenv handle Ciclo => error("tipos mutuamente recursivos", List.hd ps')
			in (venv, tenv', []) end 
	in trexp end

fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=SOME "int", body=ex}, 0)]],
						body=IntExp (0, 0)}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end

