structure tigerseman :> tigerseman =
struct

open tigerabs
open tigerpp
open tigersres
open tigertab

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=mainLevel, label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=mainLevel, label="ord",
		formals=[TString], result=TInt RW, extern=true}),
	("chr", Func{level=mainLevel, label="chr",
		formals=[TInt RW], result=TString, extern=true}),
	("size", Func{level=mainLevel, label="size",
		formals=[TString], result=TInt RW, extern=true}),
	("substring", Func{level=mainLevel, label="substring",
		formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
	("concat", Func{level=mainLevel, label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=mainLevel, label="not",
		formals=[TInt RW], result=TInt RW, extern=true}),
	("exit", Func{level=mainLevel, label="exit",
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
		(* let *)
		(* 	val a = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (1)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "No debería pasar! (1)"
  | tiposIguales a (TTipo _) =
		(* let *)
		(* 	val b = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (2)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "No debería pasar! (2)"
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=(), ty=TUnit}
		| trexp(NilExp _)= {exp=(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=(), ty=TInt RW}
		| trexp(StringExp(s, _)) = {exp=(), ty=TString}
		| trexp(CallExp({func, args}, nl)) =

			{exp=(), ty=TUnit}
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil)
                andalso tyl<>TUnit then {exp=(), ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil)
                andalso tyl<>TUnit then {exp=(), ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if esInt (tipoReal(tyl, tenv)) then
                          {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| MinusOp => if esInt (tipoReal(tyl,tenv)) then
                          {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| TimesOp => if esInt (tipoReal(tyl,tenv)) then
                          {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| DivideOp => if esInt (tipoReal(tyl,tenv)) then
                          {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| LtOp => if esInt (tipoReal(tyl,tenv)) orelse
                        tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| LeOp => if esInt (tipoReal(tyl,tenv)) orelse
                        tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| GtOp => if esInt (tipoReal(tyl,tenv)) orelse
                        tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| GeOp => if esInt (tipoReal(tyl,tenv)) orelse
                        tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
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

				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Faltan campos", nl)
				  | verificar [] (c::cs) = error("Sobran campos", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty (!t) then verificar cs ds
							 else error("Error de tipo del campo "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=(), ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=(), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let val {ty = tvar, ...} = case tabBusca(s, venv) of SOME TInt RO => error("variable read only", nl)
                                                   | SOME t => t
                                                   | NONE error("no existe la variable " ^ s, nl);
                val {ty = texp, ...} = trexp exp
                val _    = if tiposIguales tvar texp
                           then ()
                           else error("esperaba tipo " ^ ppTipo tvar ^ " pero la expresion es de tipo " ^ ppTipo texp, nl)
            in {exp=(), ty=TUnit} end
		| trexp(AssignExp({var, exp}, nl)) =
            let val {ty = tvar, ...} = trvar var
                val {ty = texp, ...} = trexp exp
                val _    = if tiposIguales tvar texp
                           then ()
                           else error("esperaba tipo " ^ ppTipo tvar ^ " pero la expresion es de tipo " ^ ppTipo texp, nl)
            in {exp=(), ty=TUnit} end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if esInt (tipoReal(tytest,tenv)) andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if esInt (tipoReal(tytest,tenv)) andalso tythen=TUnit then {exp=(), ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if esInt (tipoReal(#ty ttest, tenv)) andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
				else if not (esInt (tipoReal(#ty ttest, tenv))) then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
			 let val {explo, tylo} = trexp lo
                 val _ = if esInt tylo then () else error("la cota de for no es entera")
                 val {exphi, tyhi} = trexp hi
                 val _ = if esInt tylo then () else error("la cota de for no es entera")
               val venv' = tabInserta venv var (VarEntry {ty = TInt RO})
               val {expbody, tybody} = transExp (tenv, venv', body)
               val _ = if tybody = TUnit then () else error("el body no puede devolver un valor")
             in {exp = (), ty = TUnit} end
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in
				{exp=(), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=(), ty=TUnit}
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let
                val (tarray, u) = case tabBusca typ tenv of
                                     SOME TArray (t, u) => (t, u)
                                   | SOME t => error(ppTipo t ^ "no es un array", nl)
                                   | NONE => error("Arreglo de tipo inexistente", nl)
                val {ty = tsize, ...} = trexp size
                val {ty = tinit, ...} = trexp init
                val _ = if esInt tsize then () else error("El tamaño del arreglo no es un entero", nl)
                val _ = if tiposIguales tarray tinit then () else
                  error("arreglo de tipo " ^ ppTipo tarray ^ " inicializado con tipo " ^ ppTipo tinit, nl)
			in {exp=(), ty = TArray (tarray, u) end
        and trvar(SimpleVar s, nl) =
            case tabBusca s venv of
                SOME t => {exp = (), ty = t}
              | NONE   => error("no se encontro la variable " ^ s, nl)
		| trvar(FieldVar(v, s), nl) =
            let fun getRTipo [] x = NONE
                 |  getRTipo ((s, tr, i) :: xs) x = if s = x then SOME !tr else getRTipo xs x

                val tipo = case trvar v of
                    {ty = TRecord (l, _), ...} => case getRTipo l s of
                                                      SOME t => t
                                                    | NONE   => error(s ^ " no es un campo del record", nl)
                    _ => error("la expresion no es un record", nl)
            in {exp = (), ty = tipo} end
		| trvar(SubscriptVar(v, e), nl) =
            let val {ty = t, ...} = trexp e
                val _ = if esInt t then () else error("la expresion no evalua a un entero", nl)
                val tipo = case trvar v of
                           {ty = TArray (tr, _), ...} => !tr
                         | _ => error("la expresion no es un arreglo", nl)
			in {exp=(), ty=tipo} end

		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
		    let
		        val tinit = transExp venv tenv init
		        val venv' = tabInserta(name, tinit, venv)
		    in (venv', tenv, []) end
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
		    let
		        val tinit = transExp venv tenv init
		        val ty = case tabBusca(s, tenv) of
		                    SOME t => t
		                    | NONE => error("No se encontro el tipo " ^ s, pos)
                val _ = if tiposIguales tinit ty then () else error("La variable se declaro con tipo " ^ s ^ " pero la trataste de inicializar a algo de tipo " ^ ppTipo tinit, pos)
		        val venv' = tabInserta(name, Var tinit, venv)
		    in (venv', tenv, []) end
		| trdec (venv,tenv) (FunctionDec fs) =
		    let
                fun field2tipo {typ = NameTy s, ...} = case tabBusca(s, tenv) of
                                                          SOME t => t
                                                          | NONE => error("No eixste el tipo "^s, pos)
                |   field2tipo _ = error("Error interno")
		        fun insDecls (({name, params, result, ...}, pos), venvIn) = 
		            let 
		                val params' = List.map field2tipo  params
		                val result' = case result of
		                                SOME s => case tabBusca(s, tenv) of
		                                            SOME t => t
		                                            | NONE => error("No eixste el tipo "^s, pos)
		                                | NONE => TUnit
                        val venv' = tabInserta(name, Func {level = 0, label = name, formal = params', result = result', extern = false}, venvIn)
                    in venv' end
                val venvDecs = List.foldr insDecls venv fs
                fun trfun ({name, params, result, body, ...}, pos) =
                    let        
                        fun field2tupla {typ = NameTy s, name = n, ...} = case tabBusca(s, tenv) of
                                                                              SOME t => (n, t)
                                                                              | NONE => error("Error Interno", pos)
                        val params' = List.map field2tupla params
		                val result' = case result of
		                                SOME s => case tabBusca(s, tenv) of
		                                            SOME t => t
		                                            | NONE => error("Error interno", pos)
		                                | NONE => TUnit
                        val venv' = foldr (fn (nom, tipo) e => tabInserta (nom, tipo, e)) venvDecs params'
                        val {ty=tbody, exp=e} = transExp (venv', tenv) body
                        val _ = if tiposIguales tbody result' then () else error("La funcion " ^ name ^ " no tipa", pos)
                    in () end
                val _ = List.map trfun fs
            in (venvDecs, tenv, [])
		| trdec (venv,tenv) (TypeDec ts) =
			(venv, tenv, []) (*COMPLETAR*)
	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=NONE, body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end
