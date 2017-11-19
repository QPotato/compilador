structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero
	
type level = {parent:frame option , frame: frame, level: int}
type access = tigerframe.access

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
	frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
	{
	parent=SOME frame,
	frame=newFrame{name=name, formals=formals},
	level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	Ex of tigertree.exp
	| Nx of tigertree.stm
	| Cx of label * label -> tigertree.stm

fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
	| unEx (Nx s) = ESEQ(s, CONST 0)
	| unEx (Cx cf) =
	let
		val r = newtemp()
		val t = newlabel()
		val f = newlabel()
	in
		ESEQ(seq [MOVE(TEMP r, CONST 1),
			cf (t, f),
			LABEL f,
			MOVE(TEMP r, CONST 0),
			LABEL t],
			TEMP r)
	end

fun unNx (Ex e) = EXP e
	| unNx (Nx s) = s
	| unNx (Cx cf) =
	let
		val t = newlabel()
		val f = newlabel()
	in
		seq [cf(t,f),
			LABEL t,
			LABEL f]
	end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
	| unCx (Cx cf) = cf
	| unCx (Ex (CONST 0)) =
	(fn (t,f) => JUMP(NAME f, [f]))
	| unCx (Ex (CONST _)) =
	(fn (t,f) => JUMP(NAME t, [t]))
	| unCx (Ex e) =
	(fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
	let	fun aux(Ex e) = tigerit.tree(EXP e)
		| aux(Nx s) = tigerit.tree(s)
		| aux _ = raise Fail "bueno, a completar!"
		fun aux2(PROC{body, frame}) = aux(Nx body)
		| aux2(STRING(l, "")) = l^":\n"
		| aux2(STRING("", s)) = "\t"^s^"\n"
		| aux2(STRING(l, s)) = l^":\t"^s^"\n"
		fun aux3 [] = ""
		| aux3(h::t) = (aux2 h)^(aux3 t)
	in	aux3 e end

fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
	val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
	val pushSalida = tigerpila.pushPila salidas
	fun popSalida() = tigerpila.popPila salidas
	fun topSalida() =
		case tigerpila.topPila salidas of
		SOME l => l
		| NONE => raise Fail "break incorrecto!"			
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
	let	val label = STRING(name(#frame level), "")
		val body' = PROC{frame= #frame level, body=unNx body}
		val final = STRING(";;-------", "")
	in	datosGlobs:=(!datosGlobs@[label, body', final]) end
fun getResult() = !datosGlobs

fun stringLen s =
	let	fun aux[] = 0
		| aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
		| aux(_::t) = 1+aux(t)
	in	aux(explode s) end

fun stringExp(s: string) =
	let	val l = newlabel()
		val len = ".long "^makestring(stringLen s)
		val str = ".string \""^s^"\""
		val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
	in	Ex(NAME l) end

fun preFunctionDec() =
	(pushSalida(NONE);
	actualLevel := !actualLevel+1)

fun functionDec(e, l, proc) =
	let	val body =
				if proc then unNx e
				else MOVE(TEMP rv, unEx e)
		val body' = procEntryExit1(#frame l, body)
		val () = procEntryExit{body=Nx body', level=l}
	in	Ex(CONST 0) end

fun postFunctionDec() =
	(popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

fun simpleVar(acc, nivel) =
    
    let fun genSL 0 = TEMP fp
          | genSL n = 
                let val tmp = newtemp()
                    fun aux 0 = []
                      | aux n = (MOVE (TEMP tmp, MEM (BINOP (PLUS, TEMP tmp, CONST fpPrevLev)))) :: aux (n-1)
                in ESEQ (seq ([MOVE (TEMP tmp, TEMP fp)] @ aux n), TEMP tmp) end
        val lvl = getActualLev() - nivel
    in case acc of
           InReg t => if lvl > 0
                      then raise Fail "error interno! simpleVar inReg con nivel > 0"
                      else Ex (TEMP t)
         | InFrame off => let 
                            val sl = genSL lvl
                          in Ex (MEM (BINOP (PLUS, sl, CONST off))) end
    end
        

fun varDec(acc) = simpleVar(acc, getActualLev())

fun fieldVar(var, field) = 
    let val tmp = newtemp()
    in
      Ex (ESEQ ( MOVE (TEMP tmp, unEx var), 
                 MEM (BINOP (PLUS, TEMP tmp, BINOP (MUL, CONST field, CONST wSz))) ))
    end

fun subscriptVar(arr, ind) =
let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

fun recordExp l =
    let 
        val r = newtemp()
        fun genRecordStm [] = EXP (CONST 0)
          | genRecordStm [(e, i)] = MOVE( MEM( BINOP( PLUS, TEMP r, CONST (i*wSz))), unEx e)
          | genRecordStm ((e, i)::xs) = SEQ( MOVE( MEM( BINOP( PLUS, TEMP r, CONST (i*wSz))), unEx e),
                                           genRecordStm xs)
    in
        Ex( ESEQ( SEQ( MOVE(TEMP r, externalCall("_allocRecord", [CONST (length l)])),
                       genRecordStm l), TEMP r))
    end

fun arrayExp{size, init} =
let
	val s = unEx size
	val i = unEx init
in
	Ex (externalCall("allocArray", [s, i]))
end

fun callExp (name,external,isproc,lev:level,ls) = 
    let
 
       fun genStaticLink 0 = MEM (BINOP (PLUS, TEMP fp, CONST fpPrevLev))
         | genStaticLink n = 
               let val tmp = newtemp()
                   fun aux 0 = []
                     | aux n = (MOVE (TEMP tmp, MEM (BINOP (PLUS, TEMP tmp, CONST fpPrevLev)))) :: aux (n-1)
               in ESEQ (seq ([MOVE (TEMP tmp, TEMP fp)] @ aux n), TEMP tmp) end

       val deltaL = getActualLev() - (#level lev) (* si < 0 llamo a una función de "más abajo" *)
       val _ = if deltaL < ~1 then raise Fail "Error! llamaste a una función con deltaL < -1" else ()

       val ls' = List.map unEx ls
             
       val e = if external
               then CALL (NAME name, ls')
               else
                   let val staticLink = if deltaL = ~1 
                                        then TEMP fp 
                                        else genStaticLink deltaL
                   in CALL (NAME name, (staticLink :: ls')) end
    in 
        if isproc then (Nx (EXP e)) else (Ex e)
    end
    

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = 
        let 
            val initsStms = List.map unNx inits
        in Ex (ESEQ(seq initsStms,unEx body)) end

fun breakExp() = 
    let val s = topSalida() in Nx (JUMP (NAME s, [s])) end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
	| seqExp (exps:exp list) =
		let
			fun unx [e] = []
				| unx (s::ss) = (unNx s)::(unx ss)
				| unx[] = []
		in
			case List.last exps of
				Nx s =>
					let val unexps = map unNx exps
					in Nx (seq unexps) end
				| Ex e => Ex (ESEQ(seq(unx exps), e))
				| cond => Ex (ESEQ(seq(unx exps), unEx cond))
		end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

(* PREGUNTAR POR QUE MIERDA TOMA UN LEVEL *)
fun whileExp {test: exp, body: exp(*, lev:level*)} =
let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
end

fun forExp {lo, hi, var, body} =
    let
        val v = unEx var
        val l = unEx lo
        val h = unEx hi
        val bdy = unNx body
        val (empieza, sigue, fin) = (newlabel(), newlabel(), topSalida())
    in
        Nx (seq[CJUMP(LE, l, h, empieza, fin),  
            LABEL empieza,
            bdy,
            CJUMP(LT, v, h, sigue, fin),
            LABEL sigue,
            MOVE(v, BINOP(PLUS, v, CONST 1)),
            JUMP(NAME empieza, [empieza]),
            LABEL fin])
    end

fun ifThenExp{test, then'} =
    let
        val (tru, fin) = (newlabel(), newlabel())
        val t = unCx test
        val tn = unNx then'
    in
        Nx (seq[t(tru, fin),
                LABEL tru,
                tn,
                LABEL fin])
    end

fun ifThenElseExp {test,then',else'} =
    let
        val tmp = newtemp()
        val (tru, fols, fin) = (newlabel(), newlabel(), newlabel())
        val t = unCx test
        val den = unEx then'
        val els = unEx else'
    in
        Ex (ESEQ (seq [t(tru, fols),
            LABEL tru,
            MOVE(TEMP tmp, den),
            JUMP(NAME fin, [fin]),
            LABEL fols,
            MOVE(TEMP tmp, els),
            LABEL fin], TEMP tmp))
    end

fun ifThenElseExpUnit {test,then',else'} =
    let
        val (tru, fols, fin) = (newlabel(), newlabel(), newlabel())
        val t = unCx test
        val den = unNx then'
        val els = unNx else'
    in
        Nx (seq [t(tru, fols),
            LABEL tru,
            den,
            JUMP(NAME fin, [fin]),
            LABEL fols,
            els,
            LABEL fin])
    end

fun assignExp{var, exp} =
let
	val v = unEx var
	val vl = unEx exp
in
	Nx (MOVE(v,vl))
end

fun binOpIntExp {left, oper, right} = 
    let
        val l = unEx left
        val r = unEx right
        val exp = case oper of
                       PlusOp => BINOP(PLUS, l, r)
                     | MinusOp => BINOP(MINUS, l, r)
                     | TimesOp => BINOP(MUL, l, r) (* se puede optimizar con op de bits *)
                     | DivideOp => BINOP(DIV, l, r)
                     | _ => raise Fail "binOpIntExp no toma un operador de enteros"
    in
        Ex exp
    end

fun binOpIntRelExp {left,oper,right} =
    let
        val l = unEx left
        val r = unEx right
        val exp = case oper of
                       EqOp => (fn (l1, l2) => CJUMP(EQ, l, r, l1, l2))
                     | NeqOp => (fn (l1, l2) => CJUMP(NE, l, r, l1, l2))
                     | LtOp => (fn (l1, l2) => CJUMP(LT, l, r, l1, l2))
                     | LeOp => (fn (l1, l2) => CJUMP(LE, l, r, l1, l2))
                     | GtOp => (fn (l1, l2) => CJUMP(GT, l, r, l1, l2))
                     | GeOp => (fn (l1, l2) => CJUMP(GE, l, r, l1, l2))
                     | _ => raise Fail "binOpIntRelEp no toma un operador de relacion"
    in
        Cx exp
    end

fun binOpStrExp {left,oper,right} =
    let
        val l = unEx left
        val r = unEx right
        val comp = CALL(NAME "_stringCompare", [l, r])
        val exp = case oper of
                       EqOp => (fn (l1, l2) => CJUMP(EQ, comp, CONST 0, l1, l2))
                     | NeqOp => (fn (l1, l2) => CJUMP(NE, comp, CONST 0, l1, l2))
                     | LtOp => (fn (l1, l2) => CJUMP(LT, comp, CONST 0, l1, l2))
                     | GtOp => (fn (l1, l2) => CJUMP(GT, comp, CONST 0, l1, l2))
                     | LeOp => (fn (l1, l2) => CJUMP(LE, comp, CONST 0, l1, l2))
                     | GeOp => (fn (l1, l2) => CJUMP(GE, comp, CONST 0, l1, l2))
                     | _ => raise Fail "binOpStrExp no toma un operador de relacion de strings"
    in
        Cx exp
    end


end
