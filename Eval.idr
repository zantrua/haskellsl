module LSL.Eval

import Data.Bits
import Data.Vect

import LSL.Helpers
import LSL.Syntax
import LSL.Typecheck

%access public export

namespace VecAdd
	total (+) : Num a => (a, a, a) -> (a, a, a) -> (a, a, a)
	(+) (x, y, z) (x', y', z') = (x + x', y + y', z + z')
	
	total (-) : Neg a => (a, a, a) -> (a, a, a) -> (a, a, a)
	(-) (x, y, z) (x', y', z') = (x - x', y - y', z - z')

namespace VecScaleLeft
	total (*) : Num a => (a, a, a) -> a -> (a, a, a)
	(*) (x, y, z) a = (a * x, a * y, a * z)
	
	total (/) : Fractional a => (a, a, a) -> a -> (a, a, a)
	(/) (x, y, z) a = (x / a, y / a, z / a)
	
namespace VecScaleRight
	total (*) : Num a => a -> (a, a, a) -> (a, a, a)
	(*) a (x, y, z) = (a * x, a * y, a * z)

namespace VecDot
	total (*) : Num a => (a, a, a) -> (a, a, a) -> a
	(*) (x, y, z) (x', y', z') = x * x' + y * y' + z * z'
	
namespace VecCross
	total cross : Neg a => (a, a, a) -> (a, a, a) -> (a, a, a)
	cross (x, y, z) (x', y', z') = (y * z' - z * y', z * x' - x * z', x * y' - y * x')
	
namespace QuatRot
	total (*) : Neg a => (a, a, a) -> (a, a, a, a) -> (a, a, a)
	(*) (x, y, z) (x', y', z', s') = let halfT = cross (x', y', z') (x, y, z); t = halfT + halfT in
		(x, y, z) + t * s' + cross (x', y', z') t
	
namespace QuatMul
	total (*) : Neg a => (a, a, a, a) -> (a, a, a, a) -> (a, a, a, a)
	(*) (x, y, z, s) (x', y', z', s') =
		(x * s' + s * x' + z * y' - y * z',
		 y * s' + s * y' + x * z' - z * x',
		 z * s' + s * z' + y * x' - x * y',
		 s * s' - x * x' - y * y' - z * z')

data Value
	= IntVal Int
	| FloatVal Double
	| StringVal String
	| KeyVal String
	| VectorVal Double Double Double
	| RotationVal Double Double Double Double
	| ListVal (List Value)
	| VoidVal
	
Show Value where
	show (IntVal a) = show a
	show (FloatVal a) = show a
	show (StringVal a) = show a
	show (KeyVal a) = show a
	show (VectorVal x y z) = "<" ++ joinSepShow ", " [x, y, z] ++ ">"
	show (RotationVal x y z s) = "<" ++ joinSepShow ", " [x, y, z, s] ++ ">"
	show (ListVal as) = show as
	show VoidVal = "void"

partial type : Value -> LSLType
type (IntVal _) = LSLInteger
type (FloatVal _) = LSLFloat
type (StringVal _) = LSLString
type (KeyVal _) = LSLKey
type (VectorVal _ _ _) = LSLVector
type (RotationVal _ _ _ _) = LSLRotation
type (ListVal _) = LSLList

partial getDouble : Value -> Maybe Double
getDouble (IntVal a) = Just $ cast a
getDouble (FloatVal a) = Just a
getDouble _ = Nothing

total defaultValue : LSLType -> Value
defaultValue LSLInteger = IntVal 0
defaultValue LSLFloat = FloatVal 0.0
defaultValue LSLString = StringVal ""
defaultValue LSLKey = KeyVal ""
defaultValue LSLVector = VectorVal 0.0 0.0 0.0
defaultValue LSLRotation = RotationVal 0.0 0.0 0.0 1.0
defaultValue LSLList = ListVal []

total value : Literal -> Value
value (IntLit a) = IntVal a
value (FloatLit a) = FloatVal a
value (StringLit a) = StringVal a
value (KeyLit a) = KeyVal a

data ScriptStatus
	= Running
	| Waiting
	| Crashed String
	
Eq ScriptStatus where
	Running == Running = True
	Waiting == Waiting = True
	(Crashed _) == (Crashed _) = True
	_ == _ = False
	
Show ScriptStatus where
	show Running = "Running"
	show Waiting = "Waiting"
	show (Crashed err) = "Crashed: " ++ err

data EvStep
	= EvBlock (List Stmt)
	| EvStmt Stmt
	| EvExpr Expr
	
	| EvDrop
	
	| EvSet LSLType Symbol
	
	| EvVector
	| EvRotation
	| EvList Nat
	
	| EvCast LSLType
	
	| EvNot
	| EvAnd
	| EvOr
	
	| EvBNot
	| EvBAnd
	| EvBOr
	| EvBXor
	
	| EvNeg
	| EvAdd
	| EvSub
	| EvMul
	| EvDiv
	| EvMod
	
	| EvSHL
	| EvSHR
	
	| EvEq
	| EvNe
	| EvLt
	| EvLte
	| EvGt
	| EvGte
	
	| EvSetExpr Symbol Component
	| EvSetAddExpr Symbol Component
	| EvSetSubExpr Symbol Component
	| EvSetMulExpr Symbol Component
	| EvSetDivExpr Symbol Component
	| EvSetModExpr Symbol Component
	
Show EvStep where
	show (EvBlock as) = "Block [" ++ joinSep " " (map (showTabbed 0) as) ++ "]"
	show (EvStmt a) = "Stmt " ++ showTabbed 0 a
	
	show (EvExpr a) = "Expr " ++ show a
	
	show EvDrop = "Drop"
	
	show (EvSet t v) = "Set " ++ show t ++ " " ++ show v
	
	show EvVector = "Vector"
	show EvRotation = "Rotation"
	show (EvList n) = "List " ++ show n
	
	show (EvCast t) = "Cast " ++ show t
	
	show EvNot = "Not"
	show EvAnd = "And"
	show EvOr = "Or"
	
	show EvBNot = "BNot"
	show EvBAnd = "BAnd"
	show EvBOr = "BOr"
	show EvBXor = "BXor"
	
	show EvNeg = "Neg"
	show EvAdd = "Add"
	show EvSub = "Sub"
	show EvMul = "Mul"
	show EvDiv = "Div"
	show EvMod = "Mod"
	
	show EvSHL = "SHL"
	show EvSHR = "SHR"
	
	show EvEq = "Eq"
	show EvNe = "Ne"
	show EvLt = "Lt"
	show EvLte = "Lte"
	show EvGt = "Gt"
	show EvGte = "Gte"
	
	show (EvSetExpr v c) = "SetExpr " ++ show v ++ show c
	show (EvSetAddExpr v c) = "SetAddExpr " ++ show v ++ show c
	show (EvSetSubExpr v c) = "SetSubExpr " ++ show v ++ show c
	show (EvSetMulExpr v c) = "SetMulExpr " ++ show v ++ show c
	show (EvSetDivExpr v c) = "SetDivExpr " ++ show v ++ show c
	show (EvSetModExpr v c) = "SetModExpr " ++ show v ++ show c
	
record Frame where
	constructor MkFrame
	binds : Map Symbol Value
	evalStack : List EvStep

Show Frame where
	show f = "Frame {" ++ joinSep ", " [
		"Binds: [" ++ (joinSep ", " $ map (\(n, v) => n ++ " = " ++ show v) $ binds f) ++ "]",
		"Eval: [" ++ (joinSepShow ", " $ evalStack f) ++ "]"
		] ++ "}"

record EvalState where
	constructor MkEvalState
	
	script : Script
	status : ScriptStatus
	globals : Map Symbol Value
	state : Maybe Symbol
	events : List (EventData, List Value)
	
	valueStack : List Value
	callStack : List Frame
	
Show EvalState where
	show s = "EvalState {" ++ joinSep ", " [
		"Status: " ++ (show $ status s),
		"State: " ++ (show $ state s),
		"Events: " ++ (show $ events s),
		"CS: " ++ (show $ callStack s),
		"VS: " ++ (show $ valueStack s)
		] ++ "}"

total setStatus : ScriptStatus -> EvalState -> EvalState
setStatus st s = record { status = st} s

crash : String -> EvalState -> EvalState
crash err s = setStatus (Crashed err) s

total getState : EvalState -> Maybe State
getState s = find (\a => name a == state s) $ states $ script s

total pushValue : Value -> EvalState -> EvalState
pushValue a s = record { valueStack $= (::) a } s

total pushBool : Bool -> EvalState -> EvalState
pushBool a s = pushValue (IntVal $ ifThenElse a 1 0) s

total dropValue : EvalState -> EvalState
dropValue s = if isCons $ valueStack s
	then record { valueStack $= drop 1 } s
	else crash "Value stack is empty" s

total popValue : EvalState -> (EvalState, Maybe Value)
popValue s = (dropValue s, head' $ valueStack s)

total popValueCount : (n : Nat) -> EvalState -> (EvalState, Maybe (Vect n Value))
popValueCount Z s = (s, Just [])
popValueCount (S n) s = case popValue s of
	(s, Nothing) => (s, Nothing)
	(s, Just a) => let rest = popValueCount n s in
		(fst rest, map ((::) a) $ snd rest)

total pushCall : Frame -> EvalState -> EvalState
pushCall f s = record { callStack $= (::) f } s

total dropCall : EvalState -> EvalState
dropCall = record { callStack $= drop 1 }

partial addEvent : EventData -> List Value -> EvalState -> Maybe EvalState
addEvent e args s = toMaybe (types e == map type args) $ record { events $= (::) (e, args) } s

total dropEvent : EvalState -> EvalState
dropEvent s = record { events $= drop 1 } s

total findHandler : EventData -> EvalState -> Maybe Event
findHandler e s = do
	state <- getState s
	find (\e' => e == type e') $ body state

total handleEvent : EvalState -> EvalState
handleEvent s = case head' $ events s of
	Nothing => s
	Just (e, as) => case findHandler e s of
		Nothing => dropEvent s
		Just evt => setStatus Running
		          $ pushCall (MkFrame (zip (toList $ args evt) as) [EvBlock $ body evt])
				  $ dropEvent s

total addBind : Symbol -> Value -> EvalState -> EvalState
addBind v a s = case head' $ callStack s of
	Nothing => record { callStack = [MkFrame [(v, a)] []] } s
	Just frame => pushCall (record { binds $= (::) (v, a) } frame) $ dropCall s

-- NOTE: When you create a new frame, you need to copy the old binds in
total getBind : Symbol -> EvalState -> (EvalState, Maybe Value)
getBind v s = case (lookup v $ globals s, maybe Nothing (lookup v . binds) $ head' $ callStack s) of
	(_, Just a) => (s, Just a)
	(Just a, Nothing) => (s, Just a)
	(Nothing, Nothing) => (crash ("Variable " ++ show v ++ " not defined in scope") s, Nothing)

total setGlobal : Symbol -> Value -> EvalState -> EvalState
setGlobal v a s = case define v a $ globals s of
	(Nothing, _) => crash ("Variable " ++ show v ++ " not defined in scope") s
	(Just _, gs) => record { globals = gs } s
	
total setBind : Symbol -> Value -> EvalState -> EvalState
setBind v a s = case head' $ callStack s of
	Nothing => setGlobal v a s
	Just frame => case define v a $ binds frame of
		(Nothing, _) => setGlobal v a s
		(Just _, bs) => pushCall (record { binds = bs } frame) $ dropCall s

total pushEv : EvStep -> EvalState -> EvalState
pushEv e s = case head' $ callStack s of
	Nothing => record { callStack = [MkFrame [] [e]] } s
	Just frame => pushCall (record { evalStack $= (::) e } frame) $ dropCall s
 
total pushEvList : List EvStep -> EvalState -> EvalState
pushEvList steps s = foldr pushEv s steps

total dropEv : EvalState -> EvalState
dropEv s = case head' $ callStack s of
	Nothing => s
	Just frame => pushCall (record { evalStack $= drop 1 } frame) $ dropCall s

total popEv : EvalState -> (EvalState, Maybe EvStep)
popEv s = case head' $ callStack s of
	Nothing => (s, Nothing)
	Just frame => case head' $ evalStack frame of
		Nothing => (dropCall s, Nothing)
		Just ev => (dropEv s, Just ev)

evalGlobal : Expr -> Maybe Value
evalGlobal (LitExpr a) = Just $ value a
evalGlobal (VectorExpr x y z) = do
	x <- join $ map getDouble $ evalGlobal x
	y <- join $ map getDouble $ evalGlobal y
	z <- join $ map getDouble $ evalGlobal z
	Just $ VectorVal x y z
evalGlobal (RotationExpr x y z s) = do
	x <- join $ map getDouble $ evalGlobal x
	y <- join $ map getDouble $ evalGlobal y
	z <- join $ map getDouble $ evalGlobal z
	s <- join $ map getDouble $ evalGlobal s
	Just $ VectorVal x y z
evalGlobal (ListExpr as) = do
	as <- sequence $ map evalGlobal as
	Just $ ListVal as
evalGlobal _ = Nothing

initGlobal : (Symbol, (LSLType, Maybe Expr)) -> Maybe (Symbol, Value)
initGlobal (n, (t, Nothing)) = Just (n, defaultValue t)
initGlobal (n, (t, Just a)) = map (\v => (n, v)) $ evalGlobal a

init : Script -> Maybe EvalState
init s = do
	_ <- scopedInfer [] [] s
	gs <- sequence $ map initGlobal $ globals s
	Just $ MkEvalState s Waiting gs Nothing [(index 32 lslEvents, [])] [] []

total unaryOp : EvStep -> Expr -> EvalState -> EvalState
unaryOp f a s = pushEvList [EvExpr a, f] s

total binOp : EvStep -> Expr -> Expr -> EvalState -> EvalState
binOp f a b s = pushEvList [EvExpr b, EvExpr a, f] s

private total evalCast : LSLType -> Value -> Maybe Value
evalCast LSLInteger (IntVal a) = Just $ IntVal a
evalCast LSLInteger (FloatVal a) = Just $ IntVal $ cast a
evalCast LSLInteger (StringVal a) = Just $ IntVal $ cast a
evalCast LSLFloat (IntVal a) = Just $ FloatVal $ cast a
evalCast LSLFloat (FloatVal a) = Just $ FloatVal a
evalCast LSLFloat (StringVal a) = Just $ FloatVal $ cast a
evalCast LSLString (StringVal a) = Just $ StringVal a
evalCast LSLString a = Just $ StringVal $ assert_total $ show a
evalCast LSLKey (StringVal a) = Just $ KeyVal a
evalCast LSLList a = Just $ ListVal [a]
evalCast _ _ = Nothing

private total evalNeg : Value -> Maybe Value
evalNeg (IntVal a) = Just $ IntVal $ negate a
evalNeg (FloatVal a) = Just $ FloatVal $ negate a
evalNeg (VectorVal x y z) = Just $ VectorVal (negate x) (negate y) (negate z)
evalNeg (RotationVal x y z s) = Just $ RotationVal (negate x) (negate y) (negate z) (negate s)
evalNeg _ = Nothing

private total evalAdd : Value -> Value -> Maybe Value
evalAdd (IntVal a) (IntVal b) = Just $ IntVal $ a + b
evalAdd (IntVal a) (FloatVal b) = Just $ FloatVal $ cast a + b
evalAdd (FloatVal a) (IntVal b) = Just $ FloatVal $ a + cast b
evalAdd (FloatVal a) (FloatVal b) = Just $ FloatVal $ a + b
evalAdd (StringVal a) (StringVal a') = Just $ StringVal $ a ++ a'
evalAdd (VectorVal x y z) (VectorVal x' y' z') = Just $ VectorVal (x + x') (y + y') (z + z')
evalAdd (RotationVal x y z s) (RotationVal x' y' z' s') = Just $ RotationVal (x + x') (y + y') (z + z') (s + s')
evalAdd (ListVal as) (ListVal as') = Just $ ListVal $ as ++ as'
evalAdd a (ListVal as) = Just $ ListVal $ a :: as
evalAdd (ListVal as) a = Just $ ListVal $ as ++ [a]
evalAdd _ _ = Nothing

private total evalSub : Value -> Value -> Maybe Value
evalSub (IntVal a) (IntVal b) = Just $ IntVal $ a - b
evalSub (IntVal a) (FloatVal b) = Just $ FloatVal $ cast a - b
evalSub (FloatVal a) (IntVal b) = Just $ FloatVal $ a - cast b
evalSub (FloatVal a) (FloatVal b) = Just $ FloatVal $ a - b
evalSub (VectorVal x y z) (VectorVal x' y' z') = Just $ VectorVal (x - x') (y - y') (z - z')
evalSub (RotationVal x y z s) (RotationVal x' y' z' s') = Just $ RotationVal (x - x') (y - y') (z - z') (s - s')
evalSub _ _ = Nothing

private total evalMul : Value -> Value -> Maybe Value
evalMul (IntVal a) (IntVal b) = Just $ IntVal $ a * b
evalMul (IntVal a) (FloatVal b) = Just $ FloatVal $ cast a * b
evalMul (IntVal a) (VectorVal x y z) = Just $ uncurry3 VectorVal $ cast a * (x, y, z)
evalMul (FloatVal a) (IntVal b) = Just $ FloatVal $ a * cast b
evalMul (FloatVal a) (FloatVal b) = Just $ FloatVal $ a * b
evalMul (FloatVal a) (VectorVal x y z) = Just $ uncurry3 VectorVal $ a * (x, y, z)
evalMul (VectorVal x y z) (IntVal a) = Just $ uncurry3 VectorVal $ cast a * (x, y, z)
evalMul (VectorVal x y z) (FloatVal a) = Just $ uncurry3 VectorVal $ a * (x, y, z)
evalMul (VectorVal x y z) (VectorVal x' y' z') = Just $ FloatVal $ (x, y, z) * (x', y', z')
evalMul (VectorVal x y z) (RotationVal x' y' z' s') = Just $ uncurry3 VectorVal $ (x, y, z) * (x', y', z', s')
evalMul (RotationVal x y z s) (RotationVal x' y' z' s') = Just $ uncurry4 RotationVal $ (x, y, z, s) * (x', y', z', s')
evalMul _ _ = Nothing

private total evalDiv : Value -> Value -> Maybe Value
evalDiv (IntVal a) (IntVal b) = Just $ IntVal $ assert_total $ div a b
evalDiv (IntVal a) (FloatVal b) = Just $ FloatVal $ cast a / b
evalDiv (FloatVal a) (IntVal b) = Just $ FloatVal $ a / cast b
evalDiv (FloatVal a) (FloatVal b) = Just $ FloatVal $ a / b
evalDiv (VectorVal x y z) (IntVal a) = Just $ uncurry3 VectorVal $ (x, y, z) / cast a
evalDiv (VectorVal x y z) (FloatVal a) = Just $ uncurry3 VectorVal $ (x, y, z) / a
evalDiv (VectorVal x y z) (RotationVal x' y' z' s') = Just $ uncurry3 VectorVal $ (x, y, z) * (x', y', z', s')
evalDiv (RotationVal x y z s) (RotationVal x' y' z' s') = Just $ uncurry4 RotationVal $ (x, y, z, s) * (x', y', z', s')
evalDiv _ _ = Nothing

private total evalMod : Value -> Value -> Maybe Value
evalMod (IntVal a) (IntVal b) = Just $ IntVal $ assert_total $ mod a b
evalMod (VectorVal x y z) (VectorVal x' y' z') = Just $ uncurry3 VectorVal $ cross (x, y, z) (x', y', z')
evalMod _ _ = Nothing

step : EvalState -> EvalState
step s = case status s of
	Crashed _ => s
	Waiting => handleEvent s
	Running => case popEv s of
		(s, Nothing) => setStatus Waiting s
		(s, Just e) => case e of
			EvBlock [] => s
			EvBlock (a :: as) => pushEvList [EvStmt a, EvBlock as] s
			
			EvStmt (ExprStmt a) => unaryOp EvDrop a s
			EvStmt (DefStmt t v Nothing) => addBind v (defaultValue t) s
			EvStmt (DefStmt t v (Just a)) => unaryOp (EvSet t v) a s
			
			EvExpr (LitExpr a) => pushValue (value a) s
			
			EvExpr (VarExpr v) => case getBind v s of
				(s, Nothing) => s
				(s, Just a) => pushValue a s
			
			EvExpr (ParenExpr a) => pushEv (EvExpr a) s
			
			EvExpr (VectorExpr x y z) => pushEvList [EvExpr z, EvExpr y, EvExpr x, EvVector] s
			EvExpr (RotationExpr x y z w) => pushEvList [EvExpr w, EvExpr z, EvExpr y, EvExpr x, EvRotation] s
			EvExpr (ListExpr as) => pushEvList (map EvExpr as ++ [EvList $ length as]) s
			
			EvExpr (CastExpr t a) => unaryOp (EvCast t) a s
			
			EvExpr (NotExpr a) => unaryOp EvNot a s
			EvExpr (AndExpr a b) => binOp EvAnd a b s
			EvExpr (OrExpr a b) => binOp EvOr a b s
			
			EvExpr (BNotExpr a) => unaryOp EvBNot a s
			EvExpr (BAndExpr a b) => binOp EvBAnd a b s
			EvExpr (BOrExpr a b) => binOp EvBOr a b s
			EvExpr (BXorExpr a b) => binOp EvBXor a b s
			
			EvExpr (NegExpr a) => unaryOp EvNeg a s
			EvExpr (AddExpr a b) => binOp EvAdd a b s
			EvExpr (SubExpr a b) => binOp EvSub a b s
			EvExpr (MulExpr a b) => binOp EvMul a b s
			EvExpr (DivExpr a b) => binOp EvDiv a b s
			EvExpr (ModExpr a b) => binOp EvMod a b s
			
			EvExpr (SHLExpr a b) => binOp EvSHL a b s
			EvExpr (SHRExpr a b) => binOp EvSHR a b s
			
			EvExpr (EqExpr a b) => binOp EvEq a b s
			EvExpr (NeExpr a b) => binOp EvNe a b s
			EvExpr (LtExpr a b) => binOp EvLt a b s
			EvExpr (LteExpr a b) => binOp EvLte a b s
			EvExpr (GtExpr a b) => binOp EvGt a b s
			EvExpr (GteExpr a b) => binOp EvGte a b s
			
			EvExpr (FnExpr f as) => ?hfnexpr
			
			EvExpr (SetExpr v c a) => unaryOp (EvSetExpr v c) a s
			EvExpr (SetAddExpr v c a) => unaryOp (EvSetAddExpr v c) a s
			EvExpr (SetSubExpr v c a) => unaryOp (EvSetSubExpr v c) a s
			EvExpr (SetMulExpr v c a) => unaryOp (EvSetMulExpr v c) a s
			EvExpr (SetDivExpr v c a) => unaryOp (EvSetDivExpr v c) a s
			EvExpr (SetModExpr v c a) => unaryOp (EvSetModExpr v c) a s
			
			EvExpr (PreIncExpr v) => case getBind v s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushValue (IntVal $ a + 1) $ setBind v (IntVal $ a + 1) s
				(s, Just a) => crash ("Can't apply Inc to " ++ show (type a)) s
			EvExpr (PostIncExpr v) => case getBind v s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushValue (IntVal a) $ setBind v (IntVal $ a + 1) s
				(s, Just a) => crash ("Can't apply Inc to " ++ show (type a)) s
			EvExpr (PreDecExpr v) => case getBind v s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushValue (IntVal $ a - 1) $ setBind v (IntVal $ a - 1) s
				(s, Just a) => crash ("Can't apply Dec to " ++ show (type a)) s
			EvExpr (PostDecExpr v) => case getBind v s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushValue (IntVal $ a - 1) $ setBind v (IntVal $ a - 1) s
				(s, Just a) => crash ("Can't apply Dec to " ++ show (type a)) s
			
			EvDrop => dropValue s
			
			EvSet t v => case popValue s of
				(s, Nothing) => s
				(s, Just a) => if t == type a
					then addBind v a s
					else if t == LSLFloat && type a == LSLInteger
						then maybe (crash "Impossible?" s) (\a => addBind v (FloatVal a) s) (getDouble a)
						else crash "Invalid bind type" s

			EvVector => case popValueCount 3 s of
				(s, Nothing) => s
				(s, Just [x, y, z]) => case (getDouble x, getDouble y, getDouble z) of
					(Just x, Just y, Just z) => pushValue (VectorVal x y z) s
					_ => crash "Type of vector arguments invalid" s
			EvRotation => case popValueCount 4 s of
				(s, Nothing) => s
				(s, Just [x, y, z, w]) => case (getDouble x, getDouble y, getDouble z, getDouble w) of
					(Just x, Just y, Just z, Just w) => pushValue (RotationVal x y z w) s
					_ => crash "Type of rotation arguments invalid" s
			EvList n => case popValueCount n s of
				(s, Nothing) => s
				(s, Just as) => pushValue (ListVal $ toList as) s
				
			EvCast t => case popValue s of
				(s, Nothing) => s
				(s, Just a) => case evalCast t a of
					Nothing => crash ("Can't cast from " ++ show (type a) ++ " to " ++ show t) s
					Just a => pushValue a s
			
			EvNot => case popValue s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushBool (intToBool a) s
				(s, Just a) => crash ("Can't apply Not to " ++ show (type a)) s
			EvAnd => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [IntVal a, IntVal b]) => pushBool (intToBool a && intToBool b) s
				(s, Just [a, b]) => crash ("Can't apply And to " ++ show (type a) ++ " and " ++ show (type b)) s
			EvOr => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [IntVal a, IntVal b]) => pushBool (intToBool a || intToBool b) s
				(s, Just [a, b]) => crash ("Can't apply Or to " ++ show (type a) ++ " and " ++ show (type b)) s
			
			EvBNot => case popValue s of
				(s, Nothing) => s
				(s, Just (IntVal a)) => pushValue (IntVal $ complement a) s
				(s, Just a) => crash ("Can't apply BNot to " ++ show (type a)) s
			EvBAnd => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [IntVal a, IntVal b]) => pushValue (IntVal $ and a b) s
				(s, Just [a, b]) => crash ("Can't apply BAnd to " ++ show (type a) ++ " and " ++ show (type b)) s
			EvBOr => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [IntVal a, IntVal b]) => pushValue (IntVal $ or a b) s
				(s, Just [a, b]) => crash ("Can't apply BOr to " ++ show (type a) ++ " and " ++ show (type b)) s
			EvBXor => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [IntVal a, IntVal b]) => pushValue (IntVal $ xor a b) s
				(s, Just [a, b]) => crash ("Can't apply BXor to " ++ show (type a) ++ " and " ++ show (type b)) s

			EvNeg => case popValue s of
				(s, Nothing) => s
				(s, Just a) => case evalNeg a of
					Nothing => crash ("Can't apply Neg to " ++ show (type a)) s
					Just a => pushValue a s
			EvAdd => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [a, b]) => case evalAdd a b of
					Nothing => crash ("Can't apply Add to " ++ show (type a) ++ " and " ++ show (type b)) s
					Just a => pushValue a s
			EvSub => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [a, b]) => case evalSub a b of
					Nothing => crash ("Can't apply Sub to " ++ show (type a) ++ " and " ++ show (type b)) s
					Just a => pushValue a s
			EvMul => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [a, b]) => case evalMul a b of
					Nothing => crash ("Can't apply Mul to " ++ show (type a) ++ " and " ++ show (type b)) s
					Just a => pushValue a s
			EvDiv => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [a, b]) => case evalDiv a b of
					Nothing => crash ("Can't apply Div to " ++ show (type a) ++ " and " ++ show (type b)) s
					Just a => pushValue a s
			EvMod => case popValueCount 2 s of
				(s, Nothing) => s
				(s, Just [a, b]) => case evalMod a b of
					Nothing => crash ("Can't apply Mod to " ++ show (type a) ++ " and " ++ show (type b)) s
					Just a => pushValue a s

stepN : Nat -> EvalState -> EvalState
stepN Z s = s
stepN (S n) s = stepN n $ step s
