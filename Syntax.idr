module LSL.Syntax

import Data.Vect

import LSL.Helpers

%access public export

Symbol : Type
Symbol = String

data LSLType
	= LSLInteger
	| LSLFloat
	| LSLString
	| LSLKey
	| LSLVector
	| LSLRotation
	| LSLList
	
Eq LSLType where
	LSLInteger == LSLInteger = True
	LSLFloat == LSLFloat = True
	LSLString == LSLString = True
	LSLKey == LSLKey = True
	LSLVector == LSLVector = True
	LSLRotation == LSLRotation = True
	LSLList == LSLList = True
	_ == _ = False
	
Show LSLType where
	show LSLInteger = "integer"
	show LSLFloat = "float"
	show LSLString = "string"
	show LSLKey = "key"
	show LSLVector = "vector"
	show LSLRotation = "rotation"
	show LSLList = "list"
	
data SymbolType
	= ValueType LSLType
	| LabelType
	| FnType (Maybe LSLType) (List LSLType)
	| EventType
	| StateType
	| NoneType
	
Eq SymbolType where
	(ValueType a) == (ValueType a') = a == a'
	LabelType == LabelType = True
	(FnType r as) == (FnType r' as') = r == r' && as == as'
	EventType == EventType = True
	StateType == StateType = True
	NoneType == NoneType = True
	_ == _ = False
	
Show SymbolType where
	show (ValueType a) = show a
	show LabelType = "label"
	show (FnType r as) = "fn " ++ maybe "void" show r ++ " (" ++ joinSepShow ", " as ++ ")"
	show EventType = "event"
	show StateType = "state"
	show NoneType = "none"
	
data Literal
	= IntLit Integer
	| FloatLit Double
	| StringLit String
	| KeyLit String
	
Show Literal where
	show (IntLit a) = show a
	show (FloatLit a) = show a
	show (StringLit a) = "\"" ++ a ++ "\""
	show (KeyLit a) = a
	
data Expr
	= LitExpr Literal
	
	| VarExpr Symbol
	
	| ParenExpr Expr
	
	| VectorExpr Expr Expr Expr
	| RotationExpr Expr Expr Expr Expr
	| ListExpr (List Expr)
	
	| CastExpr LSLType Expr
	
	| NotExpr Expr
	| AndExpr Expr Expr
	| OrExpr Expr Expr
	
	| BNotExpr Expr
	| BAndExpr Expr Expr
	| BOrExpr Expr Expr
	| BXorExpr Expr Expr
	
	| NegExpr Expr
	| AddExpr Expr Expr
	| SubExpr Expr Expr
	| MulExpr Expr Expr
	| DivExpr Expr Expr
	| ModExpr Expr Expr
	
	| SHLExpr Expr Expr
	| SHRExpr Expr Expr
	
	| EqExpr Expr Expr
	| NeExpr Expr Expr
	| LtExpr Expr Expr
	| LteExpr Expr Expr
	| GtExpr Expr Expr
	| GteExpr Expr Expr
	
	| FnExpr Symbol (List Expr)
	
	| SetExpr Symbol Expr
	| SetAddExpr Symbol Expr
	| SetSubExpr Symbol Expr
	| SetMulExpr Symbol Expr
	| SetDivExpr Symbol Expr
	| SetModExpr Symbol Expr
	
	| PreIncExpr Symbol
	| PostIncExpr Symbol
	| PreDecExpr Symbol
	| PostDecExpr Symbol
	
Show Expr where
	show (LitExpr a) = show a
	
	show (VarExpr a) = a
	
	show (ParenExpr a) = "(" ++ show a ++ ")"
	
	show (VectorExpr x y z) = "<" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ">"
	show (RotationExpr x y z s) = "<" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show s ++ ">"
	show (ListExpr as) = show as
	
	show (CastExpr t a) = "(" ++ show t ++ ")" ++ show a
	
	show (NotExpr a) = "!" ++ show a
	show (AndExpr a b) = show a ++ " && " ++ show b
	show (OrExpr a b) = show a ++ " || " ++ show b
	
	show (BNotExpr a) = "~" ++ show a
	show (BAndExpr a b) = show a ++ " & " ++ show b
	show (BOrExpr a b) = show a ++ " | " ++ show b
	show (BXorExpr a b) = show a ++ " ^ " ++ show b
	
	show (NegExpr a) = "-" ++ show a
	show (AddExpr a b) = show a ++ " + " ++ show b
	show (SubExpr a b) = show a ++ " - " ++ show b
	show (MulExpr a b) = show a ++ " * " ++ show b
	show (DivExpr a b) = show a ++ " / " ++ show b
	show (ModExpr a b) = show a ++ " % " ++ show b
	
	show (SHLExpr a b) = show a ++ " << " ++ show b
	show (SHRExpr a b) = show a ++ " >> " ++ show b
	
	show (EqExpr a b) = show a ++ " == " ++ show b
	show (NeExpr a b) = show a ++ " != " ++ show b
	show (LtExpr a b) = show a ++ " < " ++ show b
	show (LteExpr a b) = show a ++ " <= " ++ show b
	show (GtExpr a b) = show a ++ " > " ++ show b
	show (GteExpr a b) = show a ++ " >= " ++ show b
	
	show (FnExpr v as) = show v ++ "(" ++ joinSepShow ", " as ++ ")"
	
	show (SetExpr v a) = v ++ " = " ++ show a
	show (SetAddExpr v a) = v ++ " += " ++ show a
	show (SetSubExpr v a) = v ++ " -= " ++ show a
	show (SetMulExpr v a) = v ++ " *= " ++ show a
	show (SetDivExpr v a) = v ++ " /= " ++ show a
	show (SetModExpr v a) = v ++ " %= " ++ show a
	
	show (PreIncExpr v) = "++" ++ v
	show (PostIncExpr v) = v ++ "++"
	show (PreDecExpr v) = "--" ++ v
	show (PostDecExpr v) = v ++ "--"

data Stmt
	= ExprStmt Expr
	| DefStmt LSLType Symbol (Maybe Expr)
	
	| ScopeStmt (List Stmt)
	
	| DefaultStmt
	| StateStmt Symbol
	
	| IfStmt Expr Stmt (Maybe Stmt)
	| DoWhileStmt Stmt Expr
	| ForStmt (List Expr) (Maybe Expr) (List Expr) Stmt
	| WhileStmt Expr Stmt
	
	| JumpStmt Symbol
	| LabelStmt Symbol
	
	| ReturnStmt (Maybe Expr)
	
interface ShowTabbed r where
	showTabbed : Nat -> r -> String
	
ShowTabbed String where
	showTabbed n a = join (replicate n "    ") ++ a
	
ShowTabbed a => ShowTabbed (List a) where
	showTabbed n as = join $ map (\a => showTabbed n a ++ "\n") as
	
mutual
	private showTabbedBody : Nat -> Stmt -> String
	showTabbedBody n (ScopeStmt body) = "{\n" ++ showTabbed (S n) body ++ showTabbed n "}"
	showTabbedBody _ a = showTabbed 0 a
		
	ShowTabbed Stmt where
		showTabbed n (ExprStmt a) = showTabbed n $ show a ++ ";"
		showTabbed n (DefStmt t v a) = showTabbed n $ show t ++ " " ++ v ++ maybe ";" (\a => " = " ++ show a ++ ";") a
		
		showTabbed n (ScopeStmt body) = showTabbed n "{\n" ++ showTabbed (S n) body ++ showTabbed n "}"
		
		showTabbed n DefaultStmt = showTabbed n $ "default;"
		showTabbed n (StateStmt v) = showTabbed n $ "state " ++ show v ++ ";"
		
		showTabbed n (IfStmt c t f) = showTabbed n ("if (" ++ show c ++ ") ")
			++ showTabbedBody n t
			++ maybe "" (\a => " else " ++ showTabbedBody n a) f
		showTabbed n (DoWhileStmt body test) = showTabbed n "do " ++ showTabbedBody n body ++ "while (" ++ show test ++ ");"
		showTabbed n (ForStmt pre test post body) = showTabbed n ("for (" ++ joinSepShow ", " pre ++ "; " ++ show @{blank} test ++ "; " ++ joinSepShow ", " post ++ ") ")
			++ showTabbedBody n body
		showTabbed n (WhileStmt test body) = showTabbed n ("while (" ++ show test ++ ") ")
			++ showTabbedBody n body
		
		showTabbed n (JumpStmt v) = showTabbed n $ "jump " ++ show v ++ ";"
		showTabbed n (LabelStmt v) = showTabbed n $ "@" ++ show v ++ ";"
		
		showTabbed n (ReturnStmt a) = showTabbed n $ "return " ++ maybe "" show a ++ ";"
	
data EventData : String -> List LSLType -> Type where
	AttachEvent : EventData "attach" [LSLKey]
	
	AtRotTargetEvent : EventData "at_rot_target" [LSLInteger, LSLRotation, LSLRotation]
	AtTargetEvent : EventData "at_target" [LSLInteger, LSLVector, LSLVector]
	NotAtRotTarget : EventData "not_at_rot_target" []
	NotAtTargetEvent : EventData "not_at_target" []
	
	ChangedEvent : EventData "changed" [LSLInteger]
	
	CollisionEvent : EventData "collision" [LSLInteger]
	CollisionStartEvent : EventData "collision_start" [LSLInteger]
	CollisionEndEvent : EventData "collision_end" [LSLInteger]
	
	ControlEvent : EventData "control" [LSLKey, LSLInteger, LSLInteger]
	
	DataserverEvent : EventData "dataserver" [LSLKey, LSLString]
	
	ExpPermsEvent : EventData "run_time_permissions" [LSLKey]
	ExpPermsDeniedEvent : EventData "experience_permissions" [LSLKey, LSLInteger]
	
	EmailEvent : EventData "email" [LSLString, LSLString, LSLString, LSLString, LSLInteger]
	HTTPRequestEvent : EventData "http_request" [LSLKey, LSLString, LSLString]
	HTTPResponseEvent : EventData "http_response" [LSLKey, LSLInteger, LSLList, LSLString]
	LinkMessageEvent : EventData "link_message" [LSLInteger, LSLInteger, LSLString, LSLKey]
	ListenEvent : EventData "listen" [LSLInteger, LSLString, LSLKey, LSLString]
	RemoteDataEvent : EventData "remote_data" [LSLInteger, LSLKey, LSLKey, LSLString, LSLInteger, LSLString]
	
	LandCollisionEvent : EventData "land_collision" [LSLVector]
	LandCollisionStartEvent : EventData "land_collision_start" [LSLVector]
	LandCollisionEndEvent : EventData "land_collision_end" [LSLVector]
	
	MoneyEvent : EventData "money" [LSLKey, LSLInteger]
	TxnResultEvent : EventData "transaction_result" [LSLKey, LSLInteger, LSLString]
	
	MovingStartEvent : EventData "moving_start" []
	MovingEndEvent : EventData "moving_end" []
	
	SensorEvent : EventData "sensor" [LSLInteger]
	NoSensorEvent : EventData "no_sensor" []
	
	ObjectRezEvent : EventData "object_rez" [LSLKey]
	
	OnRezEvent : EventData "on_rez" [LSLInteger]
	
	PathUpdateEvent : EventData "path_update" [LSLInteger, LSLList]
	
	PermsEvent : EventData "run_time_permissions" [LSLInteger]
	
	EntryEvent : EventData "state_entry" []
	ExitEvent : EventData "state_exit" []
	
	TimerEvent : EventData "timer" []
	
	TouchEvent : EventData "touch" [LSLInteger]
	TouchStartEvent : EventData "touch_start" [LSLInteger]
	TouchEndEvent : EventData "touch_end" [LSLInteger]
	
total eventName : EventData name args -> String
eventName {name} _ = name

total eventArgs : EventData name args -> List LSLType
eventArgs {args} _ = args

total namedArgs : EventData name types -> Vect (length types) Symbol -> Map Symbol SymbolType
namedArgs {types} _ args = zip (toList args) $ map ValueType types
	
record Event where
	constructor MkEvent
	type : EventData n ts
	args : Vect (length ts) Symbol
	body : List Stmt

private total showArgs : Map Symbol SymbolType -> String
showArgs as = join $ intersperse ", " $ map (\(n, t) => show t ++ " " ++ show n) as
	
ShowTabbed Event where
	showTabbed n e = showTabbed n (eventName (type e) ++ "(" ++ showArgs (namedArgs (type e) (args e)) ++ ") {\n")
		++ showTabbed (S n) (body e)
		++ showTabbed n "}"
	
record State where
	constructor MkState
	name : Maybe Symbol
	body : List Event

total stateName : State -> Symbol
stateName s = maybe "default" id $ name s

ShowTabbed State where
	showTabbed n s = showTabbed n (stateName s ++ " {\n") ++ showTabbed (S n) (body s) ++ showTabbed n "}"

record Function where
	constructor MkFunction
	result : Maybe LSLType
	name : Symbol
	args : Map Symbol LSLType
	body : List Stmt

Show Function where
	show f = maybe "" (\r => show r ++ " ") (result f) ++ show (name f)
		++ " (" ++ showArgs (map (\(n, t) => (n, ValueType t)) (args f)) ++ ") {\n"
		++ showTabbed 1 (body f) ++ "}\n"

record Script where
	constructor MkScript
	globals : Map Symbol LSLType
	funcs : List Function
	states : List State

Show Script where
	show s = join (map showGlobal (globals s) ++ map show (funcs s) ++ map (showTabbed 0) (states s)) where
		total showGlobal : (Symbol, LSLType) -> String
		showGlobal (n, t) = show t ++ " " ++ show n ++ ";\n"
