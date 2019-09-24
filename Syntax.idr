module LSL.Syntax

import Data.Vect

import LSL.Helpers

%access public export

data Symbol = Var String

Eq Symbol where
	(Var a) == (Var a') = a == a'

Show Symbol where
	show (Var a) = a

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
	| VectorLit Double Double Double
	| RotationLit Double Double Double Double
	
Show Literal where
	show (IntLit a) = show a
	show (FloatLit a) = show a
	show (StringLit a) = "\"" ++ a ++ "\""
	show (KeyLit a) = a
	show (VectorLit x y z) = "<" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ">"
	show (RotationLit x y z s) = "<" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show s ++ ">"
	
data Expr
	= LitExpr Literal
	
	| VarExpr Symbol
	
	| ParenExpr Expr
	
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
	
	show (VarExpr a) = show a
	
	show (ParenExpr a) = "(" ++ show a ++ ")"
	
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
	
	show (SetExpr v a) = show v ++ " = " ++ show a
	show (SetAddExpr v a) = show v ++ " += " ++ show a
	show (SetSubExpr v a) = show v ++ " -= " ++ show a
	show (SetMulExpr v a) = show v ++ " *= " ++ show a
	show (SetDivExpr v a) = show v ++ " /= " ++ show a
	show (SetModExpr v a) = show v ++ " %= " ++ show a
	
	show (PreIncExpr v) = "++" ++ show v
	show (PostIncExpr v) = show v ++ "++"
	show (PreDecExpr v) = "--" ++ show v
	show (PostDecExpr v) = show v ++ "--"

data Stmt
	= ExprStmt Expr
	| DefStmt LSLType Symbol (Maybe Expr)
	
	| ScopeStmt (List Stmt)
	
	| DefaultStmt
	| StateStmt Symbol
	
	| IfStmt Expr (List Stmt) (Maybe (List Stmt))
	| DoWhileStmt (List Stmt) Expr
	| ForStmt (List Expr) Expr (List Expr) (List Stmt)
	| WhileStmt Expr (List Stmt)
	
	| JumpStmt Symbol
	| LabelStmt Symbol
	
	| ReturnStmt (Maybe Expr)
	
Show Stmt where
	show (ExprStmt a) = show a ++ ";\n"
	show (DefStmt t v a) = show t ++ " " ++ show v ++ maybe ";" (\a => show a ++ ";") a
	
	show (ScopeStmt body) = "{\n" ++ joinShow body ++ "}\n"
	
	show DefaultStmt = "default" ++ ";\n"
	show (StateStmt v) = "state " ++ show v ++ ";\n"
	
	show (IfStmt c t f) = "if (" ++ show c ++ ") {\n"
		++ joinShow t ++ "}"
		++ maybe "\n" (\f => " else {\n" ++ joinShow f ++ "}\n") f
	show (DoWhileStmt body test) = "do {\n" ++ joinShow body ++ "} while (" ++ show test ++ ");\n"
	show (ForStmt pre test post body) = "for (" ++ joinSepShow ", " pre ++ "; " ++ show test ++ "; " ++ joinSepShow ", " post ++ ") {\n"
		++ joinShow body
		++ "}\n"
	show (WhileStmt test body) = "while (" ++ show test ++ ") {\n" ++ joinShow body ++ "}\n"
	
	show (JumpStmt v) = "jump " ++ show v ++ ";\n"
	show (LabelStmt v) = "@" ++ show v ++ ";\n"
	
	show (ReturnStmt a) = "return " ++ maybe "" show a ++ ";\n"
	
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
	
data Event
	= Evt (EventData name args) (Vect (length args) Symbol) (List Stmt)
	
total namedArgs : EventData name types -> Vect (length types) Symbol -> Map Symbol SymbolType
namedArgs {types} _ args = zip (toList args) $ map ValueType types

total showArgs : Map Symbol SymbolType -> String
showArgs as = join $ intersperse ", " $ map (\(n, t) => show t ++ " " ++ show n) as
	
Show Event where
	show (Evt def args body) = eventName def ++ "(" ++ showArgs (namedArgs def args) ++ ") {\n" ++ joinShow body ++ "}\n"

data State
	= DefaultState (List Event)
	| UserState Symbol (List Event)

Show State where
	show (DefaultState evts) = "default {\n" ++ joinShow evts ++ "}\n"
	show (UserState name evts) = "state " ++ show name ++ " {\n" ++ joinShow evts ++ "}\n"
	
data Function
	= Func (Maybe LSLType) Symbol (Map Symbol LSLType) (List Stmt)

total funcName : Function -> Symbol
funcName (Func _ name _ _) = name

Show Function where
	show (Func ret name args body) = maybe "" (\r => show r ++ " ") ret ++ show name ++ " (" ++ showArgs (map (\(n, t) => (n, ValueType t)) args) ++ ") {\n" ++ joinShow body ++ "}\n"

data Program
	= Script (Map Symbol LSLType) (List Function) (List State)

Show Program where
	show (Script globals funcs states) = join (map showGlobal globals ++ map show funcs ++ map show states) where
		total showGlobal : (Symbol, LSLType) -> String
		showGlobal (n, t) = show t ++ " " ++ show n ++ ";\n"
