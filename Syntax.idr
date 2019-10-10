module LSL.Syntax

import Data.Vect

import LSL.Helpers

%access public export

total Symbol : Type
Symbol = String

data LSLType
	= LSLInteger
	| LSLFloat
	| LSLString
	| LSLKey
	| LSLVector
	| LSLRotation
	| LSLList
	
total isNumeric : LSLType -> Bool
isNumeric LSLInteger = True
isNumeric LSLFloat = True
isNumeric _ = False
	
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
	= IntLit Int
	| FloatLit Double
	| StringLit String
	| KeyLit String
	
Show Literal where
	show (IntLit a) = show a
	show (FloatLit a) = show a
	show (StringLit a) = "\"" ++ a ++ "\""
	show (KeyLit a) = a
	
data Component
	= Whole
	| X
	| Y
	| Z
	| S
	
total hasComponent : LSLType -> Component -> Bool
hasComponent _ Whole = True
hasComponent LSLVector S = False
hasComponent LSLVector _ = True
hasComponent LSLRotation _ = True
hasComponent _ _ = False

Show Component where
	show Whole = ""
	show X = ".x"
	show Y = ".y"
	show Z = ".z"
	show S = ".s"
	
data Expr
	= LitExpr Literal
	
	| VarExpr Symbol -- TODO: add component accessor
	
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
	
	| SetExpr Symbol Component Expr
	| SetAddExpr Symbol Component Expr
	| SetSubExpr Symbol Component Expr
	| SetMulExpr Symbol Component Expr
	| SetDivExpr Symbol Component Expr
	| SetModExpr Symbol Component Expr
	
	| PreIncExpr Symbol
	| PostIncExpr Symbol
	| PreDecExpr Symbol
	| PostDecExpr Symbol
	
total map : (Expr -> Expr) -> Expr -> Expr
map f (ParenExpr a) = ParenExpr $ map f a

map f (VectorExpr x y z) = VectorExpr (map f x) (map f y) (map f z)
map f (RotationExpr x y z s) = RotationExpr (map f x) (map f y) (map f z) (map f s)
map f (ListExpr as) = ListExpr $ map f as

map f (CastExpr t a) = CastExpr t $ map f a

map f (NotExpr a) = NotExpr $ map f a
map f (AndExpr a b) = AndExpr (map f a) (map f b)
map f (OrExpr a b) = OrExpr (map f a) (map f b)

map f (BNotExpr a) = BNotExpr $ map f a
map f (BAndExpr a b) = BAndExpr (map f a) (map f b) 
map f (BOrExpr a b) = BOrExpr (map f a) (map f b)
map f (BXorExpr a b) = BXorExpr (map f a) (map f b)

map f (NegExpr a) = NegExpr $ map f a
map f (AddExpr a b) = AddExpr (map f a) (map f b)
map f (SubExpr a b) = SubExpr (map f a) (map f b)
map f (MulExpr a b) = MulExpr (map f a) (map f b)
map f (DivExpr a b) = DivExpr (map f a) (map f b)
map f (ModExpr a b) = ModExpr (map f a) (map f b)

map f (SHLExpr a b) = SHLExpr (map f a) (map f b)
map f (SHRExpr a b) = SHRExpr (map f a) (map f b)

map f (EqExpr a b) = EqExpr (map f a) (map f b)
map f (NeExpr a b) = NeExpr (map f a) (map f b)
map f (LtExpr a b) = LtExpr (map f a) (map f b)
map f (LteExpr a b) = LteExpr (map f a) (map f b)
map f (GtExpr a b) = GtExpr (map f a) (map f b)
map f (GteExpr a b) = GteExpr (map f a) (map f b)

map f (FnExpr fn as) = FnExpr fn $ map f as

map f (SetExpr v c a) = SetExpr v c $ map f a
map f (SetAddExpr v c a) = SetAddExpr v c $ map f a
map f (SetSubExpr v c a) = SetSubExpr v c $ map f a
map f (SetMulExpr v c a) = SetMulExpr v c $ map f a
map f (SetDivExpr v c a) = SetDivExpr v c $ map f a
map f (SetModExpr v c a) = SetModExpr v c $ map f a

map _ a = a

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
	
	show (FnExpr f as) = f ++ "(" ++ joinSepShow ", " as ++ ")"
	
	show (SetExpr v c a) = v ++ show c ++ " = " ++ show a
	show (SetAddExpr v c a) = v ++ show c ++ " += " ++ show a
	show (SetSubExpr v c a) = v ++ show c ++ " -= " ++ show a
	show (SetMulExpr v c a) = v ++ show c ++ " *= " ++ show a
	show (SetDivExpr v c a) = v ++ show c ++ " /= " ++ show a
	show (SetModExpr v c a) = v ++ show c ++ " %= " ++ show a
	
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
	
total unScope : Stmt -> List Stmt
unScope (ScopeStmt as) = as
unScope _ = []
	
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
	
record EventData where
	constructor MkEventData
	name : String
	types : List LSLType
	
Eq EventData where
	e == e' = name e == name e'
	
Show EventData where
	show e = name e
	
total lslEvents : List EventData
lslEvents =
	MkEventData "attach" [LSLKey] ::
	
	MkEventData "at_rot_target" [LSLInteger, LSLRotation, LSLRotation] ::
	MkEventData "at_target" [LSLInteger, LSLVector, LSLVector] ::
	MkEventData "not_at_rot_target" [] ::
	MkEventData "not_at_target" [] ::
	
	MkEventData "changed" [LSLInteger] ::
	
	MkEventData "collision" [LSLInteger] ::
	MkEventData "collision_start" [LSLInteger] ::
	MkEventData "collision_end" [LSLInteger] ::
	
	MkEventData "control" [LSLKey, LSLInteger, LSLInteger] ::
	
	MkEventData "dataserver" [LSLKey, LSLString] ::
	
	MkEventData "run_time_permissions" [LSLKey] ::
	MkEventData "experience_permissions" [LSLKey, LSLInteger] ::
	
	MkEventData "email" [LSLString, LSLString, LSLString, LSLString, LSLInteger] ::
	MkEventData "http_request" [LSLKey, LSLString, LSLString] ::
	MkEventData "http_response" [LSLKey, LSLInteger, LSLList, LSLString] ::
	MkEventData "link_message" [LSLInteger, LSLInteger, LSLString, LSLKey] ::
	MkEventData "listen" [LSLInteger, LSLString, LSLKey, LSLString] ::
	MkEventData "remote_data" [LSLInteger, LSLKey, LSLKey, LSLString, LSLInteger, LSLString] ::
	
	MkEventData "land_collision" [LSLVector] ::
	MkEventData "land_collision_start" [LSLVector] ::
	MkEventData "land_collision_end" [LSLVector] ::
	
	MkEventData "money" [LSLKey, LSLInteger] ::
	MkEventData "transaction_result" [LSLKey, LSLInteger, LSLString] ::
	
	MkEventData "moving_start" [] ::
	MkEventData "moving_end" [] ::
	
	MkEventData "sensor" [LSLInteger] ::
	MkEventData "no_sensor" [] ::
	
	MkEventData "object_rez" [LSLKey] ::
	
	MkEventData "on_rez" [LSLInteger] ::
	
	MkEventData "path_update" [LSLInteger, LSLList] ::
	
	MkEventData "run_time_permissions" [LSLInteger] ::
	
	MkEventData "state_entry" [] ::
	MkEventData "state_exit" [] ::
	
	MkEventData "timer" [] ::
	
	MkEventData "touch" [LSLInteger] ::
	MkEventData "touch_start" [LSLInteger] ::
	MkEventData "touch_end" [LSLInteger] ::
	Nil

total namedArgs : (e : EventData) -> Vect (length $ types e) Symbol -> Map Symbol SymbolType
namedArgs e args = zipWith (\n, t => (n, ValueType t)) (toList args) (types e)

record Event where
	constructor MkEvent
	type : EventData
	args : Vect (length $ types type) Symbol
	body : List Stmt

private total showArgs : Map Symbol SymbolType -> String
showArgs as = join $ intersperse ", " $ map (\(n, t) => show t ++ " " ++ show n) as
	
ShowTabbed Event where
	showTabbed n e = showTabbed n (name $ type e) ++ "(" ++ showArgs (namedArgs (type e) (args e)) ++ ") {\n"
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
	globals : Map Symbol (LSLType, Maybe Expr)
	funcs : List Function
	states : List State

Show Script where
	show s = join (map showGlobal (globals s) ++ map show (funcs s) ++ map (showTabbed 0) (states s)) where
		showGlobal : (Symbol, (LSLType, Maybe Expr)) -> String
		showGlobal (n, (t, v)) = show t ++ " " ++ show n ++ maybe "" (\e => " " ++ show e) v
