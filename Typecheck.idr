module LSL.Typecheck

import Data.Vect

import LSL.Helpers
import LSL.Syntax

%access public export

interface Checkable r where
	check : Map Symbol SymbolType -> r -> SymbolType -> Maybe Bool
	checkValue : Map Symbol SymbolType -> r -> LSLType -> Maybe Bool
	infer : Map Symbol SymbolType -> r -> Maybe SymbolType
	inferValue : Map Symbol SymbolType -> r -> Maybe LSLType
	
	checkValue ctx v t = check ctx v (ValueType t)
	inferValue ctx v = do
		v <- infer ctx v
		case v of
			ValueType a => Just a
			_ => Nothing
			
private total inferList : Checkable r => Map Symbol SymbolType -> List r -> Maybe ()
inferList ctx as = toMaybe (andmap (isJust . infer ctx) as) ()

Checkable Symbol where
	check ctx v t = do
		v <- lookup v ctx
		Just $ v == t
		
	infer ctx v = lookup v ctx
	
Checkable Literal where
	check ctx v t = do
		v <- infer ctx v
		Just $ v == t
	
	infer _ (IntLit _) = Just $ ValueType LSLInteger
	infer _ (FloatLit _) = Just $ ValueType LSLFloat
	infer _ (StringLit _) = Just $ ValueType LSLString
	infer _ (KeyLit _) = Just $ ValueType LSLKey
	infer _ (VectorLit _ _ _) = Just $ ValueType LSLVector
	infer _ (RotationLit _ _ _ _) = Just $ ValueType LSLRotation
	
private total castable : LSLType -> LSLType -> Bool
castable LSLInteger LSLFloat = True
castable LSLFloat LSLInteger = True
castable LSLString _ = True
castable _ LSLString = True
castable _ LSLList = True
castable a a' = a == a'

private total negable : LSLType -> Bool
negable LSLInteger = True
negable LSLFloat = True
negable LSLVector = True
negable LSLRotation = True
negable _ = False

private total inferAdd : LSLType -> LSLType -> Maybe LSLType
inferAdd LSLInteger LSLInteger = Just LSLInteger
inferAdd LSLInteger LSLFloat = Just LSLFloat
inferAdd LSLFloat LSLInteger = Just LSLFloat
inferAdd LSLFloat LSLFloat = Just LSLFloat
inferAdd LSLString LSLString = Just LSLString
inferAdd LSLVector LSLVector = Just LSLVector
inferAdd LSLRotation LSLRotation = Just LSLRotation
inferAdd LSLList _ = Just LSLList
inferAdd _ LSLList = Just LSLList
inferAdd _ _ = Nothing

private total inferSub : LSLType -> LSLType -> Maybe LSLType
inferSub LSLInteger LSLInteger = Just LSLInteger
inferSub LSLInteger LSLFloat = Just LSLFloat
inferSub LSLFloat LSLInteger = Just LSLFloat
inferSub LSLFloat LSLFloat = Just LSLFloat
inferSub LSLVector LSLVector = Just LSLVector
inferSub LSLRotation LSLRotation = Just LSLRotation
inferSub _ _ = Nothing

private total inferMul : LSLType -> LSLType -> Maybe LSLType
inferMul LSLInteger LSLInteger = Just LSLInteger
inferMul LSLInteger LSLFloat = Just LSLFloat
inferMul LSLInteger LSLVector = Just LSLVector
inferMul LSLFloat LSLInteger = Just LSLFloat
inferMul LSLFloat LSLFloat = Just LSLFloat
inferMul LSLFloat LSLVector = Just LSLVector
inferMul LSLVector LSLInteger = Just LSLVector
inferMul LSLVector LSLFloat = Just LSLVector
inferMul LSLVector LSLVector = Just LSLVector
inferMul LSLRotation LSLRotation = Just LSLRotation
inferMul _ _ = Nothing

private total inferDiv : LSLType -> LSLType -> Maybe LSLType
inferDiv LSLInteger LSLInteger = Just LSLInteger
inferDiv LSLInteger LSLFloat = Just LSLFloat
inferDiv LSLFloat LSLInteger = Just LSLFloat
inferDiv LSLFloat LSLFloat = Just LSLFloat
inferDiv LSLVector LSLInteger = Just LSLVector
inferDiv LSLVector LSLFloat = Just LSLVector
inferDiv LSLRotation LSLRotation = Just LSLRotation
inferDiv _ _ = Nothing

private total inferMod : LSLType -> LSLType -> Maybe LSLType
inferMod LSLInteger LSLInteger = Just LSLInteger
inferMod LSLVector LSLVector = Just LSLVector
inferMod _ _ = Nothing

private total inferEq : LSLType -> LSLType -> Maybe LSLType
inferEq LSLInteger LSLFloat = Just LSLInteger
inferEq LSLFloat LSLInteger = Just LSLInteger
inferEq a b = toMaybe (a == b) LSLInteger

private total inferComp : LSLType -> LSLType -> Maybe LSLType
inferComp LSLInteger LSLFloat = Just LSLInteger
inferComp LSLFloat LSLInteger = Just LSLInteger
inferComp _ _ = Nothing

Checkable Expr where
	check ctx (LitExpr a) t = check ctx a t
	
	check ctx (VarExpr v) t = check ctx v t
	
	check ctx (ParenExpr a) t = check ctx a t
	
	check ctx (ListExpr as) t = toMaybe (foldr (\e, a => isJust (inferValue ctx e) && a) True as) (t == ValueType LSLList)
	
	check ctx (CastExpr b a) t = do
		a <- inferValue ctx a
		Just $ castable a b && t == ValueType b
	
	check ctx (NotExpr a) t = do
		a <- checkValue ctx a LSLInteger
		Just $ t == ValueType LSLInteger
	check ctx (AndExpr a b) t = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		Just $ t == ValueType LSLInteger
	check ctx (OrExpr a b) t = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		Just $ t == ValueType LSLInteger
	
	check ctx (BNotExpr a) t = do
		a <- checkValue ctx a LSLInteger
		Just $ t == ValueType LSLInteger
	check ctx (BAndExpr a b) t = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		Just $ t == ValueType LSLInteger
	check ctx (BOrExpr a b) t = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		Just $ t == ValueType LSLInteger
	check ctx (BXorExpr a b) t = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		Just $ t == ValueType LSLInteger
	
	check ctx (NegExpr a) t = do
		a <- inferValue ctx a
		Just $ negable a && ValueType a == t
	check ctx (AddExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferAdd a b
		Just $ t == ValueType t'
	check ctx (SubExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferSub a b
		Just $ t == ValueType t'
	check ctx (MulExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferMul a b
		Just $ t == ValueType t'
	check ctx (DivExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferDiv a b
		Just $ t == ValueType t'
	check ctx (ModExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferMod a b
		Just $ t == ValueType t'

	check ctx (SHLExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		Just $ a == LSLInteger && b == LSLInteger && t == ValueType LSLInteger
	check ctx (SHRExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		Just $ a == LSLInteger && b == LSLInteger && t == ValueType LSLInteger
		
	check ctx (EqExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferEq a b
		Just $ t == ValueType t'
	check ctx (NeExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferEq a b
		Just $ t == ValueType t'
	check ctx (LtExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferComp a b
		Just $ t == ValueType t'
	check ctx (LteExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferComp a b
		Just $ t == ValueType t'
	check ctx (GtExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferComp a b
		Just $ t == ValueType t'
	check ctx (GteExpr a b) t = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t' <- inferComp a b
		Just $ t == ValueType t'
		
	check ctx (FnExpr f as) t = do
		f <- infer ctx f
		case f of
			FnType r as' => let checks = zipWith (checkValue ctx) as as' in
				toMaybe (andmap (maybe False id) checks) $ maybe NoneType ValueType r == t
			_ => Nothing

	check ctx (SetExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		toMaybe (v == a) $ ValueType v == t
	check ctx (SetAddExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t' <- inferAdd v a
		Just $ t == ValueType t'
	check ctx (SetSubExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t' <- inferSub v a
		Just $ t == ValueType t'
	check ctx (SetMulExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t' <- inferMul v a
		Just $ t == ValueType t'
	check ctx (SetDivExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t' <- inferDiv v a
		Just $ t == ValueType t'
	check ctx (SetModExpr v a) t = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t' <- inferMod v a
		Just $ t == ValueType t'
		
	check ctx (PreIncExpr v) t = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ t == ValueType LSLInteger
	check ctx (PostIncExpr v) t = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ t == ValueType LSLInteger
	check ctx (PreDecExpr v) t = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ t == ValueType LSLInteger
	check ctx (PostDecExpr v) t = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ t == ValueType LSLInteger
		
	infer ctx (LitExpr a) = infer ctx a
	
	infer ctx (VarExpr v) = infer ctx v
	
	infer ctx (ParenExpr a) = infer ctx a
	
	infer ctx (ListExpr as) = do
		_ <- inferList ctx as
		Just $ ValueType LSLList
	
	infer ctx (CastExpr b a) = do
		a <- inferValue ctx a
		toMaybe (castable a b) (ValueType b)
	
	infer ctx (NotExpr a) = do
		a <- checkValue ctx a LSLInteger
		toMaybe a $ ValueType LSLInteger
	infer ctx (AndExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (OrExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	
	infer ctx (BNotExpr a) = do
		a <- checkValue ctx a LSLInteger
		toMaybe a $ ValueType LSLInteger
	infer ctx (BAndExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (BOrExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (BXorExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
		
	infer ctx (NegExpr a) = do
		a <- inferValue ctx a
		toMaybe (negable a) $ ValueType a
	infer ctx (AddExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferAdd a b
		Just $ ValueType t
	infer ctx (SubExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferSub a b
		Just $ ValueType t
	infer ctx (MulExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferMul a b
		Just $ ValueType t
	infer ctx (DivExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferDiv a b
		Just $ ValueType t
	infer ctx (ModExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferMod a b
		Just $ ValueType t
	
	infer ctx (SHLExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (SHRExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
		
	infer ctx (EqExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferEq a b
		Just $ ValueType t
	infer ctx (NeExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferEq a b
		Just $ ValueType t
	infer ctx (LtExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (LteExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (GtExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (GteExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
		
	infer ctx (FnExpr f as) = do
		f <- infer ctx f
		case f of
			FnType r as' => let checks = zipWith (checkValue ctx) as as' in
				toMaybe (andmap (maybe False id) checks) $ maybe NoneType ValueType r
			_ => Nothing
			
	infer ctx (SetExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		toMaybe (v == a) $ ValueType v
	infer ctx (SetAddExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferAdd v a
		Just $ ValueType t
	infer ctx (SetSubExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferSub v a
		Just $ ValueType t
	infer ctx (SetMulExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferMul v a
		Just $ ValueType t
	infer ctx (SetDivExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferDiv v a
		Just $ ValueType t
	infer ctx (SetModExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferMod v a
		Just $ ValueType t
		
	infer ctx (PreIncExpr v) = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ ValueType LSLInteger
	infer ctx (PostIncExpr v) = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ ValueType LSLInteger
	infer ctx (PreDecExpr v) = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ ValueType LSLInteger
	infer ctx (PostDecExpr v) = do
		v <- inferValue ctx v
		toMaybe (v == LSLInteger) $ ValueType LSLInteger
		
interface ScopedCheckable r where
	scopedInfer : Map Symbol SymbolType -> Map Symbol SymbolType -> r -> Maybe (SymbolType, Map Symbol SymbolType)
	
private total scopedInferList : ScopedCheckable r => Map Symbol SymbolType -> Map Symbol SymbolType -> List r -> Maybe ()
scopedInferList _ _ [] = Just ()
scopedInferList old new (a :: as) = do
	a <- scopedInfer old new a
	scopedInferList old (snd a) as
	
private total getLabels : List Stmt -> List Symbol
getLabels = mapMaybe getLabel where
	total getLabel : Stmt -> Maybe Symbol
	getLabel (LabelStmt v) = Just v
	getLabel _ = Nothing
	
private total getLabelMap  : List Stmt -> Map Symbol SymbolType
getLabelMap as = let as = getLabels as in
	zip as $ replicate (length as) LabelType
	
ScopedCheckable Stmt where
	scopedInfer old new (ExprStmt a) = do
		a <- infer (new ++ old) a
		Just (a, new)
	scopedInfer old new (DefStmt t v a) = case lookup v new of
		Just _ => Nothing
		Nothing => let result = (NoneType, (v, ValueType t) :: new) in
			case a of
				Nothing => Just result
				Just a => do
					a <- checkValue (new ++ old) a t
					toMaybe a result
					
	scopedInfer old new (ScopeStmt body) = do
		_ <- scopedInferList (new ++ old) (getLabelMap body) body
		Just (NoneType, new)
		
	scopedInfer old new DefaultState = Just (NoneType, new)
	scopedInfer old new (StateStmt v) = do
		v <- check (new ++ old) v StateType
		toMaybe v (NoneType, new)
		
	scopedInfer old new (IfStmt test tb fb) = do
		_ <- infer (new ++ old) test
		_ <- scopedInferList (new ++ old) (getLabelMap tb) tb
		_ <- maybe (Just ()) (\fb => scopedInferList (new ++ old) (getLabelMap fb) fb) fb
		Just (NoneType, new)
	scopedInfer old new (DoWhileStmt body test) = do
		_ <- infer (new ++ old) test
		_ <- scopedInferList (new ++ old) (getLabelMap body) body
		Just (NoneType, new)
	scopedInfer old new (ForStmt pres test posts body) = do
		_ <- infer (new ++ old) test
		_ <- inferList (new ++ old) pres
		_ <- inferList (new ++ old) posts
		_ <- scopedInferList (new ++ old) (getLabelMap body) body
		Just (NoneType, new)
	scopedInfer old new (WhileStmt test body) = do
		_ <- infer (new ++ old) test
		_ <- scopedInferList (new ++ old) (getLabelMap body) body
		Just (NoneType, new)
	
	scopedInfer old new (JumpStmt v) = do
		v <- check (new ++ old) v LabelType
		toMaybe v (NoneType, new)
	scopedInfer _ new (LabelStmt _) = Just (NoneType, new)
	
	scopedInfer old new (ReturnStmt a) = do
		_ <- maybe (Just NoneType) (infer (new ++ old)) a
		Just (NoneType, new)

ScopedCheckable Event where
	scopedInfer old new (Evt def args body) = do
		_ <- scopedInferList (namedArgs def args ++ new ++ old) [] body
		Just (EventType, [])
	
checkDupedEvents : List Event -> Bool
checkDupedEvents [] = False
checkDupedEvents (a :: as) = elemBy checkDupe a as || checkDupedEvents as where
	checkDupe : Event -> Event -> Bool
	checkDupe (Evt def _ _) (Evt def' _ _) = eventName def == eventName def' -- TODO: Add a proper Eq implementation
	
ScopedCheckable State where
	scopedInfer old new (DefaultState evts) = do
		_ <- scopedInferList old new evts
		toMaybe (not (checkDupedEvents evts) && length evts > 0) (StateType, [])
	scopedInfer old new (UserState _ evts) = do
		_ <- scopedInferList old new evts
		toMaybe (not (checkDupedEvents evts) && length evts > 0) (StateType, [])
	
ScopedCheckable Function where
	scopedInfer old new (Func ret name args body) = do
		_ <- scopedInferList old new body
		Just (FnType ret $ map snd args, [])
	
checkDupedSymbols : List Symbol -> Bool
checkDupedSymbols [] = False
checkDupedSymbols (a :: as) = elem a as || checkDupedSymbols as
	
ScopedCheckable Program where
	scopedInfer old new (Script globals funcs states) = let globals = map (\(n, t) => (n, ValueType t)) globals in do
		_ <- scopedInferList (globals ++ old) new funcs
		_ <- scopedInferList (globals ++ old) new states
		toMaybe (not $ checkDupedSymbols (map fst globals ++ map funcName funcs)) (NoneType, [])
