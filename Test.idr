module LSL.Test

import Data.Vect

import LSL.Helpers
import LSL.Syntax
import LSL.Typecheck
import LSL.Compile
import LSL.Eval

tests : List Script
tests = [
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				DefStmt LSLInteger "a" (Just $ LitExpr $ IntLit 5),
				DefStmt LSLInteger "b" (Just $ LitExpr $ IntLit 6),
				IfStmt (EqExpr (VarExpr "a") (VarExpr "b"))
					(ExprStmt $ PostIncExpr "a")
					(Just $ ExprStmt $ PostIncExpr "b")
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				DefStmt LSLVector "a" Nothing,
				DefStmt LSLVector "b" Nothing,
				IfStmt (VarExpr "a")
					(ScopeStmt [
						ExprStmt (SetExpr "a" Whole (VectorExpr (LitExpr $ FloatLit 1) (LitExpr $ FloatLit 2) (LitExpr $ FloatLit 3)))
						])
					(Just $ ScopeStmt [
						ExprStmt (SetExpr "a" Whole (VarExpr "b"))
						])
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				ForStmt [] Nothing [] $ ScopeStmt [
					DefStmt LSLInteger "a" Nothing
				]
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				ExprStmt $ LitExpr $ IntLit 4
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				ExprStmt $ MulExpr (LitExpr $ IntLit 4) $ AddExpr (LitExpr $ IntLit 5) (LitExpr $ IntLit 6)
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				DefStmt LSLVector "t" Nothing,
				ExprStmt $ SetExpr "t" X (LitExpr $ IntLit 3)
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				ExprStmt $ BNotExpr $ BNotExpr $ LitExpr $ IntLit 0
			]
		]
	]
]

negTests : List Script
negTests = [
	MkScript [] [] [
		MkState Nothing [
			MkEvent (index 32 lslEvents) [] [
				DefStmt LSLVector "t" Nothing,
				ExprStmt $ SetExpr "t" S (LitExpr $ IntLit 3)
			]
		]
	]
]
