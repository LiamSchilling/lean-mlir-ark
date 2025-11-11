import SSA.Projects.Field.FuncV.Exprs
import SSA.Projects.Field.FuncV.Semantics

namespace FuncV

/-- Precisely specifies a lowering from the dialect `D` to the dialect `FuncV D'`.
The specification requires a preamble of function definitions
followed by an expression-to-expression map from `D` to `FuncV D'`,
which may use functions from the preamble.

To simplify the notion denotational equivalence for now,
we enforce that the effect monads of the dialects be equal by `effectm_eq`.
This way, we do not have to worry about raising and lowering effects,
which would involved monad lifts. -/
structure DialectLowerToFunc
    (D : Dialect) [TyDenote D.Ty] [DialectSignature D] [DialectDenote D] [Monad D.m]
    (D' : Dialect) [TyDenote D'.Ty] [DialectSignature D'] [DialectDenote D'] [Monad D'.m]
    (effectm_eq : D.m = D'.m) (tyLower : D.Ty → D'.Ty) (lowerDenote : ∀ ty, ⟦ty⟧ → ⟦tyLower ty⟧) where
  mapExpr :
    Expr D Γ eff tys →
    Expr (FuncV D') (Γ.map <| .raise ∘ tyLower) eff (tys.map <| .raise ∘ tyLower)
  denote_mapExpr : ∀ (expr : Expr D Γ eff tys) val,
    effectm_eq ▸
      @Ctxt.Valuation.toMap _ _ (Ty.raise ∘ tyLower) _ _ _ lowerDenote <$> expr.denote val =
    Ctxt.map_append _ _ _ ▸ (mapExpr expr).outContext_eq ▸
      (mapExpr expr).denote (val.toMap lowerDenote)

end FuncV
