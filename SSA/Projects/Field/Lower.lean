import LeanMLIR.Framework.Basic
import LeanMLIR.Framework.Refinement

variable {d d' : Dialect}
variable [TyDenote d.Ty] [TyDenote d'.Ty]
variable [DialectSignature d] [DialectSignature d']

/--
`DialectLowerSpecification` specifies how types in two dialects correspond,
and how to compare members of corresponding types for semantic equivalence.

Semantic equivalence is defined via a refinement relation.
In this way, `DialectLowerSpecification` is similar to `DialectHRefinement`.
The difference is that instead of specifying refinements between any two types in the dialects,
we only specify refinements between two types the correspond.

First, a correspondence between types is accessible via a representative from `Ty`.
- `mapTy` produces the corresponding member of `d.Ty` from the representative member of `Ty`
- `mapTy'` produces the corresponding member of `d'.Ty` from the representative member of `Ty`

Then, semantic equivalence is defined via a refinement relation.
- `IsRefinedBy`: a refinement between types that correspond
- `MonadIsRefinedBy`: lifts a refinement between types to a refinement between monadic types
-/
structure DialectLowerSpecification (d d' : Dialect) [TyDenote d.Ty] [TyDenote d'.Ty] where
  Ty : Type
  mapTy : Ty → d.Ty
  mapTy' : Ty → d'.Ty
  MonadIsRefinedBy {α β} [HRefinement α β] : HRefinement (d.m α) (d'.m β) := by
    solve
    | exact @Id.instRefinement
  IsRefinedBy : ∀ {t : Ty}, HRefinement ⟦mapTy t⟧ ⟦mapTy' t⟧

attribute [instance, simp, simp_denote] DialectLowerSpecification.IsRefinedBy
attribute [instance, simp, simp_denote] DialectLowerSpecification.MonadIsRefinedBy

variable (LS : DialectLowerSpecification d d')

/--
A witness that a `DialectLowerSpecification` is *signature deterministic* (`Sigdet`).
That is, every type in the source dialect `d` maps to one type in the target dialect `d'`.

This is enforced by giving the producer of corresponding types in `d` an inverse `invMapTy`.
Composing `invMapTy` with the producer of corresponding types in `d'` yields the deterministic map.
-/
class SigdetDialectLowerSpecification where
  invMapTy : d.Ty → LS.Ty
  invMapTy_rinv : ∀ {t}, LS.mapTy (invMapTy t) = t
  invMapTy_linv : ∀ {t}, invMapTy (LS.mapTy t) = t

variable [SD : SigdetDialectLowerSpecification LS]

namespace SigdetDialectLowerSpecification

omit [DialectSignature d] [DialectSignature d']
variable {LS : DialectLowerSpecification d d'} [SD : SigdetDialectLowerSpecification LS]

abbrev fullMapTy :=
  LS.mapTy' ∘ SD.invMapTy

theorem mapTy_invMapTy_eq_id : LS.mapTy ∘ SD.invMapTy = id := by
  ext; simp [invMapTy_rinv]

theorem invMapTy_mapTy_eq_id : SD.invMapTy ∘ LS.mapTy = id := by
  ext; simp [invMapTy_linv]

theorem fullMapTy_mapTy_eq_mapTy' : SD.fullMapTy ∘ LS.mapTy = LS.mapTy' := by
  ext; simp [invMapTy_linv]

end SigdetDialectLowerSpecification

/--
A version of `DialectLowerSpecification` that bundles the dialects with the specification.

This is necessary for sane `HRefinement` synthesis.
Otherwise, the conclusion of the `MonadIsRefinedBy` instance
would not refer the desired `DialectLowerSpecification`,
so this premise could not be inferred.
-/
structure SumDialectLowerSpecification where
  d : Dialect
  d' : Dialect
  tyDenote_d : TyDenote d.Ty
  tyDenote_d' : TyDenote d'.Ty
  spec : DialectLowerSpecification d d'

attribute [instance] SumDialectLowerSpecification.tyDenote_d
attribute [instance] SumDialectLowerSpecification.tyDenote_d'

variable (L : SumDialectLowerSpecification)
variable [Monad L.d.m] [Monad L.d'.m]
variable [DialectSignature L.d] [DialectSignature L.d']
variable [DialectDenote L.d] [DialectDenote L.d']

abbrev SumDialectLowerSpecification.Ty :=
  L.spec.Ty

abbrev SumDialectLowerSpecification.mapTy :=
  L.spec.mapTy

abbrev SumDialectLowerSpecification.mapTy' :=
  L.spec.mapTy'

instance [HRefinement α β] : HRefinement (L.d.m α) (L.d'.m β) :=
  L.spec.MonadIsRefinedBy

/--
A refinement between valuations of corresponding contexts.
Corresponding contexts are accessible via map from a representative context.
Valuations refine each other when the values of respective variables refine each other.
-/
instance {Γ : Ctxt L.Ty} :
    HRefinement ((Γ.map L.mapTy).Valuation) ((Γ.map L.mapTy').Valuation) where
  IsRefinedBy V₁ V₂ := ∀ t (v : Γ.Var t), V₁ v.toMap ⊑ V₂ v.toMap

/--
A refinement between expressions of corresponding signatures.
Expressions refine each other when their output valuations refine each other
for all input valuations that refine each other.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} :
    HRefinement
      (Expr L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Expr L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')) where
  IsRefinedBy e₁ e₂ :=
    ∀ V₁ V₂, V₁ ⊑ V₂ →
      Ctxt.map_append _ _ _ ▸ e₁.outContext_eq ▸ e₁.denote V₁ ⊑
      Ctxt.map_append _ _ _ ▸ e₂.outContext_eq ▸ e₂.denote V₂

/--
A version of the previous instance that assumes a pure preamble of let bindings
in the context of the right-hand expression.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} (preamble : Com L.d' ∅ .pure []) :
    HRefinement
      (Expr L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Expr L.d' (Γ.map L.mapTy' ++ preamble.outContext) eff₂ (t.map L.mapTy')) where
  IsRefinedBy e₁ e₂ :=
    ∀ V₁ (V₂ : (Γ.map L.mapTy').Valuation), V₁ ⊑ V₂ →
      Ctxt.map_append _ _ _ ▸ e₁.outContext_eq ▸
        e₁.denote V₁ ⊑
      Ctxt.map_append _ _ _ ▸ Ctxt.Valuation.fromlAppend <$> (
        Ctxt.append_assoc ▸ e₂.outContext_eq ▸
        e₂.denote (V₂ ++ EffectKind.toMonad_pure_apply ▸ preamble.denoteLets .nil) )

/--
A refinement between computations of corresponding signatures.
Computations refine each other when their output valuations refine each other
for all input valuations that refine each other.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} :
    HRefinement
      (Com L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Com L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')) where
  IsRefinedBy c₁ c₂ :=
    ∀ V₁ V₂, V₁ ⊑ V₂ →
      HVector.castFromMap L.mapTy rfl <$> c₁.denote V₁ ⊑
      HVector.castFromMap L.mapTy' rfl <$> c₂.denote V₂

/--
A version of the previous instance that assumes a pure preamble of let bindings
in the context of the right-hand computation.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} (preamble : Com L.d' ∅ .pure []) :
    HRefinement
      (Com L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Com L.d' (Γ.map L.mapTy' ++ preamble.outContext) eff₂ (t.map L.mapTy')) where
  IsRefinedBy c₁ c₂ :=
    ∀ V₁ (V₂ : (Γ.map L.mapTy').Valuation), V₁ ⊑ V₂ →
      HVector.castFromMap L.mapTy rfl <$>
        c₁.denote V₁ ⊑
      HVector.castFromMap L.mapTy' rfl <$>
        c₂.denote (V₂ ++ EffectKind.toMonad_pure_apply ▸ preamble.denoteLets .nil)

/--
A lowering between two dialects
that preserves semantics according to a `SumDialectLowerSpecification`.
-/
class DialectLower where
  lowerCom (Γ : Ctxt L.Ty) (eff₁ eff₂ : EffectKind) (t : List L.Ty) :
    Com L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy) →
    Com L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')
  lowerCom_refined : ∀ c, c ⊑ lowerCom Γ eff₁ eff₂ t c

/--
A lowering between two dialects
that preserves semantics according to a `SumDialectLowerSpecification`,
specified by an expression-to-expression map and a constant preamble.
-/
class DialectHomomorphicLower where
  preamble : Com L.d' ∅ .pure []
  lowerExpr (Γ : Ctxt L.Ty) (eff₁ eff₂ : EffectKind) (t : List L.Ty) :
    Expr L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy) →
    Expr L.d' (Γ.map L.mapTy' ++ preamble.outContext) eff₂ (t.map L.mapTy')
  lowerExpr_refined : ∀ e, e ⊑ lowerExpr Γ eff₁ eff₂ t e

namespace Com

/--
Transform a computation according to an expression-to-expression map with inserted context `Δ`,
then apply the continuation `k` to the resulting computation with with inserted context `Δ`.
-/
def mapExprCPS
    (Γ : Ctxt LS.Ty) (eff₁ eff₂ : EffectKind) (t : List LS.Ty)
    (mapExpr : ∀ (Γ : Ctxt LS.Ty) (eff₁ eff₂ : EffectKind) (t : List LS.Ty),
      Expr d (Γ.map LS.mapTy) eff₁ (t.map LS.mapTy) →
      Expr d' (Γ.map LS.mapTy' ++ Δ) eff₂ (t.map LS.mapTy') )
    (k : Com d' (Γ.map LS.mapTy' ++ Δ) eff₂ (t.map LS.mapTy') → α) :
    Com d (Γ.map LS.mapTy) eff₁ (t.map LS.mapTy) → α
| .rets vs =>
  k <| .rets <|
    SD.fullMapTy_mapTy_eq_mapTy' ▸ List.map_map ▸
    vs.map' SD.fullMapTy fun _ v => Ctxt.map_map ▸ v.toMap.appendInl
| @Com.var _ _ _ _ t' _ e body =>
  mapExprCPS (t'.map SD.invMapTy ++ Γ) eff₁ eff₂ t mapExpr (fun body' => k <| .var (
      mapExpr Γ eff₁ eff₂ _ <| List.map_map.symm ▸ SD.mapTy_invMapTy_eq_id ▸ List.map_id _ ▸ e ) <|
      Ctxt.append_assoc ▸ Ctxt.map_append _ _ _ ▸ body' ) <|
    Ctxt.map_append _ _ _ ▸ Ctxt.map_map.symm ▸ SD.mapTy_invMapTy_eq_id ▸ Ctxt.map_id _ ▸ body
decreasing_by sorry

/--
Append a computation to the tail of a pure preamble of let bindings.
The context of the input computation is permitted the let bindings from the preamble,
and the appendage of the preamble dissolves this part of the context in the result computation.
-/
def appendPreamble
    (Γ : Ctxt LS.Ty) (eff₁ eff₂ : EffectKind) (t : List LS.Ty) :
    ∀ preamble : Com d' Δ .pure [],
    Com d' (Γ.map LS.mapTy' ++ preamble.outContext) eff₂ (t.map LS.mapTy') →
    Com d' (Γ.map LS.mapTy' ++ Δ) eff₂ (t.map LS.mapTy')
| .rets []ₕ, body => body
| @Com.var _ _ _ _ t' _ e preamble', body => .var sorry (appendPreamble Γ eff₁ eff₂ t sorry sorry)
decreasing_by sorry

/--
Transform a computation according to an expression-to-expression map
with inserted context from a pure preamble of let bindings,
then append the resulting computation to the tail of the preamble,
dissolving the inserted context.

This is essentially `mapExprCPS` with `appendPreamble` as its continuation.
-/
def mapExprWithPreamble
    (Γ : Ctxt LS.Ty) (eff₁ eff₂ : EffectKind) (t : List LS.Ty)
    (preamble : Com d' Δ .pure [])
    (mapExpr : ∀ (Γ : Ctxt LS.Ty) (eff₁ eff₂ : EffectKind) (t : List LS.Ty),
      Expr d (Γ.map LS.mapTy) eff₁ (t.map LS.mapTy) →
      Expr d' (Γ.map LS.mapTy' ++ preamble.outContext) eff₂ (t.map LS.mapTy') ) :
    Com d (Γ.map LS.mapTy) eff₁ (t.map LS.mapTy) →
    Com d' (Γ.map LS.mapTy' ++ Δ) eff₂ (t.map LS.mapTy') :=
  mapExprCPS LS Γ eff₁ eff₂ t mapExpr (appendPreamble LS Γ eff₁ eff₂ t preamble)

end Com
