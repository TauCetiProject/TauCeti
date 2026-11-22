/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# Degrees and bases after a linearly disjoint extension of constants

Let `F' = F · k'` in a common overfield, with `F` and `k'` linearly disjoint over `k`.
For every intermediate field `C` of `F/k` with `F/C` algebraic, a `C`-basis of `F` remains a
basis of `F'` over `k' · C`. In particular, `[F' : k'(x)] = [F : k(x)]` for every `x ∈ F`, and
when `F` and `F'` carry compatible algebras over `RatFunc k` and `RatFunc k'`, linear independence
over `RatFunc k`, bases of algebraic extensions `F / RatFunc k`, and the degree
`[F : RatFunc k]` all persist over `RatFunc k'`.
The extension `k'/k` can be transcendental; no perfectness or exact-constants hypothesis
is needed once linear disjointness is supplied.

Linear independence is transported by
`IntermediateField.LinearDisjoint.linearIndependent_adjoin_algebraMap_comp`.
Spanning uses algebraicity of `F/C`: adjoining the algebraic image of `F` to `k' · C`
already gives the whole field compositum. A transcendental element also remains
transcendental, so a linearly disjoint extension of constants of a one-variable function
field is again a one-variable function field. Conversely, preserving the finite degree over
a shared transcendental parameter `x` (or over `k(t)`) recovers linear disjointness.

## Main definitions and results

* `TauCeti.constantExtensionBasisOfLinearDisjoint` and `TauCeti.constantExtensionRatFuncBasis`:
  transport a basis over `C` or over `RatFunc k` along a linearly disjoint constant extension,
  together with `TauCeti.constantExtensionRatFuncBasis_repr_algebraMap`.
* `IntermediateField.LinearDisjoint.linearIndependent_ratFunc_algebraMap_comp`: linearly disjoint
  extensions preserve linear independence over `RatFunc`.
* `TauCeti.finrank_over_adjoin_simple_eq_of_linearDisjoint` and
  `TauCeti.finrank_ratFunc_eq_of_linearDisjoint`: preserve the degree over `k(x)` and `RatFunc k`.
* `TauCeti.IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint`: preserve the
  one-variable function-field property under an arbitrary linearly disjoint extension of constants.
* `TauCeti.linearDisjoint_of_transcendental_of_finrank_eq` and
  `TauCeti.linearDisjoint_of_finrank_ratFunc_eq`: degree preservation over a shared parameter or
  `k(t)` implies linear disjointness of constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), for the algebraic constant-extension specialization.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A basis of an algebraic extension `F/C` stays a basis over `k' · C` in the linearly disjoint
constant compositum `F' = F · k'`. The constants `k'/k` need not be algebraic. -/
noncomputable def constantExtensionBasisOfLinearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  Module.Basis.mk (H.linearIndependent_adjoin_algebraMap_comp C b.linearIndependent)
    (span_range_basis_of_isAlgebraic_constantCompositum h C b).ge

/-- The transported basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionBasisOfLinearDisjoint_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasisOfLinearDisjoint H h C b i = algebraMap F F' (b i) :=
  Module.Basis.mk_apply _ _ i

/-- An arbitrary linearly disjoint extension of constants preserves the degree over a
simple intermediate field: `[F · k' : k'(x)] = [F : k(x)]`. -/
theorem finrank_over_adjoin_simple_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (x : F) :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F
  have hadj : IntermediateField.adjoin k' (Set.range (algebraMap k⟮x⟯ F')) =
      k'⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right]
  by_cases hfin : FiniteDimensional k⟮x⟯ F
  · have : Algebra.IsAlgebraic k⟮x⟯ F := Algebra.IsAlgebraic.of_finite k⟮x⟯ F
    have hdegree :=
      Module.finrank_eq_nat_card_basis (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b)
    rwa [hadj, ← Module.finrank_eq_nat_card_basis b] at hdegree
  · have hfin' : ¬ FiniteDimensional k'⟮algebraMap F F' x⟯ F' := fun hfin' ↦ hfin <| by
      have : FiniteDimensional
          (IntermediateField.adjoin k' (Set.range (algebraMap k⟮x⟯ F'))) F' := hadj ▸ hfin'
      have : Finite (Module.Basis.ofVectorSpaceIndex k⟮x⟯ F) :=
        (H.linearIndependent_adjoin_algebraMap_comp k⟮x⟯ b.linearIndependent).finite
      exact Module.Finite.of_basis b
    rw [Module.finrank_of_not_finite hfin', Module.finrank_of_not_finite hfin]

/-- Extending constants linearly disjointly, even transcendently, preserves the one-variable
function-field property. -/
theorem IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  have := finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) h x
  exact (H.transcendental_algebraMap hx).isFunctionField_adjoin.finite_extension

/-- **Linear disjointness over a shared parameter from degree preservation.** -/
theorem linearDisjoint_of_transcendental_of_finrank_eq (h : constantCompositum F k' F' = ⊤) {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (hn : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let b := Module.finBasis k⟮x⟯ F
  have hspan := span_range_basis_of_isAlgebraic_constantCompositum h k⟮x⟯ b
  rw [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right] at hspan
  exact IntermediateField.linearDisjoint_of_transcendental_of_linearIndependent hx' b
    (linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin, ← hn]))

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- **Degree preservation over `k(t)` implies linear disjointness of constants.** -/
theorem linearDisjoint_of_finrank_ratFunc_eq [FiniteDimensional (RatFunc k) F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hn : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    hX ▸ (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq h hx' ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hn]

/-- **Linearly disjoint extensions preserve linear independence over `RatFunc`**: if the images of
`k'` and `F` in `F'` are linearly disjoint over `k` and `RatFunc.X` acts compatibly on `F` and
`F'`, then any `RatFunc k`-linearly independent family in `F` maps to a `RatFunc k'`-linearly
independent family in `F'`. Neither algebraicity of `k' / k` nor algebraicity of `F / RatFunc k`
is required. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_ratFunc_algebraMap_comp
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} {c : ι → F} (hc : LinearIndependent (RatFunc k) c) :
    LinearIndependent (RatFunc k') (algebraMap F F' ∘ c) := by
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hc₁ : LinearIndependent k⟮algebraMap (RatFunc k) F RatFunc.X⟯ c := by
    simpa using hc.map_of_surjective_injectiveₛ (RatFunc.algEquivOfTranscendental _ hx) (.id F)
      (RatFunc.algEquivOfTranscendental _ hx).surjective Function.injective_id
      fun r m ↦ (algEquivOfTranscendental_algebraMap_X_smul r m).symm
  simpa using (H.linearIndependent_adjoin_algebraMap_comp _ hc₁).map_of_surjective_injectiveₛ
    (adjoinRangeAlgEquivRatFunc hX) (.id F') (adjoinRangeAlgEquivRatFunc hX).surjective
    Function.injective_id fun r m ↦ (adjoinRangeAlgEquivRatFunc_smul hX r m).symm

/-- **Transport of a `RatFunc k`-basis along a linearly disjoint extension of constants.**
If `F' = F · k'` linearly disjointly over `k`, `F / RatFunc k` is algebraic, and the rational
variable `X` acts compatibly on `F` and `F'`, any `RatFunc k`-basis of `F` maps to a
`RatFunc k'`-basis of `F'`. The constant extension `k' / k` may be transcendental. -/
noncomputable def constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc k') F' :=
  haveI := (isAlgebraic_adjoin_algebraMap_X_iff (k := k) (F := F)).mpr ‹_›
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  (constantExtensionBasisOfLinearDisjoint H h _
    (b.mapCoeffs (RatFunc.algEquivOfTranscendental _ hx).toRingEquiv
      (fun _ _ ↦ by simp))).mapCoeffs
    (adjoinRangeAlgEquivRatFunc hX).toRingEquiv (fun _ _ ↦ by simp)

/-- The transported `RatFunc k'`-basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionRatFuncBasis_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    constantExtensionRatFuncBasis H h hX b i = algebraMap F F' (b i) := by
  simp [constantExtensionRatFuncBasis]

/-- **Linearly disjoint constant extensions preserve degree over the rational function field.**
If `F' = F · k'` linearly disjointly over `k` and `X` acts compatibly on `F` and `F'`, then
`[F' : RatFunc k'] = [F : RatFunc k]`. Unlike
`TauCeti.finrank_ratFunc_eq_of_constantCompositum_eq_top`, the extension `k' / k` may be
transcendental or inseparable once linear disjointness holds. -/
theorem finrank_ratFunc_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F := by
  rw [← finrank_adjoin_algebraMap_X (k := k') (F := F'), ← hX,
    finrank_over_adjoin_simple_eq_of_linearDisjoint H h, finrank_adjoin_algebraMap_X]

/-- The coordinates of an element of `F` in `constantExtensionRatFuncBasis` are the images of its
coordinates over `RatFunc k`. -/
@[simp]
theorem constantExtensionRatFuncBasis_repr_algebraMap
    [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F)
    (x : F) (i : ι) :
    (constantExtensionRatFuncBasis H h hXF b).repr (algebraMap F F' x) i =
      algebraMap (RatFunc k) (RatFunc k') (b.repr x i) := by
  let φ : F →ₛₗ[algebraMap (RatFunc k) (RatFunc k')] F' :=
    { toFun := algebraMap F F'
      map_add' := map_add _
      map_smul' := fun r y ↦ by
        simp [Algebra.smul_def, ← algebraMap_ratFunc_apply_eq hX hXF] }
  have hφ : φ = b.semilinearMap (algebraMap (RatFunc k) (RatFunc k'))
      (constantExtensionRatFuncBasis H h hXF b) :=
    b.ext fun j ↦ by simp [φ]
  simpa [φ] using congrArg ((constantExtensionRatFuncBasis H h hXF b).repr · i)
    (LinearMap.congr_fun hφ x)

end RatFunc

end TauCeti
