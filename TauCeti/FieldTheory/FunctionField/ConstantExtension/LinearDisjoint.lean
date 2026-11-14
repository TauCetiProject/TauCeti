/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
public import TauCeti.FieldTheory.RatFunc.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Degrees and linear disjointness in extensions of constants

Let `F' = F · k'` in a common overfield, with `F` and `k'` linearly disjoint over `k`.
For every intermediate field `C` of `F/k` with `F/C` algebraic, a `C`-basis of `F` remains a
basis of `F'` over `k' · C`, with the same multiplication matrices, traces and discriminant.
In particular, `[F' : k'(x)] = [F : k(x)]` and `[F' : RatFunc k'] = [F : RatFunc k]`.
The extension `k'/k` can be transcendental; no perfectness or exact-constants hypothesis
is needed once linear disjointness is supplied.

Conversely, if an element `x ∈ F` stays transcendental over `k'`, then `k(x)` and `k'` are
linearly disjoint over `k`, and equality of finite degrees `[F' : k'(x)] = [F : k(x)]` inside
`F' = F · k'` forces `F` and `k'` themselves to be linearly disjoint over `k`. Under linear
disjointness, exactness of the constant field also descends from `F'/k'` to `F/k`.

## Main results

* `TauCeti.constantExtensionBasisOfLinearDisjoint`: transport a basis over `C`.
* `TauCeti.coe_discr_constantExtensionBasisOfLinearDisjoint`: transport its discriminant.
* `TauCeti.finrank_over_adjoin_simple_eq_of_linearDisjoint` and
  `TauCeti.finrank_ratFunc_eq_of_linearDisjoint`: preserve the degree over `k(x)` and `RatFunc k`.
* `TauCeti.linearDisjoint_adjoin_simple_of_transcendental`: `k(x)` and `k'` are linearly disjoint
  when the image of `x` is transcendental over `k'`.
* `TauCeti.linearDisjoint_fieldRange_of_finrank_over_adjoin_simple_eq` and
  `TauCeti.linearDisjoint_fieldRange_of_finrank_ratFunc_eq`: degree preservation in `F · k'`
  recovers linear disjointness of `F` and `k'`.
* `TauCeti.isIntegrallyClosedIn_of_linearDisjoint`: exact constants descend along any linearly
  disjoint extension.
* `TauCeti.IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint`: preserve the
  one-variable function-field property under an arbitrary linearly disjoint extension of constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), for the algebraic constant-extension specialization.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin nonZeroDivisors

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

/-- Coordinates of an element of `F` in the transported basis are the images of its coordinates in
the original basis. -/
theorem coe_constantExtensionBasisOfLinearDisjoint_repr_algebraMap
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (y : F) (i : ι) :
    ((constantExtensionBasisOfLinearDisjoint H h C b).repr (algebraMap F F' y) i : F') =
      algebraMap C F' (b.repr y i) := by
  set C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  set b' := constantExtensionBasisOfLinearDisjoint H h C b
  let g : C →+* C' := (IsScalarTower.toAlgHom k C F').toRingHom.codRestrict C'.toSubring
    fun c ↦ IntermediateField.subset_adjoin k' _ ⟨c, rfl⟩
  let f : ι →₀ C' := (b.repr y).mapRange g g.map_zero
  have hsum : b'.repr.symm f = algebraMap F F' y := by
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    dsimp only [f]
    rw [Finsupp.sum_mapRange_index (fun j ↦ zero_smul C' (b' j))]
    conv_rhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [g, b', Algebra.smul_def, IsScalarTower.algebraMap_apply C F F']
  simpa [f, g] using congrArg (fun q : ι →₀ C' ↦ (q i : F')) (b'.repr.symm_apply_eq.mp hsum).symm

/-- Trace from `F'` to `k' · C` agrees with trace from `F` to `C` on elements of `F`. -/
theorem coe_trace_adjoin_algebraMap
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [FiniteDimensional C F] (y : F) :
    (Algebra.trace (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F'
        (algebraMap F F' y) : F') =
      algebraMap C F' (Algebra.trace C F y) := by
  classical
  let b := Module.finBasis C F
  let b' := constantExtensionBasisOfLinearDisjoint H h C b
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace,
    Matrix.trace, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, b',
    constantExtensionBasisOfLinearDisjoint_apply, ← map_mul,
    coe_constantExtensionBasisOfLinearDisjoint_repr_algebraMap]

/-- **The discriminant of the transported basis is the image of the original discriminant.** -/
theorem coe_discr_constantExtensionBasisOfLinearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι C F) :
    (Algebra.discr (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
        (constantExtensionBasisOfLinearDisjoint H h C b) : F') =
      algebraMap C F' (Algebra.discr C b) := by
  have : FiniteDimensional C F := Module.Finite.of_basis b
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  let g : C →+* C' := (IsScalarTower.toAlgHom k C F').toRingHom.codRestrict C'.toSubring
    fun c ↦ IntermediateField.subset_adjoin k' _ ⟨c, rfl⟩
  have hmat : g.mapMatrix (Algebra.traceMatrix C b) =
      Algebra.traceMatrix C' (constantExtensionBasisOfLinearDisjoint H h C b) := by
    ext i j
    simp [C', g, Algebra.traceMatrix_apply, ← map_mul, coe_trace_adjoin_algebraMap H h C]
  rw [Algebra.discr_def, Algebra.discr_def, ← hmat, ← g.map_det]
  rfl

/-- An arbitrary linearly disjoint extension of constants preserves the finite degree over a
simple intermediate field: `[F · k' : k'(x)] = [F : k(x)]`. -/
theorem finrank_over_adjoin_simple_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (x : F) [FiniteDimensional k⟮x⟯ F] :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  let b := Module.finBasis k⟮x⟯ F
  have hdegree := Module.finrank_eq_card_basis (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b)
  rwa [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right, Fintype.card_fin] at hdegree

/-- An arbitrary linearly disjoint extension of constants preserves the degree over the rational
function field when `X` acts compatibly on both fields. -/
theorem finrank_ratFunc_eq_of_linearDisjoint [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
    [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F := by
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F := by
    have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
      (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
        RatFunc.transcendental_X
    exact Module.Finite.of_equiv_equiv (RatFunc.algEquivOfTranscendental _ hx).toRingEquiv
      (RingEquiv.refl F) (RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply)
  rw [← finrank_adjoin_algebraMap_X (k := k'), ← hX,
    finrank_over_adjoin_simple_eq_of_linearDisjoint H h, finrank_adjoin_algebraMap_X]

/-- **A parameter that stays transcendental generates a linearly disjoint rational subfield.** If
`y ∈ F'` is transcendental over `k'`, then `k(y)` and the image of `k'` in `F'` are linearly
disjoint over `k`. -/
theorem linearDisjoint_adjoin_simple_of_transcendental {y : F'}
    (hy : Transcendental k' y) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint k⟮y⟯ := by
  set A := (IsScalarTower.toAlgHom k k' F').fieldRange
  let φ : Polynomial k →ₐ[k] F' := Polynomial.aeval y
  have hφ : Function.Injective φ := transcendental_iff_injective.mp (hy.of_tower_top k)
  -- First, `k[y]` and `k'` are linearly disjoint in `F'` via the monomial basis `y ^ n`.
  have hdisj_poly : (Algebra.adjoin k {y}).LinearDisjoint A.toSubalgebra := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    let e : Polynomial k ≃ₐ[k] φ.range := AlgEquiv.ofInjective φ hφ
    refine Subalgebra.LinearDisjoint.of_basis_left φ.range A.toSubalgebra
      ((Polynomial.basisMonomials k).map e.toLinearEquiv) ?_
    have hpow : LinearIndependent A (fun n : ℕ ↦ y ^ n) :=
      hy.linearIndependent_pow.map_of_surjective_injective
        (IsScalarTower.toAlgHom k k' F').equivFieldRange (AddMonoidHom.id F')
        (AlgEquiv.surjective _) (by simp)
        fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl
    convert hpow using 1
    ext n
    simp [e, φ, AlgEquiv.ofInjective_apply]
  -- Pass from `k[y]` to its fraction field `k(y)` on a `k`-basis of `A`.
  let a := Module.Basis.ofVectorSpace k A
  have hli : LinearIndependent k⟮y⟯ (A.val ∘ a) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin k {y}) k⟮y⟯).mp
      (hdisj_poly.symm.linearIndependent_left_of_flat a.linearIndependent)
  exact _root_.IntermediateField.LinearDisjoint.of_basis_left a hli

/-- **Degree preservation recovers linear disjointness.** Let `F' = F · k'` with `x ∈ F` remaining
transcendental over `k'`. If `[F' : k'(x)] = [F : k(x)]` (with `F / k(x)` finite), then `F` and the
image of `k'` in `F'` are linearly disjoint over `k`. -/
theorem linearDisjoint_fieldRange_of_finrank_over_adjoin_simple_eq {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (h : constantCompositum F k' F' = ⊤)
    (hdeg : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set y := algebraMap F F' x
  have H₀ : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint k⟮x⟯ := by
    have hrange : (IsScalarTower.toAlgHom k k⟮x⟯ F').range = k⟮y⟯.toSubalgebra := by
      ext z
      change z ∈ Set.range (algebraMap k⟮x⟯ F') ↔ z ∈ (k⟮y⟯ : Set F')
      rw [IntermediateField.range_algebraMap_adjoin_simple]
    rw [_root_.IntermediateField.linearDisjoint_iff, hrange,
      ← _root_.IntermediateField.linearDisjoint_iff']
    exact linearDisjoint_adjoin_simple_of_transcendental (k := k) hx'
  let γ := Module.Basis.ofVectorSpace k k⟮x⟯
  let b := Module.finBasis k⟮x⟯ F
  have hspan : ⊤ ≤ Submodule.span k'⟮y⟯ (Set.range (algebraMap F F' ∘ b)) := by
    have hs := span_range_basis_of_isAlgebraic_constantCompositum (k := k) h k⟮x⟯ b
    rw [IntermediateField.range_algebraMap_adjoin_simple,
      _root_.IntermediateField.adjoin_adjoin_right] at hs
    exact hs.ge
  have hb' : LinearIndependent k'⟮y⟯ (algebraMap F F' ∘ b) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp [hdeg])
  let γ' : _ → k'⟮y⟯ := fun m ↦ ⟨algebraMap k⟮x⟯ F' (γ m), by
    have hm : algebraMap k⟮x⟯ F' (γ m) ∈
        _root_.IntermediateField.adjoin k' (Set.range (algebraMap k⟮x⟯ F')) :=
      _root_.IntermediateField.subset_adjoin k' _ ⟨γ m, rfl⟩
    rwa [IntermediateField.range_algebraMap_adjoin_simple,
      _root_.IntermediateField.adjoin_adjoin_right] at hm⟩
  have hγ' : LinearIndependent k' γ' :=
    (H₀.linearIndependent_algebraMap_comp γ.linearIndependent).of_comp k'⟮y⟯.val.toLinearMap
  have hprod : LinearIndependent k' (algebraMap F F' ∘ (γ.smulTower b)) := by
    convert linearIndependent_smul hγ' hb' using 1
    ext p
    simp [γ', Module.Basis.smulTower_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply k⟮x⟯ F F']
  refine _root_.IntermediateField.LinearDisjoint.of_basis_right' (γ.smulTower b) ?_
  exact hprod.map_of_surjective_injective (IsScalarTower.toAlgHom k k' F').equivFieldRange
    (AddMonoidHom.id F') (AlgEquiv.surjective _) (by simp)
    fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl

/-- **Degree preservation over `RatFunc` recovers linear disjointness.** Let `F' = F · k'` carry a
`RatFunc k'`-algebra structure sending `X` to the image of `X ∈ RatFunc k`. If
`[F' : RatFunc k'] = [F : RatFunc k]`, then `F` and the image of `k'` in `F'` are linearly disjoint
over `k`. -/
theorem linearDisjoint_fieldRange_of_finrank_ratFunc_eq [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
    [FiniteDimensional (RatFunc k) F] (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hdeg : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  set x := algebraMap (RatFunc k) F RatFunc.X
  have hx : Transcendental k x :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
      RatFunc.transcendental_X
  have hx' : Transcendental k' (algebraMap F F' x) := by
    rw [hX]
    exact (transcendental_algebraMap_iff (algebraMap (RatFunc k') F').injective).mpr
      RatFunc.transcendental_X
  have : FiniteDimensional k⟮x⟯ F :=
    Module.Finite.of_equiv_equiv (RatFunc.algEquivOfTranscendental _ hx).toRingEquiv
      (RingEquiv.refl F) (RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply)
  refine linearDisjoint_fieldRange_of_finrank_over_adjoin_simple_eq hx' h ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hdeg]

/-- **Exact constants descend along any linearly disjoint extension.** If `F` and the image of `k'`
in `F'` are linearly disjoint over `k` and `k'` is integrally closed in `F'`, then `k` is integrally
closed in `F`. Neither finiteness nor generation of `F'` is required. -/
theorem isIntegrallyClosedIn_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') : IsIntegrallyClosedIn k F := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k F).injective, fun {z} hz ↦ ?_⟩
  have hz' : IsIntegral k' (algebraMap F F' z) :=
    (hz.map (IsScalarTower.toAlgHom k F F')).tower_top
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hz'
  have hmem : algebraMap F F' z ∈
      (IsScalarTower.toAlgHom k k' F').fieldRange.toSubalgebra ⊓
        (IsScalarTower.toAlgHom k F F').range :=
    ⟨⟨c, hc⟩, ⟨z, rfl⟩⟩
  rw [Subalgebra.LinearDisjoint.inf_eq_bot H, Algebra.mem_bot] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, (algebraMap F F').injective ?_⟩
  rwa [← IsScalarTower.algebraMap_apply k F F']

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

end TauCeti
