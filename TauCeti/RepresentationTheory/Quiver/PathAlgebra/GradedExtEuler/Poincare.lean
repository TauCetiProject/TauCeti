/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Poincare
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.CartanMatrix
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.LinearResolution

/-!
# Bigraded Ext dimensions and Poincaré series of quiver path algebras

Give the path algebra `kQ` of a quiver `Q` with finitely many vertices its path-length grading.
Because every graded vertex simple `Sᵢ` admits the linear length-one projective resolution
`TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`:

* Over any commutative ring `k`, with no finiteness assumption on arrows or on the target, all
  off-diagonal Ext groups `Extⁿ(Sᵢ, Y{p})` (`n ≠ p`) against a degree-zero target `Y` vanish, all
  higher Ext groups `Extⁿ(Sᵢ, Y)` (`n ≥ 2`) vanish against an arbitrary graded target `Y`,
  `Ext⁰(Sᵢ, Y{0})` is `k`-linearly isomorphic to `eᵢ • Y₀`, and `Ext¹(Sᵢ, Y{1})` is `k`-linearly
  isomorphic to `∏_{a : i ⟶ j} (eⱼ • Y₀)`.
* Over a field `k`, for any finite-vertex quiver (with no acyclicity or arrow-finiteness assumption
  on `Q`), `dim_k Extⁿ(Sᵢ, Sⱼ{p})` between graded vertex simples is `δᵢⱼ` at `(0, 0)`,
  `Nat.card (i ⟶ j)` at `(1, 1)`, and `0` in all other bidegrees.
* Consequently, for every truncation bound `b ≥ 2`, the diagonal Ext Poincaré polynomial is
  `δᵢⱼ + Nat.card (i ⟶ j) · X`, the full bigraded Ext Poincaré series (when internally finite) is
  diagonally supported and equal to `δᵢⱼ + Nat.card (i ⟶ j) · (1, 1)`, and its Alexander- and
  Maslov-graded Euler characteristics coincide at `δᵢⱼ - Nat.card (i ⟶ j) · q`.
* When `kQ` is finite-dimensional, evaluating the diagonal Ext Poincaré matrix `P(X)` at `-q`
  inverts the transposed graded Cartan matrix: `Cᵀ P(-q) = 1` and `P(-q) = (Cᵀ)⁻¹`.

## Main definitions and results

* `TauCeti.PathAlgebra.subsingleton_ext_gradedVertexSimple_shiftObj_of_ne` and
  `TauCeti.PathAlgebra.subsingleton_gradedExt_gradedVertexSimple_of_ne`: off-diagonal Ext vanishing
  against any degree-zero target.
* `TauCeti.PathAlgebra.extZeroGradedVertexSimpleShiftObjLinearEquiv`,
  `TauCeti.PathAlgebra.extOneGradedVertexSimpleShiftObjLinearEquiv`, and
  `TauCeti.PathAlgebra.extOneGradedVertexSimpleShiftObjPiLinearEquiv`: `k`-linear identifications
  of `Ext⁰(Sᵢ, Y{0})` and `Ext¹(Sᵢ, Y{1})` for degree-zero targets over a commutative ring.
* `TauCeti.PathAlgebra.finrank_ext_gradedVertexSimple_shiftObj` and
  `TauCeti.PathAlgebra.finrank_gradedExt_gradedVertexSimple`: complete bigraded Ext dimensions
  between graded vertex simples.
* `TauCeti.PathAlgebra.diagonalExtPoincarePolynomial_gradedVertexSimple`,
  `TauCeti.PathAlgebra.diagonalExtPoincareMatrix_gradedVertexSimple`,
  `TauCeti.PathAlgebra.bigradedExtPoincareSeries_gradedVertexSimple`, and
  `TauCeti.PathAlgebra.bigradedExtPoincareMatrix_gradedVertexSimple`: explicit Poincaré series and
  matrices for `b ≥ 2`.
* `TauCeti.PathAlgebra.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one` and
  `TauCeti.PathAlgebra.diagonalExtPoincareMatrix_map_eq_inv_gradedCartanMatrix_transpose`: the
  path-algebra Koszul Cartan--Poincaré identities `Cᵀ P(-q) = 1` and `P(-q) = (Cᵀ)⁻¹`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for diagonal Ext and the Koszul Cartan--Poincaré relation.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded
  Cartan and Euler conventions on path algebras.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

attribute [local instance] integerGradedAlgebra

universe u v w t

section CommRing

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]

/-! ### Graded Hom equivalences for vertex projectives and the arrow kernel -/

/-- Graded morphisms out of `kQ eᵢ` into `Y` are `k`-linearly isomorphic to `eᵢ • Y₀`. -/
def gradedVertexProjectiveHomEquiv (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) :
    (gradedVertexProjective k Q i ⟶ Y) ≃ₗ[k] ↥(vertexIdempotent k i • Y.grading.piece 0) :=
  (Linear.homCongr k (eqToIso (gradedVertexProjective_def k Q i)) (Iso.refl Y)).trans
    (GradedModuleCat.ofIdealSpanSingletonHomEquiv
      (vertexIdempotent_mul_self i : IsIdempotentElem (vertexIdempotent k i : pathAlgebra k Q))
      (vertexIdempotent_mem_integerGrade_zero k Q i)
      (isHomogeneous_span_vertexIdempotent k Q i) Y)

/-- Graded morphisms from the shifted arrow kernel `⨁_{a : i ⟶ j} (kQ eⱼ){1}` into `Y{1}` are
`k`-linearly isomorphic to `∏_{a : i ⟶ j} (eⱼ • Y₀)`. -/
def gradedArrowSumHomShiftOneEquiv (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) :
    (gradedArrowSum k Q i ⟶ Y.shiftObj 1) ≃ₗ[k]
      ∀ a : (j : Q) × (i ⟶ j), ↥(vertexIdempotent k a.1 • Y.grading.piece 0) := by
  let M : (j : Q) × (i ⟶ j) → GradedModuleCat.{max u v w} (integerGrade k Q) :=
    fun a => (gradedVertexProjective k Q a.1).shiftObj 1
  let c := GradedModuleCat.coproductCofan.{w, max u v w, max u v w, max u v} M
  let eCoprod : (gradedArrowSum k Q i ⟶ Y.shiftObj 1) ≃ₗ[k]
      ∀ a : (j : Q) × (i ⟶ j), (M a ⟶ Y.shiftObj 1) :=
    { toFun := fun f a => c.inj a ≫ f
      map_add' := fun _ _ => funext fun _ => by simp
      map_smul' := fun _ _ => funext fun _ => by simp
      invFun := fun g =>
        GradedModuleCat.coproductDesc.{w, max u v w, max u v w, max u v} M
          (Limits.Cofan.mk (Y.shiftObj 1) g)
      left_inv := fun f =>
        (GradedModuleCat.coproductCofanIsColimit.{w, max u v w, max u v w, max u v} M).hom_ext
          fun ⟨a⟩ =>
            GradedModuleCat.coproductCofan_inj_desc.{w, max u v w, max u v w, max u v} M
              (Limits.Cofan.mk (Y.shiftObj 1) fun b => c.inj b ≫ f) a
      right_inv := fun g => funext fun a =>
        GradedModuleCat.coproductCofan_inj_desc.{w, max u v w, max u v w, max u v} M
          (Limits.Cofan.mk (Y.shiftObj 1) g) a }
  let eShift (j : Q) : ((gradedVertexProjective k Q j).shiftObj 1 ⟶ Y.shiftObj 1) ≃ₗ[k]
      (gradedVertexProjective k Q j ⟶ Y) :=
    (LinearEquiv.ofBijective
      ((GradedModuleCat.shift (integerGrade k Q)).functor.mapLinearMap k
        (X := gradedVertexProjective k Q j) (Y := Y))
      ⟨(GradedModuleCat.shift (integerGrade k Q)).functor.map_injective,
        (GradedModuleCat.shift (integerGrade k Q)).functor.map_surjective⟩).symm
  exact eCoprod.trans <|
    LinearEquiv.piCongrRight fun a =>
      (eShift a.1).trans (gradedVertexProjectiveHomEquiv k Q a.1 Y)

/-! ### Diagonal Ext vanishing and linear equivalences over a commutative ring -/

variable [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- Off-diagonal Ext from a graded vertex simple `Sᵢ` into a target `Y` concentrated in internal
degree `0` vanishes: `Extⁿ(Sᵢ, Y{p}) = 0` for `n ≠ p`. -/
theorem subsingleton_ext_gradedVertexSimple_shiftObj_of_ne (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) (n : ℕ) (p : ℤ) (hnp : (n : ℤ) ≠ p) :
    Subsingleton (Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj p) n) :=
  (isLinear_gradedVertexSimpleProjectiveResolution k Q i).subsingleton_ext_shiftObj_of_ne
    hY n p hnp

/-- Off-diagonal `GradedExt` from `Sᵢ` into a degree-zero target `Y` vanishes whenever `n ≠ p`. -/
theorem subsingleton_gradedExt_gradedVertexSimple_of_ne (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) (n : ℕ) (p : ℤ) (hnp : (n : ℤ) ≠ p) :
    Subsingleton
      (GradedExt.{t} (GradedModuleCat.shift (integerGrade k Q))
        (gradedVertexSimple k Q i) Y n p) := by
  have : Subsingleton
      (Ext.{t} (gradedVertexSimple k Q i) ((GradedModuleCat.shiftFunctor p).obj Y) n) := by
    rw [GradedModuleCat.shiftFunctor_obj]
    exact subsingleton_ext_gradedVertexSimple_shiftObj_of_ne k Q i hY n p hnp
  exact (extAddEquivOfIso (Iso.refl _)
    ((GradedModuleCat.shiftPowIso (integerGrade k Q) p).app Y) n).injective.subsingleton

/-- Higher Ext from `Sᵢ` into any graded module vanishes from cohomological degree `2` on. -/
theorem subsingleton_ext_gradedVertexSimple_of_two_le (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (Ext.{t} (gradedVertexSimple k Q i) Y n) := by
  let _ := hasProjectiveDimensionLT_two_gradedVertexSimple k Q i
  exact HasProjectiveDimensionLT.subsingleton (gradedVertexSimple k Q i) 2 n hn Y

/-- Every graded vertex simple has uniform cohomological Ext bound `2` against any graded target. -/
theorem isGradedExtBoundedBy_two_gradedVertexSimple (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) :
    IsGradedExtBoundedBy.{t} (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) Y 2 :=
  ⟨fun _ hn _ => subsingleton_ext_gradedVertexSimple_of_two_le k Q i _ hn⟩

/-- Against a target `Y` concentrated in internal degree `0`, `Ext⁰(Sᵢ, Y{0})` is `k`-linearly
isomorphic to `eᵢ • Y₀`. -/
def extZeroGradedVertexSimpleShiftObjLinearEquiv (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 0) 0 ≃ₗ[k]
      ↥(vertexIdempotent k i • Y.grading.piece 0) := by
  have hs := shortExact_gradedVertexSimpleResolution k Q i
  rw [gradedVertexSimpleResolution_def] at hs
  let aug : (gradedVertexSimple k Q i ⟶ Y.shiftObj 0) ≃ₗ[k]
      (gradedVertexProjective k Q i ⟶ Y.shiftObj 0) :=
    LinearEquiv.ofBijective (Linear.leftComp k _ (gradedVertexProjectiveToSimple k Q i))
      ⟨fun _ _ h => (cancel_epi _).mp h, fun f =>
        hs.exact.desc' f <|
          (isLinear_gradedVertexSimpleProjectiveResolution k Q i).hom_eq_zero 1
            (by simpa [sub_eq_add_neg] using hY 1 one_ne_zero)
            (gradedArrowSumToVertexProjective k Q i ≫ f)⟩
  exact (Ext.linearEquiv₀ (R := k)).trans <| aug.trans <|
    (Linear.homCongr k (Iso.refl _)
      ((GradedModuleCat.shiftFunctorZeroIso (integerGrade k Q)).app Y)).trans
      (gradedVertexProjectiveHomEquiv k Q i Y)

/-- Against a target `Y` concentrated in internal degree `0`, `Ext¹(Sᵢ, Y{1})` is `k`-linearly
isomorphic to the graded Hom module `gradedArrowSum k Q i ⟶ Y.shiftObj 1`. -/
def extOneGradedVertexSimpleShiftObjLinearEquiv (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    (gradedArrowSum k Q i ⟶ Y.shiftObj 1) ≃ₗ[k]
      Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1 :=
  (isLinear_gradedVertexSimpleProjectiveResolution k Q i).extLinearEquivShiftObj hY 0

/-- `extOneGradedVertexSimpleShiftObjLinearEquiv` sends a graded morphism from `gradedArrowSum` to
its class in `Ext¹(Sᵢ, Y{1})` computed via `gradedVertexSimpleProjectiveResolution`. -/
@[simp]
theorem extOneGradedVertexSimpleShiftObjLinearEquiv_apply (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (f : gradedArrowSum k Q i ⟶ Y.shiftObj 1) :
    extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY f =
      (gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolution.extMk
        (((gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolutionXIso 1).hom ≫ f)
        2 rfl (by simp) :=
  (isLinear_gradedVertexSimpleProjectiveResolution k Q i).extLinearEquivShiftObj_apply hY 0 f

/-- Against a target `Y` concentrated in internal degree `0`, `Ext¹(Sᵢ, Y{1})` is `k`-linearly
isomorphic to `∏_{a : i ⟶ j} (eⱼ • Y₀)`. -/
def extOneGradedVertexSimpleShiftObjPiLinearEquiv (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1 ≃ₗ[k]
      ∀ a : (j : Q) × (i ⟶ j), ↥(vertexIdempotent k a.1 • Y.grading.piece 0) :=
  (extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm.trans
    (gradedArrowSumHomShiftOneEquiv k Q i Y)

/-- Against a target `Y` concentrated in internal degree `0`, the bidegree `(0, 0)` Ext `finrank`
from `Sᵢ` equals the `finrank` of `eᵢ • Y₀`. -/
theorem finrank_ext_gradedVertexSimple_shiftObj_zero (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    Module.finrank k (Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 0) 0) =
      Module.finrank k ↥(vertexIdempotent k i • Y.grading.piece 0) :=
  (extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).finrank_eq

end CommRing

section Field

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-! ### Diagonal Ext dimensions and Poincaré series over a field -/

/-- Against a degree-zero target `Y` whose idempotent degree-`0` subspaces are finite-dimensional,
the bidegree `(1, 1)` Ext dimension from a vertex simple `Sᵢ` with finitely many outgoing arrows is
`∑_{a : i ⟶ j} dim_k (eⱼ • Y₀)`. -/
theorem finrank_ext_gradedVertexSimple_shiftObj_one (i : Q)
    [Fintype ((j : Q) × (i ⟶ j))]
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    [∀ j : Q, Module.Finite k ↥(vertexIdempotent k j • Y.grading.piece 0)]
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    Module.finrank k (Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1) =
      ∑ a : (j : Q) × (i ⟶ j),
        Module.finrank k ↥(vertexIdempotent k a.1 • Y.grading.piece 0) := by
  rw [(extOneGradedVertexSimpleShiftObjPiLinearEquiv k Q i hY).finrank_eq]
  exact Module.finrank_pi_fintype k

/-- For every truncation bound `b`, the bigraded Ext Poincaré series of `(Sᵢ, Sⱼ)` is diagonally
supported. -/
theorem isDiagonal_bigradedExtPoincareSeries_gradedVertexSimple (i j : Q)
    (h : IsGradedExtInternallyFinite.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j))
    (b : ℕ) :
    Bigraded.IsDiagonal
      (bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b) := by
  rw [Bigraded.isDiagonal_iff]
  intro m p hmp
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, coeff_bigradedExtPoincareSeries]
    split_ifs with hn
    · let _ := subsingleton_gradedExt_gradedVertexSimple_of_ne.{u, v, w, t} k Q i
        (fun _ => gradedVertexSimple_piece_eq_bot k Q j) n p hmp
      exact Module.finrank_zero_of_subsingleton
    · rfl
  | negSucc n => exact coeff_bigradedExtPoincareSeries_negSucc _ _ _ _ _ _

section VertexSimple

variable [DecidableEq Q]

omit [Finite Q] [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))] in
private def sigmaArrowPiLinearEquiv (i j : Q)
    (M : Q → Type (max u v w)) [∀ l, AddCommGroup (M l)] [∀ l, Module k (M l)]
    (hsub : ∀ l, l ≠ j → Subsingleton (M l)) :
    (∀ a : (l : Q) × (i ⟶ l), M a.1) ≃ₗ[k] ((i ⟶ j) → M j) where
  toFun f a := f ⟨j, a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g a := if h : a.1 = j then h ▸ g (h ▸ a.2) else 0
  left_inv f := funext fun ⟨l, a⟩ => by
    by_cases hl : l = j
    · subst hl; simp
    · have := hsub l hl
      exact Subsingleton.elim _ _
  right_inv g := funext fun _ => by simp

/-- **Complete bigraded Ext dimensions between graded vertex simples**: `dim_k Extⁿ(Sᵢ, Sⱼ{p})` is
`δᵢⱼ` in bidegree `(0, 0)`, `Nat.card (i ⟶ j)` in bidegree `(1, 1)`, and `0` everywhere else. No
acyclicity, finite-dimensionality, or arrow-finiteness assumption on `Q` is needed. -/
@[simp]
theorem finrank_ext_gradedVertexSimple_shiftObj (i j : Q) (n : ℕ) (p : ℤ) :
    Module.finrank k
        (Ext.{t} (gradedVertexSimple k Q i) ((gradedVertexSimple k Q j).shiftObj p) n) =
      if n = 0 ∧ p = 0 then (if i = j then 1 else 0)
      else if n = 1 ∧ p = 1 then Nat.card (i ⟶ j)
      else 0 := by
  by_cases hnp : (n : ℤ) = p
  · subst hnp
    rcases n with _ | _ | n
    · rw [Nat.cast_zero, finrank_ext_gradedVertexSimple_shiftObj_zero k Q i
          (fun _ => gradedVertexSimple_piece_eq_bot k Q j),
        finrank_vertexIdempotent_smul_gradedVertexSimple_piece_zero]
      simp
    · rw [zero_add, Nat.cast_one,
        (extOneGradedVertexSimpleShiftObjPiLinearEquiv k Q i
          (fun _ => gradedVertexSimple_piece_eq_bot k Q j)).finrank_eq]
      simp only [one_ne_zero, and_self, ite_false, ite_true]
      let M (l : Q) := ↥(vertexIdempotent k l • (gradedVertexSimple k Q j).grading.piece 0)
      have hsub (l : Q) (hl : l ≠ j) : Subsingleton (M l) :=
        (Module.finrank_eq_zero_iff_of_free k (M l)).mp
          (by simp [M, finrank_vertexIdempotent_smul_gradedVertexSimple_piece_zero, hl])
      let eMj : M j ≃ₗ[k] k :=
        LinearEquiv.ofFinrankEq (M j) k (by
          simp [M, finrank_vertexIdempotent_smul_gradedVertexSimple_piece_zero])
      rw [((sigmaArrowPiLinearEquiv k Q i j M hsub).trans
          (LinearEquiv.piCongrRight fun _ => eMj)).finrank_eq]
      by_cases hfin : Finite (i ⟶ j)
      · let _ := Fintype.ofFinite (i ⟶ j)
        rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
      · classical
        let _ : Infinite (i ⟶ j) := not_finite_iff_infinite.mp hfin
        rw [(Pi.linearIndependent_single_one (i ⟶ j) k).finrank_eq_zero_of_infinite,
          Nat.card_eq_zero_of_infinite]
    · let _ := subsingleton_ext_gradedVertexSimple_of_two_le.{u, v, w, t} k Q i
        ((gradedVertexSimple k Q j).shiftObj ((n + 2 : ℕ) : ℤ)) (Nat.le_add_left 2 n)
      rw [Module.finrank_zero_of_subsingleton, ite_eq_right (by omega), ite_eq_right (by omega)]
  · let _ := subsingleton_ext_gradedVertexSimple_shiftObj_of_ne.{u, v, w, t} k Q i
      (fun _ => gradedVertexSimple_piece_eq_bot k Q j) n p hnp
    rw [Module.finrank_zero_of_subsingleton]
    have h0 : ¬(n = 0 ∧ p = 0) := by rintro ⟨rfl, rfl⟩; exact hnp rfl
    have h1 : ¬(n = 1 ∧ p = 1) := by rintro ⟨rfl, rfl⟩; exact hnp rfl
    rw [ite_eq_right h0, ite_eq_right h1]

/-- Complete bigraded `GradedExt` dimensions between graded vertex simples. -/
@[simp]
theorem finrank_gradedExt_gradedVertexSimple (i j : Q) (n : ℕ) (p : ℤ) :
    Module.finrank k
        (GradedExt.{t} (GradedModuleCat.shift (integerGrade k Q))
          (gradedVertexSimple k Q i) (gradedVertexSimple k Q j) n p) =
      if n = 0 ∧ p = 0 then (if i = j then 1 else 0)
      else if n = 1 ∧ p = 1 then Nat.card (i ⟶ j)
      else 0 := by
  rw [(extLinearEquivOfIso k (Iso.refl _)
      ((GradedModuleCat.shiftPowIso (integerGrade k Q) p).app _) n).finrank_eq,
    GradedModuleCat.shiftFunctor_obj, finrank_ext_gradedVertexSimple_shiftObj]

/-- For any truncation bound `b ≥ 2`, the diagonal Ext Poincaré polynomial of `(Sᵢ, Sⱼ)` is
`δᵢⱼ + Nat.card (i ⟶ j) · X`. -/
theorem diagonalExtPoincarePolynomial_gradedVertexSimple (i j : Q) {b : ℕ} (hb : 2 ≤ b) :
    diagonalExtPoincarePolynomial.{t} k
        (gradedVertexSimple k Q i) (gradedVertexSimple k Q j) b =
      (if i = j then 1 else 0) + Polynomial.C (Nat.card (i ⟶ j) : ℤ) * Polynomial.X := by
  rw [diagonalExtPoincarePolynomial_eq_of_le
      (isGradedExtBoundedBy_two_gradedVertexSimple k Q i _) hb,
    diagonalExtPoincarePolynomial_def, Finset.sum_range_succ, Finset.sum_range_one]
  ext m
  simp only [finrank_ext_gradedVertexSimple_shiftObj, Nat.cast_zero, Nat.cast_one, and_self,
    ite_true, one_ne_zero, ite_false, Polynomial.coeff_add, Polynomial.coeff_monomial,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  by_cases hij : i = j <;> rcases m with _ | _ | m <;>
    simp [hij, Polynomial.coeff_one]

/-- For any truncation bound `b ≥ 2`, the diagonal Ext Poincaré matrix of the graded vertex
simples is `1 + X • A`, where `Aᵢⱼ = Nat.card (i ⟶ j)`. -/
theorem diagonalExtPoincareMatrix_gradedVertexSimple {b : ℕ} (hb : 2 ≤ b) :
    diagonalExtPoincareMatrix.{t} k (gradedVertexSimple k Q) b =
      1 + (Polynomial.X : Polynomial ℤ) •
        Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : Polynomial ℤ) := by
  ext i j
  rw [diagonalExtPoincareMatrix_apply,
    diagonalExtPoincarePolynomial_gradedVertexSimple k Q i j hb]
  by_cases hij : i = j <;> simp [hij, mul_comm]

/-- For any truncation bound `b ≥ 2`, the full bigraded Ext Poincaré series of `(Sᵢ, Sⱼ)` is
`δᵢⱼ + Nat.card (i ⟶ j) · (1, 1)`. -/
theorem bigradedExtPoincareSeries_gradedVertexSimple (i j : Q)
    (h : IsGradedExtInternallyFinite.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j))
    {b : ℕ} (hb : 2 ≤ b) :
    bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b =
      (if i = j then 1 else 0) + AddMonoidAlgebra.single (1, 1) (Nat.card (i ⟶ j)) := by
  ext ⟨m, p⟩
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, coeff_bigradedExtPoincareSeries, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rcases n with _ | _ | n
    · have hb0 : 0 < b := by omega
      by_cases hij : i = j <;>
        simp [hij, hb0, AddMonoidAlgebra.one_def, Finsupp.single_apply, Prod.zero_eq_mk, eq_comm]
    · have hb1 : 1 < b := by omega
      by_cases hij : i = j <;>
        simp [hij, hb1, AddMonoidAlgebra.one_def, Prod.zero_eq_mk, eq_comm]
    · by_cases hij : i = j <;>
        simp [hij, AddMonoidAlgebra.one_def, Finsupp.single_apply, Prod.ext_iff]
      · split_ifs <;> omega
      · omega
  | negSucc n =>
    rw [coeff_bigradedExtPoincareSeries_negSucc, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hij : i = j <;> simp [hij, AddMonoidAlgebra.one_def, Prod.zero_eq_mk]

/-- For any truncation bound `b ≥ 2`, the full bigraded Ext Poincaré matrix of the graded vertex
simples is `1 + Matrix.of fun i j => AddMonoidAlgebra.single (1, 1) (Nat.card (i ⟶ j))`. -/
theorem bigradedExtPoincareMatrix_gradedVertexSimple
    (h : ∀ i j : Q, IsGradedExtInternallyFinite.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j))
    {b : ℕ} (hb : 2 ≤ b) :
    bigradedExtPoincareMatrix (gradedVertexSimple k Q) h b =
      1 + Matrix.of fun i j : Q => AddMonoidAlgebra.single (1, 1) (Nat.card (i ⟶ j)) := by
  ext i j
  rw [bigradedExtPoincareMatrix_apply,
    bigradedExtPoincareSeries_gradedVertexSimple k Q i j (h i j) hb]
  by_cases hij : i = j <;> simp [hij]

/-- The Alexander-graded Euler characteristic of the bigraded Ext Poincaré series of `(Sᵢ, Sⱼ)`
is `δᵢⱼ - Nat.card (i ⟶ j) · q` for `b ≥ 2`. -/
theorem euler_bigradedExtPoincareSeries_gradedVertexSimple (i j : Q)
    (h : IsGradedExtInternallyFinite.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j))
    {b : ℕ} (hb : 2 ≤ b) :
    Bigraded.euler
        (bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b) =
      (if i = j then 1 else 0) - (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) * T 1 := by
  rw [bigradedExtPoincareSeries_gradedVertexSimple k Q i j h hb, map_add, Bigraded.euler_single]
  have h1 : Bigraded.euler (if i = j then 1 else 0) = if i = j then 1 else 0 := by
    split_ifs <;> simp
  have hs : AddMonoidAlgebra.single (1 : ℤ) ((1 : ℤ).negOnePow : ℤ) =
      -(T 1 : LaurentPolynomial ℤ) := by
    ext d
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, AddMonoidAlgebra.coeff_neg,
      Finsupp.neg_apply, T_apply]
    rcases eq_or_ne 1 d with rfl | hd
    · decide
    · simp [hd]
  rw [h1, hs, mul_neg, sub_eq_add_neg]

/-- Because `bigradedExtPoincareSeries` of `(Sᵢ, Sⱼ)` is diagonal, its Maslov-graded Euler
characteristic agrees with its Alexander-graded Euler characteristic
`δᵢⱼ - Nat.card (i ⟶ j) · q`. -/
theorem maslovEuler_bigradedExtPoincareSeries_gradedVertexSimple (i j : Q)
    (h : IsGradedExtInternallyFinite.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j))
    {b : ℕ} (hb : 2 ≤ b) :
    Bigraded.maslovEuler
        (bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b) =
      (if i = j then 1 else 0) - (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) * T 1 := by
  have hdiag := isDiagonal_bigradedExtPoincareSeries_gradedVertexSimple k Q i j h b
  have heq : Bigraded.euler
      (bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b) =
      Bigraded.maslovEuler
        (bigradedExtPoincareSeries.{t} k (GradedModuleCat.shift (integerGrade k Q)) h b) :=
    (Bigraded.euler_eq_maslovEuler_iff_isDiagonal _
      (Or.inl fun m a hlt => (Bigraded.isDiagonal_iff _).mp hdiag m a hlt.ne')).mpr hdiag
  rw [← heq, euler_bigradedExtPoincareSeries_gradedVertexSimple k Q i j h hb]

end VertexSimple

end Field

/-! ### Path-algebra Koszul Cartan--Poincaré identities -/

section CartanPoincare

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q] [DecidableEq Q]
  [FiniteDimensional k (pathAlgebra k Q)]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- **The path-algebra Koszul Cartan--Poincaré identity**: for any truncation bound `b ≥ 2`,
evaluating the diagonal Ext Poincaré matrix `P(X)` of the graded vertex simples at `-q` gives a
right inverse to the transposed graded Cartan matrix, `Cᵀ P(-q) = 1`. -/
theorem gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one
    {b : ℕ} (hb : 2 ≤ b) :
    (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q))ᵀ *
      (diagonalExtPoincareMatrix.{t} k (gradedVertexSimple k Q) b).map
        (Polynomial.eval₂RingHom C (-T 1)) = 1 := by
  have hC := congrArg Matrix.transpose
    (one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one k Q)
  rw [Matrix.transpose_mul, Matrix.transpose_one] at hC
  convert hC using 2
  rw [diagonalExtPoincareMatrix_gradedVertexSimple k Q hb]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.of_apply, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_natCast,
    smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, Polynomial.eval₂_one]
    ring
  · simp only [hij, Ne.symm hij, ite_false, Polynomial.eval₂_zero]
    ring

/-- **The diagonal Ext Poincaré matrix at `-q` is the inverse of the transposed graded Cartan
matrix**: `P(-q) = (Cᵀ)⁻¹` for every finite-dimensional path algebra and every `b ≥ 2`. -/
theorem diagonalExtPoincareMatrix_map_eq_inv_gradedCartanMatrix_transpose
    {b : ℕ} (hb : 2 ≤ b) :
    (diagonalExtPoincareMatrix.{t} k (gradedVertexSimple k Q) b).map
        (Polynomial.eval₂RingHom C (-T 1)) =
      (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q))ᵀ⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one k Q hb)).symm

end CartanPoincare

end TauCeti.PathAlgebra
