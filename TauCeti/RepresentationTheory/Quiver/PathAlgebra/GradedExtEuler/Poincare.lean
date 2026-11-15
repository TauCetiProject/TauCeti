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
import TauCeti.LinearAlgebra.Pi

/-!
# Bigraded Ext finranks and Poincaré series of quiver path algebras

Give the path algebra `kQ` of a quiver `Q` with finitely many vertices its path-length grading.
Because every graded vertex simple `Sᵢ` admits the linear length-one projective resolution
`TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`:

* Over any commutative ring `k`, with no finiteness assumption on arrows or on the target, all
  off-diagonal Ext groups `Extⁿ(Sᵢ, Y{p})` (`n ≠ p`) against a degree-zero target `Y` vanish, all
  higher Ext groups `Extⁿ(Sᵢ, Y)` (`n ≥ 2`) vanish against an arbitrary graded target `Y`,
  `Ext⁰(Sᵢ, Y{0})` is `k`-linearly isomorphic to `eᵢ • Y₀`, and `Ext¹(Sᵢ, Y{1})` is `k`-linearly
  isomorphic to `∏_{a : i ⟶ j} (eⱼ • Y₀)`.
* Over a field `k`, for any finite-vertex quiver (with no acyclicity or arrow-finiteness assumption
  on `Q`), `Module.finrank k (Extⁿ(Sᵢ, Sⱼ{p}))` between graded vertex simples is `δᵢⱼ` at `(0, 0)`,
  `Nat.card (i ⟶ j)` at `(1, 1)`, and `0` in all other bidegrees. When `i ⟶ j` is finite this is
  the true `k`-dimension `dim_k Ext¹(Sᵢ, Sⱼ{1}) = #(i ⟶ j)`; when `i ⟶ j` is infinite,
  `Ext¹(Sᵢ, Sⱼ{1}) ≅ ((i ⟶ j) → k)` is infinite-dimensional while both `Module.finrank` and
  `Nat.card (i ⟶ j)` evaluate to `0` by convention.
* Consequently, for every truncation bound `b ≥ 2`, the `Module.finrank`-based diagonal Ext
  Poincaré polynomial is `δᵢⱼ + Nat.card (i ⟶ j) · X` (recording true Ext dimensions when `i ⟶ j`
  is finite, and setting the `X`-coefficient to `0` when `i ⟶ j` is infinite). When internally
  finite (so each `Extⁿ(Sᵢ, Sⱼ{p})` is finite-dimensional), the full bigraded Ext Poincaré series
  is diagonally supported and equal to `δᵢⱼ + Nat.card (i ⟶ j) · (1, 1)`, and its Alexander- and
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
  of `Ext⁰(Sᵢ, Y{0})` and `Ext¹(Sᵢ, Y{1})` for degree-zero targets over a commutative ring, with
  `@[simp]` evaluation and inverse-evaluation lemmas.
* `TauCeti.PathAlgebra.finrank_ext_gradedVertexSimple_shiftObj` and
  `TauCeti.PathAlgebra.finrank_gradedExt_gradedVertexSimple`: `Module.finrank` of all bigraded Ext
  groups between graded vertex simples (giving `dim_k` when `i ⟶ j` is finite, and `0` at `(1, 1)`
  by the `finrank`/`Nat.card` convention when `i ⟶ j` is infinite).
* `TauCeti.PathAlgebra.diagonalExtPoincarePolynomial_gradedVertexSimple`,
  `TauCeti.PathAlgebra.diagonalExtPoincareMatrix_gradedVertexSimple`,
  `TauCeti.PathAlgebra.bigradedExtPoincareSeries_gradedVertexSimple`, and
  `TauCeti.PathAlgebra.bigradedExtPoincareMatrix_gradedVertexSimple`: explicit `finrank`-based
  Poincaré series and matrices for `b ≥ 2`.
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

/-- `extZeroGradedVertexSimpleShiftObjLinearEquiv` sends an `Ext⁰` class to the image of the
head generator of `Sᵢ` under the corresponding morphism `Sᵢ ⟶ Y{0}`. -/
@[simp]
theorem coe_extZeroGradedVertexSimpleShiftObjLinearEquiv_apply (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (α : Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 0) 0) :
    (extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY α : Y) =
      (Ext.linearEquiv₀ (R := k) α).hom
        ((gradedVertexProjectiveToSimple k Q i).hom
          (gradedVertexProjectiveGenerator k Q i)) := by
  simp [extZeroGradedVertexSimpleShiftObjLinearEquiv, Linear.homCongr_apply]
  rfl

/-- On `Ext.mk₀ f`, `extZeroGradedVertexSimpleShiftObjLinearEquiv` evaluates `f` at the head
generator of `Sᵢ`. -/
theorem coe_extZeroGradedVertexSimpleShiftObjLinearEquiv_mk₀ (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (f : gradedVertexSimple k Q i ⟶ Y.shiftObj 0) :
    (extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY (Ext.mk₀ f) : Y) =
      f.hom
        ((gradedVertexProjectiveToSimple k Q i).hom
          (gradedVertexProjectiveGenerator k Q i)) := by
  rw [coe_extZeroGradedVertexSimpleShiftObjLinearEquiv_apply,
    show Ext.mk₀ f = (Ext.linearEquiv₀ (R := k)).symm f from
      (Ext.linearEquiv₀_symm_apply (R := k) f).symm,
    LinearEquiv.apply_symm_apply]

/-- Precomposing the morphism representing
`(extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm m` with the quotient map
`kQ eᵢ ⟶ Sᵢ` recovers the graded map out of `kQ eᵢ` corresponding to `m`. -/
@[reassoc (attr := simp)]
theorem gradedVertexProjectiveToSimple_comp_extZeroGradedVertexSimpleShiftObjLinearEquiv_symm
    (i : Q) {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (m : ↥(vertexIdempotent k i • Y.grading.piece 0)) :
    gradedVertexProjectiveToSimple k Q i ≫
        Ext.linearEquiv₀ (R := k)
          ((extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm m) =
      (gradedVertexProjectiveHomEquiv k Q i Y).symm m ≫
        ((GradedModuleCat.shiftFunctorZeroIso (integerGrade k Q)).app Y).inv := by
  set α := (extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm m
  have hα : gradedVertexProjectiveHomEquiv k Q i Y
      ((gradedVertexProjectiveToSimple k Q i ≫ Ext.linearEquiv₀ (R := k) α) ≫
        ((GradedModuleCat.shiftFunctorZeroIso (integerGrade k Q)).app Y).hom) = m := by
    have h1 : extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY α = m :=
      LinearEquiv.apply_symm_apply _ m
    simp only [extZeroGradedVertexSimpleShiftObjLinearEquiv, LinearEquiv.trans_apply,
      Linear.homCongr_apply, Iso.refl_inv, Category.id_comp] at h1
    exact h1
  have hhom : (gradedVertexProjectiveToSimple k Q i ≫ Ext.linearEquiv₀ (R := k) α) ≫
      ((GradedModuleCat.shiftFunctorZeroIso (integerGrade k Q)).app Y).hom =
      (gradedVertexProjectiveHomEquiv k Q i Y).symm m :=
    (LinearEquiv.eq_symm_apply _).mpr hα
  exact (Iso.eq_comp_inv ((GradedModuleCat.shiftFunctorZeroIso (integerGrade k Q)).app Y)).mpr hhom

/-- On the image of `x ∈ kQ eᵢ` in `Sᵢ`, the morphism representing
`(extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm m` acts by scalar multiplication on
`m`. -/
@[simp]
theorem hom_linearEquiv₀_extZeroGradedVertexSimpleShiftObjLinearEquiv_symm_apply
    (i : Q) {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (m : ↥(vertexIdempotent k i • Y.grading.piece 0))
    (x : gradedVertexProjective k Q i) :
    (Ext.linearEquiv₀ (R := k)
        ((extZeroGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm m)).hom
      ((gradedVertexProjectiveToSimple k Q i).hom x) =
      gradedVertexProjectiveSubtype k Q i x • (m : Y) := by
  have h := congrArg (fun φ => φ.hom x)
    (gradedVertexProjectiveToSimple_comp_extZeroGradedVertexSimpleShiftObjLinearEquiv_symm
      k Q i hY m)
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, Iso.app_inv,
    GradedModuleCat.hom_shiftFunctorZeroIso_inv_app, LinearMap.id_apply,
    hom_gradedVertexProjectiveHomEquiv_symm_apply] at h
  exact h

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

/-- The inverse of `extOneGradedVertexSimpleShiftObjLinearEquiv` transports a cocycle on
`gradedVertexSimpleProjectiveResolution` along `toProjectiveResolutionXIso 1`. -/
@[simp]
theorem extOneGradedVertexSimpleShiftObjLinearEquiv_symm_extMk (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (g : (gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolution.complex.X 1 ⟶
      Y.shiftObj 1)
    (h12 : 1 + 1 = 2)
    (hg : (gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolution.complex.d 2 1 ≫
      g = 0) :
    (extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm
        ((gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolution.extMk
          g 2 h12 hg) =
      ((gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolutionXIso 1).inv ≫ g := by
  apply (extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).injective
  rw [LinearEquiv.apply_symm_apply, extOneGradedVertexSimpleShiftObjLinearEquiv_apply]
  cases h12
  simp only [Iso.hom_inv_id_assoc]

/-- Against a target `Y` concentrated in internal degree `0`, `Ext¹(Sᵢ, Y{1})` is `k`-linearly
isomorphic to `∏_{a : i ⟶ j} (eⱼ • Y₀)`. -/
def extOneGradedVertexSimpleShiftObjPiLinearEquiv (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥) :
    Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1 ≃ₗ[k]
      ∀ a : (j : Q) × (i ⟶ j), ↥(vertexIdempotent k a.1 • Y.grading.piece 0) :=
  (extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm.trans
    (gradedArrowSumHomShiftOneEquiv k Q i Y)

/-- `extOneGradedVertexSimpleShiftObjPiLinearEquiv` factors through the inverse of
`extOneGradedVertexSimpleShiftObjLinearEquiv` followed by `gradedArrowSumHomShiftOneEquiv`. -/
theorem extOneGradedVertexSimpleShiftObjPiLinearEquiv_apply (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (α : Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1) :
    extOneGradedVertexSimpleShiftObjPiLinearEquiv k Q i hY α =
      gradedArrowSumHomShiftOneEquiv k Q i Y
        ((extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm α) :=
  (rfl)

/-- At an arrow `a : i ⟶ j`, `extOneGradedVertexSimpleShiftObjPiLinearEquiv` evaluates the
representing morphism out of `gradedArrowSum k Q i` on the `a`th summand generator. -/
@[simp]
theorem coe_extOneGradedVertexSimpleShiftObjPiLinearEquiv_apply (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (α : Ext.{t} (gradedVertexSimple k Q i) (Y.shiftObj 1) 1)
    (a : (j : Q) × (i ⟶ j)) :
    (extOneGradedVertexSimpleShiftObjPiLinearEquiv k Q i hY α a : Y) =
      ((extOneGradedVertexSimpleShiftObjLinearEquiv k Q i hY).symm α).hom
        (((GradedModuleCat.coproductCofan fun b : (j : Q) × (i ⟶ j) =>
            (gradedVertexProjective k Q b.1).shiftObj 1).inj a).hom
          (gradedVertexProjectiveGenerator k Q a.1)) :=
  coe_gradedArrowSumHomShiftOneEquiv_apply k Q i _ a

/-- The inverse of `extOneGradedVertexSimpleShiftObjPiLinearEquiv` sends a family
`v ∈ ∏_{a : i ⟶ j} (eⱼ • Y₀)` to the `Ext¹` class of the corresponding morphism out of
`gradedArrowSum k Q i`. -/
@[simp]
theorem extOneGradedVertexSimpleShiftObjPiLinearEquiv_symm_apply (i : Q)
    {Y : GradedModuleCat.{max u v w} (integerGrade k Q)}
    (hY : ∀ p, p ≠ 0 → Y.grading.piece p = ⊥)
    (v : ∀ a : (j : Q) × (i ⟶ j), ↥(vertexIdempotent k a.1 • Y.grading.piece 0)) :
    (extOneGradedVertexSimpleShiftObjPiLinearEquiv k Q i hY).symm v =
      (gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolution.extMk
        (((gradedVertexSimpleProjectiveResolution k Q i).toProjectiveResolutionXIso 1).hom ≫
          (gradedArrowSumHomShiftOneEquiv k Q i Y).symm v)
        2 rfl (by simp) :=
  extOneGradedVertexSimpleShiftObjLinearEquiv_apply k Q i hY _

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

/-! ### Diagonal Ext finranks and Poincaré series over a field -/

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

/-- **Bigraded Ext `finrank` between graded vertex simples**: `Module.finrank k (Extⁿ(Sᵢ, Sⱼ{p}))`
is `δᵢⱼ` in bidegree `(0, 0)`, `Nat.card (i ⟶ j)` in bidegree `(1, 1)`, and `0` everywhere else.
When `i ⟶ j` is finite this gives `dim_k Extⁿ(Sᵢ, Sⱼ{p})`; when `i ⟶ j` is infinite,
`Ext¹(Sᵢ, Sⱼ{1})` is infinite-dimensional while both `Module.finrank` and `Nat.card (i ⟶ j)`
evaluate to `0` by convention. -/
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
      have hsub (l : Q) (hl : l ≠ j) : Subsingleton ((i ⟶ l) → M l) := by
        have := (Module.finrank_eq_zero_iff_of_free k (M l)).mp
          (by simp [M, finrank_vertexIdempotent_smul_gradedVertexSimple_piece_zero, hl])
        infer_instance
      let eMj : M j ≃ₗ[k] k :=
        LinearEquiv.ofFinrankEq (M j) k (by
          simp [M, finrank_vertexIdempotent_smul_gradedVertexSimple_piece_zero])
      rw [(((LinearEquiv.piCurry (R := k) fun l (_ : i ⟶ l) => M l).trans
          (LinearEquiv.piProjOfSubsingleton k j hsub)).trans
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

/-- `Module.finrank` of `GradedExt` between graded vertex simples in every bidegree `(n, p)`
(giving `dim_k` when `i ⟶ j` is finite, and `0` at `(1, 1)` by convention when `i ⟶ j` is
infinite). -/
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

/-- For any truncation bound `b ≥ 2`, the `Module.finrank`-based diagonal Ext Poincaré polynomial
of `(Sᵢ, Sⱼ)` is `δᵢⱼ + Nat.card (i ⟶ j) · X` (recording `dim_k Ext¹(Sᵢ, Sⱼ{1})` when `i ⟶ j` is
finite, and `0` when `i ⟶ j` is infinite). -/
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

/-- For any truncation bound `b ≥ 2`, the `Module.finrank`-based diagonal Ext Poincaré matrix of
the graded vertex simples is `1 + X • A`, where `Aᵢⱼ = Nat.card (i ⟶ j)` (equal to `0` for any pair
with infinitely many arrows `i ⟶ j`). -/
theorem diagonalExtPoincareMatrix_gradedVertexSimple {b : ℕ} (hb : 2 ≤ b) :
    diagonalExtPoincareMatrix.{t} k (gradedVertexSimple k Q) b =
      1 + (Polynomial.X : Polynomial ℤ) •
        Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : Polynomial ℤ) := by
  ext i j
  rw [diagonalExtPoincareMatrix_apply,
    diagonalExtPoincarePolynomial_gradedVertexSimple k Q i j hb]
  by_cases hij : i = j <;> simp [hij, mul_comm]

/-- For any truncation bound `b ≥ 2` and internally finite `(Sᵢ, Sⱼ)`, the full bigraded Ext
Poincaré series of `(Sᵢ, Sⱼ)` is `δᵢⱼ + Nat.card (i ⟶ j) · (1, 1)`. -/
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

/-- For any truncation bound `b ≥ 2` and internally finite `(Sᵢ, Sⱼ)`, the full bigraded Ext
Poincaré matrix of the graded vertex simples is
`1 + Matrix.of fun i j => AddMonoidAlgebra.single (1, 1) (Nat.card (i ⟶ j))`. -/
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
