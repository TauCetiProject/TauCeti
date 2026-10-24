/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

import Mathlib.Algebra.GroupWithZero.Action.Regular

/-!
# Isometries of quadratic maps

This file records general properties of quadratic-map isometries.  It also reindexes a weighted
sum of squares along an equivalence of its index type, which complements Mathlib's
`QuadraticForm.weightedSumSquaresCongr` for equal weights and
`QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares` for weights rescaled by squares.

## Main results

* `QuadraticMap.Isometry.polar_apply`: an isometry preserves polarization.
* `QuadraticForm.isIsometry_polarBilin_of_forall_map_app`: a form-preserving linear map preserves
  the polar bilinear form.
* `QuadraticMap.apply_eq_zero_of_apply_eq_smul`: an eigenvector of a form-preserving endomorphism
  whose eigenvalue does not square to `1` (in the sense of regularity of `μ² - 1`) is isotropic.
* `QuadraticMap.IsometryEquiv.polar_apply`: an isometric equivalence preserves polarization.
* `QuadraticMap.IsometryEquiv.polarKernelEquiv`: an isometric equivalence restricts to an
  equivalence of the kernels of polarization against corresponding vectors.
* `QuadraticMap.IsometryEquiv.trans_apply`: composition of isometries acts by composition.
* `QuadraticMap.IsometryEquiv.nondegenerate_iff`: nondegeneracy is invariant under isometry.
* `QuadraticMap.isometryEquivNeg`: if `u * u = -1`, multiplication by `u` is an isometry from
  `Q` to `-Q`.
* `QuadraticForm.isometryEquivWeightedSumSquaresReindex`: reindexing the weights of a weighted sum
  of squares along an equivalence of index types gives an isometric quadratic form.
* `QuadraticForm.equivalent_weightedSumSquares_of_comp_eq`: weighted sums of squares whose weights
  agree after reindexing are equivalent.
* `QuadraticForm.equivalent_zero_iff_finrank_eq_zero`: a form is isometric to the canonical
  zero-dimensional form exactly when its space has dimension zero.
-/

public section

namespace TauCeti

open QuadraticMap

universe u v w

/-- An isometry preserves the polarization of a quadratic map. -/
@[simp]
theorem _root_.QuadraticMap.Isometry.polar_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N}
    {Q₂ : QuadraticMap R M₂ N} (f : Q₁ →qᵢ Q₂) (x y : M₁) :
    polar Q₂ (f x) (f y) = polar Q₁ x y := by
  simp only [QuadraticMap.polar, ← map_add f, QuadraticMap.Isometry.map_app]

/-- A linear map preserving a quadratic form is an isometry of its polar bilinear form. -/
theorem _root_.QuadraticForm.isIsometry_polarBilin_of_forall_map_app
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} {f : Module.End R M} (hf : ∀ x, Q (f x) = Q x) :
    TauCeti.BilinForm.IsIsometry Q.polarBilin f := by
  apply TauCeti.BilinForm.isIsometry_iff.mpr
  intro x y
  have hp : polar Q (f x) (f y) = polar Q x y :=
    (⟨f, hf⟩ : Q →qᵢ Q).polar_apply x y
  simpa only [QuadraticMap.polarBilin_apply_apply] using hp

/-- An eigenvector of a form-preserving endomorphism is isotropic as soon as `μ² - 1` is a regular
scalar for its eigenvalue `μ`: from `f v = μ • v` and `Q (f v) = Q v` one gets `μ² • Q v = Q v`.
Over a field it suffices that `μ² ≠ 1`. -/
theorem _root_.QuadraticMap.apply_eq_zero_of_apply_eq_smul {R : Type u} {M : Type v}
    {N : Type w} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Q : QuadraticMap R M N} {f : Module.End R M} (hf : ∀ x, Q (f x) = Q x) {μ : R}
    (hμ : IsSMulRegular N (μ * μ - 1)) {v : M} (hv : f v = μ • v) : Q v = 0 := by
  have h := hf v
  rw [hv, QuadraticMap.map_smul] at h
  exact hμ.right_eq_zero_of_smul (by rw [sub_smul, h, one_smul, sub_self])

/-- An isometric equivalence preserves the polarization of a quadratic map. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.polar_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x y : M₁) : polar Q₂ (e x) (e y) = polar Q₁ x y := by
  simpa using e.toIsometry.polar_apply x y

/-- An isometric equivalence maps the kernel of polarization against `x` onto the kernel of
polarization against its image. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.map_polarKernel
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x : M₁) :
    (LinearMap.ker (Q₁.polarBilin x)).map e.toLinearMap =
      LinearMap.ker (Q₂.polarBilin (e x)) := by
  ext y
  simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, polarBilin_apply_apply,
    IsometryEquiv.coe_symm_toLinearEquiv, IsometryEquiv.coe_toLinearEquiv]
  rw [← e.polar_apply x (e.symm y), e.apply_symm_apply]

/-- The restriction of an isometric equivalence to the kernels of polarization against
corresponding vectors. -/
def _root_.QuadraticMap.IsometryEquiv.polarKernelEquiv
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x : M₁) :
    LinearMap.ker (Q₁.polarBilin x) ≃ₗ[R] LinearMap.ker (Q₂.polarBilin (e x)) :=
  e.toLinearEquiv.ofSubmodules _ _ (e.map_polarKernel x)

/-- The equivalence between polar kernels acts through the original isometry. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.coe_polarKernelEquiv_apply
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x : M₁) (y : LinearMap.ker (Q₁.polarBilin x)) :
    ((e.polarKernelEquiv x y : LinearMap.ker (Q₂.polarBilin (e x))) : M₂) = e y :=
  e.toLinearEquiv.ofSubmodules_apply (e.map_polarKernel x) y

/-- The inverse equivalence between polar kernels acts through the inverse isometry. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.coe_polarKernelEquiv_symm_apply
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (x : M₁) (y : LinearMap.ker (Q₂.polarBilin (e x))) :
    (((e.polarKernelEquiv x).symm y : LinearMap.ker (Q₁.polarBilin x)) : M₁) = e.symm y :=
  e.toLinearEquiv.ofSubmodules_symm_apply (e.map_polarKernel x) y

/-- The composition of two isometric equivalences acts by composing their underlying maps. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.trans_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {M₃ : Type*} {N : Type w} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N]
    [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) (x : M₁) :
    f.trans g x = g (f x) :=
  rfl

/-- Nondegeneracy of a quadratic map is invariant under an isometric equivalence. -/
theorem _root_.QuadraticMap.IsometryEquiv.nondegenerate_iff
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w}
    [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.Nondegenerate ↔ Q₂.Nondegenerate := by
  -- This follows the proof of Mathlib's `QuadraticMap.IsometryEquiv.map_radical`
  -- (`Mathlib/LinearAlgebra/QuadraticForm/Radical.lean`), with the polar kernel for the radical.
  have hpolar : Q₁.polarBilin.ker.map e.toLinearMap = Q₂.polarBilin.ker := by
    ext
    simp [LinearMap.ext_iff, e.toEquiv.forall_congr_left]
  constructor
  · intro hQ₁
    have hradical := e.map_radical
    rw [hQ₁.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    rw [← hpolar]
    apply Cardinal.lift_le_one_iff.mp
    rw [e.toLinearEquiv.lift_rank_map_eq]
    exact Cardinal.lift_le_one_iff.mpr hQ₁.rank_rad_polar_le
  · intro hQ₂
    have hradical := e.symm.map_radical
    rw [hQ₂.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    apply Cardinal.lift_le_one_iff.mp
    rw [← e.toLinearEquiv.lift_rank_map_eq Q₁.polarBilin.ker, hpolar]
    exact Cardinal.lift_le_one_iff.mpr hQ₂.rank_rad_polar_le

section Neg

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {Q Q' : QuadraticMap R M N} {u : R}

/-- If `u * u = -1`, multiplication by `u` is an isometry from `Q` to `Q' = -Q`, with inverse
multiplication by `-u`. -/
def _root_.QuadraticMap.isometryEquivNeg (h : Q' = -Q) (hu : u * u = -1) :
    Q.IsometryEquiv Q' where
  toLinearEquiv := LinearEquiv.smulOfUnit ⟨u, -u, by rw [mul_neg, hu, neg_neg],
    by rw [neg_mul, hu, neg_neg]⟩
  map_app' m := by
    simp [LinearEquiv.smulOfUnit, h, QuadraticMap.map_smul, hu]

/-- The isometry `QuadraticMap.isometryEquivNeg` multiplies each vector by `u`. -/
@[simp]
theorem _root_.QuadraticMap.isometryEquivNeg_apply (h : Q' = -Q) (hu : u * u = -1) (m : M) :
    QuadraticMap.isometryEquivNeg h hu m = u • m :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

/-- The inverse of `QuadraticMap.isometryEquivNeg` for `u` is the same construction for `-u`, in
the opposite direction. -/
theorem _root_.QuadraticMap.isometryEquivNeg_symm (h : Q' = -Q) (hu : u * u = -1) :
    (QuadraticMap.isometryEquivNeg h hu).symm =
      QuadraticMap.isometryEquivNeg (by rw [h, neg_neg]) (u := -u) (by rw [neg_mul_neg, hu]) := by
  dsimp only [IsometryEquiv.symm, QuadraticMap.isometryEquivNeg]
  congr 1
  exact LinearEquiv.ext fun _ ↦ rfl

/-- The inverse of `QuadraticMap.isometryEquivNeg` multiplies each vector by `-u`. -/
@[simp]
theorem _root_.QuadraticMap.isometryEquivNeg_symm_apply (h : Q' = -Q) (hu : u * u = -1) (m : M) :
    (QuadraticMap.isometryEquivNeg h hu).symm m = -(u • m) := by
  rw [QuadraticMap.isometryEquivNeg_symm, QuadraticMap.isometryEquivNeg_apply, neg_smul]

end Neg

section Reindex

variable {ι ι' R S : Type*} [Fintype ι] [Fintype ι'] [CommSemiring R] [Monoid S]
  [DistribMulAction S R] [SMulCommClass S R R]

/-- Reindexing the weights of a weighted sum of squares along an equivalence of the index types
gives an isometric quadratic form.  The isometry is precomposition with the equivalence. -/
def _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex (w : ι → S) (e : ι' ≃ ι) :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R (w ∘ e)) where
  __ := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    simpa [weightedSumSquares_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      using e.sum_comp fun i ↦ w i • (x i * x i)

/-- The reindexing isometry acts on a vector by precomposition with the equivalence. -/
@[simp]
theorem _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex_apply (w : ι → S) (e : ι' ≃ ι)
    (x : ι → R) (i : ι') :
    QuadraticForm.isometryEquivWeightedSumSquaresReindex w e x i = x (e i) :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

/-- Weighted sums of squares whose weights agree after reindexing are equivalent. -/
theorem _root_.QuadraticForm.equivalent_weightedSumSquares_of_comp_eq
    {w : ι → S} {w' : ι' → S} (e : ι' ≃ ι) (h : w ∘ e = w') :
    (weightedSumSquares R w').Equivalent (weightedSumSquares R w) :=
  ⟨((QuadraticForm.isometryEquivWeightedSumSquaresReindex w e).trans
    (QuadraticForm.weightedSumSquaresCongr h)).symm⟩

end Reindex

/-- A quadratic form is isometric to the canonical zero-dimensional form exactly when
its underlying space has dimension zero. -/
@[simp]
theorem _root_.QuadraticForm.equivalent_zero_iff_finrank_eq_zero {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) :
    Q.Equivalent (0 : QuadraticForm K (Fin 0 → K)) ↔ Module.finrank K V = 0 := by
  constructor
  · rintro ⟨e⟩
    simpa using e.toLinearEquiv.finrank_eq
  · intro h
    have := Module.finrank_zero_iff.mp h
    exact ⟨{ LinearEquiv.ofSubsingleton V (Fin 0 → K) with
      map_app' x := by rw [zero_apply, Subsingleton.elim x 0, map_zero] }⟩

end TauCeti
