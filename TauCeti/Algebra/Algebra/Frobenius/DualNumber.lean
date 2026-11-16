/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Graded
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.Algebra.DualNumber.TensorProduct
public import TauCeti.Algebra.DualNumber.Trace

/-!
# Frobenius algebra structure on the dual numbers

This file instantiates the trace-reconstructed Frobenius coalgebra, handle element, and
even-supported grading theory on the dual numbers `R[ε]` over a commutative semiring `R`.

## Main results

* `TauCeti.isPerfPair_compr₂_mul_sndHom`, `TauCeti.bilinForm_toMatrix_compr₂_mul_smul_sndHom`,
  `TauCeti.det_bilinForm_toMatrix_compr₂_mul_smul_sndHom`: the canonical trace pairing is perfect,
  and `c • TrivSqZeroExt.sndHom R R` has pairing matrix `!![0, c; c, 0]` (determinant `-c ^ 2`).
* `TauCeti.isPerfPair_compr₂_mul_smul_sndHom_iff`,
  `TauCeti.isFrobeniusFunctional_smul_sndHom_iff`,
  `TauCeti.isFrobeniusFunctional_two_smul_sndHom_int`,
  `TauCeti.not_isPerfPair_compr₂_mul_two_smul_sndHom_int`: unit vs regularity criteria and the
  explicit `2 • sndHom` separation over `ℤ`.
* `TauCeti.traceDualBasis_sndHom_dualNumberBasis`, `TauCeti.frobeniusCoalgebra_sndHom_comul_one`,
  `TauCeti.frobeniusCoalgebra_sndHom_comul_eps`, `TauCeti.handleElement_frobeniusCoalgebra_sndHom`,
  `TauCeti.sndHom_handleElement_frobeniusCoalgebra_sndHom`,
  `TauCeti.handleElement_frobeniusCoalgebra_sndHom_sq`: trace-reconstructed coproduct and handle
  identities.
* `TauCeti.odd_dualNumberIntegerGrade_eq_bot`,
  `TauCeti.isHomogeneous_sndHom_dualNumberIntegerGrade`,
  `TauCeti.isHomogeneous_frobeniusCoalgebra_sndHom_comul`,
  `TauCeti.handleElement_frobeniusCoalgebra_sndHom_mem_grade`,
  `TauCeti.sndHom_comp_dualNumberAlgebraTensorAlgEquiv`,
  `TauCeti.isHomogeneous_dualNumberAlgebraTensorAlgEquiv`: even-supported grading and base change.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
* J. Goertz, A. Marino, P. Wedrich, *The gl(N) web algebra and foams* (v1), Example 2.9.
-/

public section

open scoped DualNumber Matrix TensorProduct

namespace TauCeti

section Pairing

variable (R : Type*) [CommSemiring R]

/-- The canonical trace pairing `(x, y) ↦ (x * y).snd` on `R[ε]` is perfect. -/
instance isPerfPair_compr₂_mul_sndHom :
    ((LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R)).IsPerfPair := by
  have h : (LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R) = dualNumberTracePairing R := by
    ext x y; simp
  rw [h]
  exact dualNumberTracePairing_isPerfPair R

/-- The matrix of the scaled trace pairing `(x, y) ↦ c * (x * y).snd` in the basis `(1, ε)` is
`!![0, c; c, 0]`. -/
theorem bilinForm_toMatrix_compr₂_mul_smul_sndHom (c : R) :
    LinearMap.BilinForm.toMatrix (dualNumberBasis R)
        ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R)) =
      !![0, c; c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- The matrix of `TauCeti.dualNumberTracePairing R` in the basis `(1, ε)` is `!![0, 1; 1, 0]`. -/
theorem bilinForm_toMatrix_dualNumberTracePairing :
    LinearMap.BilinForm.toMatrix (dualNumberBasis R) (dualNumberTracePairing R) =
      !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- The scaled trace pairing `(x, y) ↦ c * (x * y).snd` on `R[ε]` is perfect if and only if
`c` is a unit in `R`. -/
theorem isPerfPair_compr₂_mul_smul_sndHom_iff (c : R) :
    ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R)).IsPerfPair ↔
      IsUnit c := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.bijective_left.surjective (TrivSqZeroExt.sndHom R R)
    have hε := LinearMap.congr_fun hx (DualNumber.eps : R[ε])
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.smul_apply,
      TrivSqZeroExt.sndHom_apply, smul_eq_mul, DualNumber.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, mul_one, mul_zero, add_zero] at hε
    exact isUnit_iff_exists_inv.mpr ⟨x.fst, hε⟩
  · rintro ⟨u, rfl⟩
    have hcomp :
        (LinearMap.mul R R[ε]).compr₂ ((u : R) • TrivSqZeroExt.sndHom R R) =
          ((LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R)).compl₁₂
            (LinearEquiv.smulOfUnit (R := R) (M := R[ε]) u).toLinearMap
            (LinearEquiv.refl R R[ε]).toLinearMap := by
      ext x y
      simp [LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul]
    rw [hcomp]
    exact LinearMap.IsPerfPair.compl₁₂
      (p := (LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R))
      (LinearEquiv.smulOfUnit u) (LinearEquiv.refl R R[ε])

/-- Over a commutative semiring `R`, the scaled trace `c • TrivSqZeroExt.sndHom R R` is a
Frobenius functional if and only if multiplication by `c` has trivial kernel. -/
theorem isFrobeniusFunctional_smul_sndHom_iff_mul_eq_zero (c : R) :
    (c • TrivSqZeroExt.sndHom R R).IsFrobeniusFunctional ↔ ∀ r : R, c * r = 0 → r = 0 := by
  rw [LinearMap.isFrobeniusFunctional_iff]
  constructor
  · intro h r hr
    have h0 : TrivSqZeroExt.inl r = (0 : R[ε]) := h.1 (TrivSqZeroExt.inl r) fun b ↦ by
      simp [smul_eq_mul, ← mul_assoc, hr]
    simpa using congrArg TrivSqZeroExt.fst h0
  · intro hc
    have hleft : ∀ a : R[ε], (∀ b : R[ε], (c • TrivSqZeroExt.sndHom R R) (a * b) = 0) → a = 0 := by
      intro a ha
      have hε := ha (DualNumber.eps : R[ε])
      have h1 := ha (1 : R[ε])
      simp only [LinearMap.smul_apply, TrivSqZeroExt.sndHom_apply, smul_eq_mul, DualNumber.snd_mul,
        DualNumber.fst_eps, DualNumber.snd_eps, mul_one, mul_zero, add_zero] at hε h1
      exact TrivSqZeroExt.ext (hc a.fst hε) (hc a.snd h1)
    exact ⟨hleft, fun b hb ↦ hleft b fun a ↦ by rw [mul_comm]; exact hb a⟩

end Pairing

section CommRingPairing

variable (R : Type*) [CommRing R]

/-- Over a commutative ring `R`, the pairing matrix of `c • TrivSqZeroExt.sndHom R R` in the basis
`(1, ε)` has determinant `-(c ^ 2)`. -/
theorem det_bilinForm_toMatrix_compr₂_mul_smul_sndHom (c : R) :
    (LinearMap.BilinForm.toMatrix (dualNumberBasis R)
        ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R))).det = -(c ^ 2) := by
  rw [bilinForm_toMatrix_compr₂_mul_smul_sndHom, Matrix.det_fin_two]
  simp [sq]

/-- Over a commutative ring `R`, `c • TrivSqZeroExt.sndHom R R` is a Frobenius functional if and
only if `c` is regular. -/
theorem isFrobeniusFunctional_smul_sndHom_iff (c : R) :
    (c • TrivSqZeroExt.sndHom R R).IsFrobeniusFunctional ↔ IsRegular c := by
  rw [isFrobeniusFunctional_smul_sndHom_iff_mul_eq_zero, Commute.isRegular_iff (Commute.all c)]
  refine ⟨fun hc a b hab ↦
      sub_eq_zero.mp (hc (a - b) (by dsimp at hab; rw [mul_sub, hab, sub_self])),
    fun hc r hr ↦ hc (by simpa using hr)⟩

/-- Over `ℤ`, the pairing matrix of `2 • TrivSqZeroExt.sndHom ℤ ℤ` in `(1, ε)` has
determinant `-4`. -/
theorem det_bilinForm_toMatrix_two_smul_sndHom_int :
    (LinearMap.BilinForm.toMatrix (dualNumberBasis ℤ)
        ((LinearMap.mul ℤ ℤ[ε]).compr₂ ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ))).det = -4 := by
  rw [det_bilinForm_toMatrix_compr₂_mul_smul_sndHom]
  norm_num

/-- Over `ℤ`, `2 • TrivSqZeroExt.sndHom ℤ ℤ` is a Frobenius functional (nondegenerate). -/
theorem isFrobeniusFunctional_two_smul_sndHom_int :
    ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ).IsFrobeniusFunctional :=
  (isFrobeniusFunctional_smul_sndHom_iff ℤ 2).mpr
    ⟨mul_right_injective₀ (by decide), mul_left_injective₀ (by decide)⟩

/-- Over `ℤ`, the trace pairing of `2 • TrivSqZeroExt.sndHom ℤ ℤ` is not perfect, showing
that nondegeneracy does not imply perfectness over a general commutative ring. -/
theorem not_isPerfPair_compr₂_mul_two_smul_sndHom_int :
    ¬((LinearMap.mul ℤ ℤ[ε]).compr₂ ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ)).IsPerfPair := by
  rw [isPerfPair_compr₂_mul_smul_sndHom_iff, Int.isUnit_iff]
  decide

end CommRingPairing

section CoalgebraAndHandle

variable (R : Type*) [CommSemiring R]

/-- The trace-dual basis of `(1, ε)` with respect to `TrivSqZeroExt.sndHom R R` is `(ε, 1)`. -/
@[simp]
theorem traceDualBasis_sndHom_dualNumberBasis (i : Fin 2) :
    LinearMap.traceDualBasis (TrivSqZeroExt.sndHom R R) (dualNumberBasis R) i =
      dualNumberBasis R i.rev := by
  apply ((LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R)).toPerfPair.injective
  refine dualNumber_linearMap_ext ?_ ?_ <;>
    simp only [LinearMap.toPerfPair_apply, LinearMap.compr₂_apply, LinearMap.mul_apply_apply,
      LinearMap.traceDualBasis_mul] <;>
    fin_cases i <;> simp

/-- The trace-reconstructed comultiplication on `R[ε]` sends `1` to `1 ⊗ ε + ε ⊗ 1`. -/
@[simp]
theorem frobeniusCoalgebra_sndHom_comul_one :
    (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul (1 : R[ε]) =
      (1 : R[ε]) ⊗ₜ[R] DualNumber.eps + DualNumber.eps ⊗ₜ[R] (1 : R[ε]) := by
  rw [LinearMap.frobeniusCoalgebra_comul_eq_sum (TrivSqZeroExt.sndHom R R) (dualNumberBasis R) 1]
  simp [Fin.sum_univ_two]

/-- The trace-reconstructed comultiplication on `R[ε]` sends `ε` to `ε ⊗ ε`. -/
@[simp]
theorem frobeniusCoalgebra_sndHom_comul_eps :
    (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul (DualNumber.eps : R[ε]) =
      DualNumber.eps ⊗ₜ[R] DualNumber.eps := by
  rw [LinearMap.frobeniusCoalgebra_comul_eq_sum (TrivSqZeroExt.sndHom R R) (dualNumberBasis R)
    DualNumber.eps]
  simp [Fin.sum_univ_two]

/-- The handle element of the trace-reconstructed Frobenius algebra `R[ε]` is `2 * ε`. -/
theorem handleElement_frobeniusCoalgebra_sndHom :
    (letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra; Coalgebra.handleElement R R[ε]) =
      2 * DualNumber.eps := by
  rw [LinearMap.handleElement_frobeniusCoalgebra_eq_sum (TrivSqZeroExt.sndHom R R)
    (dualNumberBasis R)]
  simp [Fin.sum_univ_two, two_mul]

/-- The canonical trace evaluates the handle element of `R[ε]` to `2`. -/
theorem sndHom_handleElement_frobeniusCoalgebra_sndHom :
    TrivSqZeroExt.sndHom R R
        (letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra; Coalgebra.handleElement R R[ε]) =
      2 := by
  rw [handleElement_frobeniusCoalgebra_sndHom]
  simp [two_mul, one_add_one_eq_two]

/-- The handle element of the trace-reconstructed Frobenius algebra `R[ε]` squares to zero. -/
theorem handleElement_frobeniusCoalgebra_sndHom_sq :
    (letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra; Coalgebra.handleElement R R[ε]) ^ 2 =
      0 := by
  rw [handleElement_frobeniusCoalgebra_sndHom]
  simp [sq, mul_assoc, mul_left_comm]

end CoalgebraAndHandle

section GradedAndBaseChange

variable (R : Type*) [CommSemiring R]

/-- The integer grading `TauCeti.dualNumberIntegerGrade R` has even support: every odd degree piece
is `⊥`. -/
theorem odd_dualNumberIntegerGrade_eq_bot {p : ℤ} (hp : Odd p) :
    dualNumberIntegerGrade R p = ⊥ := by
  by_cases hneg : p < 0
  · exact dualNumberIntegerGrade_eq_bot_of_neg R hneg
  · lift p to ℕ using (not_lt.mp hneg)
    rw [dualNumberIntegerGrade_ofNat]
    rcases hp with ⟨k, hk⟩
    exact dualNumberGrade_eq_bot R (by omega) (by omega)

/-- With `deg ε = 2`, the canonical trace `TrivSqZeroExt.sndHom R R` is homogeneous of degree
`-2`. -/
theorem isHomogeneous_sndHom_dualNumberIntegerGrade :
    TauCeti.LinearMap.IsHomogeneous (TrivSqZeroExt.sndHom R R)
      (dualNumberIntegerGrade R) (trivialGrading R R) (-2) := by
  rw [isHomogeneous_trivialGrading_neg_iff]
  intro p hp x hx
  by_cases hneg : p < 0
  · rw [dualNumberIntegerGrade_eq_bot_of_neg R hneg] at hx
    simp [(Submodule.mem_bot R).mp hx]
  · lift p to ℕ using (not_lt.mp hneg)
    rw [dualNumberIntegerGrade_ofNat] at hx
    rcases eq_or_ne p 0 with rfl | h0
    · exact (mem_dualNumberGrade_zero R).mp hx
    · rw [dualNumberGrade_eq_bot R h0 (by omega)] at hx
      simp [(Submodule.mem_bot R).mp hx]

/-- With `deg ε = 2`, the trace-reconstructed comultiplication on `R[ε]` is homogeneous of degree
`2`. -/
theorem isHomogeneous_frobeniusCoalgebra_sndHom_comul :
    letI := dualNumberIntegerGradedAlgebra R
    TauCeti.LinearMap.IsHomogeneous (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul
      (dualNumberIntegerGrade R)
      ((InternalGrading.ofDecomposition (dualNumberIntegerGrade R)).tensorProduct
        (InternalGrading.ofDecomposition (dualNumberIntegerGrade R))).piece 2 := by
  let := dualNumberIntegerGradedAlgebra R
  exact LinearMap.isHomogeneous_frobeniusCoalgebra_comul (dualNumberIntegerGrade R)
    (TrivSqZeroExt.sndHom R R) (isHomogeneous_sndHom_dualNumberIntegerGrade R)

/-- With `deg ε = 2`, the handle element of `R[ε]` lies in degree `2`. -/
theorem handleElement_frobeniusCoalgebra_sndHom_mem_grade :
    (letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra; Coalgebra.handleElement R R[ε]) ∈
      dualNumberIntegerGrade R 2 := by
  rw [handleElement_frobeniusCoalgebra_sndHom, two_mul]
  exact (dualNumberIntegerGrade R 2).add_mem
    (eps_mem_dualNumberIntegerGrade_two R) (eps_mem_dualNumberIntegerGrade_two R)

variable (S : Type*) [CommSemiring S] [Algebra R S]

/-- Base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` intertwines the canonical traces of `R[ε]` and
`S[ε]`. -/
theorem sndHom_comp_dualNumberAlgebraTensorAlgEquiv :
    TrivSqZeroExt.sndHom S S ∘ₗ (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap =
      Module.Dual.baseChange S (TrivSqZeroExt.sndHom R R) :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp [Algebra.smul_def, mul_comm]

/-- Base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` is homogeneous of degree zero between the
base-changed integer grading and `TauCeti.dualNumberIntegerGrade S`. -/
theorem isHomogeneous_dualNumberAlgebraTensorAlgEquiv :
    TauCeti.LinearMap.IsHomogeneous (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap
      (fun p ↦ (dualNumberIntegerGrade R p).baseChange S) (dualNumberIntegerGrade S) 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p z hz
  rw [add_zero]
  have hle : (dualNumberIntegerGrade R p).baseChange S ≤
      (dualNumberIntegerGrade S p).comap (dualNumberAlgebraTensorAlgEquiv R S).toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply]
    by_cases hneg : p < 0
    · rw [dualNumberIntegerGrade_eq_bot_of_neg R hneg] at hx
      simp [(Submodule.mem_bot R).mp hx]
    · lift p to ℕ using (not_lt.mp hneg)
      rw [dualNumberIntegerGrade_ofNat] at hx ⊢
      rcases eq_or_ne p 0 with rfl | h0
      · rw [mem_dualNumberGrade_zero] at hx ⊢; simp [hx]
      · rcases eq_or_ne p 2 with rfl | h2
        · rw [mem_dualNumberGrade_two] at hx ⊢; simp [hx]
        · rw [dualNumberGrade_eq_bot R h0 h2] at hx; simp [(Submodule.mem_bot R).mp hx]
  exact hle hz

end GradedAndBaseChange

end TauCeti
