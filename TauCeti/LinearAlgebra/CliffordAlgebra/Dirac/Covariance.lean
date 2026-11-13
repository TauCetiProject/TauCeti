/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dirac.ThreeOne
public import TauCeti.LinearAlgebra.Matrix.Pauli

/-!
# Lorentz covariance of the Dirac matrices and changes of spinor frame

This file continues the Weyl model of the Dirac representation of `Cl(3,1)` on
`ℂ⁴ = ℂ² ⊕ ℂ²` from `TauCeti.LinearAlgebra.CliffordAlgebra.Dirac.ThreeOne`.

A Spin element `s ↦ A ∈ SL₂(ℂ)` acts on time-first physical coordinates by the Lorentz
transformation `Λ = P⁻¹ ∘ (s • ·) ∘ P`, which preserves the Minkowski form `g`. Its inverse has
matrix `η Λᵀ η` for `η = diag(1, -1, -1, -1)`. The dual-frame Dirac matrices are covariant:

`∑_μ (Λ⁻¹)^ν_μ Γ^μ ρ_W(A) = ρ_W(A) Γ^ν`,

which is the identity making `ψ'(x) = ρ_W(A) ψ(Λ⁻¹ x)` a symmetry of the Dirac operator
`i Γ^μ ∂_μ`.

The Weyl action `ρ_W(A) = diag(A, (Aᴴ)⁻¹)` is the conjugate Weyl action
`ρ_conj(A) = diag(A, conj A)` written in the spinor frame `T = diag(1, ε)` with
`ε = !![0, 1; -1, 0]`, because `ε (conj A) ε⁻¹ = (Aᴴ)⁻¹` on `SL₂(ℂ)`. In the original frame the
invariant Hermitian pairing `H₀ = [[0, 1], [1, 0]]` becomes `Tᴴ H₀ T = [[0, ε], [-ε, 0]]`.

Exchanging the two Weyl summands by `U = H₀` and relabelling the spatial coordinates as
`y = (x₂, x₃, x₁)` puts the Dirac matrices in the textbook form `γ⁰ = [[0, 1], [1, 0]]`,
`γⁱ = [[0, σᵢ], [-σᵢ, 0]]` with the Pauli matrices in the order `(σ₁, σ₂, σ₃)`; under the same
swap the chirality matrix becomes `diag(-1, 1)` and the Weyl action becomes `diag((Aᴴ)⁻¹, A)`.

## Main definitions and results

* `TauCeti.diracLorentz`: the Lorentz transformation of time-first coordinates induced by Spin,
  with `TauCeti.realCliffordForm_one_three_diracLorentz` and
  `TauCeti.diracLorentz_symm_apply_single`.
* `TauCeti.sum_smul_diracGamma_mul_diracWeyl`: Lorentz covariance of the Dirac matrices.
* `TauCeti.diracConjWeyl`: the conjugate Weyl action, with
  `TauCeti.diracEpsilon_mul_map_conj_mul_inv` and `TauCeti.diracWeyl_eq_mul_diracConjWeyl_mul`.
* `TauCeti.conjTranspose_diracConjWeyl_mul_mul`: invariance of the pairing `[[0, ε], [-ε, 0]]`.
* `TauCeti.fromBlocks_mul_diracGamma_mul`: the Dirac matrices after the Weyl swap.

## References

* M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory* (1995), §§3.2–3.4,
  for the covariance law of the Dirac matrices and the Weyl representation.
-/

public section

open Matrix
open scoped Matrix ComplexConjugate

namespace TauCeti

/-! ## The Lorentz transformation of a Spin element -/

/-- The Lorentz transformation `Λ = P⁻¹ ∘ (s • ·) ∘ P` of time-first physical coordinates induced
by a Spin element `s`. -/
noncomputable def diracLorentz :
    spinGroup (realCliffordForm 3 1) →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun s := timeFirstToNative ≪≫ₗ CliffordAlgebra.spinVectorAction _ s ≪≫ₗ
    timeFirstToNative.symm
  map_one' := by
    ext x : 1
    simp
  map_mul' s t := by
    ext x : 1
    simp only [LinearEquiv.trans_apply, CliffordAlgebra.spinVectorAction_mul, mul_apply_eq_comp,
      LinearEquiv.apply_symm_apply]

/-- The defining formula `Λ x = P⁻¹ (s • P x)`. -/
theorem diracLorentz_apply (s : spinGroup (realCliffordForm 3 1)) (x : Fin 4 → ℝ) :
    diracLorentz s x = timeFirstToNative.symm (s • timeFirstToNative x) := by
  simp [diracLorentz]

/-- The coordinate change intertwines the Lorentz transformation with the native Spin action:
`P (Λ x) = s • P x`. -/
theorem timeFirstToNative_diracLorentz (s : spinGroup (realCliffordForm 3 1))
    (x : Fin 4 → ℝ) : timeFirstToNative (diracLorentz s x) = s • timeFirstToNative x := by
  rw [diracLorentz_apply, LinearEquiv.apply_symm_apply]

/-- The Lorentz transformation of a Spin element preserves the Minkowski form `g`. -/
theorem realCliffordForm_one_three_diracLorentz (s : spinGroup (realCliffordForm 3 1))
    (x : Fin 4 → ℝ) : realCliffordForm 1 3 (diracLorentz s x) = realCliffordForm 1 3 x := by
  have h := realCliffordForm_three_one_timeFirstToNative (diracLorentz s x)
  rw [timeFirstToNative_diracLorentz, CliffordAlgebra.spinGroup_smul_apply,
    CliffordAlgebra.spinVectorAction_map_app, realCliffordForm_three_one_timeFirstToNative] at h
  exact neg_injective h.symm

/-- The Lorentz transformation of a Spin element preserves the polar Minkowski form. -/
@[simp]
theorem polar_realCliffordForm_one_three_diracLorentz (s : spinGroup (realCliffordForm 3 1))
    (x y : Fin 4 → ℝ) :
    QuadraticMap.polar (realCliffordForm 1 3) (diracLorentz s x) (diracLorentz s y) =
      QuadraticMap.polar (realCliffordForm 1 3) x y := by
  simp only [QuadraticMap.polar, ← map_add, realCliffordForm_one_three_diracLorentz]

/-- The inverse Lorentz transformation has matrix `η Λᵀ η`:
`(Λ⁻¹)^ν_μ = η^{μμ} η^{νν} Λ^μ_ν`. -/
theorem diracLorentz_symm_apply_single (s : spinGroup (realCliffordForm 3 1)) (μ ν : Fin 4) :
    (diracLorentz s).symm (Pi.single μ 1) ν =
      realCliffordWeight 1 3 μ * realCliffordWeight 1 3 ν * diracLorentz s (Pi.single ν 1) μ := by
  have h := polar_realCliffordForm_one_three_diracLorentz s ((diracLorentz s).symm (Pi.single μ 1))
    (Pi.single ν 1)
  rw [LinearEquiv.apply_symm_apply, QuadraticMap.polar_comm, polar_realCliffordForm_single,
    polar_realCliffordForm_single] at h
  have hν := realCliffordWeight_mul_self 1 3 ν
  linear_combination (-realCliffordWeight 1 3 ν / 2) * h -
    ((diracLorentz s).symm (Pi.single μ 1) ν) * hν

/-! ## Covariance of the Dirac matrices -/

/-- Expansion of the vector Clifford map in the dual-frame Dirac matrices:
`C(P x) = ∑_μ η^{μμ} x_μ Γ^μ`. -/
theorem diracVector_timeFirstToNative_eq_sum (x : Fin 4 → ℝ) :
    diracVector (timeFirstToNative x) =
      ∑ μ, ((realCliffordWeight 1 3 μ * x μ : ℝ) : ℂ) • diracGamma μ := by
  conv_lhs => rw [pi_eq_sum_univ x]
  simp only [map_sum, map_smul, diracGamma_def, smul_smul, Complex.coe_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_comm, ← mul_assoc, realCliffordWeight_mul_self, one_mul]
  simp [Pi.single_apply, eq_comm]

/-- **Lorentz covariance of the Dirac matrices**:
`∑_μ (Λ⁻¹)^ν_μ Γ^μ ρ_W(s) = ρ_W(s) Γ^ν`, for the Lorentz transformation `Λ` of `s`. -/
theorem sum_smul_diracGamma_mul_diracWeyl (s : spinGroup (realCliffordForm 3 1)) (ν : Fin 4) :
    ∑ μ, (((diracLorentz s).symm (Pi.single μ 1) ν : ℝ) : ℂ) • (diracGamma μ * diracWeyl s) =
      diracWeyl s * diracGamma ν := by
  rw [diracGamma_def, mul_smul_comm, ← diracVector_smul_mul_diracWeyl, ←
    timeFirstToNative_diracLorentz, diracVector_timeFirstToNative_eq_sum, Finset.sum_mul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [diracLorentz_symm_apply_single, smul_mul_assoc,
    ← Complex.coe_smul (realCliffordWeight 1 3 ν), smul_smul, ← Complex.ofReal_mul]
  congr 2
  ring

/-! ## The conjugate Weyl carrier -/

/-- The matrix `ε = !![0, 1; -1, 0]` of the standard symplectic form on a Weyl summand `ℂ²`. -/
def diracEpsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The entries of `ε`. -/
theorem diracEpsilon_def : diracEpsilon = !![0, 1; -1, 0] := (rfl)

/-- `ε² = -1`. -/
@[simp]
theorem diracEpsilon_mul_self : diracEpsilon * diracEpsilon = -1 := by
  rw [diracEpsilon_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `ε⁻¹ = -ε`. -/
@[simp]
theorem inv_diracEpsilon : diracEpsilon⁻¹ = -diracEpsilon :=
  inv_eq_left_inv (by rw [neg_mul, diracEpsilon_mul_self, neg_neg])

/-- `εᴴ = -ε`. -/
@[simp]
theorem conjTranspose_diracEpsilon : diracEpsilonᴴ = -diracEpsilon := by
  rw [diracEpsilon_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation by `ε` turns the complex conjugate of a two-by-two matrix into the conjugate
transpose of its adjugate: `ε (conj A) ε⁻¹ = (adj A)ᴴ`. -/
theorem diracEpsilon_mul_map_conj_mul_inv (A : Matrix (Fin 2) (Fin 2) ℂ) :
    diracEpsilon * A.map conj * diracEpsilon⁻¹ = (adjugate A)ᴴ := by
  rw [inv_diracEpsilon, diracEpsilon_def, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- On `SL₂(ℂ)`, conjugation by `ε` turns the complex conjugate into the inverse conjugate
transpose: `ε (conj A) ε⁻¹ = (Aᴴ)⁻¹`. -/
theorem diracEpsilon_mul_map_conj_mul_inv_eq_inv_conjTranspose
    (A : SpecialLinearGroup (Fin 2) ℂ) :
    diracEpsilon * (A : Matrix (Fin 2) (Fin 2) ℂ).map conj * diracEpsilon⁻¹ =
      ((A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)⁻¹ := by
  rw [diracEpsilon_mul_map_conj_mul_inv, adjugate_conjTranspose, inv_def, det_conjTranspose,
    SpecialLinearGroup.det_coe, star_one, Ring.inverse_one, one_smul]

/-- The conjugate Weyl action of `Spin(3,1)` on `ℂ⁴`: the element corresponding to
`A ∈ SL₂(ℂ)` acts by `diag(A, conj A)`. -/
noncomputable def diracConjWeyl :
    spinGroup (realCliffordForm 3 1) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ where
  toFun s := fromBlocks (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    ((realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ).map conj)
  map_one' := by simp
  map_mul' s t := by simp [fromBlocks_multiply, Matrix.map_mul]

/-- The defining block formula of the conjugate Weyl action. -/
theorem diracConjWeyl_apply (s : spinGroup (realCliffordForm 3 1)) :
    diracConjWeyl s =
      fromBlocks (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        ((realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ).map conj) :=
  (rfl)

/-- The Weyl action is the conjugate Weyl action in the spinor frame `T = diag(1, ε)`:
`ρ_W(s) = T ρ_conj(s) T⁻¹`. -/
theorem diracWeyl_eq_mul_diracConjWeyl_mul (s : spinGroup (realCliffordForm 3 1)) :
    diracWeyl s =
      fromBlocks 1 0 0 diracEpsilon * diracConjWeyl s * fromBlocks 1 0 0 diracEpsilon⁻¹ := by
  rw [diracWeyl_apply, diracConjWeyl_apply, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add,
    diracEpsilon_mul_map_conj_mul_inv]

/-- In the original frame of the conjugate Weyl carrier, the Hermitian pairing `H₀` is
`Tᴴ H₀ T = [[0, ε], [-ε, 0]]`. -/
theorem conjTranspose_fromBlocks_diracEpsilon_mul_mul :
    (fromBlocks 1 0 0 diracEpsilon)ᴴ * fromBlocks 0 1 1 0 * fromBlocks 1 0 0 diracEpsilon =
      fromBlocks 0 diracEpsilon (-diracEpsilon) 0 := by
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- The conjugate Weyl action preserves the pairing `[[0, ε], [-ε, 0]]`. -/
theorem conjTranspose_diracConjWeyl_mul_mul (s : spinGroup (realCliffordForm 3 1)) :
    (diracConjWeyl s)ᴴ * fromBlocks 0 diracEpsilon (-diracEpsilon) 0 * diracConjWeyl s =
      fromBlocks 0 diracEpsilon (-diracEpsilon) 0 := by
  set T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fromBlocks 1 0 0 diracEpsilon
  have hT : fromBlocks 1 0 0 diracEpsilon⁻¹ * T = 1 := by
    simp [T, fromBlocks_multiply, inv_diracEpsilon]
  -- Transport the invariance of `H₀` under the Weyl action through `ρ_W = T ρ_conj T⁻¹`.
  have hconj : T * diracConjWeyl s = diracWeyl s * T := by
    rw [diracWeyl_eq_mul_diracConjWeyl_mul, Matrix.mul_assoc _ _ T, hT, Matrix.mul_one]
  rw [← conjTranspose_fromBlocks_diracEpsilon_mul_mul]
  calc (diracConjWeyl s)ᴴ * (Tᴴ * fromBlocks 0 1 1 0 * T) * diracConjWeyl s
      = (T * diracConjWeyl s)ᴴ * fromBlocks 0 1 1 0 * (T * diracConjWeyl s) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Tᴴ * ((diracWeyl s)ᴴ * fromBlocks 0 1 1 0 * diracWeyl s) * T := by
        rw [hconj]
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Tᴴ * fromBlocks 0 1 1 0 * T := by rw [conjTranspose_diracWeyl_mul_mul]

/-! ## The Weyl swap and the textbook Dirac matrices -/

/-- The native Hermitian matrix of `P x` is `x₀ + y · σ` for the spatial coordinates
`y = (x₂, x₃, x₁)` in the Pauli order `(σ₁, σ₂, σ₃)`. -/
theorem realCliffordThreeOneVectorEquivHermitian_timeFirstToNative (x : Fin 4 → ℝ) :
    (realCliffordThreeOneVectorEquivHermitian (timeFirstToNative x) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (x 0 : ℂ) • 1 + pauli ![x 2, x 3, x 1] := by
  rw [coe_realCliffordThreeOneVectorEquivHermitian_apply, pauli_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

/-- After the Weyl swap `U = H₀`, the vector Clifford map is
`U C(P x) U⁻¹ = [[0, x₀ - y · σ], [x₀ + y · σ, 0]]` for `y = (x₂, x₃, x₁)`. -/
theorem fromBlocks_mul_diracVector_timeFirstToNative_mul (x : Fin 4 → ℝ) :
    fromBlocks 0 1 1 0 * diracVector (timeFirstToNative x) * fromBlocks 0 1 1 0 =
      fromBlocks 0 ((x 0 : ℂ) • 1 - pauli ![x 2, x 3, x 1])
        ((x 0 : ℂ) • 1 + pauli ![x 2, x 3, x 1]) 0 := by
  rw [diracVector_apply, realCliffordThreeOneVectorEquivHermitian_timeFirstToNative,
    adjugate_fin_two_eq_trace_smul_one_sub, fromBlocks_multiply, fromBlocks_multiply]
  simp only [trace_add, trace_smul, trace_one, trace_pauli, Fintype.card_fin, Nat.cast_ofNat,
    Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  congr 1
  module

/-- After the Weyl swap `U = H₀`, the Dirac matrices take the textbook form:
`U Γ⁰ U⁻¹ = [[0, 1], [1, 0]]` and `U Γ^{c(i)} U⁻¹ = [[0, σᵢ], [-σᵢ, 0]]`, where the spatial
coordinate cycle `c = (2, 3, 1)` lists the physical index carrying the Pauli matrix `σᵢ`. -/
theorem fromBlocks_mul_diracGamma_mul (i : Fin 3) :
    fromBlocks 0 1 1 0 * diracGamma (![2, 3, 1] i) * fromBlocks 0 1 1 0 =
      fromBlocks 0 (pauli (Pi.single i 1)) (-pauli (Pi.single i 1)) 0 := by
  rw [diracGamma_def, mul_smul_comm, smul_mul_assoc,
    fromBlocks_mul_diracVector_timeFirstToNative_mul, realCliffordWeight_of_le (by fin_cases i <;>
      decide)]
  fin_cases i <;> simp [fromBlocks_neg, pauli_apply]

/-- The Weyl swap fixes `Γ⁰ = H₀`: `U Γ⁰ U⁻¹ = [[0, 1], [1, 0]]`. -/
theorem fromBlocks_mul_diracGamma_zero_mul :
    fromBlocks 0 1 1 0 * diracGamma 0 * fromBlocks 0 1 1 0 = fromBlocks 0 1 1 0 := by
  rw [diracGamma_zero, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- After the Weyl swap the chirality matrix is `U Γ⁵ U⁻¹ = diag(-1, 1)`. -/
theorem fromBlocks_mul_diracChirality_mul :
    fromBlocks 0 1 1 0 * diracChirality * fromBlocks 0 1 1 0 = fromBlocks (-1) 0 0 1 := by
  rw [diracChirality_eq, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- After the Weyl swap the Weyl action is `U ρ_W(s) U⁻¹ = diag((adj A)ᴴ, A)`, that is,
`diag((Aᴴ)⁻¹, A)` for `A ∈ SL₂(ℂ)` corresponding to `s`. -/
theorem fromBlocks_mul_diracWeyl_mul (s : spinGroup (realCliffordForm 3 1)) :
    fromBlocks 0 1 1 0 * diracWeyl s * fromBlocks 0 1 1 0 =
      fromBlocks (adjugate (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ))ᴴ 0
        0 (realSpinThreeOneEquivSpecialLinear s : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [diracWeyl_apply, fromBlocks_multiply, fromBlocks_multiply]
  simp

end TauCeti
