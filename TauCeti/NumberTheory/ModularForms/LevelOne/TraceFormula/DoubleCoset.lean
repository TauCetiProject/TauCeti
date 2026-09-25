/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule

import TauCeti.LinearAlgebra.Matrix.SmithNormalForm
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Equivalence

/-!
# Double cosets of `PSL(2, ℤ)` in `ℳₙ`

Let `Γ = PSL(2, ℤ)` act on the projective determinant-`n` matrix module `ℳₙ` by left and by
right multiplication. For `n > 0` the elementary divisor theorem puts every `M ∈ ℳₙ` into the
double coset of a diagonal matrix: `M = g · diag(d₀, d₁) · g'` with `g ∈ SL(2, ℤ)`, `g' ∈ Γ`,
`0 < d₀`, `d₀ ∣ d₁` and `d₀ d₁ = n`. Writing `d₀ = a` and `d₁ = am`, the double cosets
`Γ (a 0; 0 am) Γ` with `a, m ≥ 1` therefore cover `ℳ = ⋃_{n ≥ 1} ℳₙ`, as in Popa and Zagier's
decomposition of `ℳ` into double cosets.

The right coset `diag(d₀, d₁) · Γ` and the orbit of `diag(d₀, d₁)` under left multiplication by
`Γ_∞ = ⟨T⟩` are described explicitly below; for `diag(1, m)` the former is Popa and Zagier's coset
`K₀ = (1 0; 0 m) Γ`.

## Main definitions

* `TauCeti.TraceFormulaMatrix.diagonal d₀ d₁ h`: the matrix `diag(d₀, d₁)` of determinant
  `n = d₀ d₁`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.exists_eq_smul_op_smul_mk_diagonal`: for `n > 0`, every
  element of `ℳₙ` lies in the double coset of some `diag(d₀, d₁)` with `0 < d₀`, `d₀ ∣ d₁`.
* `TauCeti.TraceFormulaMatrixModule.mk_mem_orbit_op_mk_diagonal_iff`: for `n ≠ 0`, the class of
  `A` lies in the right coset `diag(d₀, d₁) · Γ` if and only if `d₀` divides the first row of `A`
  and `d₁` its second row.
* `TauCeti.TraceFormulaMatrixModule.mk_mem_orbit_zpowers_T_mk_diagonal_iff`: the
  `Γ_∞`-orbit of `diag(d₀, d₁)` consists of the classes of `(d₀, j d₁; 0, d₁)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105–122, arXiv:1711.00327. The decomposition into double
  cosets and the description of `K₀` are in §4, proof of Theorem 4(b); the `Γ_∞`-orbits of the
  matrices `(1 b; 0 n)` are used in §3, proof of Theorem 2(b).
-/

public section

open Matrix ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti

variable {n : ℤ}

/-- The diagonal matrix `diag(d₀, d₁)`, as a matrix of determinant `n = d₀ d₁`. -/
def TraceFormulaMatrix.diagonal (d₀ d₁ : ℤ) (h : d₀ * d₁ = n) : TraceFormulaMatrix n :=
  ⟨!![d₀, 0; 0, d₁], by simp [Matrix.det_fin_two_of, h]⟩

/-- The underlying matrix of `TraceFormulaMatrix.diagonal d₀ d₁ h` is `diag(d₀, d₁)`. -/
@[simp]
theorem TraceFormulaMatrix.val_diagonal (d₀ d₁ : ℤ) (h : d₀ * d₁ = n) :
    (TraceFormulaMatrix.diagonal d₀ d₁ h).1 = !![d₀, 0; 0, d₁] := (rfl)

namespace TraceFormulaMatrixModule

/-- **Diagonal representatives of the double cosets** (Popa–Zagier, §4, proof of
Theorem 4(b)): for `n > 0`, every `x ∈ ℳₙ` is `g · diag(d₀, d₁) · γ` for some `g ∈ SL(2, ℤ)`,
`γ ∈ PSL(2, ℤ)` and `d₀ d₁ = n` with `0 < d₀` and `d₀ ∣ d₁`. -/
theorem exists_eq_smul_op_smul_mk_diagonal (hn : 0 < n) (x : TraceFormulaMatrixModule n) :
    ∃ (d₀ d₁ : ℤ) (h : d₀ * d₁ = n), 0 < d₀ ∧ d₀ ∣ d₁ ∧
      ∃ (g : SL(2, ℤ)) (γ : PSL(2, ℤ)), x = g • mk (TraceFormulaMatrix.diagonal d₀ d₁ h) <• γ := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  -- the Smith normal form `L A R = diag(d₀, d₁)` gives `A = L⁻¹ diag(d₀, d₁) R⁻¹`
  obtain ⟨L, R, d, hd, hdvd, hLR⟩ := A.1.exists_smith_normal_form_of_det_pos (A.2.symm ▸ hn)
  have hdet : d 0 * d 1 = n := by
    simpa [Fin.prod_univ_two, A.2] using prod_eq_det_of_mul_mul_eq_diagonal hLR
  refine ⟨d 0, d 1, hdet, hd 0, hdvd (Fin.zero_le 1), L⁻¹, (R : PSL(2, ℤ))⁻¹, ?_⟩
  rw [eq_inv_smul_iff, MulOpposite.op_inv, eq_inv_smul_iff, smul_mk, op_smul_mk]
  congr 1
  apply FixedDetMatrices.ext'
  simp [FixedDetMatrices.smul_coe, hLR, diagonal_fin_two]

/-- **The right coset of a diagonal matrix** (Popa–Zagier, §4, proof of Theorem 4(b)): for
`n = d₀ d₁ ≠ 0`, the class of a determinant-`n` matrix `A` lies in the right coset
`diag(d₀, d₁) · Γ` if and only if `d₀` divides the first row of `A` and `d₁` its second row. -/
theorem mk_mem_orbit_op_mk_diagonal_iff {d₀ d₁ : ℤ} (h : d₀ * d₁ = n) (hn : n ≠ 0)
    {A : TraceFormulaMatrix n} :
    mk A ∈ MulAction.orbit PSL(2, ℤ)ᵐᵒᵖ (mk (TraceFormulaMatrix.diagonal d₀ d₁ h)) ↔
      d₀ ∣ A.1 0 0 ∧ d₀ ∣ A.1 0 1 ∧ d₁ ∣ A.1 1 0 ∧ d₁ ∣ A.1 1 1 := by
  rw [mk_mem_orbit_op_mk_iff, TraceFormulaMatrix.val_diagonal, ← Matrix.diagonal_vec2,
    Matrix.exists_eq_diagonal_mul_iff (by simp [A.2, h]) (A.2 ▸ IsRegular.of_ne_zero hn).left]
  simp [Fin.forall_fin_two, and_assoc]

/-- **The `Γ_∞`-orbit of a diagonal matrix**: the class of `A` lies in the orbit of
`diag(d₀, d₁)` under left multiplication by `Γ_∞ = ⟨T⟩` if and only if
`A = ±(d₀, j d₁; 0, d₁)` for some `j ∈ ℤ`. -/
theorem mk_mem_orbit_zpowers_T_mk_diagonal_iff {d₀ d₁ : ℤ} (h : d₀ * d₁ = n)
    {A : TraceFormulaMatrix n} :
    mk A ∈ MulAction.orbit (Subgroup.zpowers T) (mk (TraceFormulaMatrix.diagonal d₀ d₁ h)) ↔
      ∃ j : ℤ, A.1 = !![d₀, j * d₁; 0, d₁] ∨ A.1 = -!![d₀, j * d₁; 0, d₁] := by
  rw [MulAction.mem_orbit_iff, Subgroup.exists_zpowers]
  refine exists_congr fun j ↦ ?_
  have hT : (T ^ j • TraceFormulaMatrix.diagonal d₀ d₁ h).1 = !![d₀, j * d₁; 0, d₁] := by
    simp [FixedDetMatrices.smul_coe, coe_T_zpow]
  rw [Subgroup.smul_def, smul_mk, mk_eq_iff]
  grind [FixedDetMatrices.ext', TraceFormulaMatrix.val_neg]

end TraceFormulaMatrixModule

end TauCeti
