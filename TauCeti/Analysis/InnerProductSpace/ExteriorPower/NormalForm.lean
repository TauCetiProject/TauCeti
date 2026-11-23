/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.NormalForm

/-!
# Normal form and Pfaffian divided power of a two-vector

Applying the real block-diagonal normal form of a skew-adjoint endomorphism
(`LinearMap.exists_orthonormalBasis_skew_normalForm`) to the contraction
`TauCeti.twoVectorContraction F` of a two-vector `F ∈ ⋀² E` on a `2r`-dimensional real inner product
space writes `F` in an orthonormal basis `(b₀, b₁, …, b_{2r-1})` as `∑ j, μ j • (b_{2j} ∧ b_{2j+1})`
with nonnegative weights `μ j`. Applying the divided exterior power formula
(`exteriorPower.inv_factorial_smul_pow_sum_smul_ιMulti_two`) then evaluates the Pfaffian power:
`(r!)⁻¹ • exteriorPower.pow F r = (∏ j, μ j) • (b₀ ∧ ⋯ ∧ b_{2r-1})`.

## Main results

* `TauCeti.exists_orthonormalBasis_twoVector_normalForm`: simultaneous normal form and Pfaffian
  divided-power identity for any two-vector in even dimension `2 * r`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.6.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
-/

public section

open Module
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Simultaneous normal form and Pfaffian divided power of a two-vector**: on a `2r`-dimensional
real inner product space `E`, every two-vector `F ∈ ⋀² E` admits an orthonormal basis
`b : OrthonormalBasis (Fin (2 * r)) ℝ E` and nonnegative weights `μ : Fin r → ℝ` putting
`TauCeti.twoVectorContraction F` in block-diagonal normal form, decomposing
`F = ∑ j, μ j • (b_{2j} ∧ b_{2j+1})`, and evaluating the divided `r`-th exterior power as
`(r!)⁻¹ • Fʳ = (∏ j, μ j) • (b₀ ∧ ⋯ ∧ b_{2r-1})`. -/
theorem exists_orthonormalBasis_twoVector_normalForm {r : ℕ}
    (hdim : finrank ℝ E = 2 * r) (F : ⋀[ℝ]^2 E) :
    ∃ (b : OrthonormalBasis (Fin (2 * r)) ℝ E) (μ : Fin r → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j : Fin r, twoVectorContraction F (b ⟨2 * (j : ℕ), by omega⟩) =
        μ j • b ⟨2 * (j : ℕ) + 1, by omega⟩) ∧
      (∀ j : Fin r, twoVectorContraction F (b ⟨2 * (j : ℕ) + 1, by omega⟩) =
        -(μ j • b ⟨2 * (j : ℕ), by omega⟩)) ∧
      F = ∑ j : Fin r, μ j • exteriorPower.ιMulti ℝ 2
        ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] ∧
      (r.factorial : ℝ)⁻¹ • exteriorPower.pow F r =
        (∏ j : Fin r, μ j) • exteriorPower.ιMulti ℝ (2 * r) b := by
  obtain ⟨b₀, μ, hμ, h0, h1⟩ := (twoVectorContraction F).exists_orthonormalBasis_skew_normalForm
    hdim (inner_twoVectorContraction_apply_left F)
  let e : Fin r × Fin 2 ≃ Fin (2 * r) := finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2))
  let b : OrthonormalBasis (Fin (2 * r)) ℝ E := b₀.reindex e
  have he0 (j : Fin r) : e (j, 0) = ⟨2 * (j : ℕ), by omega⟩ := by
    ext
    simp [e, mul_comm]
  have he1 (j : Fin r) : e (j, 1) = ⟨2 * (j : ℕ) + 1, by omega⟩ := by
    ext
    simp [e, mul_comm, add_comm]
  have hb0 (j : Fin r) : b ⟨2 * (j : ℕ), by omega⟩ = b₀ (j, 0) := by
    rw [← he0 j]
    simp only [b, OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  have hb1 (j : Fin r) : b ⟨2 * (j : ℕ) + 1, by omega⟩ = b₀ (j, 1) := by
    rw [← he1 j]
    simp only [b, OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  have hF : F = ∑ j : Fin r, μ j • exteriorPower.ιMulti ℝ 2
      ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
    simpa only [hb0, hb1] using twoVector_eq_sum_of_skew_normalForm F b₀ μ h0 h1
  refine ⟨b, μ, hμ, fun j ↦ by simpa only [hb0, hb1] using h0 j,
    fun j ↦ by simpa only [hb0, hb1] using h1 j, hF, ?_⟩
  rw [hF]
  exact exteriorPower.inv_factorial_smul_pow_sum_smul_ιMulti_two μ b

end TauCeti
