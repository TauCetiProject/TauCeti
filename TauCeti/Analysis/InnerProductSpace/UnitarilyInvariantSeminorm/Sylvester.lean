/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The Frobenius bound for the Sylvester equation

Let `A` and `B` be symmetric operators on finite-dimensional inner product spaces `E` and `F`, with
orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`. The Sylvester operator
`X ↦ A X - X B` multiplies the matrix coefficient `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫` by `αᵢ - βⱼ`, so the Frobenius
seminorm of `A X - X B` is

`‖A X - X B‖_F² = ∑ᵢ ∑ⱼ (αᵢ - βⱼ)² ‖Xᵢⱼ‖²`.

If the spectra of `A` and `B` are at distance at least `δ`, every factor `(αᵢ - βⱼ)²` is at least
`δ²`, and therefore `δ ‖X‖_F ≤ ‖A X - X B‖_F`. Equivalently, every solution of the Sylvester
equation `A X - X B = C` satisfies `δ ‖X‖_F ≤ ‖C‖_F`. For the Frobenius seminorm the constant is
`1`; the corresponding bound for a general unitarily invariant seminorm under the same pairwise
separation hypothesis carries the constant `π / 2`.

## Main statements

* `ContinuousLinearMap.sq_frobenius_sylvester_apply`: the exact formula for `‖A X - X B‖_F²` in
  orthonormal eigenbases of `A` and `B`.
* `ContinuousLinearMap.mul_frobenius_le_frobenius_sylvester_apply`: if the point spectra of `A`
  and `B` are at distance at least `δ`, then `δ ‖X‖_F ≤ ‖A X - X B‖_F`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open Module TauCeti.UnitarilyInvariantSeminorm
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} {n m : ℕ} {δ : ℝ}

/-- **The Frobenius seminorm of `A X - X B` in eigenbases.** For symmetric `A` and `B` with
ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`,
`‖A X - X B‖_F² = ∑ᵢ ∑ⱼ (αᵢ - βⱼ)² ‖⟪uᵢ, X vⱼ⟫‖²`. -/
theorem sq_frobenius_sylvester_apply (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (X : F →L[𝕜] E) :
    frobenius 𝕜 F E (A.sylvester B X) ^ 2 =
      ∑ i, ∑ j, (hA.eigenvalues hn i - hB.eigenvalues hm j) ^ 2 *
        ‖⟪hA.eigenvectorBasis hn i, X (hB.eigenvectorBasis hm j)⟫_𝕜‖ ^ 2 := by
  rw [sq_frobenius_apply_eq_sum_norm_inner_sq (hB.eigenvectorBasis hm) (hA.eigenvectorBasis hn),
    Finset.sum_comm]
  simp_rw [coe_coe, inner_sylvester_apply_eigenvectorBasis hA hB hn hm, norm_mul,
    RCLike.norm_ofReal, mul_pow, sq_abs]

/-- **The Frobenius Sylvester bound.** In finite dimension, if `A` and `B` are symmetric and every
eigenvalue of `A` is at distance at least `δ` from every eigenvalue of `B`, then
`δ ‖X‖_F ≤ ‖A X - X B‖_F` for every `X`. In particular every solution of the Sylvester equation
`A X - X B = C` satisfies `δ ‖X‖_F ≤ ‖C‖_F`. -/
theorem mul_frobenius_le_frobenius_sylvester_apply (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (X : F →L[𝕜] E) :
    δ * frobenius 𝕜 F E X ≤ frobenius 𝕜 F E (A.sylvester B X) := by
  rcases lt_or_ge δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ.le (apply_nonneg _ _)).trans (apply_nonneg _ _)
  rw [← pow_le_pow_iff_left₀ (by positivity) (apply_nonneg _ _) two_ne_zero, mul_pow,
    sq_frobenius_sylvester_apply hA hB rfl rfl,
    sq_frobenius_apply_eq_sum_norm_inner_sq (hB.eigenvectorBasis rfl) (hA.eigenvectorBasis rfl),
    Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right ?_ (by positivity)
  -- Each eigenvalue difference is at least `δ` in absolute value.
  have hij := h.le_abs_sub
    (by simpa using hA.hasEigenvalue_eigenvalues rfl i)
    (by simpa using hB.hasEigenvalue_eigenvalues rfl j)
  simpa using pow_le_pow_left₀ hδ hij 2

end ContinuousLinearMap
