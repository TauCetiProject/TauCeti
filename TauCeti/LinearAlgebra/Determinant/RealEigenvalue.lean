/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# The sign of `det (1 - f)` from the real eigenvalues of `f`

Let `f` be an endomorphism of a finite-dimensional real vector space `V` of dimension `n`. The
determinant `det (1 - f)` is the value at `1` of the characteristic polynomial
`χ_f(t) = det (t - f)`, a monic polynomial whose real roots are the real eigenvalues of `f`. So
its sign is controlled by where the real eigenvalues of `f` lie:

* if `f` has no real eigenvalue `μ ≥ 1`, for instance if `f` strictly contracts some norm, then
  `det (1 - f) > 0` (`LinearMap.det_one_sub_pos_of_not_hasEigenvalue`), since `χ_f` is monic and
  has no root at or beyond `1`;
* if `f` has no real eigenvalue in `[0, 1]`, for instance if `f` strictly expands some norm, then
  `sign det (1 - f) = (-1)ⁿ sign det f` (`LinearMap.sign_det_one_sub_of_not_hasEigenvalue`): `f` is
  invertible, `1 - f = (-f) (1 - f⁻¹)`, and `f⁻¹` has no real eigenvalue `μ ≥ 1`.

For a map `f × g` of a product `V × W` that expands along `V` and contracts along `W` in this
sense, `det (1 - f × g) = det (1 - f) det (1 - g)`, so

`sign det (1 - f × g) = (-1)^(dim V) sign det f`

(`LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`). This is the sign
`sign det (1 - A)` of the fixed-point index of a linear map `A` at its nondegenerate fixed point
`0` (`ContinuousMap.localFixedPointIndex_eq_sign_det`), computed for a map that expands an
invariant subspace and contracts a complementary one: it is `(-1)^(dim V) ε`, where `ε = ±1`
records whether the expansion preserves the orientation of `V`.

The norm conditions are `Module.End.not_hasEigenvalue_of_norm_apply_lt` (strict contraction) and
`Module.End.not_hasEigenvalue_of_lt_norm_apply` (strict expansion).

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index of a linear map).
-/

public section

open Module Set Polynomial

namespace Module.End

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Module.End ℝ E}

/-- A map that strictly decreases the norm of every nonzero vector has no real eigenvalue of
absolute value at least `1`. -/
theorem not_hasEigenvalue_of_norm_apply_lt (hf : ∀ v, v ≠ 0 → ‖f v‖ < ‖v‖) {μ : ℝ}
    (hμ : 1 ≤ |μ|) : ¬ f.HasEigenvalue μ := fun h ↦ by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hlt := hf v hv.2
  rw [mem_eigenspace_iff.mp hv.1, norm_smul, Real.norm_eq_abs] at hlt
  nlinarith [norm_nonneg v]

/-- A map that strictly increases the norm of every nonzero vector has no real eigenvalue of
absolute value at most `1`. -/
theorem not_hasEigenvalue_of_lt_norm_apply (hf : ∀ v, v ≠ 0 → ‖v‖ < ‖f v‖) {μ : ℝ}
    (hμ : |μ| ≤ 1) : ¬ f.HasEigenvalue μ := fun h ↦ by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hlt := hf v hv.2
  rw [mem_eigenspace_iff.mp hv.1, norm_smul, Real.norm_eq_abs] at hlt
  nlinarith [norm_nonneg v]

end Module.End

namespace LinearMap

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- If `f` has no real eigenvalue `μ ≥ 1`, then `det (1 - f) > 0`: the characteristic polynomial
`det (t - f)` is monic and has no root `t ≥ 1`. -/
theorem det_one_sub_pos_of_not_hasEigenvalue {f : Module.End ℝ V}
    (hf : ∀ μ : ℝ, 1 ≤ μ → ¬ f.HasEigenvalue μ) : 0 < (1 - f).det := by
  have h := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (P := f.charpoly) (x := 1)
    (fun y hy ↦ lt_of_not_ge fun h1 ↦
      hf y h1 ((Module.End.hasEigenvalue_iff_isRoot_charpoly f y).mpr hy))
    (f.charpoly_monic.leadingCoeff ▸ zero_le_one)
  rwa [eval_charpoly, map_one] at h

/-- If `f` has no real eigenvalue in `[0, 1]`, then `sign det (1 - f) = (-1)ⁿ sign det f`, where
`n = dim V`: `f` is invertible, `1 - f = (-f) (1 - f⁻¹)`, and `det (1 - f⁻¹) > 0` because `f⁻¹`
has no real eigenvalue `μ ≥ 1`. -/
theorem sign_det_one_sub_of_not_hasEigenvalue {f : Module.End ℝ V}
    (hf : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ f.HasEigenvalue μ) :
    SignType.sign (1 - f).det = (-1) ^ finrank ℝ V * SignType.sign f.det := by
  have hinj : Function.Injective f := by
    rw [← ker_eq_bot]
    exact ((not_hasEigenvalue_zero_tfae f).out 1 5).mp (hf 0 ⟨le_rfl, zero_le_one⟩)
  set g : Module.End ℝ V := ((LinearEquiv.ofInjectiveEndo f hinj).symm : V →ₗ[ℝ] V)
  have hfg : f * g = 1 := LinearEquiv.ofInjectiveEndo_right_inv f hinj
  -- An eigenvector of `g` for `μ ≥ 1` is an eigenvector of `f` for `μ⁻¹ ∈ (0, 1]`.
  have hg : ∀ μ : ℝ, 1 ≤ μ → ¬ g.HasEigenvalue μ := fun μ hμ h ↦ by
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hgv : g v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    have h : μ • f v = v := by
      simpa [hgv] using congr($hfg v)
    have hfv : f v = μ⁻¹ • v := by
      conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    exact hf μ⁻¹ ⟨by positivity, inv_le_one_of_one_le₀ hμ⟩
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hfv, hv.2⟩)
  have hsplit : 1 - f = -f * (1 - g) := by
    rw [neg_mul, mul_sub, mul_one, hfg]
    abel
  rw [hsplit, map_mul, ← neg_one_smul ℝ f, det_smul, sign_mul, sign_mul,
    sign_pos (det_one_sub_pos_of_not_hasEigenvalue hg), sign_pow, sign_neg neg_one_lt_zero, mul_one]

/-- **The sign of `det (1 - A)` at an expanding-contracting splitting.** If `f` has no real
eigenvalue in `[0, 1]` and `g` has no real eigenvalue `μ ≥ 1`, then
`sign det (1 - f × g) = (-1)^(dim V) sign det f`. -/
theorem sign_det_one_sub_prodMap_of_not_hasEigenvalue {f : Module.End ℝ V} {g : Module.End ℝ W}
    (hf : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ f.HasEigenvalue μ) (hg : ∀ μ : ℝ, 1 ≤ μ → ¬ g.HasEigenvalue μ) :
    SignType.sign (1 - f.prodMap g).det = (-1) ^ finrank ℝ V * SignType.sign f.det := by
  have h : (1 : Module.End ℝ (V × W)) - f.prodMap g = (1 - f).prodMap (1 - g) := by
    ext <;> simp
  rw [h, det_prodMap, sign_mul, sign_det_one_sub_of_not_hasEigenvalue hf,
    sign_pos (det_one_sub_pos_of_not_hasEigenvalue hg), mul_one]

end LinearMap
