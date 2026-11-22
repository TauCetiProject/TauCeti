/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.HaarBasis.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily

/-!
# `L²` orthogonality of the Haar basis

The Haar basis `haarBasis 𝕜 2 ENNReal.ofNat_ne_top` of `L²([0, 1]; 𝕜)` is an orthogonal family
whose `j`-th vector has squared `L²` norm `2 ^ (-⌊log₂ j⌋)`
(`TauCeti.unitInterval.inner_haarBasis_two`). Consequently finite Haar sums satisfy Parseval's
identity (`TauCeti.unitInterval.norm_sq_sum_haarBasis_two`) and unimodular Haar multipliers are
`L²` isometries (`TauCeti.unitInterval.norm_sum_unimodular_haarBasis_two`).
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped ENNReal InnerProductSpace unitInterval

namespace TauCeti.unitInterval

/-- Inner product of two Haar basis vectors in `L²([0, 1]; 𝕜)`: it vanishes off the diagonal and
equals the squared `L²` norm `2 ^ (-⌊log₂ j⌋)` on the diagonal. -/
theorem inner_haarBasis_two (𝕜 : Type*) [RCLike 𝕜] (j k : ℕ) :
    ⟪haarBasis 𝕜 2 ENNReal.ofNat_ne_top j, haarBasis 𝕜 2 ENNReal.ofNat_ne_top k⟫_𝕜 =
      if j = k then ((2 ^ Nat.log 2 j : ℕ) : 𝕜)⁻¹ else 0 := by
  rw [L2.inner_def]
  have hcongr :
      ∫ x, ⟪haarBasis 𝕜 2 ENNReal.ofNat_ne_top j x, haarBasis 𝕜 2 ENNReal.ofNat_ne_top k x⟫_𝕜 =
        ((∫ x, haarFun j x * haarFun k x : ℝ) : 𝕜) := by
    rw [← integral_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_haarBasis (𝕜 := 𝕜) (p := 2) ENNReal.ofNat_ne_top j,
      coeFn_haarBasis (𝕜 := 𝕜) (p := 2) ENNReal.ofNat_ne_top k] with x hj hk
    rw [hj, hk, RCLike.inner_apply, RCLike.conj_ofReal]
    push_cast
    ring
  rw [hcongr]
  split_ifs with hjk
  · subst hjk
    rw [integral_haarFun_mul_self, RCLike.ofReal_inv, RCLike.ofReal_natCast]
  · simp [hjk]

-- Not `@[simp]`: `haarBasis_apply` and `inner_self_eq_norm_sq_to_K` simplify the LHS.
/-- Diagonal inner product of a Haar basis vector in `L²([0, 1]; 𝕜)`. -/
theorem inner_haarBasis_two_self (𝕜 : Type*) [RCLike 𝕜] (j : ℕ) :
    ⟪haarBasis 𝕜 2 ENNReal.ofNat_ne_top j, haarBasis 𝕜 2 ENNReal.ofNat_ne_top j⟫_𝕜 =
      ((2 ^ Nat.log 2 j : ℕ) : 𝕜)⁻¹ := by
  rw [inner_haarBasis_two, ite_eq_left rfl]

-- Not `@[simp]`: `haarBasis_apply` simplifies the LHS.
/-- Distinct Haar basis vectors are orthogonal in `L²([0, 1]; 𝕜)`. -/
theorem inner_haarBasis_two_of_ne (𝕜 : Type*) [RCLike 𝕜] {j k : ℕ} (hjk : j ≠ k) :
    ⟪haarBasis 𝕜 2 ENNReal.ofNat_ne_top j, haarBasis 𝕜 2 ENNReal.ofNat_ne_top k⟫_𝕜 = 0 := by
  rw [inner_haarBasis_two, ite_eq_right hjk]

/-- **Parseval's identity for finite Haar sums in `L²([0, 1]; 𝕜)`.** -/
theorem norm_sq_sum_haarBasis_two (𝕜 : Type*) [RCLike 𝕜] (c : ℕ → 𝕜) (A : Finset ℕ) :
    ‖∑ k ∈ A, c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ ^ 2 =
      ∑ k ∈ A, ‖c k‖ ^ 2 * ∫ x, haarFun k x ^ 2 := by
  have horth : (A : Set ℕ).Pairwise fun j k =>
      ⟪c j • haarBasis 𝕜 2 ENNReal.ofNat_ne_top j,
        c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k⟫_𝕜 = 0 := by
    intro j _ k _ hjk
    rw [inner_smul_left, inner_smul_right, inner_haarBasis_two_of_ne 𝕜 hjk, mul_zero, mul_zero]
  rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero horth]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_smul, mul_pow]
  congr 1
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), inner_haarBasis_two_self, integral_haarFun_sq,
    ← RCLike.ofReal_natCast, ← RCLike.ofReal_inv, RCLike.ofReal_re]

/-- Unimodular Haar multipliers (`‖u k‖ = 1` for `k ∈ A`, in particular real signs `±1`) are
`L²` isometries. -/
theorem norm_sum_unimodular_haarBasis_two (𝕜 : Type*) [RCLike 𝕜]
    (c : ℕ → 𝕜) {u : ℕ → 𝕜} (A : Finset ℕ) (hu : ∀ k ∈ A, ‖u k‖ = 1) :
    ‖∑ k ∈ A, (u k * c k) • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ =
      ‖∑ k ∈ A, c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ := by
  refine sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.1 ?_
  rw [norm_sq_sum_haarBasis_two, norm_sq_sum_haarBasis_two]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [norm_mul, hu k hk, one_mul]

end TauCeti.unitInterval
