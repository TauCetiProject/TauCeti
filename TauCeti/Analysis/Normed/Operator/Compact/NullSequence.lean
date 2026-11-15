/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
import TauCeti.Analysis.Normed.Module.RCLike.TendstoZero

/-!
# Null families as images of null families in `ℓ¹` under compact operators

A family `x` tending to zero along the cofinite filter in a Banach space over `𝕜 = ℝ` or `ℂ` is
the image of a family in `ℓ¹` tending to zero under a compact operator `ℓ¹ →L[𝕜] E`. Writing
`x i = r i • s i • v i` with three null factors, the operator is `a ↦ ∑ aᵢ sᵢ vᵢ`, the
composite of the compact diagonal operator with multiplier `s` and the synthesis operator of
the bounded family `v`, and it sends the null family `r i • eᵢ` to `x`. This is the
compact-disk construction in Grothendieck's characterization of the approximation property.

## Main statements

* `TauCeti.exists_isCompactOperator_apply_eq`: a family tending to zero in a Banach space is the
  image of a family tending to zero in `ℓ¹` under a compact operator.
-/

public section

open Filter
open scoped ENNReal Topology lp

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A family `x` in a Banach space tending to zero along the cofinite filter is the image, under a
compact operator `T : ℓ¹ →L[𝕜] E`, of a family in `ℓ¹` tending to zero along the cofinite
filter. -/
theorem exists_isCompactOperator_apply_eq [CompleteSpace E] {ι : Type*} {x : ι → E}
    (hx : Tendsto x cofinite (𝓝 0)) :
    ∃ T : ℓ^1(ι, 𝕜) →L[𝕜] E, IsCompactOperator T ∧
      ∃ y : ι → ℓ^1(ι, 𝕜), Tendsto y cofinite (𝓝 0) ∧ ∀ i, T (y i) = x i := by
  classical
  -- Write `x i = r i • s i • v i` with null factors; `T` multiplies by `s` and then synthesizes
  -- with `v`, and the family in `ℓ¹` is `r i • eᵢ`.
  obtain ⟨r, hr, w, hw, hrw⟩ := exists_smul_eq_of_tendsto_zero (𝕜 := 𝕜) hx
  obtain ⟨s, hs, v, hv, hsv⟩ := exists_smul_eq_of_tendsto_zero (𝕜 := 𝕜) hw
  let d : ℓ^∞(ι, 𝕜) := ⟨s, memℓp_infty hs.norm.bddAbove_range_of_cofinite⟩
  let v' : ℓ^∞(ι, E) := ⟨v, memℓp_infty hv.norm.bddAbove_range_of_cofinite⟩
  -- The synthesis operator `a ↦ ∑ aᵢ • vᵢ`, from the `ℓ¹`-`ℓ∞` pairing.
  let V : ℓ^1(ι, 𝕜) →L[𝕜] E :=
    (lp.dualPairing 1 ∞ (fun _ ↦ ContinuousLinearMap.lsmul 𝕜 𝕜) (K := 1)
      fun _ ↦ ContinuousLinearMap.opNorm_lsmul_le.trans_eq NNReal.coe_one.symm).flip v'
  refine ⟨V ∘L lp.diagonalCLM d, (lp.isCompactOperator_diagonalCLM d ?_).clm_comp V,
    fun i ↦ lp.single 1 i (r i), ?_, fun i ↦ ?_⟩
  · simpa [d] using hs.norm
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [lp.norm_single] using hr.norm
  · rw [← hrw, ← hsv, smul_smul]
    simp only [V, ContinuousLinearMap.comp_apply, lp.diagonalCLM_single,
      ContinuousLinearMap.flip_apply]
    rw [lp.dualPairing_apply, tsum_eq_single i fun j hj ↦ by simp [hj]]
    simp [d, v', mul_comm]

end TauCeti
