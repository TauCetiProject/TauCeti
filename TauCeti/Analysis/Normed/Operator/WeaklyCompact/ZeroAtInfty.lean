/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.WeaklyCompact
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# Weakly compact operators into `c₀`

A weakly null sequence `f` of continuous linear functionals on a real or complex normed space `E`
defines a bounded operator `E →L[𝕜] C₀(ℕ, 𝕜)`, sending `y` to the sequence of values `f n y`.
This operator is weakly compact (`TauCeti.exists_isWeaklyCompact_apply_eq`): by Gantmacher's
criterion it suffices that its bidual adjoint sends each `Φ ∈ E**` to the canonical image of the
sequence `n ↦ Φ (f n)`, which is checked against the coordinate series of functionals on `c₀`,
using the duality `c₀* = ℓ¹`.

## Main results

* `TauCeti.exists_isWeaklyCompact_apply_eq`: a weakly null sequence of functionals defines a
  weakly compact operator into `c₀`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.4.
-/

public section

open Filter Function NormedSpace Set Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open ZeroAtInftyContinuousMap in
/-- A weakly null sequence of functionals defines a weakly compact operator into `c₀`, sending
`y` to the sequence of values `f n y`. -/
theorem exists_isWeaklyCompact_apply_eq {f : ℕ → StrongDual 𝕜 E}
    (hf : Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop (𝓝 0)) :
    ∃ T : E →L[𝕜] C₀(ℕ, 𝕜), T.IsWeaklyCompact ∧ ∀ y n, T y n = f n y := by
  have hf' : Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop
      (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 E) 0)) := by
    simpa using hf
  have hev (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) : Tendsto (fun n ↦ Φ (f n)) cofinite (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hf' Φ
  obtain ⟨C, hC₀, hC⟩ := hf'.isBounded_range_of_toWeakSpace.exists_pos_norm_le
  replace hC (n : ℕ) : ‖f n‖ ≤ C := hC _ (mem_range_self n)
  have hy (y : E) : Tendsto (fun n ↦ f n y) cofinite (𝓝 0) := by
    simpa using hev (inclusionInDoubleDual 𝕜 E y)
  let L : E →ₗ[𝕜] C₀(ℕ, 𝕜) :=
    { toFun y := mkOfDiscrete (fun n ↦ f n y) (hy y)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  have hL (y : E) (n : ℕ) : L y n = f n y := by simp [L]
  let T : E →L[𝕜] C₀(ℕ, 𝕜) := L.mkContinuous C fun y ↦ (norm_le (by positivity)).2 fun n ↦ by
    rw [hL]
    exact ((f n).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg y))
  have hT (y : E) (n : ℕ) : T y n = f n y := by simp [T, hL]
  refine ⟨T, ?_, hT⟩
  -- Gantmacher's criterion: `T** Φ` is the canonical image of the sequence `n ↦ Φ (f n)`.
  rw [ContinuousLinearMap.isWeaklyCompact_iff_range_subset]
  rintro _ ⟨Φ, rfl⟩
  refine ⟨mkOfDiscrete (fun n ↦ Φ (f n)) (hev Φ), ContinuousLinearMap.ext fun Λ ↦ ?_⟩
  -- The functional `Λ ∘ T` is the norm-convergent series `∑ Λ (single n 1) • f n`.
  have hs : Summable fun n ↦ Λ (single n 1) • f n :=
    Summable.of_norm_bounded ((summable_norm_apply_single_one Λ).mul_right C) fun n ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
  have hsum : HasSum (fun n ↦ Λ (single n 1) • f n) (Λ.comp T) := by
    convert hs.hasSum
    refine ContinuousLinearMap.ext fun y ↦ (hasSum_apply_single_one_mul Λ (T y)).unique ?_
    simpa [hT] using hs.hasSum.mapL (ContinuousLinearMap.apply 𝕜 𝕜 y)
  have h₁ := hsum.mapL Φ
  have h₂ := hasSum_apply_single_one_mul Λ (mkOfDiscrete (fun n ↦ Φ (f n)) (hev Φ))
  simp only [map_smul, smul_eq_mul, coe_mkOfDiscrete] at h₁ h₂
  simpa using (h₁.unique h₂).symm

end TauCeti
