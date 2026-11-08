/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinates on `lp`

The characteristic equation for Mathlib's bundled coordinate evaluation lets users compute
with `lp.evalCLM` without unfolding its construction as a bounded linear map, and the ℓ¹ norm is
the sum of the norms of the coordinates (`lp.hasSum_norm_one`); for `1 ≤ p` it bounds the
`ℓ^p` norm (`lp.norm_le_tsum_norm`). The scalar
coordinate vectors are linearly independent, and vectors in their span vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent.
-/

public section

open scoped ENNReal

namespace lp

variable {ι 𝕜 : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  {p : ℝ≥0∞}

/-- The bundled coordinate evaluation returns the corresponding coordinate. -/
@[simp]
theorem evalCLM_apply [Fact (1 ≤ p)] (i : ι) (x : lp E p) : evalCLM 𝕜 E p i x = x i := (rfl)

/-- The ℓ¹ norm is the sum of the norms of the coordinates. -/
theorem hasSum_norm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖) ‖y‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) y

/-- For `1 ≤ p`, the `ℓ^p` norm of a sequence is at most its `ℓ¹` norm. -/
theorem norm_le_tsum_norm [Fact (1 ≤ p)] (f : lp E p)
    (hf : Summable fun i ↦ ‖f i‖) : ‖f‖ ≤ ∑' i, ‖f i‖ := by
  have hC : 0 ≤ ∑' i, ‖f i‖ := tsum_nonneg fun i ↦ norm_nonneg _
  have hle (i : ι) : ‖f i‖ ≤ ∑' i, ‖f i‖ := hf.le_tsum i fun j _ ↦ norm_nonneg _
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact lp.norm_le_of_forall_le hC hle
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (Fact.out : 1 ≤ p)
  refine lp.norm_le_of_forall_sum_le (by linarith) hC fun s ↦ ?_
  -- `x ^ p ≤ x * C ^ (p - 1)` for `0 ≤ x ≤ C`, and the `x` sum to at most `C`
  calc ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑ i ∈ s, ‖f i‖ * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc ‖f i‖ ^ p.toReal = ‖f i‖ * ‖f i‖ ^ (p.toReal - 1) := by
              rw [← Real.rpow_one_add' (norm_nonneg _) (by linarith), add_sub_cancel]
          _ ≤ ‖f i‖ * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
              gcongr
              exact hle i
    _ = (∑ i ∈ s, ‖f i‖) * (∑' i, ‖f i‖) ^ (p.toReal - 1) := (Finset.sum_mul ..).symm
    _ ≤ (∑' i, ‖f i‖) * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
        gcongr
        exact hf.sum_le_tsum s fun i _ ↦ norm_nonneg _
    _ = (∑' i, ‖f i‖) ^ p.toReal := by
        rw [← Real.rpow_one_add' hC (by linarith), add_sub_cancel]

section Single

variable [DecidableEq ι]

/-- The scalar coordinate vectors in `lp` are linearly independent. -/
theorem linearIndependent_single_one :
    LinearIndependent 𝕜 (fun i : ι ↦ lp.single p i (1 : 𝕜)) := by
  apply LinearIndependent.of_comp (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype
  have hcoe : (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype ∘
      (fun i : ι ↦ lp.single p i (1 : 𝕜)) = fun i ↦ Pi.single i (1 : 𝕜) := by
    funext i
    exact lp.coeFn_single p i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ι 𝕜

/-- A vector in the span of a family of coordinate vectors vanishes outside their indices. -/
theorem apply_eq_zero_of_mem_span_single {κ : Type*} (f : κ → ι) {x : ℓ^p(ι, 𝕜)}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)))
    {i : ι} (hi : i ∉ Set.range f) : x i = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)) ≤
      LinearMap.ker (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [evalₗ_apply]
    exact lp.single_apply_ne (E := fun _ : ι ↦ 𝕜) p (f j) 1
      (fun hij ↦ hi ⟨j, hij.symm⟩)
  simpa only [evalₗ_apply] using LinearMap.mem_ker.mp (hle hx)

end Single

end lp
