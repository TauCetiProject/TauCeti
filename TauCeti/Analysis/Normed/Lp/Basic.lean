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
the sum of the norms of the coordinates (`lp.hasSum_norm_one`). For `0 < p ≤ q` the `ℓ^q` norm of
a sequence is at most its `ℓᵖ` norm (`lp.norm_le_norm_of_exponent_le`), the norm form of Mathlib's
inclusion `Memℓp.of_exponent_ge`. The scalar
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

/-- **The `ℓᵖ` norms decrease in the exponent.** For `0 < p ≤ q`, a sequence `f ∈ ℓᵖ` lies in
`ℓ^q` (`Memℓp.of_exponent_ge`), and its `ℓ^q` norm is at most its `ℓᵖ` norm. -/
theorem norm_le_norm_of_exponent_le {q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) {f : lp E p}
    {g : lp E q} (hfg : ∀ i, g i = f i) : ‖g‖ ≤ ‖f‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · exact norm_le_of_forall_le (norm_nonneg' f) fun i ↦ (hfg i).symm ▸ norm_apply_le_norm hp f i
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq)
  have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  have hqr : 0 < q.toReal := hpr.trans_le hpq'
  -- Split `t ^ q = t ^ (q - p) * t ^ p` and bound the first factor by `‖f‖ ^ (q - p)`.
  have hsplit (t : ℝ) (ht : 0 ≤ t) : t ^ q.toReal = t ^ (q.toReal - p.toReal) * t ^ p.toReal := by
    rw [← Real.rpow_add' ht (by simpa using hqr.ne'), sub_add_cancel]
  refine norm_le_of_forall_sum_le hqr (norm_nonneg' f) fun s ↦ ?_
  calc ∑ i ∈ s, ‖g i‖ ^ q.toReal
      ≤ ∑ i ∈ s, ‖f‖ ^ (q.toReal - p.toReal) * ‖f i‖ ^ p.toReal := by
        gcongr with i
        rw [hfg i, hsplit _ (norm_nonneg _)]
        gcongr
        exact norm_apply_le_norm hp f i
    _ = ‖f‖ ^ (q.toReal - p.toReal) * ∑ i ∈ s, ‖f i‖ ^ p.toReal := (Finset.mul_sum ..).symm
    _ ≤ ‖f‖ ^ (q.toReal - p.toReal) * ‖f‖ ^ p.toReal :=
        mul_le_mul_of_nonneg_left (sum_rpow_le_norm_rpow hpr f s)
          (Real.rpow_nonneg (norm_nonneg' f) _)
    _ = ‖f‖ ^ q.toReal := (hsplit _ (norm_nonneg' f)).symm

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
