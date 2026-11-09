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
the sum of the norms of the coordinates (`lp.hasSum_norm_one`). A geometric sequence with ratio in
`[0, 1)` lies in every `ℓ^q` with `q ≠ 0` (`memℓp_geometric_of_lt_one`). The scalar
coordinate vectors are linearly independent, and vectors in their span vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent.
-/

public section

open scoped ENNReal

/-- A geometric sequence `(ρ ^ j)ⱼ` with `0 ≤ ρ < 1` lies in `ℓ^q` for every `q ≠ 0`. -/
theorem memℓp_geometric_of_lt_one {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) {q : ℝ≥0∞} (hq : q ≠ 0) :
    Memℓp (fun j : ℕ ↦ ρ ^ j) q := by
  rcases q.trichotomy with rfl | rfl | hq'
  · exact absurd rfl hq
  · refine memℓp_infty ⟨1, ?_⟩
    rintro _ ⟨j, rfl⟩
    dsimp only
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_one₀ hρ₀ hρ₁.le
  · refine memℓp_gen ((summable_geometric_of_lt_one (Real.rpow_nonneg hρ₀ _)
      (Real.rpow_lt_one hρ₀ hρ₁ hq')).congr fun j ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hρ₀, ← Real.rpow_mul hρ₀, mul_comm]

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
