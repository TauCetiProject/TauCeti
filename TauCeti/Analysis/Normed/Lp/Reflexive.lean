/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Reflexive

/-!
# `ℓ¹` is not reflexive

For `1 ≤ p < ∞`, the coordinate basis of `ℓᵖ` is boundedly complete: bounded partial sums
`∑ i < n, a i • eᵢ` bound the partial sums of `‖a i‖ ^ p`, so `a` lies in `ℓᵖ`.

Over real or complex scalars, on an infinite index type, `ℓ¹` is not reflexive
(`lp.not_surjective_inclusionInDoubleDual_one`). Indeed `ℓ¹` is isometric to the dual of `c₀`,
a Banach space is reflexive exactly when its dual is, and `c₀` is not reflexive. By James's
basis criterion the coordinate basis of `ℓ¹` is therefore not shrinking. Together with the
coordinate basis of `c₀`, which is shrinking but not boundedly complete, this shows that the two
conditions of James's criterion are independent.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapters 1 and 3.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §4.4.
-/

public section

noncomputable section

open Filter Function NormedSpace Set Topology
open scoped ENNReal ZeroAtInfty

namespace lp

section Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `1 ≤ p < ∞`, the coordinate basis of `ℓᵖ` is boundedly complete. -/
theorem isBoundedlyComplete_toSchauderBasis_unconditionalBasis (hp : p ≠ ⊤) :
    (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜) hp).toSchauderBasis.IsBoundedlyComplete := by
  have hp₀ : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [SchauderBasis.isBoundedlyComplete_iff]
  rintro a ⟨C, hC⟩
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, ‖a i‖ ^ p.toReal ≤ C ^ p.toReal := by
    have h := hC (mem_range_self n)
    simp only [UnconditionalSchauderBasis.coe_toSchauderBasis, unconditionalBasis_apply,
      ← lp.single_smul, smul_eq_mul, mul_one] at h
    rw [← lp.norm_sum_single hp₀]
    exact Real.rpow_le_rpow (norm_nonneg _) h hp₀.le
  have ha : Memℓp a p :=
    (memℓp_gen_iff hp₀).2 (summable_of_sum_range_le (fun _ ↦ by positivity) hsum)
  exact ⟨⟨a, ha⟩, fun i ↦ by simp⟩

end Basis

variable {𝕜 ι : Type*} [RCLike 𝕜]

/-- On an infinite index type, `ℓ¹` is not reflexive. -/
theorem not_surjective_inclusionInDoubleDual_one [Infinite ι] :
    ¬ Surjective (inclusionInDoubleDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) := by
  -- `ℓ¹` is the dual of `c₀` on the discrete topology.
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  -- The target is named so that its module structure is the one of the continuous dual.
  rw [ContinuousLinearEquiv.surjective_inclusionInDoubleDual_iff (F := StrongDual 𝕜 C₀(ι, 𝕜))
    (ZeroAtInftyContinuousMap.dualEquiv 𝕜 ι).toContinuousLinearEquiv,
    TauCeti.surjective_inclusionInDoubleDual_strongDual_iff]
  exact ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual

/-- The coordinate basis of `ℓ¹` is not shrinking. -/
theorem not_isShrinking_toSchauderBasis_unconditionalBasis_one :
    ¬ (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜) ENNReal.one_ne_top).toSchauderBasis.IsShrinking :=
  fun h ↦
  -- A shrinking and boundedly complete basis would make `ℓ¹` reflexive.
  not_surjective_inclusionInDoubleDual_one <|
    (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜) ENNReal.one_ne_top).toSchauderBasis
      |>.surjective_inclusionInDoubleDual_of_isShrinking_of_isBoundedlyComplete h
        (isBoundedlyComplete_toSchauderBasis_unconditionalBasis _)

end lp
