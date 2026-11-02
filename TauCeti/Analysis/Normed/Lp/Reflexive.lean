/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Reflexive

/-!
# Reflexivity of `ℓᵖ`

Over real or complex scalars, `ℓᵖ` is reflexive for `1 < p < ∞`
(`lp.surjective_inclusionInDoubleDual`): its dual is `ℓ^q` for the conjugate exponent `q`, whose
dual is in turn `ℓᵖ`, and the two scalar series pairings agree.

On an infinite index type, `ℓ¹` is not reflexive
(`lp.not_surjective_inclusionInDoubleDual_one`). Indeed `ℓ¹` is isometric to the dual of `c₀`,
a Banach space is reflexive exactly when its dual is, and `c₀` is not reflexive. By James's
basis criterion the coordinate basis of `ℓ¹` is therefore not shrinking. Together with the
coordinate basis of `c₀`, which is shrinking but not boundedly complete, this shows that the two
conditions of James's criterion are independent. The bounded completeness of the coordinate basis
of `ℓ¹` is `lp.isBoundedlyComplete_toSchauderBasis_unconditionalBasis` in `Lp.Basis`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapters 1 and 3.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §4.4.
-/

public section

noncomputable section

open Filter Function NormedSpace Set Topology
open scoped ENNReal ZeroAtInfty

namespace lp

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

/-- For `1 < p < ∞`, `ℓᵖ` is reflexive. -/
theorem surjective_inclusionInDoubleDual {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p ≠ ∞) :
    Surjective (inclusionInDoubleDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p)) := by
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  have hq : p.conjExponent ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt _ p).2 hp₁).ne
  let D := dualEquiv 𝕜 ι p.conjExponent p hp
  let D' := dualEquiv 𝕜 ι p p.conjExponent hq
  intro Φ
  -- The preimage of `Φ` is the element of `ℓᵖ` representing `Φ ∘ D` on `ℓ^q`.
  set φ := Φ.comp D.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨D'.symm φ, ContinuousLinearMap.ext fun f ↦ ?_⟩
  obtain ⟨a, rfl⟩ := D.surjective f
  have h : Φ (D a) = D' (D'.symm φ) a := by
    simp [φ]
  rw [dual_def, h]
  simp only [D, D', dualEquiv_apply, mul_comm]

end lp
