/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.Basic

/-!
# Population-gap bounds for right singular vectors

For rectangular maps `A` and `Â`, bounds with constants `a`, `â`, and `ε`
on `A`, `Â`, and `Â - A` control the cross-block overlap of their right singular bases:
`Γ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, v̂ⱼ⟫|² ≤ 4 |s| ((a + â) ε)²`.
The theorem is stated in multiplied form, which also covers `Γ = 0`.

The separation is imposed only on the squared singular values of the population
operator. No gap is required for the perturbed operator, and the index block need
not be contiguous.

The pointwise bound for `A† A` is available in
`TauCeti.Analysis.InnerProductSpace.Gram.Perturbation`.

## Provenance

Adapted from the maintained
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0):

* `ForTauCeti/Analysis/InnerProductSpace/Singular/Subspace.lean`
  (original Gram perturbation reduction, Jon Crall and Claude Opus 4.8).
* `YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`
  (singular-vector population bound, Jon Crall and GPT 5.6 High).

## References

* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
-/

public section

namespace LinearMap

open Module (finrank)
open scoped InnerProductSpace BigOperators

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Yu–Wang–Samworth bound for right singular vectors.** A population gap in squared
singular values gives
`Γ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, v̂ⱼ⟫|² ≤ 4 |s| ((a + â) ε)²`,
where `vₖ` and `v̂ⱼ` belong to the right singular bases of `A` and `Â`.
Only the population squared singular values need a gap. -/
theorem sq_mul_sum_sum_norm_inner_rightSingularBasis_sq_le_four_mul_card_mul_sq
    (A Â : E →ₗ[𝕜] F) {Γ a â ε : ℝ} (hΓ : 0 ≤ Γ)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    (s : Finset (Fin (finrank 𝕜 E)))
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.singularValues j ^ 2 - A.singularValues k ^ 2|) :
    Γ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪A.rightSingularBasis k, Â.rightSingularBasis j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ((a + â) * ε) ^ 2 := by
  have hgap' : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.isSymmetric_adjoint_comp_self.eigenvalues rfl j -
        A.isSymmetric_adjoint_comp_self.eigenvalues rfl k| := by
    intro j hj k hk
    rw [← A.sq_singularValues_fin rfl j, ← A.sq_singularValues_fin rfl k]
    exact hgap j hj k hk
  rw [A.rightSingularBasis_def, Â.rightSingularBasis_def]
  refine A.isSymmetric_adjoint_comp_self.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq
    Â.isSymmetric_adjoint_comp_self rfl hΓ hgap' ?_
  intro x
  simpa only [add_comm â a] using
    (LinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_apply_le
      Â A hÂ hA hE x)

end LinearMap
