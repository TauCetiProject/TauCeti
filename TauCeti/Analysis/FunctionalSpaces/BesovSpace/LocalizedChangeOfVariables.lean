/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
import TauCeti.Analysis.Distribution.ChangeOfVariables.Localized

/-!
# Localized changes of variables in Besov spaces

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, such as a transition map between two charts of a manifold, and let `θ` be
a smooth function with compact support in the source of `e`. This file shows that the operator
`u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz functions in the
`B^s_{p,q}` norm, for every real `s` and all `1 ≤ p, q ≤ ∞`
(`TauCeti.BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp`). This includes the
Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}` and negative orders. These are the estimates comparing the
readings of a function on a manifold in two overlapping charts, through which Besov estimates
proved in charts are patched together on a manifold.

## The argument

The pullback along a bijection `Φ` of `E` with bounded derivatives is bounded on `B^s_{p,q}`
(`TauCeti.BesovSpace.compCLM`), and so is multiplication by a Schwartz function
(`TauCeti.BesovSpace.smulLeftCLM`). A partition of unity writes `θ · (u ∘ e)` as a finite sum
`∑ᵢ χᵢ · (u ∘ Φᵢ)` of such pullbacks multiplied by Schwartz functions
(`TauCeti.exists_sum_smul_comp_eq_smul_comp`), so `u ↦ θ · (u ∘ e)` is bounded in every norm in
which these pullbacks and multiplications are bounded (`TauCeti.exists_norm_le_of_eq_smul_comp`),
as for `H^s` (`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.10.2 (diffeomorphisms and
  localization in Besov spaces).
-/

public section

noncomputable section

namespace TauCeti.BesovSpace

open scoped ENNReal SchwartzMap ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Localized changes of variables are bounded on `B^s_{p,q}`.** Let `e` be a smooth open partial
homeomorphism of `E` with smooth inverse and `θ` a smooth function with compact support in the
source of `e`. Then `u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz
functions in the `B^s_{p,q}` norm, for every real `s` and all `1 ≤ p, q ≤ ∞`: there is a constant
`C` with `‖v‖_{B^s_{p,q}} ≤ C ‖u‖_{B^s_{p,q}}` whenever `v = θ · (u ∘ e)`. -/
theorem exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source)
    (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ C, ∀ u v : 𝓢(E, F), (∀ x, v x = θ x • u (e x)) →
      ‖SchwartzMap.toBesovSpaceCLM F φ s p q v‖ ≤
        C * ‖SchwartzMap.toBesovSpaceCLM F φ s p q u‖ := by
  refine TauCeti.exists_norm_le_of_eq_smul_comp (SchwartzMap.toBesovSpaceCLM F φ s p q)
    (fun Φ hΦ hΨ hΦb hΨb ↦ ?_) (fun χ ↦ ?_) he he' hθ hθc hθe
  · let T := compCLM F φ s p q Φ hΦ hΨ (fun k hk _ ↦ hΦb k hk) (fun k hk _ ↦ hΨb k hk)
    exact ⟨‖T‖, fun u ↦ by simpa [T] using T.le_opNorm (SchwartzMap.toBesovSpaceCLM F φ s p q u)⟩
  · let T := smulLeftCLM F φ s p q (χ : E → ℂ) χ.hasTemperateGrowth
      fun k _ ↦ ⟨_, χ.norm_iteratedFDeriv_le_seminorm ℝ k⟩
    exact ⟨‖T‖, fun u ↦ by simpa [T] using T.le_opNorm (SchwartzMap.toBesovSpaceCLM F φ s p q u)⟩

end TauCeti.BesovSpace
