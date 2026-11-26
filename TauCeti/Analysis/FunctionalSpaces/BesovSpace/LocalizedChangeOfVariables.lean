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
(`TauCeti.exists_sum_smul_comp_eq_smul_comp`), which is the image of `u` under a bounded operator
on `B^s_{p,q}`. This is the argument of
`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp` for `H^s`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.10.2 (diffeomorphisms and
  localization in Besov spaces).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1.
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
  obtain ⟨t, Φ, χ, hΦ, hsum⟩ :=
    TauCeti.exists_sum_smul_comp_eq_smul_comp (F := F) he he' hθ hθc hθe
  choose hΦs hΨs hΦb hΨb using hΦ
  have hΦt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΦs x) (hΦb x)
  have hΨt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΨs x) (hΨb x)
  have hχb (x : e.source) (k : ℕ) (_ : k ≤ ⌊|s|⌋₊ + 1) :
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (χ x : E → ℂ) y‖ ≤ C :=
    ⟨_, (χ x).norm_iteratedFDeriv_le_seminorm ℝ k⟩
  -- `v` is the image of `u` under the bounded operator `∑ x, χ x · Φ x^*`.
  let T : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q := ∑ x ∈ t,
    smulLeftCLM F φ s p q (χ x) (χ x).hasTemperateGrowth (hχb x) ∘L
      compCLM F φ s p q (Φ x) (hΦt x) (hΨt x) (fun k hk _ ↦ hΦb x k hk) (fun k hk _ ↦ hΨb x k hk)
  refine ⟨‖T‖, fun u v hv ↦ ?_⟩
  have hvT : v = ∑ x ∈ t, SchwartzMap.smulLeftCLM F (χ x : E → ℂ)
      (SchwartzMap.compCLM ℂ (hΦt x) ((hΨt x).exists_norm_le_of_leftInverse (Φ x).left_inv)
        u) := by
    ext y
    simp only [sum_apply, SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.hasTemperateGrowth _), SchwartzMap.compCLM_apply, Function.comp_apply, hv,
      hsum]
  have hT : T (SchwartzMap.toBesovSpaceCLM F φ s p q u) =
      SchwartzMap.toBesovSpaceCLM F φ s p q v := by
    simp [T, hvT, map_sum]
  rw [← hT]
  exact T.le_opNorm _

end TauCeti.BesovSpace
