/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Analysis.Distribution.ChangeOfVariables.Localized
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier

/-!
# Localized changes of variables in Bessel-potential spaces

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, such as a transition map between two charts of a manifold, and let `θ` be
a smooth function with compact support in the source of `e`. This file shows that the operator
`u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz functions in the
`H^{s,p}` norm, for every real `s` and `1 < p < ∞`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`). These are the
estimates comparing the readings of a function on a manifold in two overlapping charts, through
which Sobolev estimates proved in charts are patched together on a manifold.

## The argument

The pullback along a bijection `Φ` of `E` with bounded derivatives is an isomorphism of
`H^{s,p}` (`BesselPotentialSpace.compCLE`), and multiplication by a Schwartz function maps
`H^{s,p}` into itself (`TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap`), hence is bounded
on it (`BesselPotentialSpace.mapCLM`). A partition of unity writes `θ · (u ∘ e)` as a finite sum
`∑ᵢ φᵢ · (u ∘ Φᵢ)` of such pullbacks multiplied by Schwartz functions
(`TauCeti.exists_sum_smul_comp_eq_smul_comp`), so `u ↦ θ · (u ∘ e)` is bounded in every norm in
which these pullbacks and multiplications are bounded (`TauCeti.exists_norm_le_of_eq_smul_comp`).

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and its localization). Taylor treats `p = 2`; for
  general `1 < p < ∞` the same localization argument runs through `BesselPotentialSpace.compCLE`
  and `TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap`.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1.
-/

public section

noncomputable section

namespace BesselPotentialSpace

open MeasureTheory TemperedDistribution Filter Set
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **Localized changes of variables are bounded on `H^{s,p}`.** Let `e` be a smooth open partial
homeomorphism of `E` with smooth inverse and `θ` a smooth function with compact support in the
source of `e`. Then `u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz
functions in the `H^{s,p}` norm, for every real `s` and `1 < p < ∞`: there is a constant `C` with
`‖v‖_{H^{s,p}} ≤ C ‖u‖_{H^{s,p}}` whenever `v = θ · (u ∘ e)`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (s : ℝ) :
    ∃ C, ∀ u v : 𝓢(E, F), (∀ x, v x = θ x • u (e x)) →
      ‖SchwartzMap.toBesselPotentialSpaceCLM s p v‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s p u‖ := by
  refine TauCeti.exists_norm_le_of_eq_smul_comp (SchwartzMap.toBesselPotentialSpaceCLM s p)
    (fun Φ hΦ hΨ hΦb hΨb ↦ ?_) (fun φ ↦ ?_) he he' hθ hθc hθe
  · let T : H^{s, p}(E, F) →L[ℂ] H^{s, p}(E, F) := compCLE F hp hp_top s Φ
      hΦ hΨ (fun k hk _ ↦ hΦb k hk) (fun k hk _ ↦ hΨb k hk)
    exact ⟨‖T‖, fun u ↦ by
      simpa [T] using T.le_opNorm (SchwartzMap.toBesselPotentialSpaceCLM s p u)⟩
  · let T : H^{s, p}(E, F) →L[ℂ] H^{s, p}(E, F) :=
      mapCLM (TemperedDistribution.smulLeftCLM F (φ : E → ℂ))
        (fun u ↦ u.memSobolev_toDistr.smulLeftCLM_schwartzMap hp hp_top φ)
    refine ⟨‖T‖, fun u ↦ ?_⟩
    have h : T (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
        SchwartzMap.toBesselPotentialSpaceCLM s p (SchwartzMap.smulLeftCLM F (φ : E → ℂ) u) :=
      ext (by simp [T, smulLeftCLM_toTemperedDistributionCLM_eq])
    rw [← h]
    exact T.le_opNorm _

end BesselPotentialSpace
