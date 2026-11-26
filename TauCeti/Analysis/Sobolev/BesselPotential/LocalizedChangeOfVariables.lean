/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.Distribution.ChangeOfVariables.Localized
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Localized changes of variables in Bessel-potential spaces

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, such as a transition map between two charts of a manifold, and let `θ` be
a smooth function with compact support in the source of `e`. This file shows that the operator
`u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz functions in the `H^s`
norm, for every real `s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`). These are the
estimates comparing the readings of a function on a manifold in two overlapping charts, through
which Sobolev estimates proved in charts are patched together on a manifold.

## The argument

The pullback along a bijection `Φ` of `E` with bounded derivatives is an isomorphism of `H^s`
(`BesselPotentialSpace.compCLE`), and multiplication by a Schwartz function is bounded on `H^s`
(`BesselPotentialSpace.smulLeftCLM`). A partition of unity writes `θ · (u ∘ e)` as a finite sum
`∑ᵢ φᵢ · (u ∘ Φᵢ)` of such pullbacks multiplied by Schwartz functions
(`TauCeti.exists_sum_smul_comp_eq_smul_comp`), which is the image of `u` under a bounded operator
on `H^s`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and its localization).
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

/-- **Localized changes of variables are bounded on `H^s`.** Let `e` be a smooth open partial
homeomorphism of `E` with smooth inverse and `θ` a smooth function with compact support in the
source of `e`. Then `u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz
functions in the `H^s` norm, for every real `s`: there is a constant `C` with
`‖v‖_{H^s} ≤ C ‖u‖_{H^s}` whenever `v = θ · (u ∘ e)`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source) (s : ℝ) :
    ∃ C, ∀ u v : 𝓢(E, F), (∀ x, v x = θ x • u (e x)) →
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 v‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨t, Φ, φ, hΦ, hsum⟩ :=
    TauCeti.exists_sum_smul_comp_eq_smul_comp (F := F) he he' hθ hθc hθe
  choose hΦs hΨs hΦb hΨb using hΦ
  have hΦt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΦs x) (hΦb x)
  have hΨt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΨs x) (hΨb x)
  -- `v` is the image of `u` under the bounded operator `∑ x, φ x · Φ x^*`.
  let T : H^{s}(E, F) →L[ℂ] H^{s}(E, F) := ∑ x ∈ t, smulLeftCLM s (φ x) ∘L
    (compCLE F ENNReal.one_lt_two ENNReal.ofNat_ne_top s (Φ x) (hΦt x) (hΨt x)
      (fun k hk _ ↦ hΦb x k hk) (fun k hk _ ↦ hΨb x k hk) : H^{s}(E, F) →L[ℂ] H^{s}(E, F))
  refine ⟨‖T‖, fun u v hv ↦ ?_⟩
  have hvT : v = ∑ x ∈ t, SchwartzMap.smulLeftCLM F (φ x : E → ℂ)
      (SchwartzMap.compCLM ℂ (hΦt x) ((hΨt x).exists_norm_le_of_leftInverse (Φ x).left_inv)
        u) := by
    ext y
    simp only [sum_apply, SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.hasTemperateGrowth _), SchwartzMap.compCLM_apply, Function.comp_apply, hv,
      hsum]
  have hT : T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 v := by
    simp only [T, hvT, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, compCLE_toBesselPotentialSpaceCLM, map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ext ?_
    simp [smulLeftCLM_toTemperedDistributionCLM_eq]
  rw [← hT]
  exact T.le_opNorm _

end BesselPotentialSpace
