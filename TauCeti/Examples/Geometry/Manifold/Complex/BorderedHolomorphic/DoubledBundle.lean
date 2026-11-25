/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle

/-!
# The doubled bundle over the double of the closed upper half-plane

On the closed upper half-plane the vertical projection `z ↦ re z` is a collar projection onto the
real axis, and read on the Schottky double through the fold it is `w ↦ re w` in the doubled chart,
so it is smooth across the seam. Every complex core whose transitions are smooth and constant along
vertical lines therefore has a smooth double; the trivial core is the basic instance. The lifted
involution of the doubled bundle is smooth with no hypothesis on the transitions.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.Examples.DoubledBundle

open SchottkyDouble

local notation "B" => ClosedUpperHalfPlane
local notation "A" => (borderedInterior B : Set B)ᶜ

/-- The vertical projection of the closed upper half-plane onto the real axis. -/
def verticalProjection (z : B) : B :=
  ClosedUpperHalfPlane.ofReal (z : ℂ).re

/-- The vertical projection lands on the boundary of the closed upper half-plane. -/
theorem verticalProjection_mem_boundary (z : B) : verticalProjection z ∈ A := by
  rw [mem_compl_iff, SetLike.mem_coe, mem_borderedInterior_iff_im_chartAt_pos, chartAt_self_eq]
  simp [verticalProjection, ClosedUpperHalfPlane.coe_ofReal]

/-- Read on the Schottky double through the fold, the vertical projection is smooth across the
seam: in the doubled chart it is `w ↦ re w`. -/
theorem contMDiff_verticalProjection_comp_fold {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel n
      (verticalProjection ∘ DoubleAlong.fold A) := by
  intro y
  refine contMDiffAt_iff.2 ⟨?_, ?_⟩
  · refine (Continuous.comp ?_ (DoubleAlong.fold A).continuous).continuousAt
    refine continuous_induced_rng.2 ?_
    simpa only [Function.comp_def, verticalProjection, ClosedUpperHalfPlane.coe_ofReal] using
      Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_subtypeVal)
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  refine (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).contDiffAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq, chartAt_eq,
    Function.comp_apply, verticalProjection]
  simp [ClosedUpperHalfPlane.coe_ofReal, ClosedUpperHalfPlane.re_fold]

/-- The double of the trivial core over the closed upper half-plane has smooth transitions, through
the vertical collar projection. -/
example (r : ℕ) (i j : SchottkyDouble B) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore (FiniteRankBundleCore.trivial ℂ B r)
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore (FiniteRankBundleCore.trivial ℂ B r)
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ)) ∞
      ((doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.coordChange i j)
      ((doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.baseSet i ∩
        (doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.baseSet j) :=
  contMDiffOn_coordChange_doubledBundleCore _ _
    (fun _ _ ↦ contMDiffOn_const.congr fun _ _ ↦ rfl) isOpen_univ (subset_univ _)
    (fun z _ ↦ verticalProjection_mem_boundary z)
    contMDiff_verticalProjection_comp_fold.contMDiffOn
    (fun _ _ _ _ _ _ ↦ ⟨mem_univ _, mem_univ _, rfl⟩) i j

/-- The lifted involution of the doubled trivial bundle over the double of the closed upper
half-plane is smooth. -/
example (r : ℕ) :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin ((FiniteRankBundleCore.trivial ℂ B r).doubleAlong
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ))
      (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin ((FiniteRankBundleCore.trivial ℂ B r).doubleAlong
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ)) ∞
      ((FiniteRankBundleCore.trivial ℂ B r).doubleAlongSwap
        (FiniteRankBundleCore.isRealAlong_trivial r A)) :=
  contMDiff_doubleAlongSwap _ _

end TauCeti.Examples.DoubledBundle
