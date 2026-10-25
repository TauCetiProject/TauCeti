/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.LocallyBounded
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences

/-!
# Compactness from local bounds on differentials

A family of differentiable maps on an open subset of a proper real normed space is
equicontinuous if its differentials are uniformly bounded on compact subsets. If its images
lie in a fixed compact set, every sequence has a locally uniformly convergent subsequence.
The target need not be finite dimensional or complete.

The mean value inequality supplies a common continuity modulus on each small ball.
`ArzelaAscoli.isCompact_closure_of_equicontinuous` then gives compactness of the continuous
restrictions in the compact-open topology. Properness of the source gives second countability,
so this compactness yields a subsequence, not merely a subnet. As in `TauCeti.montel`, the
continuous limit on the domain is extended by zero only to express convergence of ambient maps.

This is useful when estimates control the differentials but no equation for the limit is yet
available, as in compactness arguments for nonlinear differential equations.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U : Set X} {F : ι → X → Y}

/-- Local uniform bounds on the differentials of a differentiable family imply
equicontinuity on its open domain. -/
theorem equicontinuousOn_of_isLocallyBoundedOn_fderiv (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℝ (F i) U)
    (hb : IsLocallyBoundedOn (fun i ↦ fderiv ℝ (F i)) U) : EquicontinuousOn F U := by
  intro x hx
  apply EquicontinuousAt.equicontinuousWithinAt _ U
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hhalf : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hsub
  obtain ⟨M, hM⟩ := isLocallyBoundedOn_def.mp hb _ hhalf (isCompact_closedBall x (r / 2))
  refine Metric.equicontinuousAt_of_continuity_modulus (fun y ↦ M * dist x y) ?_ F ?_
  · have hc : Continuous (fun y : X ↦ M * dist x y) :=
      continuous_const.mul (continuous_const.dist continuous_id)
    simpa using hc.tendsto x
  · filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy i
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (F i x), norm_sub_rev x]
    exact (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ (hF i z (hhalf hz)).differentiableAt (hU.mem_nhds (hhalf hz)))
      (hM i) (mem_closedBall_self (half_pos hr).le) (ball_subset_closedBall hy)

/-- A sequence of differentiable maps with locally uniformly bounded differentials and images
in a compact set has a locally uniformly convergent subsequence. The continuous limit stays
in that compact set; no differentiability of the limit is asserted. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_of_isLocallyBoundedOn_fderiv
    {F : ℕ → X → Y} {K : Set Y} (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℝ (F n) U)
    (hb : IsLocallyBoundedOn (fun n ↦ fderiv ℝ (F n)) U)
    (hK : IsCompact K) (hFK : ∀ n, MapsTo (F n) U K) :
    ∃ (φ : ℕ → ℕ) (g : X → Y), StrictMono φ ∧ ContinuousOn g U ∧ MapsTo g U K ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) g atTop U := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let f : ℕ → C(U, Y) := fun n ↦ ⟨U.domRestrict (F n), (hF n).continuousOn.domRestrict⟩
  have hequi : Equicontinuous fun n ↦ ⇑(f n) :=
    (equicontinuous_restrict_iff F).mpr (equicontinuousOn_of_isLocallyBoundedOn_fderiv hU hF hb)
  have hcompact : IsCompact (closure (range f)) :=
    ArzelaAscoli.isCompact_closure_of_equicontinuous (by
      rw [← Set.comp_rangeSplitting f]
      exact hequi.comp (Set.rangeSplitting f)) (fun x ↦
        ⟨K, hK, by rintro _ ⟨n, rfl⟩; exact hFK n x.2⟩)
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcompact.tendsto_subseq (x := f)
    (fun n ↦ subset_closure (mem_range_self n))
  let g : X → Y := fun x ↦ if hx : x ∈ U then a ⟨x, hx⟩ else 0
  have hrestrict : g ∘ (Subtype.val : U → X) = a := by funext x; simp [g, x.2]
  have hconvOn : TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hrestrict]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  refine ⟨φ, g, hφ, ?_, ?_, hconvOn⟩
  · exact hconvOn.continuousOn (Frequently.of_forall fun n ↦ (hF (φ n)).continuousOn)
  · intro x hx
    exact hK.isClosed.mem_of_tendsto (hconvOn.tendsto_at hx)
      (Eventually.of_forall fun n ↦ hFK (φ n) hx)

end TauCeti
