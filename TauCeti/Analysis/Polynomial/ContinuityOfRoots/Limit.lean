/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.Algebra.Polynomial.Root.Extension

/-!
# Roots at a puncture

Let `F y` be polynomials over a proper algebraically closed normed field, such as `ℂ`, whose
coefficients are continuous at a point `c`. If `F y` has degree exactly `d` near `c`, a root of
`F y`, continuous on a punctured ball about `c` in a real normed space of dimension greater than
one, converges at `c` to a root of `F c`
(`TauCeti.Polynomial.exists_isRoot_tendsto_of_continuousOn`): near `c` the roots of `F y` lie close
to the roots of `F c` (`Polynomial.eventually_rel_roots_norm_sub_lt`), so the root is bounded there,
and the cluster set at `c` of a bounded root over the connected punctured balls is a single root
of `F c` (`TauCeti.subsingleton_clusterSetOn_of_polynomial_root`).
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti.Polynomial

/-- **A continuous root extends across a puncture.** Let `F y` be polynomials over a proper
algebraically closed normed field, of degree `d` near `c`, a point of a real normed space of
dimension greater than one, with coefficients continuous at `c`. A root `v` of `F`, continuous
on a punctured ball about `c`, converges at `c` to a root of `F c`. -/
theorem exists_isRoot_tendsto_of_continuousOn {K E : Type*} [NormedField K] [IsAlgClosed K]
    [ProperSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E)
    {F : E → K[X]} {c : E} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun y => (F y).coeff i) c)
    (hdeg : ∀ᶠ y in 𝓝 c, (F y).degree = d) {δ : ℝ} (hδ : 0 < δ) {v : E → K}
    (hv : ContinuousOn v (ball c δ \ {c})) (hroot : ∀ z ∈ ball c δ \ {c}, (F z).IsRoot (v z)) :
    ∃ w, (F c).IsRoot w ∧ Tendsto v (𝓝[≠] c) (𝓝 w) := by
  classical
  -- near `c`, every root of `F y` lies within `1` of a root of `F c`
  obtain ⟨ε, hε, hnear⟩ :=
    eventually_nhds_iff_ball.1 ((eventually_rel_roots_norm_sub_lt hF hdeg one_pos).and hdeg)
  obtain ⟨δ', hδ', hδ'δ, hδ'ε⟩ : ∃ δ', 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ ε :=
    ⟨min δ ε, lt_min hδ hε, min_le_left _ _, min_le_right _ _⟩
  have hU : ball c δ' \ {c} ⊆ ball c δ \ {c} := sdiff_subset_sdiff_left (ball_subset_ball hδ'δ)
  have hroot' (z) (hz : z ∈ ball c δ' \ {c}) : (F z).eval (v z) = 0 := hroot z (hU hz)
  have hbdd : Bornology.IsBounded (v '' (ball c δ' \ {c})) := by
    refine ((F c).roots.toFinset.finite_toSet.isBounded.thickening (δ := 1)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hrel, hzd⟩ := hnear z (ball_subset_ball hδ'ε hz.1)
    have hvz : v z ∈ (F z).roots := (mem_roots (ne_zero_of_coe_le_degree hzd.ge)).2 (hroot' z hz)
    obtain ⟨s, hs, hsv⟩ := Multiset.exists_mem_of_rel_of_mem (Multiset.rel_flip.2 hrel) hvz
    exact mem_thickening_iff.2 ⟨s, Multiset.mem_toFinset.2 hs, by rwa [dist_eq_norm, norm_sub_rev]⟩
  -- the punctured balls about `c` are connected, so the cluster set of `v` at `c` is too
  have hconn : IsPreconnectedApproachAt (ball c δ' \ {c}) c :=
    isPreconnectedApproachAt_of_isPreconnected_inter_ball hδ' fun r hr hrδ' => by
      rw [show ball c δ' \ {c} ∩ ball c r = ball c r \ {c} from Set.ext fun z =>
        ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨ball_subset_ball hrδ' h.1, h.2⟩, h.1⟩⟩]
      exact (isPathConnected_ball_sdiff_singleton hE c hr).isConnected.isPreconnected
  have hUc : 𝓝[ball c δ' \ {c}] c = 𝓝[≠] c := by
    rw [sdiff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hδ'))]
  have : Nontrivial E := rank_pos_iff_nontrivial.1 (zero_lt_one.trans hE)
  have hc : c ∈ closure (ball c δ' \ {c}) :=
    mem_closure_iff_nhdsWithin_neBot.2 (hUc ▸ inferInstance)
  -- evaluation is jointly continuous at `c`, so the cluster values are among the roots of `F c`
  have hdeg' : ∀ᶠ y in 𝓝 c, (F y).natDegree ≤ d :=
    hdeg.mono fun y hy => natDegree_le_of_degree_le hy.le
  have hp (t : K) :
      ContinuousWithinAt (fun z : E × K ↦ (F z.1).eval z.2) ((ball c δ' \ {c}) ×ˢ univ) (c, t) :=
    (continuousAt_eval (fun i hi => (hF i hi).fst')
      ((continuousAt_fst (p := (c, t))).tendsto.eventually hdeg')
      continuousAt_snd).continuousWithinAt
  have hsub := subsingleton_clusterSetOn_of_polynomial_root hp hroot'
    (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge)
    (isConnected_clusterSetOn_of_isBounded (hv.mono hU) hbdd hc hconn).isPreconnected
  obtain ⟨w, hw⟩ := exists_tendsto_of_clusterSetOn_subsingleton hbdd.isCompact_closure
    (fun y hy => subset_closure (mem_image_of_mem v hy)) hc hsub
  refine ⟨w, eval_eq_zero_of_mem_clusterSetOn (hp w) hroot' ?_, hUc ▸ hw⟩
  rw [clusterSetOn_eq_singleton_of_tendsto hc hw]
  exact mem_singleton w

end TauCeti.Polynomial
