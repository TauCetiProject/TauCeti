/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Continuous radii for covers and diagonal neighbourhoods

A map inducing the topology from a pseudometric space admits a positive continuous radius.
For each source point `x`, the preimage of the ball around `f x` with twice the chosen
radius lies in one member of a prescribed open cover of the source. The radius can also
be bounded by a positive constant assigned to that member. No local finiteness of the
given cover or compactness of the source space is required.

This combines Mathlib's convex-valued partition-of-unity selection theorem
`exists_continuous_forall_mem_convex_of_local_const` with metric balls. In tubular
neighbourhood arguments, comparing the larger of two radii puts both base points
in a single local injectivity neighbourhood.

An open family of diagonal neighbourhoods on a compact pseudometric space also admits a
positive continuous radius over a normal paracompact parameter space, without compactness
of that parameter space. This uses Mathlib's generalized tube lemma, its compact-space
diagonal/uniformity comparison, and the same convex selection theorem. The radii control
individual steps of local transports, without averaging invertible operators.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24, the variable-radius shrinking argument.
-/

public section

open Set Filter Topology

namespace Topology.IsInducing

variable {X Y ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] {f : X → Y}

/-- Choose positive continuous radii subordinate to an open cover of the source space.
At each point, one cover member contains every point whose image is within twice the
chosen radius, and its assigned positive bound exceeds that radius. -/
theorem exists_continuous_radius_subordinate (hf : IsInducing f)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ r : C(X, ℝ), (∀ x, 0 < r x) ∧ ∀ x, ∃ i, x ∈ U i ∧ r x < ε i ∧
      ∀ y, dist (f x) (f y) < 2 * r x → y ∈ U i := by
  let := hf.pseudoMetrizableSpace
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  -- At each point the admissible radii form an interval: shrinking preserves admissibility.
  let T : X → Set ℝ := fun x => {r | 0 < r ∧ ∃ i, x ∈ U i ∧ r < ε i ∧
    ∀ y, dist (f x) (f y) < 2 * r → y ∈ U i}
  have hT : ∀ x, Convex ℝ (T x) := by
    intro x
    apply Set.OrdConnected.convex
    constructor
    rintro a ⟨ha, -⟩ b ⟨-, i, hxi, hb, hball⟩ c ⟨hac, hcb⟩
    exact ⟨ha.trans_le hac, i, hxi, hcb.trans_lt hb,
      fun y hy => hball y (hy.trans_le (mul_le_mul_of_nonneg_left hcb (by norm_num)))⟩
  have hlocal : ∀ x, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    obtain ⟨i, hxi⟩ := hcov x
    obtain ⟨O, hO, hpre⟩ := hf.isOpen_iff.mp (hU i)
    have hxO : f x ∈ O := by simpa only [← hpre, mem_preimage] using hxi
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hxO)
    let c := min (d / 4) (ε i / 2)
    have hc : 0 < c := lt_min (by positivity) (half_pos (hε i))
    have hcd : c ≤ d / 4 := min_le_left _ _
    have hcε : c < ε i := (min_le_right _ _).trans_lt (half_lt_self (hε i))
    refine ⟨c, ?_⟩
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (f x) hc)] with y hy
    have hyx : dist (f y) (f x) < c := hy
    have hyU : y ∈ U i := by
      rw [← hpre]
      apply hball
      exact hyx.trans_le (by linarith)
    refine ⟨hc, i, hyU, hcε, fun z hz => ?_⟩
    rw [← hpre]
    apply hball
    have hzy : dist (f z) (f y) < 2 * c := by simpa [dist_comm] using hz
    have := dist_triangle (f z) (f y) (f x)
    have := add_lt_add hzy hyx
    simp only [Metric.mem_ball]
    linarith
  obtain ⟨r, hr⟩ := exists_continuous_forall_mem_convex_of_local_const hT hlocal
  exact ⟨r, fun x => (hr x).1, fun x => (hr x).2⟩

end Topology.IsInducing

open Metric
open scoped Uniformity

namespace IsOpen

variable {X K : Type*} [TopologicalSpace X] [PseudoMetricSpace K] [CompactSpace K]
  {W : Set (X × K × K)}

/-- Near a parameter whose whole diagonal lies in an open set, one positive radius works
uniformly for all pairs of sufficiently close points of the compact pseudometric space. -/
theorem exists_pos_forall_dist_le (hW : IsOpen W) (x : X)
    (hdiag : ∀ s : K, (x, s, s) ∈ W) :
    ∃ ε > 0, ∀ᶠ y in 𝓝 x, ∀ s t : K, dist s t ≤ ε → (y, s, t) ∈ W := by
  obtain ⟨U, V, hU, hV, hxU, hdiagV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_diagonal hW (by
      rintro ⟨y, s, t⟩ ⟨rfl, hst⟩
      have : s = t := hst
      subst t
      exact hdiag s)
  have hVuniform : V ∈ 𝓤 K := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    exact hV.mem_nhdsSet.mpr hdiagV
  obtain ⟨ε, hε, hεV⟩ := uniformity_basis_dist_le.mem_iff.mp hVuniform
  exact ⟨ε, hε, Filter.mem_of_superset (hU.mem_nhds (hxU (mem_singleton x)))
    fun y hy s t hst ↦ hUV ⟨hy, hεV hst⟩⟩

/-- An open family of diagonal neighbourhoods on a compact pseudometric space admits a continuous
positive radius, bounded by one. No compactness assumption on the parameter space is needed. -/
theorem exists_continuous_pos_forall_dist_le [NormalSpace X] [ParacompactSpace X]
    (hW : IsOpen W) (hdiag : ∀ (x : X) (s : K), (x, s, s) ∈ W) :
    ∃ δ : C(X, ℝ), (∀ x, δ x ∈ Ioo 0 1) ∧
      ∀ (x : X) (s t : K), dist s t ≤ δ x → (x, s, t) ∈ W := by
  let R (x : X) : Set ℝ := Ioo 0 1 ∩
    ⋂ s : K, ⋂ t : K, ⋂ (_ : (x, s, t) ∉ W), Iio (dist s t)
  have hconv (x : X) : Convex ℝ (R x) :=
    (convex_Ioo 0 1).inter (convex_iInter fun s ↦
      convex_iInter fun t ↦ convex_iInter fun _ ↦ convex_Iio (dist s t))
  have hlocal (x : X) : ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ R y := by
    obtain ⟨ε, hε, hnear⟩ := hW.exists_pos_forall_dist_le x (hdiag x)
    refine ⟨min ε 1 / 2, ?_⟩
    filter_upwards [hnear] with y hy
    refine ⟨⟨by positivity, by have := min_le_right ε (1 : ℝ); linarith⟩, ?_⟩
    simp only [mem_iInter, mem_Iio]
    intro s t hbad
    have hdist : ε < dist s t := lt_of_not_ge fun h ↦ hbad (hy s t h)
    have := min_le_left ε (1 : ℝ)
    linarith [lt_min hε zero_lt_one]
  obtain ⟨δ, hδ⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  refine ⟨δ, fun x ↦ (hδ x).1, fun x s t hst ↦ ?_⟩
  by_contra hbad
  have hlt : δ x < dist s t :=
    mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (hδ x).2 s) t) hbad
  exact (not_lt_of_ge hst) hlt

end IsOpen
