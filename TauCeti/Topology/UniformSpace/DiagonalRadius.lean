/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Continuous radii inside parameterized diagonal neighbourhoods

An open neighbourhood of the diagonal in a compact pseudometric space contains a uniform metric
entourage. For an open family of such neighbourhoods parameterized by a normal paracompact
space, the radius can be chosen positive and continuous in the parameter. The parameter
space need not be compact, and the radii need not have a global positive lower bound.

This is useful for composing local transport maps along a compact interval: a continuous
radius controls how far each individual step may travel. We use Mathlib's generalized tube
lemma, its compact-space diagonal/uniformity comparison, and its partition-of-unity convex
selection theorem. In particular, we select radii, not an average of invertible operators.
-/

public section

open Filter Set Topology Metric
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
