/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Interval.Finset.Nat

/-!
# Closures of images of bounded cylinders of Baire space

For coordinate bounds `N : ℕ → ℕ`, the subsets `{β | ∀ k < n, β k ≤ N k}` of Baire space `ℕ → ℕ`
decrease to the compact box `Iic N`. Their images under a continuous map `f` into a Hausdorff
space need not be closed, but the intersection of the closures of these images is still contained
in `f '' Iic N`. The proof refines the filters of points with bounded initial coordinates whose
images approach a given point to an ultrafilter; every coordinate eventually lies in a finite set,
so the ultrafilter converges in `ℕ → ℕ`, and uniqueness of limits identifies the image.

This is the compactness step of the capacity argument proving that analytic sets are universally
measurable: it needs neither a metric nor separability on the target.

## Main results

* `TauCeti.iInter_closure_image_subset_image_Iic`: a point in the closure of every finite-stage
  image is the image of a point of `Iic N`.

## Provenance

The statement adapts the closure lemma of Daniel Lyng's Apache-2.0 Econlib development,
`Econlib/Math/MeasureTheory/AnalyticNullMeasurable.lean`, commit
`003655ccf010cdf44c4f67d6675167b54ce0e9df`, which assumed a metrizable target; the ultrafilter
proof removes that assumption.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- For continuous `f` on Baire space and coordinate bounds `N`, a point in all the finite-stage
image closures is already the image of a point satisfying every coordinate bound. -/
theorem iInter_closure_image_subset_image_Iic
    {X : Type*} [TopologicalSpace X] [T2Space X] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    (N : ℕ → ℕ) :
    ⋂ n, closure (f '' {β | ∀ k < n, β k ≤ N k}) ⊆ f '' Iic N := by
  intro x hx
  -- Points whose first `n` coordinates are bounded and whose images approach `x` form a
  -- decreasing family of nontrivial filters; refine its infimum to an ultrafilter `𝓤`.
  set 𝓕 : ℕ → Filter (ℕ → ℕ) := fun n => comap f (𝓝 x) ⊓ 𝓟 {β | ∀ k < n, β k ≤ N k}
  have hne : (⨅ n, 𝓕 n).NeBot := by
    refine iInf_neBot_of_directed' (Antitone.directed_ge fun m n hmn => ?_) fun n => ?_
    · exact inf_le_inf_left _ (principal_mono.2 fun β hβ k hk => hβ k (hk.trans_le hmn))
    · have := mem_closure_iff_clusterPt.1 (mem_iInter.1 hx n)
      exact (comap_inf_principal_neBot_of_image_mem this
        (mem_inf_of_right (mem_principal_self _))).mono
        (inf_le_inf_right _ (comap_mono inf_le_left))
  let 𝓤 := Ultrafilter.of (⨅ n, 𝓕 n)
  have h𝓤 : ∀ n, (𝓤 : Filter (ℕ → ℕ)) ≤ 𝓕 n := fun n => (Ultrafilter.of_le _).trans (iInf_le _ n)
  -- Each coordinate eventually lies in a finite set, so it converges along `𝓤`.
  have hcoord : ∀ k, ∃ b ∈ Iic (N k), ↑(𝓤.map fun β => β k) ≤ 𝓝 b := fun k =>
    (finite_Iic (N k)).isCompact.ultrafilter_le_nhds _ <| le_principal_iff.2 <| mem_map.2 <|
      mem_of_superset (le_principal_iff.1 ((h𝓤 (k + 1)).trans inf_le_right))
        fun β hβ => hβ k k.lt_succ_self
  choose b hb hlim using hcoord
  have hb_lim : Tendsto id (𝓤 : Filter (ℕ → ℕ)) (𝓝 b) := tendsto_pi_nhds.2 hlim
  exact ⟨b, hb, tendsto_nhds_unique ((hf.tendsto b).comp hb_lim)
    (tendsto_iff_comap.2 ((h𝓤 0).trans inf_le_left))⟩

end TauCeti
