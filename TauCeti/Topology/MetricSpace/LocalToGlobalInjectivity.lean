/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Global injectivity of close maps from local injectivity

Let `f` be a continuous injection from a compact space into a metric space, and fix an open
cover of the source. Every sufficiently uniformly close map that is injective on each cover
member is globally injective. No continuity of the approximating map is needed.

This separates the two issues in proving that an approximation remains an embedding: local
injectivity on fixed patches and exclusion of collisions between distant patches. In secant
approximation of a finite complex the patches can be vertex stars. On the compact set of pairs
not lying together in any patch, the images under `f` have a positive minimum separation.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966),
  Chapter II, Section 9 (local and global control in secant approximation).
-/

public section

open Set Function

namespace Continuous

variable {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
  {f : X → Y}

/-- Given a continuous injection from a compact space and an open cover of its source, every
sufficiently uniformly close map which is injective on each cover member is globally injective.
The approximating map need not be continuous, and the cover need not be finite. -/
theorem exists_pos_forall_injective_of_injOn_cover (hf : Continuous f) (hinj : Injective f)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ) :
    ∃ ε > 0, ∀ g : X → Y, (∀ x, dist (g x) (f x) < ε) →
      (∀ i, InjOn g (U i)) → Injective g := by
  let S : Set (X × X) := (⋃ i, U i ×ˢ U i)ᶜ
  have hS : IsClosed S := (isOpen_iUnion fun i ↦ (hU i).prod (hU i)).isClosed_compl
  have hsep : ∀ p ∈ S, 0 < dist (f p.1) (f p.2) := by
    intro p hp
    refine dist_pos.mpr (hinj.ne ?_)
    intro heq
    have hx : p.1 ∈ ⋃ i, U i := hcover.symm ▸ mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hp (mem_iUnion.mpr ⟨i, hi, heq ▸ hi⟩)
  obtain ⟨δ, hδ, hδS⟩ := hS.isCompact.exists_forall_le'
    (((hf.comp continuous_fst).dist (hf.comp continuous_snd)).continuousOn) hsep
  refine ⟨δ / 3, by positivity, fun g hclose hlocal x y hxy ↦ ?_⟩
  by_cases hpatch : ∃ i, x ∈ U i ∧ y ∈ U i
  · obtain ⟨i, hx, hy⟩ := hpatch
    exact hlocal i hx hy hxy
  · have hpair : (x, y) ∈ S := by
      simpa only [S, mem_compl_iff, mem_iUnion, mem_prod] using hpatch
    have hx : dist (f x) (g x) < δ / 3 := by
      simpa only [dist_comm] using hclose x
    have hy : dist (g x) (f y) < δ / 3 := hxy ▸ hclose y
    have hsmall : dist (f x) (f y) < δ := by
      linarith [dist_triangle (f x) (g x) (f y)]
    exact False.elim ((not_lt_of_ge (hδS (x, y) hpair)) hsmall)

end Continuous
