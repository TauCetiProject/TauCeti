/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Separation.Basic

/-!
# Coherent topologies: products and compact subsets

The topology of `X` is coherent with a family `S` of subsets (`Topology.IsCoherentWith S`) when a
set is open as soon as its trace on each member of `S` is relatively open. The typical example is
an increasing union `X = ⋃ₙ Xₙ` carrying the final topology, such as a CW complex filtered by its
skeleta or a manifold exhausted by compact sublevels. This file records two properties of such
topologies used to pass from the stages of a tower to its union.

* Coherence survives multiplication by a locally compact space: if `S` covers `X` and the
  topology of `X` is coherent with `S`, then the topology of `Y × X` is coherent with the sets
  `univ ×ˢ s` for `s ∈ S`, whenever `Y` is locally compact
  (`Topology.IsCoherentWith.univ_prod`). With `Y = [0, 1]`, a homotopy on the union is continuous
  as soon as it is continuous on each stage.
* For an increasing sequence of stages in a `T₁` space, every compact subset of the union lies in
  a single stage (`Topology.IsCoherentWith.exists_subset_of_isCompact`). Otherwise a sequence of
  points of the compact set escaping every stage would be an infinite closed discrete subset.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.1, whose proof for CW complexes is the argument used here for compact
  subsets.
-/

public section

open Set Filter

namespace Topology.IsCoherentWith

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (Set X)}

/-- If the topology of `X` is coherent with a family `S` covering `X`, then the topology of `Y × X`
is coherent with the sets `univ ×ˢ s` for `s ∈ S`, provided `Y` is locally compact. -/
theorem univ_prod [LocallyCompactSpace Y] (hS : IsCoherentWith S) (hSU : ⋃₀ S = univ) :
    IsCoherentWith ((univ ×ˢ ·) '' S : Set (Set (Y × X))) := by
  refine of_continuous_prop fun f hf => ?_
  have hfs (s : Set X) (hs : s ∈ S) : ContinuousOn f (univ ×ˢ s) := hf _ ⟨s, hs, rfl⟩
  -- Curry `f` along `Y`: each slice is continuous, and the curried map is continuous on each
  -- member of `S`, hence continuous.
  have hslice (x : X) : Continuous fun y => f (y, x) := by
    obtain ⟨s, hs, hx⟩ := mem_sUnion.1 (hSU ▸ mem_univ x)
    exact (hfs s hs).comp_continuous (by fun_prop) fun y => ⟨mem_univ y, hx⟩
  let G : X → C(Y, Prop) := fun x => ⟨fun y => f (y, x), hslice x⟩
  have hG : Continuous G := hS.continuous_iff.2 fun s hs => by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (ContinuousMap.curry ⟨fun p : s × Y => f (p.2, p.1),
      (hfs s hs).comp_continuous (by fun_prop) fun p => ⟨mem_univ _, p.1.2⟩⟩).continuous
  exact (ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩).comp continuous_swap

/-- **Compact subsets of an increasing union lie in a finite stage.** If the topology of a `T₁`
space `X` is coherent with an increasing sequence of subsets `s n`, then every compact subset of
their union lies in one of them. -/
theorem exists_subset_of_isCompact [T1Space X] {s : ℕ → Set X} (hs : Monotone s)
    (hsX : IsCoherentWith (range s)) {K : Set X} (hK : IsCompact K) (hKs : K ⊆ ⋃ n, s n) :
    ∃ n, K ⊆ s n := by
  by_contra! h
  choose x hxK hxs using fun n => not_subset.1 (h n)
  -- A point `x k` lies in `s m` only for `k < m`, so every set of these points is closed.
  have hlt {k m : ℕ} (hk : x k ∈ s m) : k < m := by
    by_contra! hmk
    exact hxs k (hs hmk hk)
  have hclosed (Q : Set X) (hQ : Q ⊆ range x) : IsClosed Q := by
    refine hsX.isClosed_iff.2 ?_
    rintro _ ⟨m, rfl⟩
    have hfin : (Q ∩ s m).Finite := ((finite_Iio m).image x).subset fun y ⟨hyQ, hym⟩ => by
      obtain ⟨k, rfl⟩ := hQ hyQ
      exact ⟨k, hlt hym, rfl⟩
    have hpre : ((↑) ⁻¹' Q : Set (s m)) = (↑) ⁻¹' (Q ∩ s m) := by
      ext y
      simp
    rw [hpre]
    exact hfin.isClosed.preimage continuous_subtype_val
  -- The tails `{x k | k ≥ n}` are closed, nonempty and decreasing in the compact set `K`, so
  -- they have a common point, which lies in some stage `s m` and is then some `x k` with `k ≥ m`.
  let F : ℕ → Set X := fun n => x '' Ici n
  have hF (n : ℕ) : F n ⊆ range x := image_subset_range x _
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
    (fun n => image_mono (Ici_subset_Ici.2 n.le_succ)) (fun n => ⟨x n, n, self_mem_Ici, rfl⟩)
    (hK.of_isClosed_subset (hclosed _ (hF 0)) (by rintro _ ⟨k, -, rfl⟩; exact hxK k))
    (fun n => hclosed _ (hF n))
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hKs ((mem_iInter.1 hz 0).elim fun k hk => hk.2 ▸ hxK k))
  obtain ⟨k, hk, rfl⟩ := mem_iInter.1 hz m
  exact (hlt hm).not_ge hk

end Topology.IsCoherentWith
