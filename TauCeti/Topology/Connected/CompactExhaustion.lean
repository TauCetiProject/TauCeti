/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact exhaustions with preconnected interiors

A weakly locally compact, sigma-compact, locally connected Hausdorff preconnected space has a
compact exhaustion whose interiors are preconnected and all contain a prescribed point.
The construction takes components of the interiors of an internally chosen compact exhaustion.
In a noncompact space these give open preconnected stages with compact proper closures, each
closure strictly inside the next stage.

Adapted from Otis Chodosh's original formalization in
`ForTauCeti.Topology.Connected.CompactExhaustion`:
https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/8aec9bbc07081bb020b19f55d4aaa32c13db6667/ForTauCeti/Topology/Connected/CompactExhaustion.lean
-/

public section

open Set

namespace CompactExhaustion

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PreconnectedSpace X]

/-- The interior components containing a fixed point exhaust a locally connected
preconnected space. -/
private theorem iUnion_connectedComponentIn_interior_eq_univ (K : CompactExhaustion X) (p : X) :
    ⋃ n, connectedComponentIn (interior (K n)) p = univ := by
  let U := fun n ↦ connectedComponentIn (interior (K n)) p
  have hopen : IsOpen (⋃ n, U n) := isOpen_iUnion fun _ ↦ isOpen_interior.connectedComponentIn
  have hclosed : IsClosed (⋃ n, U n) := by
    apply closure_subset_iff_isClosed.mp
    intro x hx
    obtain ⟨m, hm⟩ := K.exists_mem x
    have hxm : x ∈ interior (K (m + 1)) := K.subset_interior_succ m hm
    let V := connectedComponentIn (interior (K (m + 1))) x
    have hV : IsOpen V := isOpen_interior.connectedComponentIn
    have hxV : x ∈ V := mem_connectedComponentIn hxm
    obtain ⟨z, hzV, hzU⟩ := mem_closure_iff.mp hx V hV hxV
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzU
    let k := max (m + 1) n
    have hmk : interior (K (m + 1)) ⊆ interior (K k) :=
      interior_mono (K.subset (Nat.le_max_left (m + 1) n))
    have hnk : interior (K n) ⊆ interior (K k) :=
      interior_mono (K.subset (Nat.le_max_right (m + 1) n))
    have hz₁ : z ∈ connectedComponentIn (interior (K k)) x :=
      connectedComponentIn_mono x hmk hzV
    have hz₂ : z ∈ connectedComponentIn (interior (K k)) p :=
      connectedComponentIn_mono p hnk hzn
    have heq : connectedComponentIn (interior (K k)) x =
        connectedComponentIn (interior (K k)) p :=
      (connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm
    have hxU : x ∈ U k := by
      simp only [U, ← heq]
      exact mem_connectedComponentIn (hmk hxm)
    exact mem_iUnion.mpr ⟨k, hxU⟩
  have hclopen : IsClopen (⋃ n, U n) := ⟨hclosed, hopen⟩
  obtain ⟨n, hn⟩ := K.exists_mem p
  exact hclopen.eq_univ
    ⟨p, mem_iUnion.mpr ⟨n + 1, mem_connectedComponentIn (K.subset_interior_succ n hn)⟩⟩


variable [T2Space X]

omit [LocallyConnectedSpace X] [PreconnectedSpace X] in
private theorem closure_component_interior_subset_succ (K : CompactExhaustion X) (p : X)
    (n : ℕ) (hp : p ∈ interior (K n)) :
    closure (connectedComponentIn (interior (K n)) p) ⊆
      connectedComponentIn (interior (K (n + 1))) p :=
  isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hp))
    ((closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) (K.isClosed n))
      |>.trans (K.subset_interior_succ n))

end CompactExhaustion

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PreconnectedSpace X]
  [T2Space X]

/-- A sigma-compact, weakly locally compact, locally connected Hausdorff preconnected space
has a native compact exhaustion with preconnected interiors containing the chosen point. -/
theorem exists_compactExhaustion_isPreconnected_interior
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (p : X) : ∃ L : CompactExhaustion X,
      (∀ n, p ∈ interior (L n)) ∧ ∀ n, IsPreconnected (interior (L n)) := by
  classical
  let K := CompactExhaustion.choice X
  let C := fun n ↦ connectedComponentIn (interior (K n)) p
  obtain ⟨m, hpm⟩ := K.exists_mem p
  have hopen (n : ℕ) : IsOpen (C n) := isOpen_interior.connectedComponentIn
  have hp (n : ℕ) : p ∈ C (n + m + 1) :=
    mem_connectedComponentIn (K.subset_interior (by omega) hpm)
  have hcover : ⋃ n, closure (C (n + m + 1)) = univ := by
    apply subset_antisymm (subset_univ _)
    rw [← CompactExhaustion.iUnion_connectedComponentIn_interior_eq_univ K p]
    exact iUnion_mono fun n ↦
      (connectedComponentIn_mono p (interior_mono (K.subset (by omega)))).trans subset_closure
  let L : CompactExhaustion X :=
    { toFun := fun n ↦ closure (C (n + m + 1))
      isCompact' := fun n ↦ (K.isCompact _).closure_of_subset
        ((connectedComponentIn_subset _ _).trans interior_subset)
      subset_interior_succ' := fun n ↦ by
        have hshift : (n + 1) + m + 1 = (n + m + 1) + 1 := by omega
        rw [hshift]
        exact (CompactExhaustion.closure_component_interior_subset_succ K p (n + m + 1)
          (connectedComponentIn_subset _ _ (hp n))).trans
            (hopen _).subset_interior_closure
      iUnion_eq' := hcover }
  refine ⟨L, fun n ↦ (hopen _).subset_interior_closure (hp n), fun n ↦ ?_⟩
  exact isPreconnected_connectedComponentIn.subset_closure
    (hopen _).subset_interior_closure interior_subset

variable [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [NoncompactSpace X]

/-- A noncompact space with the stated topology admits an open preconnected exhaustion
through a chosen point, with compact proper closures strictly inside subsequent stages. -/
theorem exists_isOpen_isPreconnected_exhaustion (p : X) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n) ∧ IsPreconnected (U n) ∧ p ∈ U n ∧
        IsCompact (closure (U n)) ∧ closure (U n) ≠ univ ∧ closure (U n) ⊂ U (n + 1)) ∧
      ⋃ n, U n = univ := by
  obtain ⟨L, hp, hconn⟩ := exists_compactExhaustion_isPreconnected_interior p
  have hc (n : ℕ) : IsCompact (closure (interior (L n))) :=
    (L.isCompact n).closure_of_subset interior_subset
  have hsub (n : ℕ) : closure (interior (L n)) ⊆ interior (L (n + 1)) :=
    (closure_minimal interior_subset (L.isClosed n)).trans (L.subset_interior_succ n)
  refine ⟨fun n ↦ interior (L n), fun n ↦ ⟨isOpen_interior, hconn n, hp n, hc n,
    (hc n).ne_univ, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (hsub n) ?_
    intro heq
    have hclopen : IsClopen (closure (interior (L n))) :=
      ⟨isClosed_closure, heq.symm ▸ isOpen_interior⟩
    have hu : closure (interior (L n)) = univ := hclopen.eq_univ ⟨p, subset_closure (hp n)⟩
    exact (hc n).ne_univ hu
  · apply subset_antisymm (subset_univ _)
    rw [← L.iUnion_eq]
    exact iUnion_mono' fun n ↦ ⟨n + 1, L.subset_interior_succ n⟩

end TauCeti
