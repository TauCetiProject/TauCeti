/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact exhaustions with preconnected interiors

A weakly locally compact, sigma-compact, locally connected Hausdorff preconnected space has a
compact exhaustion whose interiors are preconnected and all contain a prescribed point.
The construction takes components of the interiors of an internally chosen compact exhaustion.
In a noncompact space these give open preconnected stages with compact proper closures, each
closure strictly inside the next stage.
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
      change x ∈ connectedComponentIn (interior (K k)) p
      rw [← heq]
      exact mem_connectedComponentIn (hmk hxm)
    exact mem_iUnion.mpr ⟨k, hxU⟩
  obtain ⟨n, hn⟩ := K.exists_mem p
  exact (show IsClopen (⋃ n, U n) from ⟨hclosed, hopen⟩).eq_univ
    ⟨p, mem_iUnion.mpr ⟨n + 1, mem_connectedComponentIn (K.subset_interior_succ n hn)⟩⟩


variable [T2Space X]

omit [LocallyConnectedSpace X] [PreconnectedSpace X] in
private theorem isCompact_closure_component_interior (K : CompactExhaustion X) (p : X) (n : ℕ) :
    IsCompact (closure (connectedComponentIn (interior (K n)) p)) :=
  (K.isCompact n).of_isClosed_subset isClosed_closure
    (closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) (K.isClosed n))

omit [LocallyConnectedSpace X] [PreconnectedSpace X] in
private theorem closure_component_interior_subset_succ (K : CompactExhaustion X) (p : X)
    (n : ℕ) (hp : p ∈ interior (K n)) :
    closure (connectedComponentIn (interior (K n)) p) ⊆
      connectedComponentIn (interior (K (n + 1))) p :=
  isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hp))
    ((closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) (K.isClosed n))
      |>.trans (K.subset_interior_succ n))

/-- A sigma-compact, weakly locally compact, locally connected Hausdorff preconnected space
has a native compact exhaustion with preconnected interiors containing the chosen point. -/
theorem exists_isPreconnected_interior [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
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
    rw [← iUnion_connectedComponentIn_interior_eq_univ K p]
    exact iUnion_mono fun n ↦
      (connectedComponentIn_mono p (interior_mono (K.subset (by omega)))).trans subset_closure
  let L : CompactExhaustion X :=
    { toFun := fun n ↦ closure (C (n + m + 1))
      isCompact' := fun n ↦ isCompact_closure_component_interior K p (n + m + 1)
      subset_interior_succ' := fun n ↦ by
        rw [show (n + 1) + m + 1 = (n + m + 1) + 1 by omega]
        exact (closure_component_interior_subset_succ K p (n + m + 1)
          (connectedComponentIn_subset _ _ (hp n))).trans
            (hopen _).subset_interior_closure
      iUnion_eq' := hcover }
  refine ⟨L, fun n ↦ (hopen _).subset_interior_closure (hp n), fun n ↦ ?_⟩
  exact isPreconnected_connectedComponentIn.subset_closure
    (hopen _).subset_interior_closure interior_subset

end CompactExhaustion

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
  [PreconnectedSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [NoncompactSpace X]

/-- A noncompact space with the stated topology admits an open preconnected exhaustion
through a chosen point, with compact proper closures strictly inside subsequent stages. -/
theorem exists_isOpen_isPreconnected_exhaustion (p : X) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n) ∧ IsPreconnected (U n) ∧ p ∈ U n ∧
        IsCompact (closure (U n)) ∧ closure (U n) ≠ univ ∧ closure (U n) ⊂ U (n + 1)) ∧
      ⋃ n, U n = univ := by
  obtain ⟨L, hp, hconn⟩ := CompactExhaustion.exists_isPreconnected_interior p
  have hc (n : ℕ) : IsCompact (closure (interior (L n))) :=
    (L.isCompact n).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (L.isClosed n))
  have hsub (n : ℕ) : closure (interior (L n)) ⊆ interior (L (n + 1)) :=
    (closure_minimal interior_subset (L.isClosed n)).trans (L.subset_interior_succ n)
  refine ⟨fun n ↦ interior (L n), fun n ↦ ⟨isOpen_interior, hconn n, hp n, hc n,
    (hc n).ne_univ, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (hsub n) ?_
    intro heq
    have hu : closure (interior (L n)) = univ :=
      (show IsClopen (closure (interior (L n))) from
        ⟨isClosed_closure, heq.symm ▸ isOpen_interior⟩).eq_univ ⟨p, subset_closure (hp n)⟩
    exact (hc n).ne_univ hu
  · apply subset_antisymm (subset_univ _)
    rw [← L.iUnion_eq]
    exact iUnion_mono' fun n ↦ ⟨n + 1, L.subset_interior_succ n⟩

end TauCeti
