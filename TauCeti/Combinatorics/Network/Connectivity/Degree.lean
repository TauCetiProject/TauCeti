/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Connectivity.Basic

/-!
# Loop-free degree bounds for directed connectivity

The arc connectivity of an arrow family on at least two vertices is bounded by the number of
nonloop arrows leaving or entering any chosen vertex. Loops are excluded because they cannot help
reach a distinct vertex. Unlike the bounds by the full in-degree and out-degree, these results need
only the corresponding nonloop arrows to be finite; the family may have infinitely many loops.

These are the directed analogues of the bound of multigraph edge connectivity by the number of
nonloop edges incident to a vertex.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.1.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v}

/-- On at least two vertices, arc connectivity is at most the number of nonloop arrows leaving a
chosen vertex. Only these nonloop arrows need to be finite. -/
theorem arcConnectivity_le_card_nonloop_out [Nontrivial V] (v : V)
    [Finite (Σ w : {w : V // w ≠ v}, Q v w)] :
    arcConnectivity Q ≤ Nat.card (Σ w : {w : V // w ≠ v}, Q v w) := by
  let _ := Fintype.ofFinite (Σ w : {w : V // w ≠ v}, Q v w)
  obtain ⟨w, hwv⟩ := exists_ne v
  let ι₁ : (Σ w : {w : V // w ≠ v}, Q v w) ↪ (Σ w, Q v w) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype _) fun _ ↦
      Function.Embedding.refl _
  let ι₂ : (Σ w, Q v w) ↪ (Σ x y, Q x y) :=
    @Function.Embedding.sigmaMk V (fun x ↦ Σ y, Q x y) v
  let ι := ι₁.trans ι₂
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ Nat.cast_le.2 ?_
  have hstrong := (isArcStrong_iff_le_arcConnectivity k).2 hk
  have hcard := (hstrong.isArcReachable v w).le_card (C := {v}) rfl hwv
    (F := univ.map ι) fun x y e hx hy ↦ by
      subst x
      exact mem_map.2 ⟨⟨⟨y, by simpa using hy⟩, e⟩, mem_univ _, rfl⟩
  simpa [Nat.card_eq_fintype_card] using hcard

/-- On at least two vertices, arc connectivity is at most the number of nonloop arrows entering a
chosen vertex. Only these nonloop arrows need to be finite. -/
theorem arcConnectivity_le_card_nonloop_in [Nontrivial V] (v : V)
    [Finite (Σ w : {w : V // w ≠ v}, Q w v)] :
    arcConnectivity Q ≤ Nat.card (Σ w : {w : V // w ≠ v}, Q w v) := by
  let _ := Fintype.ofFinite (Σ w : {w : V // w ≠ v}, Q w v)
  obtain ⟨w, hwv⟩ := exists_ne v
  let ι₁ : (Σ w : {w : V // w ≠ v}, Q w v) ↪ (Σ w, Q w v) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype _) fun _ ↦
      Function.Embedding.refl _
  let ι₂ : (Σ w, Q w v) ↪ (Σ x y, Q x y) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) fun _ ↦
      Function.Embedding.sigmaMk v
  let ι := ι₁.trans ι₂
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ Nat.cast_le.2 ?_
  have hstrong := (isArcStrong_iff_le_arcConnectivity k).2 hk
  have hcard := (hstrong.isArcReachable w v).le_card (C := {v}ᶜ) hwv (by simp)
    (F := univ.map ι) fun x y e hx hy ↦ by
      have hy' : y = v := by simpa using hy
      subst y
      exact mem_map.2 ⟨⟨⟨x, by simpa using hx⟩, e⟩, mem_univ _, rfl⟩
  simpa [Nat.card_eq_fintype_card] using hcard

end TauCeti
