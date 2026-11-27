/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Connectivity.Basic
public import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Loop-free degree bounds for directed connectivity

The arc connectivity of an arrow family is bounded by the extended cardinality of every directed
cut. On at least two vertices, it is therefore bounded by the number of nonloop arrows leaving or
entering any chosen vertex. Loops are excluded because they cannot help reach a distinct vertex.
The extended-cardinality bounds need no finiteness; their `Nat.card` corollaries require only the
corresponding nonloop arrows to be finite, so the family may have infinitely many loops.

These are the directed analogues of the bound of multigraph edge connectivity by the number of
nonloop edges incident to a vertex.

## Main results

* `TauCeti.arcConnectivity_le_encard_cut`: the bound by an arbitrary directed cut.
* `TauCeti.arcConnectivity_le_enatCard_nonloop_out` and
  `TauCeti.arcConnectivity_le_enatCard_nonloop_in`: the loop-free extended-cardinality bounds.
* `TauCeti.arcConnectivity_le_card_nonloop_out` and
  `TauCeti.arcConnectivity_le_card_nonloop_in`: their finite-cardinality forms.
* `TauCeti.arcConnectivity_le_card_out` and `TauCeti.arcConnectivity_le_card_in`: the bounds by
  the full out-degree and in-degree, derived from the loop-free bounds.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.1.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v}

private def restrictedArrowEquiv (v : V) :
    {a : Σ x y, Q x y | a.1 = v ∧ a.2.1 ≠ v} ≃
      (Σ w : {w : V // w ≠ v}, Q v w) := by
  let e₁ : {a : Σ x y, Q x y | a.1 = v ∧ a.2.1 ≠ v} ≃
      {a : {a : Σ x y, Q x y // a.1 = v} // a.val.2.1 ≠ v} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun a : Σ x y, Q x y ↦ a.1 = v) (fun a ↦ a.2.1 ≠ v)).symm
  let e₂ : {a : {a : Σ x y, Q x y // a.1 = v} // a.val.2.1 ≠ v} ≃
      {a : Σ y, Q v y // a.1 ≠ v} :=
    (Equiv.sigmaSubtype v).subtypeEquiv fun a ↦ by
      rcases a with ⟨⟨x, y, a⟩, h⟩
      cases h
      rfl
  exact e₁.trans <| e₂.trans <| Equiv.subtypeSigmaEquiv (Q v) (fun w ↦ w ≠ v)

/-- Arc connectivity is at most the extended cardinality of every directed cut separating two
specified vertices. -/
theorem arcConnectivity_le_encard_cut {C : Set V} {s t : V} (hs : s ∈ C) (ht : t ∉ C) :
    arcConnectivity Q ≤ {a : Σ x y, Q x y | a.1 ∈ C ∧ a.2.1 ∉ C}.encard := by
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  have hstrong := (isArcStrong_iff_le_arcConnectivity k).2 hk
  let A := {a : Σ x y, Q x y | a.1 ∈ C ∧ a.2.1 ∉ C}
  by_cases hA : A.Finite
  · rw [hA.encard_eq_coe_toFinset_card]
    exact Nat.cast_le.2 <| (hstrong.isArcReachable s t).le_card hs ht fun _ _ e hx hy ↦ by
      apply hA.mem_toFinset.mpr
      exact ⟨hx, hy⟩
  · rw [Set.encard_eq_top hA]
    exact le_top

/-- On at least two vertices, arc connectivity is at most the extended cardinality of the
nonloop arrows leaving a chosen vertex. -/
theorem arcConnectivity_le_enatCard_nonloop_out [Nontrivial V] (v : V) :
    arcConnectivity Q ≤ ENat.card (Σ w : {w : V // w ≠ v}, Q v w) := by
  obtain ⟨w, hwv⟩ := exists_ne v
  let A := {a : Σ x y, Q x y | a.1 ∈ ({v} : Set V) ∧ a.2.1 ∉ ({v} : Set V)}
  let e : A ≃ (Σ w : {w : V // w ≠ v}, Q v w) :=
    (Equiv.subtypeEquivRight fun a ↦ by simp [A]).trans <|
      restrictedArrowEquiv (Q := Q) v
  refine (arcConnectivity_le_encard_cut (Q := Q) (C := {v}) (s := v) (t := w) rfl hwv).trans_eq ?_
  exact (ENat.card_coe_set_eq A).symm.trans (ENat.card_congr e)

/-- On at least two vertices, arc connectivity is at most the extended cardinality of the
nonloop arrows entering a chosen vertex. -/
theorem arcConnectivity_le_enatCard_nonloop_in [Nontrivial V] (v : V) :
    arcConnectivity Q ≤ ENat.card (Σ w : {w : V // w ≠ v}, Q w v) := by
  obtain ⟨w, hwv⟩ := exists_ne v
  let A := {a : Σ x y, Q x y | a.1 ∈ ({v}ᶜ : Set V) ∧ a.2.1 ∉ ({v}ᶜ : Set V)}
  let e : A ≃ (Σ w : {w : V // w ≠ v}, Q w v) :=
    (Equiv.subtypeEquivRight fun a ↦ by simp [A]).trans <|
      (Equiv.subtypeSigmaEquivSigma (p := fun x ↦ x ≠ v)
        (q := fun _ a ↦ a.1 = v)).trans <|
        Equiv.sigmaCongrRight fun _ ↦ Equiv.sigmaSubtype v
  refine (arcConnectivity_le_encard_cut (Q := Q) (C := {v}ᶜ) (s := w) (t := v) ?_ ?_).trans_eq ?_
  · simpa using hwv
  · simp
  · exact (ENat.card_coe_set_eq A).symm.trans (ENat.card_congr e)

/-- On at least two vertices, arc connectivity is at most the number of nonloop arrows leaving a
chosen vertex. Only these nonloop arrows need to be finite. -/
theorem arcConnectivity_le_card_nonloop_out [Nontrivial V] (v : V)
    [Finite (Σ w : {w : V // w ≠ v}, Q v w)] :
    arcConnectivity Q ≤ Nat.card (Σ w : {w : V // w ≠ v}, Q v w) := by
  simpa only [ENat.card_eq_coe_natCard] using arcConnectivity_le_enatCard_nonloop_out (Q := Q) v

/-- On at least two vertices, arc connectivity is at most the number of nonloop arrows entering a
chosen vertex. Only these nonloop arrows need to be finite. -/
theorem arcConnectivity_le_card_nonloop_in [Nontrivial V] (v : V)
    [Finite (Σ w : {w : V // w ≠ v}, Q w v)] :
    arcConnectivity Q ≤ Nat.card (Σ w : {w : V // w ≠ v}, Q w v) := by
  simpa only [ENat.card_eq_coe_natCard] using arcConnectivity_le_enatCard_nonloop_in (Q := Q) v

private def nonloopEmbedding (v : V) (P : V → Type v) :
    (Σ w : {w : V // w ≠ v}, P w) ↪ (Σ w, P w) :=
  Function.Embedding.sigmaMap (Function.Embedding.subtype _) fun _ ↦
    Function.Embedding.refl _

/-- On at least two vertices, the arc connectivity is at most the number of arrows leaving any
vertex, loops included. -/
theorem arcConnectivity_le_card_out [Nontrivial V] (v : V) [Fintype (Σ w, Q v w)] :
    arcConnectivity Q ≤ Fintype.card (Σ w, Q v w) := by
  let ι := nonloopEmbedding v (Q v)
  let _ : Finite (Σ w : {w : V // w ≠ v}, Q v w) := Finite.of_injective ι ι.injective
  refine (arcConnectivity_le_card_nonloop_out v).trans (Nat.cast_le.2 ?_)
  exact (Nat.card_le_card_of_injective ι ι.injective).trans_eq Nat.card_eq_fintype_card

/-- On at least two vertices, the arc connectivity is at most the number of arrows entering any
vertex, loops included. -/
theorem arcConnectivity_le_card_in [Nontrivial V] (v : V) [Fintype (Σ w, Q w v)] :
    arcConnectivity Q ≤ Fintype.card (Σ w, Q w v) := by
  let ι := nonloopEmbedding v (Q · v)
  let _ : Finite (Σ w : {w : V // w ≠ v}, Q w v) := Finite.of_injective ι ι.injective
  refine (arcConnectivity_le_card_nonloop_in v).trans (Nat.cast_le.2 ?_)
  exact (Nat.card_le_card_of_injective ι ι.injective).trans_eq Nat.card_eq_fintype_card

end TauCeti
