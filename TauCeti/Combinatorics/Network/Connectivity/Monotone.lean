/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Connectivity.Basic
public import Mathlib.Data.Finset.Preimage

/-!
# Directed connectivity under arrow maps and deletion

Adding arrows preserves directed connectivity. For vertex strong connectivity an arbitrary
endpoint-preserving arrow map suffices, whereas arc connectivity requires an injection on each
arrow type: identifying parallel arrows can reduce the number of disjoint routes.

This file proves these monotonicity statements for both the threshold predicates and their
numerical invariants. It also proves that deleting a finite set of arrows reduces local and global
arc-connectivity thresholds by at most the number deleted. No finiteness of vertices or arrow
types is required, and loops and parallel arrows retain their identities.

The deletion bound is the directed analogue of the usual edge-connectivity bound; see
J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
Springer, 2009, Section 5.1.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {R : V → V → Type w}
variable {k : ℕ} {s t : V}

/-- An endpoint-preserving injection on each arrow type preserves local arc reachability.
Injectivity prevents distinct parallel arrows from being identified. -/
theorem IsArcReachable.map (h : IsArcReachable Q k s t)
    (φ : ∀ x y, Q x y ↪ R x y) : IsArcReachable R k s t := by
  classical
  let ι : (Σ x y, Q x y) ↪ (Σ x y, R x y) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V) fun x ↦
      Function.Embedding.sigmaMap (Function.Embedding.refl V) (φ x)
  have hι (x y : V) (e : Q x y) : ι ⟨x, y, e⟩ = ⟨x, y, φ x y e⟩ := rfl
  rw [isArcReachable_def]
  intro F hF
  have hcard : #(F.preimage ι ι.injective.injOn) < k := by
    rw [card_preimage]
    exact (card_filter_le _ _).trans_lt hF
  exact ((isArcReachable_def.1 h) _ hcard).mem_of_mem
    (C := {v | ReachableWithout (F : Set (Σ x y, R x y)) s v})
    (.refl _ s) fun x y e hx he ↦ hx.tail (φ x y e) (by
      simpa only [mem_coe, mem_preimage, hι] using he)

/-- Endpoint-preserving arrow embeddings preserve global arc connectivity thresholds. -/
theorem IsArcStrong.map (h : IsArcStrong Q k) (φ : ∀ x y, Q x y ↪ R x y) :
    IsArcStrong R k :=
  isArcStrong_def.2 fun s t ↦ (h.isArcReachable s t).map φ

/-- Endpoint-preserving arrow maps preserve vertex strong connectivity. Unlike arc
connectivity, this does not require injectivity on arrows. -/
theorem IsVertexStrong.map (h : IsVertexStrong Q k) (φ : ∀ x y, Q x y → R x y) :
    IsVertexStrong R k := by
  apply isVertexStrong_def.2
  refine ⟨h.lt_card, fun X hX s hs t ht ↦ ?_⟩
  exact (h.reachableAvoiding hX hs ht).mem_of_mem
    (C := {v | ReachableAvoiding R (X : Set V) s v}) (.refl hs)
    fun x y e hx _ hy ↦ hx.tail (φ x y e) hy

/-- Adding arrows without identifying any existing arrows cannot decrease arc connectivity. -/
theorem arcConnectivity_mono (φ : ∀ x y, Q x y ↪ R x y) :
    arcConnectivity Q ≤ arcConnectivity R := by
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  exact (isArcStrong_iff_le_arcConnectivity k).1
    (((isArcStrong_iff_le_arcConnectivity k).2 hk).map φ)

/-- An endpoint-preserving arrow map cannot decrease vertex strong connectivity, including
on an empty vertex type. -/
theorem vertexStrongConnectivity_mono (φ : ∀ x y, Q x y → R x y) :
    vertexStrongConnectivity Q ≤ vertexStrongConnectivity R := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have := hV
    simp
  · have := hV
    refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
    exact (isVertexStrong_iff_le_vertexStrongConnectivity k).1
      (((isVertexStrong_iff_le_vertexStrongConnectivity k).2 hk).map φ)

/-- Relabelling arrows at each ordered pair preserves local arc reachability. -/
theorem isArcReachable_congr (e : ∀ x y, Q x y ≃ R x y) :
    IsArcReachable Q k s t ↔ IsArcReachable R k s t :=
  ⟨fun h ↦ h.map fun x y ↦ (e x y).toEmbedding,
    fun h ↦ h.map fun x y ↦ (e x y).symm.toEmbedding⟩

/-- Relabelling arrows at each ordered pair preserves arc-strong thresholds. -/
theorem isArcStrong_congr (e : ∀ x y, Q x y ≃ R x y) :
    IsArcStrong Q k ↔ IsArcStrong R k :=
  ⟨fun h ↦ h.map fun x y ↦ (e x y).toEmbedding,
    fun h ↦ h.map fun x y ↦ (e x y).symm.toEmbedding⟩

/-- Relabelling arrows at each ordered pair preserves vertex-strong thresholds. -/
theorem isVertexStrong_congr (e : ∀ x y, Q x y ≃ R x y) :
    IsVertexStrong Q k ↔ IsVertexStrong R k :=
  ⟨fun h ↦ h.map fun x y ↦ e x y, fun h ↦ h.map fun x y ↦ (e x y).symm⟩

/-- Arc connectivity is invariant under endpoint-preserving relabelling of arrows. -/
theorem arcConnectivity_congr (e : ∀ x y, Q x y ≃ R x y) :
    arcConnectivity Q = arcConnectivity R :=
  le_antisymm (arcConnectivity_mono fun x y ↦ (e x y).toEmbedding)
    (arcConnectivity_mono fun x y ↦ (e x y).symm.toEmbedding)

/-- Vertex strong connectivity is invariant under endpoint-preserving relabelling of arrows. -/
theorem vertexStrongConnectivity_congr (e : ∀ x y, Q x y ≃ R x y) :
    vertexStrongConnectivity Q = vertexStrongConnectivity R :=
  le_antisymm (vertexStrongConnectivity_mono fun x y ↦ e x y)
    (vertexStrongConnectivity_mono fun x y ↦ (e x y).symm)

/-- Deleting `F` reduces a local arc-reachability threshold by at most `F.card`. The deleted
arrows are counted as identities, including parallel arrows and loops. -/
theorem IsArcReachable.withoutHom (h : IsArcReachable Q k s t)
    (F : Finset (Σ x y, Q x y)) :
    IsArcReachable (WithoutHom (F : Set (Σ x y, Q x y))) (k - #F) s t := by
  classical
  rw [isArcReachable_def]
  intro B hB
  let ι : (Σ x y, WithoutHom (F : Set (Σ x y, Q x y)) x y) → (Σ x y, Q x y) :=
    fun a ↦ ⟨a.1, a.2.1, a.2.2.1⟩
  have hcard : #(F ∪ B.image ι) < k := by
    have hle := (card_union_le F (B.image ι)).trans (Nat.add_le_add_left card_image_le _)
    omega
  exact ((isArcReachable_def.1 h) _ hcard).mem_of_mem
    (C := {v | ReachableWithout
      (B : Set (Σ x y, WithoutHom (F : Set (Σ x y, Q x y)) x y)) s v})
    (.refl _ s) fun x y e hx he ↦ by
      have heF : (⟨x, y, e⟩ : Σ x y, Q x y) ∉ (F : Set _) :=
        fun heF ↦ he (mem_union_left _ heF)
      refine hx.tail ⟨e, heF⟩ fun heB ↦ ?_
      exact he (mem_union_right _ (mem_image_of_mem ι heB))

/-- Deleting `F` reduces a global arc-connectivity threshold by at most `F.card`. -/
theorem IsArcStrong.withoutHom (h : IsArcStrong Q k) (F : Finset (Σ x y, Q x y)) :
    IsArcStrong (WithoutHom (F : Set (Σ x y, Q x y))) (k - #F) :=
  isArcStrong_def.2 fun s t ↦ (h.isArcReachable s t).withoutHom F

/-- The arc connectivity before deleting `F` is at most the arc connectivity afterwards plus
`F.card`. This also applies when either invariant is infinite. -/
theorem arcConnectivity_le_withoutHom_add_card (F : Finset (Σ x y, Q x y)) :
    arcConnectivity Q ≤ arcConnectivity (WithoutHom (F : Set (Σ x y, Q x y))) + #F := by
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  have h := ((isArcStrong_iff_le_arcConnectivity k).2 hk).withoutHom F
  have hle := (isArcStrong_iff_le_arcConnectivity (k - #F)).1 h
  have hnat : k ≤ (k - #F) + #F := by omega
  calc
    (k : ℕ∞) ≤ ((k - #F) + #F : ℕ) := Nat.cast_le.2 hnat
    _ = (k - #F : ℕ) + (#F : ℕ∞) := by simp
    _ ≤ _ := add_le_add hle le_rfl

end TauCeti
