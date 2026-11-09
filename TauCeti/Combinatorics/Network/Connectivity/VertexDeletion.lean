/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Combinatorics.Network.Connectivity.Basic
public import TauCeti.Combinatorics.Network.InducedWalk

/-!
# Directed vertex connectivity after deleting vertices

Using the induced-family walk API, this file proves that deleting `m` vertices from an
`(m + k)`-vertex-strong family leaves a `k`-vertex-strong family.

The result is the directed analogue of preservation of vertex connectivity under vertex deletion.
It does not require finiteness of the ambient vertex type or arrow types; only the deleted set is
finite.

## Main results

* `TauCeti.IsVertexStrong.inducedHom_compl`: deleting a finite set of `m` vertices from an
  `(m + k)`-vertex-strong family leaves a `k`-vertex-strong family.
* `TauCeti.IsVertexStrong.inducedHom_compl_of_card_le`: deleting at most `k` vertices from a
  `k`-vertex-strong family preserves the remaining threshold.
* `TauCeti.vertexStrongConnectivity_le_inducedHom_compl_add_card`: the corresponding numerical
  connectivity bound.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.1.
-/

public section

open Set.Notation

universe u v

namespace TauCeti

variable {V : Type u} {Q : V → V → Type v}

open Finset

variable {k : ℕ}

/-- Deleting a finite set `X` of vertices from an `(#X + k)`-vertex-strong arrow family leaves a
`k`-vertex-strong induced arrow family on the complement. -/
theorem IsVertexStrong.inducedHom_compl {X : Finset V}
    (h : IsVertexStrong Q (#X + k)) :
    IsVertexStrong (((X : Set V)ᶜ).inducedHom Q) k := by
  classical
  rw [isVertexStrong_def] at h ⊢
  refine ⟨?_, fun Y hY s hs t ht ↦ ?_⟩
  · have hcard := h.1
    rw [Nat.cast_add, ← Set.encard_add_encard_compl (X : Set V),
      Set.encard_coe_eq_coe_finsetCard] at hcard
    rw [ENat.card_coe_set_eq]
    exact (ENat.add_lt_add_iff_left (by simp : (X.card : ℕ∞) ≠ ⊤)).1 hcard
  · rw [Set.reachableAvoiding_inducedHom_iff]
    let Z : Finset V := X ∪ Y.image Subtype.val
    have hZ : #Z < #X + k := by
      calc
        #Z ≤ #X + #(Y.image Subtype.val) := card_union_le _ _
        _ ≤ #X + #Y := Nat.add_le_add_left card_image_le _
        _ < #X + k := Nat.add_lt_add_left hY _
    have hnotMemZ (v : ↑((X : Set V)ᶜ)) (hv : v ∉ Y) : (v : V) ∉ Z := by
      rintro hmem
      rcases mem_union.1 hmem with hmem | hmem
      · exact v.2 hmem
      · obtain ⟨y, hy, hyv⟩ := mem_image.1 hmem
        exact hv ((Subtype.ext hyv).symm ▸ hy)
    have hr := h.2 Z hZ (hnotMemZ s hs) (hnotMemZ t ht)
    exact hr.mono fun x hx ↦ by simpa [Z] using hx

/-- Deleting at most `k` vertices from a `k`-vertex-strong arrow family leaves a
`(k - #X)`-vertex-strong family. -/
theorem IsVertexStrong.inducedHom_compl_of_card_le {X : Finset V}
    (h : IsVertexStrong Q k) (hX : #X ≤ k) :
    IsVertexStrong (((X : Set V)ᶜ).inducedHom Q) (k - #X) := by
  rw [← Nat.add_sub_of_le hX] at h
  exact h.inducedHom_compl

/-- Deleting a finite set of vertices reduces vertex strong connectivity by at most its
cardinality. This includes empty and infinite ambient vertex types. -/
theorem vertexStrongConnectivity_le_inducedHom_compl_add_card (X : Finset V) :
    vertexStrongConnectivity Q ≤
      vertexStrongConnectivity (((X : Set V)ᶜ).inducedHom Q) + #X := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have := hV
    simp [vertexStrongConnectivity_eq_zero_of_subsingleton]
  · have := hV
    refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
    have hk' : IsVertexStrong Q k :=
      (isVertexStrong_iff_le_vertexStrongConnectivity k).2 hk
    by_cases hXk : #X ≤ k
    · have hdel := hk'.inducedHom_compl_of_card_le hXk
      let _ : Nonempty ↑((X : Set V)ᶜ) :=
        (ENat.card_pos_iff_nonempty _).1
          (lt_of_le_of_lt zero_le hdel.lt_card)
      have hle : (k - #X : ℕ) ≤
          vertexStrongConnectivity (((X : Set V)ᶜ).inducedHom Q) :=
        (isVertexStrong_iff_le_vertexStrongConnectivity (k - #X)).1 hdel
      calc
        (k : ℕ∞) = (k - #X : ℕ) + (#X : ℕ∞) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel hXk]
        _ ≤ _ := add_le_add hle le_rfl
    · have hkX : k ≤ #X := Nat.le_of_lt (Nat.lt_of_not_ge hXk)
      exact (Nat.cast_le.2 hkX).trans (self_le_add_left (#X : ℕ∞) _)

end TauCeti
