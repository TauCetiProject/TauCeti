/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Combinatorics.Network.Connectivity.Basic

/-!
# Directed vertex connectivity after deleting vertices

Restricting an arrow family to a set of vertices retains exactly the arrows whose endpoints lie in
that set. This file identifies reachability in the restricted family with ambient reachability
avoiding the discarded vertices, then proves that deleting `m` vertices from an
`(m + k)`-vertex-strong family leaves a `k`-vertex-strong family.

The result is the directed analogue of preservation of vertex connectivity under vertex deletion.
It does not require finiteness of the ambient vertex type or arrow types; only the deleted set is
finite.

## Main results

* `Set.inducedHom`: the arrow family induced on a vertex set.
* `Set.reachableAvoiding_inducedHom_iff`: reachability in an induced family is ambient
  reachability avoiding both discarded vertices and a further set of induced vertices.
* `TauCeti.IsVertexStrong.inducedHom_compl`: deleting a finite set of `m` vertices from an
  `(m + k)`-vertex-strong family leaves a `k`-vertex-strong family.
* `TauCeti.vertexStrongConnectivity_le_inducedHom_compl_add_card`: the corresponding numerical
  connectivity bound.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.1.
-/

public section

open Set.Notation

universe u v

namespace Set

variable {V : Type u}

/-- The arrow family induced by `Q` on a set `S` of vertices. -/
abbrev inducedHom (S : Set V) (Q : V → V → Type v) (x y : S) : Type v :=
  Q x y

/-- The inclusion of the arrow family induced on `S` into its ambient arrow family. -/
def inducedHomInclusion (S : Set V) (Q : V → V → Type v) :
    @Prefunctor S (Quiver.mk fun x y ↦ S.inducedHom Q x y) V (Quiver.mk Q) := by
  letI : Quiver S := Quiver.mk fun x y ↦ S.inducedHom Q x y
  letI : Quiver V := Quiver.mk Q
  exact { obj := Subtype.val, map := fun e ↦ e }

@[simp]
theorem inducedHomInclusion_obj (S : Set V) (Q : V → V → Type v) (x : S) :
    @Prefunctor.obj S (Quiver.mk fun x y ↦ S.inducedHom Q x y) V (Quiver.mk Q)
      (S.inducedHomInclusion Q) x = x :=
  (rfl)

@[simp]
theorem inducedHomInclusion_map (S : Set V) (Q : V → V → Type v) {x y : S}
    (e : S.inducedHom Q x y) :
    HEq (@Prefunctor.map S (Quiver.mk fun x y ↦ S.inducedHom Q x y) V (Quiver.mk Q)
      (S.inducedHomInclusion Q) x y e) e :=
  by simp [inducedHomInclusion]

end Set

namespace TauCeti

variable {V : Type u} {Q : V → V → Type v}

namespace ArrowWalk

/-- Forget the subtype witnesses from a walk in an induced arrow family. -/
def coeInduced {S : Set V} {s t : S} (p : ArrowWalk (S.inducedHom Q) s t) :
    ArrowWalk Q s t := by
  letI : Quiver S := Quiver.mk fun x y ↦ S.inducedHom Q x y
  letI : Quiver V := Quiver.mk Q
  simpa only [Set.inducedHomInclusion] using (S.inducedHomInclusion Q).mapPath p

@[simp]
theorem coeInduced_nil {S : Set V} (s : S) :
    coeInduced (Q := Q) (nil s) = nil (Q := Q) (s : V) :=
  (rfl)

@[simp]
theorem coeInduced_cons {S : Set V} {s t x : S} (p : ArrowWalk (S.inducedHom Q) s t)
    (e : S.inducedHom Q t x) : coeInduced (p.cons e) =
      (coeInduced p).cons (show Q t x from e) :=
  (rfl)

@[simp]
theorem vertices_coeInduced {S : Set V} {s t : S}
    (p : ArrowWalk (S.inducedHom Q) s t) :
    (coeInduced p).vertices = p.vertices.map Subtype.val := by
  exact @Prefunctor.vertices_mapPath S V
    (Quiver.mk fun x y ↦ S.inducedHom Q x y) (Quiver.mk Q) (S.inducedHomInclusion Q) s t p

/-- A walk all of whose vertices lie in `S` lifts to the induced arrow family on `S`, without
changing its ambient walk. -/
theorem exists_induced_coe_eq {S : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hs : s ∈ S) (ht : t ∈ S) (hp : ∀ x ∈ p.vertices, x ∈ S) :
    ∃ p' : ArrowWalk (S.inducedHom Q) ⟨s, hs⟩ ⟨t, ht⟩, p'.coeInduced = p := by
  induction p with
  | nil => exact ⟨.nil _, coeInduced_nil _⟩
  | @cons x y p e ih =>
      -- The path recursor exposes `p` and `e` through its local quiver instance.
      change ArrowWalk Q s x at p
      change Q x y at e
      have hx : x ∈ S := hp x (by simp)
      have hy : y ∈ S := hp y (by simp)
      have hp' : ∀ z ∈ p.vertices, z ∈ S := fun z hz ↦ hp z (by
        rw [vertices_cons, List.concat_eq_append, List.mem_append]
        exact .inl hz)
      obtain ⟨p', rfl⟩ := ih hx hp'
      let e' : S.inducedHom Q ⟨x, hx⟩ ⟨y, hy⟩ := e
      refine ⟨p'.cons e', ?_⟩
      rw [coeInduced_cons]

end ArrowWalk

namespace Set

variable {S : Set V} {X : Set S} {s t : S}

/-- Avoiding `X` in the arrow family induced on `S` is the same as avoiding the discarded
vertices and the ambient image of `X` in the original arrow family. -/
theorem reachableAvoiding_inducedHom_iff :
    ReachableAvoiding (S.inducedHom Q) X s t ↔
      ReachableAvoiding Q (Sᶜ ∪ Subtype.val '' X) s t := by
  rw [reachableAvoiding_def, reachableAvoiding_def]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.coeInduced, fun x hx ↦ ?_⟩
    rw [ArrowWalk.vertices_coeInduced, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rintro (hSc | ⟨z, hz, hzy⟩)
    · exact hSc y.2
    · have hzy' : z = y := Subtype.ext hzy
      exact hp y hy (hzy' ▸ hz)
  · rintro ⟨p, hp⟩
    have hs : (s : V) ∈ S := s.2
    have ht : (t : V) ∈ S := t.2
    have hmem : ∀ x ∈ p.vertices, x ∈ S := fun x hx ↦ by
      by_contra hxc
      exact hp x hx (.inl (by simpa using hxc))
    obtain ⟨p', hp'⟩ := p.exists_induced_coe_eq hs ht hmem
    refine ⟨p', fun x hx hX ↦ ?_⟩
    exact hp x.1 (by rw [← hp', ArrowWalk.vertices_coeInduced]; exact List.mem_map.2 ⟨x, hx, rfl⟩)
      (.inr ⟨x, hX, rfl⟩)

end Set

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
    have hsZ : (s : V) ∉ Z := by
      rintro hmem
      rcases mem_union.1 hmem with hmem | hmem
      · exact s.2 hmem
      · obtain ⟨y, hy, hys⟩ := mem_image.1 hmem
        exact hs ((Subtype.ext hys).symm ▸ hy)
    have htZ : (t : V) ∉ Z := by
      rintro hmem
      rcases mem_union.1 hmem with hmem | hmem
      · exact t.2 hmem
      · obtain ⟨y, hy, hyt⟩ := mem_image.1 hmem
        exact ht ((Subtype.ext hyt).symm ▸ hy)
    have hr := h.2 Z hZ hsZ htZ
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
          ((show (0 : ℕ∞) ≤ (k - #X : ℕ) from zero_le).trans_lt hdel.lt_card)
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
