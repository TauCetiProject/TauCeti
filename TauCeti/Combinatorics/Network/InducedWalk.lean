/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Walk

/-!
# Walks in induced arrow families

Restricting an arrow family to a set of vertices retains exactly the arrows whose endpoints lie in
that set. This file transports walks between an induced family and its ambient family and identifies
reachability in the restricted family with ambient reachability avoiding the discarded vertices.

## Main results

* `Set.inducedHom`: the arrow family induced on a vertex set.
* `TauCeti.ArrowWalk.coeInduced`: the ambient walk underlying a walk in an induced family.
* `TauCeti.Set.reachableAvoiding_inducedHom_iff`: reachability in an induced family is ambient
  reachability avoiding both discarded vertices and a further set of induced vertices.
-/

public section

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
    (e : S.inducedHom Q t x) : coeInduced (p.cons e) = (coeInduced p).cons e :=
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

end TauCeti
