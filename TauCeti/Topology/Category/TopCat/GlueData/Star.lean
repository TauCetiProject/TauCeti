/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing

/-!
# Star gluing about a common centre

Let `X` be a space, the *centre*, and let `U i` be a family of spaces, the *pieces*. Attach each
piece to the centre by a homeomorphism `ψ i : W i ≃ₜ A i` from an open subset `W i` of the piece
onto an open subset `A i` of the centre. The star gluing `TauCeti.starGlueData ψ` glues the
pieces so that every identification passes through the centre: a point of `W i` and a point of
`W j` are identified exactly when `ψ i` and `ψ j` send them to the same point of `X`
(`TauCeti.starGlueData_ι_eq_iff`). Points outside `W i` are identified with nothing else.
Accordingly, the overlap of the pieces `i ≠ j` is the open set of points of `W i` whose image lies
in `A j`, and the transition to the piece `j` is `ψ j⁻¹ ∘ ψ i`. The cocycle condition holds
because all these transitions factor through `X`.

Two distinct pieces overlap exactly when their images in `X` meet
(`TauCeti.nonempty_starGlueData_V_iff`). The centre need not be one of the pieces. When it is, as a
piece with `W = A = ⊤` attached by the identity, the other pieces are arms attached to this hub,
and arms with pairwise disjoint images in the hub meet only the hub: the overlap graph of the
gluing is a star.
For instance, two copies of `X` attached to it by the identity along an open subset `U` are glued
along `U` by the identity, as in the double of `X` along `U`.

The glued space is Mathlib's `TopCat.GlueData` carrier, built with `TopCat.GlueData.mk'`.

## Main declarations

* `TauCeti.starGlueData`: the pieces `U i` glued about the centre `X` along the `ψ i`.
* `TauCeti.starGlueData_ι_eq_iff`, `TauCeti.starGlueData_ι_eq_iff_of_ne`: the gluing
  relation.
* `TauCeti.nonempty_starGlueData_V_iff`: distinct pieces overlap exactly when their images in the
  centre meet.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
-/

public section

open CategoryTheory TopologicalSpace Set Topology

universe u

namespace TauCeti

variable {J : Type u} {X : Type*} [TopologicalSpace X] {U : J → Type u}
  [∀ i, TopologicalSpace (U i)] {W : ∀ i, Opens (U i)} {A : J → Opens X}
  (ψ : ∀ i, W i ≃ₜ A i)

/-- The overlap of the pieces `i` and `j` of a star gluing, as an open subset of the piece `i`:
all of it if `i = j`, and otherwise the points of `W i` sent by `ψ i` into `A j`. -/
def starOverlap (i j : J) : Opens (U i) where
  carrier := {y | i = j ∨ ∃ h : y ∈ W i, (ψ i ⟨y, h⟩ : X) ∈ A j}
  is_open' := by
    have : IsOpen {y : U i | ∃ h : y ∈ W i, (ψ i ⟨y, h⟩ : X) ∈ A j} := by
      have hc : Continuous fun y : W i ↦ (ψ i y : X) := by fun_prop
      convert (W i).isOpen.isOpenMap_subtypeVal _ ((A j).isOpen.preimage hc) using 1
      ext y
      simp
    by_cases h : i = j
    · simp [h]
    · simpa [h] using this

variable {ψ} in
/-- A point of the piece `i` lies in its overlap with the piece `j` exactly when `i = j` or it lies
in `W i` and `ψ i` sends it into `A j`. -/
@[simp]
theorem mem_starOverlap {i j : J} {y : U i} :
    y ∈ starOverlap ψ i j ↔ i = j ∨ ∃ h : y ∈ W i, (ψ i ⟨y, h⟩ : X) ∈ A j :=
  Iff.rfl

/-- The overlap of a piece of a star gluing with itself is the whole piece. -/
@[simp]
theorem starOverlap_self (i : J) : starOverlap ψ i i = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_starOverlap.2 (Or.inl rfl)

/-- The transition from the overlap of the pieces `i` and `j` of a star gluing to the overlap of
`j` and `i`: the identity if `i = j`, and `ψ j⁻¹ ∘ ψ i` otherwise. -/
noncomputable def starTransition (i j : J) :
    C(starOverlap ψ i j, starOverlap ψ j i) := by
  classical
  refine if h : i = j then by subst h; exact ContinuousMap.id _ else ?_
  have hx (x : starOverlap ψ i j) : ∃ h : (x : U i) ∈ W i, (ψ i ⟨x, h⟩ : X) ∈ A j :=
    (mem_starOverlap.1 x.property).resolve_left h
  -- The point of `A j` to which `ψ i` sends a point of the overlap.
  let a : C(starOverlap ψ i j, A j) :=
    ⟨fun x ↦ ⟨ψ i ⟨x, (hx x).1⟩, (hx x).2⟩, by
      fun_prop⟩
  exact ⟨fun x ↦ ⟨((ψ j).symm (a x) : U j),
    mem_starOverlap.2 <| .inr ⟨((ψ j).symm _).property, by simp [a]⟩⟩, by fun_prop⟩

/-- The transition from a piece of a star gluing to itself is the identity. -/
@[simp]
theorem starTransition_self (i : J) : starTransition ψ i i = ContinuousMap.id _ := by
  simp [starTransition]

variable {ψ}

/-- The transition between distinct pieces of a star gluing is `ψ j⁻¹ ∘ ψ i`. -/
theorem coe_starTransition_apply_of_ne {i j : J} (hij : i ≠ j) (x : starOverlap ψ i j)
    (hx : (x : U i) ∈ W i) (hA : (ψ i ⟨x, hx⟩ : X) ∈ A j) :
    (starTransition ψ i j x : U j) = (ψ j).symm ⟨ψ i ⟨x, hx⟩, hA⟩ := by
  simp [starTransition, hij]

/-- The transition of a star gluing sends a point of the attaching set `W i` of the piece `i` into
the attaching set `W j` of the piece `j`. -/
theorem starTransition_mem {i j : J} (x : starOverlap ψ i j) (hx : (x : U i) ∈ W i) :
    (starTransition ψ i j x : U j) ∈ W j := by
  by_cases hij : i = j
  · subst hij
    simpa using hx
  · have hA := ((mem_starOverlap.1 x.property).resolve_left hij).2
    rw [coe_starTransition_apply_of_ne hij x hx hA]
    exact Subtype.prop _

/-- The transitions of a star gluing commute with the attaching maps to the centre. -/
theorem apply_starTransition {i j : J} (x : starOverlap ψ i j) (hx : (x : U i) ∈ W i)
    (h : (starTransition ψ i j x : U j) ∈ W j) :
    (ψ j ⟨starTransition ψ i j x, h⟩ : X) = ψ i ⟨x, hx⟩ := by
  by_cases hij : i = j
  · subst hij
    simp
  · have hA := ((mem_starOverlap.1 x.property).resolve_left hij).2
    simp_rw [coe_starTransition_apply_of_ne hij x hx hA]
    simp

/-- The overlap of distinct pieces `i` and `j` of a star gluing lies in the attaching set of `i`. -/
theorem starOverlap_le {i j : J} (hij : i ≠ j) : starOverlap ψ i j ≤ W i :=
  fun _ hy ↦ ((mem_starOverlap.1 hy).resolve_left hij).1

/-- A point of a piece of a star gluing outside its attaching set lies only in the overlap of the
piece with itself. -/
theorem eq_of_mem_starOverlap_of_notMem {i j : J} {y : U i} (hy : y ∈ starOverlap ψ i j)
    (hW : y ∉ W i) : i = j :=
  (mem_starOverlap.1 hy).resolve_right fun ⟨h, _⟩ ↦ hW h

/-- Two points of the attaching set of a piece with the same image in the centre are equal. -/
private theorem eq_of_apply_eq {i : J} {y z : U i} (hy : y ∈ W i) (hz : z ∈ W i)
    (h : (ψ i ⟨y, hy⟩ : X) = ψ i ⟨z, hz⟩) : y = z :=
  congrArg Subtype.val ((ψ i).injective (Subtype.ext h))

/-- The transition from the overlap of the pieces `i` and `j` of a star gluing sends its
intersection with the overlap of `i` and `k` into the overlap of `j` and `k`. -/
theorem starTransition_mem_starOverlap {i j k : J} (x : starOverlap ψ i j)
    (hxk : (x : U i) ∈ starOverlap ψ i k) : (starTransition ψ i j x : U j) ∈ starOverlap ψ j k := by
  by_cases hjk : j = k
  · exact Or.inl hjk
  by_cases hW : (x : U i) ∈ W i
  · refine Or.inr ⟨starTransition_mem x hW, ?_⟩
    rw [apply_starTransition x hW]
    rcases mem_starOverlap.1 hxk with rfl | ⟨_, hA⟩
    · exact Subtype.prop _
    · exact hA
  · exact absurd ((eq_of_mem_starOverlap_of_notMem x.property hW).symm.trans
      (eq_of_mem_starOverlap_of_notMem hxk hW)) hjk

/-- **The cocycle condition of a star gluing.** The transition from `i` to `j` followed by the
transition from `j` to `k` is the transition from `i` to `k`. -/
theorem starTransition_starTransition {i j k : J} (x : starOverlap ψ i j)
    (hxk : (x : U i) ∈ starOverlap ψ i k) :
    (starTransition ψ j k ⟨starTransition ψ i j x, starTransition_mem_starOverlap x hxk⟩ : U k) =
      starTransition ψ i k ⟨x, hxk⟩ := by
  by_cases hW : (x : U i) ∈ W i
  · -- Both points lie in `W k` and have the image of `x` under `ψ i` as image under `ψ k`.
    refine eq_of_apply_eq (ψ := ψ) (starTransition_mem _ (starTransition_mem x hW))
      (starTransition_mem _ hW) ?_
    rw [apply_starTransition (⟨_, starTransition_mem_starOverlap x hxk⟩ : starOverlap ψ j k)
      (starTransition_mem x hW), apply_starTransition x hW,
      apply_starTransition (⟨x, hxk⟩ : starOverlap ψ i k) hW]
  · -- Otherwise `x` lies only in the overlap of its piece with itself, and all transitions are
    -- the identity.
    obtain rfl := eq_of_mem_starOverlap_of_notMem x.property hW
    obtain rfl := eq_of_mem_starOverlap_of_notMem hxk hW
    simp

variable (ψ)

/-- The star gluing of the pieces `U i` about the centre `X`: the piece `i` is attached to `X` by
the homeomorphism `ψ i` from its open subset `W i` onto the open subset `A i` of `X`, and two
pieces are glued along the points they attach to the same points of `X`. -/
@[expose] noncomputable def starGlueData : TopCat.GlueData.{u} :=
  TopCat.GlueData.mk'
    { J := J
      U := fun i ↦ TopCat.of (U i)
      V := fun i j ↦ starOverlap ψ i j
      t := fun i j ↦ TopCat.ofHom (starTransition ψ i j)
      V_id := starOverlap_self ψ
      t_id := fun i ↦ congrArg (DFunLike.coe (F := C(starOverlap ψ i i, starOverlap ψ i i)))
        (starTransition_self ψ i)
      t_inter := fun _ _ _ x hxk ↦ starTransition_mem_starOverlap x hxk
      cocycle := fun _ _ _ x hxk ↦ starTransition_starTransition x hxk }

/-- The pieces of a star gluing are indexed by `J`. -/
@[simp] theorem starGlueData_J : (starGlueData ψ).J = J := (rfl)

/-- The pieces of a star gluing are the spaces `U i`. -/
@[simp] theorem starGlueData_U (i : J) :
    (starGlueData ψ).U i = TopCat.of (U i) := (rfl)

/-- The overlap of the pieces `i` and `j` of a star gluing is `starOverlap ψ i j`. -/
@[simp] theorem starGlueData_V (i j : J) :
    (starGlueData ψ).V (i, j) = TopCat.of (starOverlap ψ i j) := (rfl)

/-- The overlap of the pieces `i` and `j` of a star gluing includes into the piece `i` as an open
subset. -/
@[simp] theorem starGlueData_f (i j : J) :
    (starGlueData ψ).f i j =
      TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(starOverlap ψ i j, U i)) :=
  (rfl)

/-- The transition maps of a star gluing are the maps `starTransition ψ i j`. -/
@[simp] theorem starGlueData_t (i j : J) :
    (starGlueData ψ).t i j = TopCat.ofHom (starTransition ψ i j) :=
  (rfl)

variable {ψ}

/-- Points of the pieces `i` and `j` of a star gluing are identified in the glued space exactly
when they are a point of the overlap `starOverlap ψ i j` and its transition. -/
theorem starGlueData_ι_eq_iff_exists {i j : J} {x : U i} {y : U j} :
    (starGlueData ψ).toGlueData.ι i x = (starGlueData ψ).toGlueData.ι j y ↔
      ∃ z : starOverlap ψ i j, (z : U i) = x ∧ (starTransition ψ i j z : U j) = y :=
  -- This is `TopCat.GlueData.ι_eq_iff_rel`, whose overlaps and maps are those of
  -- `starGlueData_V`, `starGlueData_f` and `starGlueData_t` by definition.
  (starGlueData ψ).ι_eq_iff_rel i j x y

/-- **The gluing relation of a star gluing.** Points of the attaching sets of two pieces are
identified in the glued space exactly when they have the same image in the centre. -/
@[grind =]
theorem starGlueData_ι_eq_iff {i j : J} {x : U i} {y : U j} (hx : x ∈ W i) (hy : y ∈ W j) :
    (starGlueData ψ).toGlueData.ι i x = (starGlueData ψ).toGlueData.ι j y ↔
      (ψ i ⟨x, hx⟩ : X) = ψ j ⟨y, hy⟩ := by
  refine starGlueData_ι_eq_iff_exists.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨z, rfl, rfl⟩
    exact (apply_starTransition z hx hy).symm
  · -- The point `x` lies in the overlap of `i` and `j`, and its transition is `y`.
    have hz : x ∈ starOverlap ψ i j := by
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr ⟨hx, h ▸ (ψ j _).property⟩
    refine ⟨⟨x, hz⟩, rfl, eq_of_apply_eq (ψ := ψ) (starTransition_mem ⟨x, hz⟩ hx) hy ?_⟩
    rw [apply_starTransition ⟨x, hz⟩ hx, h]

/-- Points of two distinct pieces of a star gluing are identified in the glued space exactly when
they lie in the attaching sets and have the same image in the centre. -/
@[simp, grind =]
theorem starGlueData_ι_eq_iff_of_ne {i j : J} (hij : i ≠ j) {x : U i} {y : U j} :
    (starGlueData ψ).toGlueData.ι i x = (starGlueData ψ).toGlueData.ι j y ↔
      ∃ (hx : x ∈ W i) (hy : y ∈ W j), (ψ i ⟨x, hx⟩ : X) = ψ j ⟨y, hy⟩ := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy, h⟩ ↦ (starGlueData_ι_eq_iff hx hy).2 h⟩
  obtain ⟨z, rfl, rfl⟩ := starGlueData_ι_eq_iff_exists.1 h
  have hz : (z : U i) ∈ W i := starOverlap_le hij z.property
  exact ⟨hz, starTransition_mem z hz, (starGlueData_ι_eq_iff _ _).1 h⟩

/-- Two distinct pieces of a star gluing overlap exactly when their images in the centre meet.
In particular, when the centre is one of the pieces, pieces with pairwise disjoint images meet
only the centre. -/
theorem nonempty_starGlueData_V_iff {i j : J} (hij : i ≠ j) :
    Nonempty ((starGlueData ψ).V (i, j)) ↔ ((A i : Set X) ∩ A j).Nonempty := by
  rw [starGlueData_V]
  refine ⟨fun ⟨z⟩ ↦ ?_, fun ⟨a, hai, haj⟩ ↦ ?_⟩
  · obtain ⟨hz, hA⟩ := (mem_starOverlap.1 z.property).resolve_left hij
    exact ⟨_, (ψ i _).property, hA⟩
  · -- The point of `W i` sent to `a` by `ψ i` lies in the overlap.
    refine ⟨⟨((ψ i).symm ⟨a, hai⟩ : U i), Or.inr ⟨((ψ i).symm _).property, ?_⟩⟩⟩
    simpa using haj

end TauCeti
