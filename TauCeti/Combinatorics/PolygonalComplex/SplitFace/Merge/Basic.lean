/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Iso
public import TauCeti.Combinatorics.PolygonalComplex.SplitFace.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring

/-!
# Merging two faces of a polygonal complex

Merging two faces `g₁ = X d` and `g₂ = d⁻¹ Y` of a polygonal complex along their common side `d`
deletes the edge of `d` and replaces the two faces by the single face `X Y`. This is the operation
(P2)⁻¹ of Gallier and Xu, the inverse of splitting a face along a fresh side. It applies when the
two faces are distinct, the last side of `g₁` is traversed backwards by the first side of `g₂`,
these are the only two side occurrences along the edge of `d`, and the merged face `X Y` is
nonempty (`PolygonalComplex.IsMergeable`); either of `X` and `Y` may be empty. Faces sharing a side
in other positions are brought into this one by changing their starting points and orientations.

The one-skeleton of `C.mergeFaces h` is `C.graph.deleteEdge d`. Its faces are the faces of `C`
other than `g₁` and `g₂`, together with `none` for the merged face `X Y`. The side occurrences of
`C` are those of the merged complex and the two occurrences of `d`
(`PolygonalComplex.mergeFacesCornerEquiv`), so the remaining darts keep their side counts and link
degrees. Away from the two corners where `X` and `Y` meet, the
corners of the merged face keep both of their sides (`PolygonalComplex.coe_incoming_mergeFaces`).
The move removes one edge and one face, so the Euler characteristic is unchanged, and it does not
change orientability: in an orientation of `C` the faces `g₁` and `g₂` are oriented alike, since
they traverse `d` in opposite directions, and the merged face takes their common orientation.

Merging undoes splitting. The two new faces `a₀ ⋯ aₚ₋₁ d` and `d⁻¹ aₚ ⋯ aₙ₋₁` of `C.splitFace f p`
can be merged (`PolygonalComplex.isMergeable_splitFace`), and merging them gives back `C` up to an
isomorphism of polygonal complexes which is the identity on vertices and keeps the orientation and
the starting point of every face (`PolygonalComplex.mergeFacesSplitFaceIso`). Conversely, when `Y`
is nonempty, splitting the merged face of `C.mergeFaces h` at the corner where `Y` starts gives
back `C` in the same sense (`PolygonalComplex.splitFaceMergeFacesIso`). When `Y` is empty the pair
`X d`, `d⁻¹` is not of the form produced by a split, whose second face always has at least two
sides.

## Main definitions

* `TauCeti.PolygonalComplex.IsMergeable`: two faces can be merged along the last side of the
  first.
* `TauCeti.PolygonalComplex.mergeFaces`: the complex obtained by merging two faces.
* `TauCeti.PolygonalComplex.mergeFacesCornerEquiv`: the side occurrences of `C` are those of the
  merged complex and the two occurrences of the deleted edge.
* `TauCeti.PolygonalComplex.mergeFacesSplitFaceIso`,
  `TauCeti.PolygonalComplex.splitFaceMergeFacesIso`: merging the two faces of a split face, and
  splitting a merged face, give back the original complex up to isomorphism. Their side
  bijections are `TauCeti.PolygonalComplex.mergeFacesSplitFaceCornerEquiv` and
  `TauCeti.PolygonalComplex.splitFaceMergeFacesCornerEquiv`.

## Main results

* `TauCeti.PolygonalComplex.sideCount_mergeFaces`, `TauCeti.PolygonalComplex.linkDegree_mergeFaces`:
  the remaining darts keep their side counts and link degrees.
* `TauCeti.PolygonalComplex.mergeFacesCornerOrigin_prevCorner`,
  `TauCeti.PolygonalComplex.coe_incoming_mergeFaces`: away from the two corners where `X` and `Y`
  meet, the corners of the merged face are those of `g₁` and `g₂`.
* `TauCeti.PolygonalComplex.eulerChar_mergeFaces`: the Euler characteristic is unchanged.
* `TauCeti.PolygonalComplex.isOrientable_mergeFaces_iff`: orientability is unchanged.
* `TauCeti.PolygonalComplex.isMergeable_splitFace`: the two new faces of a split face can be merged.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P2), its inverse (P2)⁻¹ before Lemma 6.1, and the
  invariance of orientability and of the Euler characteristic after Definition 6.4.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w})

/-! ### Mergeable faces -/

/-- The faces `g₁ = X d` and `g₂ = d⁻¹ Y` of `C` can be merged along the last side `d` of `g₁`:
they are distinct, the first side of `g₂` traverses `d` backwards, these two side occurrences are
the only ones along the edge of `d`, and the merged face `X Y` is nonempty. The two new faces of a
split face are an example (`PolygonalComplex.isMergeable_splitFace`). -/
structure IsMergeable (g₁ g₂ : C.Face) : Prop where
  /-- The two faces are distinct. -/
  ne : g₁ ≠ g₂
  /-- The merged face `X Y` has at least one side. -/
  two_lt_sides_add_sides : 2 < C.sides g₁ + C.sides g₂
  /-- The first side of `g₂` traverses the last side of `g₁` backwards. -/
  outgoing_eq : C.outgoing ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ =
    C.graph.rev (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
  /-- The last side of `g₁` and the first side of `g₂` are the only side occurrences along the
  edge of the last side of `g₁`. -/
  eq_or_eq_of_toGeomEdge_eq : ∀ c : C.Corner, C.graph.toGeomEdge (C.outgoing c) =
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) →
    c = C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ ∨ c = ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩

variable (g₁ g₂ : C.Face)

/-- The numbers of sides of the faces of the merged complex: the faces other than `g₁` and `g₂`
keep their sides, and the merged face `X Y` has `sides g₁ + sides g₂ - 2`. It is reducible, so that
the positions along the faces of the merged complex are indices in these explicit ranges. -/
abbrev mergeFacesSides : Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂} → ℕ
  | none => C.sides g₁ + C.sides g₂ - 2
  | some g => C.sides g.1

/-- The side occurrence of `C` at a position along a face of the merged complex. On the merged
face `X Y`, the positions before `sides g₁ - 1` are the sides of `X`, those of `g₁`, and the
position `k ≥ sides g₁ - 1` is the side `k + 2 - sides g₁` of `g₂`. -/
def mergeFacesCornerOrigin :
    (Σ g : Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂}, Fin (C.mergeFacesSides g₁ g₂ g)) → C.Corner
  | ⟨some g, k⟩ => ⟨g.1, k⟩
  | ⟨none, k⟩ => if hk : (k : ℕ) < C.sides g₁ - 1 then ⟨g₁, ⟨k, by omega⟩⟩ else
      ⟨g₂, ⟨k + 2 - C.sides g₁, by
        have : (k : ℕ) < C.sides g₁ + C.sides g₂ - 2 := k.2
        have := C.sides_pos g₁
        omega⟩⟩

variable {C g₁ g₂}

@[simp] theorem mergeFacesCornerOrigin_some (g : {g : C.Face // g ≠ g₁ ∧ g ≠ g₂})
    (k : Fin (C.sides g.1)) : C.mergeFacesCornerOrigin g₁ g₂ ⟨some g, k⟩ = ⟨g.1, k⟩ :=
  (rfl)

theorem mergeFacesCornerOrigin_none_of_lt {k : Fin (C.mergeFacesSides g₁ g₂ none)}
    (hk : (k : ℕ) < C.sides g₁ - 1) :
    C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩ = ⟨g₁, ⟨k, by omega⟩⟩ := by
  simp [mergeFacesCornerOrigin, hk]

theorem mergeFacesCornerOrigin_none_of_not_lt {k : Fin (C.mergeFacesSides g₁ g₂ none)}
    (hk : ¬(k : ℕ) < C.sides g₁ - 1) :
    C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩ = ⟨g₂, ⟨k + 2 - C.sides g₁, by
      have : (k : ℕ) < C.sides g₁ + C.sides g₂ - 2 := k.2
      have := C.sides_pos g₁
      omega⟩⟩ := by
  simp [mergeFacesCornerOrigin, hk]

/-- When `Y` is nonempty, the merged face `X Y` has a corner at the position `sides g₁ - 1`, where
`Y` starts. -/
theorem sides_sub_one_lt_mergeFacesSides (h₂ : 1 < C.sides g₂) :
    C.sides g₁ - 1 < C.mergeFacesSides g₁ g₂ none := by
  have := C.sides_pos g₁
  simp only [mergeFacesSides]
  omega

/-- The merged face consists of corners of `g₁` and `g₂`. -/
private theorem mergeFacesCornerOrigin_none_fst (k : Fin (C.mergeFacesSides g₁ g₂ none)) :
    (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩).1 = g₁ ∨
      (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩).1 = g₂ := by
  by_cases hk : (k : ℕ) < C.sides g₁ - 1
  · exact .inl (by rw [mergeFacesCornerOrigin_none_of_lt hk])
  · exact .inr (by rw [mergeFacesCornerOrigin_none_of_not_lt hk])

/-- Distinct side occurrences of the merged complex come from distinct side occurrences of `C`. -/
theorem mergeFacesCornerOrigin_injective (hne : g₁ ≠ g₂) :
    Function.Injective (C.mergeFacesCornerOrigin g₁ g₂) := by
  rintro ⟨_ | g, k⟩ ⟨_ | g', k'⟩ hkk
  · refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
    dsimp only
    by_cases hk : (k : ℕ) < C.sides g₁ - 1 <;> by_cases hk' : (k' : ℕ) < C.sides g₁ - 1
    · rw [mergeFacesCornerOrigin_none_of_lt hk, mergeFacesCornerOrigin_none_of_lt hk'] at hkk
      simpa using hkk
    · rw [mergeFacesCornerOrigin_none_of_lt hk, mergeFacesCornerOrigin_none_of_not_lt hk'] at hkk
      exact absurd (congrArg Sigma.fst hkk) hne
    · rw [mergeFacesCornerOrigin_none_of_not_lt hk, mergeFacesCornerOrigin_none_of_lt hk'] at hkk
      exact absurd (congrArg Sigma.fst hkk).symm hne
    · rw [mergeFacesCornerOrigin_none_of_not_lt hk, mergeFacesCornerOrigin_none_of_not_lt hk']
        at hkk
      simp only [Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and] at hkk
      omega
  · have := congrArg Sigma.fst hkk
    rcases mergeFacesCornerOrigin_none_fst k with h₁ | h₁ <;> rw [h₁] at this
    exacts [absurd this.symm g'.2.1, absurd this.symm g'.2.2]
  · have := congrArg Sigma.fst hkk
    rcases mergeFacesCornerOrigin_none_fst k' with h₁ | h₁ <;> rw [h₁] at this
    exacts [absurd this g.2.1, absurd this g.2.2]
  · simp only [mergeFacesCornerOrigin_some, Sigma.mk.injEq] at hkk
    obtain ⟨hg, hk⟩ := hkk
    obtain rfl := Subtype.ext hg
    obtain rfl := eq_of_heq hk
    rfl

/-- The last side of `g₁` is not a side of the merged complex. -/
theorem mergeFacesCornerOrigin_ne_prevCorner (hne : g₁ ≠ g₂) (c) :
    C.mergeFacesCornerOrigin g₁ g₂ c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ := by
  rw [prevCorner_mk_zero]
  obtain ⟨_ | g, k⟩ := c
  · by_cases hk : (k : ℕ) < C.sides g₁ - 1
    · rw [mergeFacesCornerOrigin_none_of_lt hk]
      simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and]
      omega
    · rw [mergeFacesCornerOrigin_none_of_not_lt hk]
      exact fun he => hne (congrArg Sigma.fst he).symm
  · exact fun he => g.2.1 (congrArg Sigma.fst he)

/-- The first side of `g₂` is not a side of the merged complex. -/
theorem mergeFacesCornerOrigin_ne_mk_zero (hne : g₁ ≠ g₂) (c) :
    C.mergeFacesCornerOrigin g₁ g₂ c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ := by
  obtain ⟨_ | g, k⟩ := c
  · by_cases hk : (k : ℕ) < C.sides g₁ - 1
    · rw [mergeFacesCornerOrigin_none_of_lt hk]
      exact fun he => hne (congrArg Sigma.fst he)
    · rw [mergeFacesCornerOrigin_none_of_not_lt hk]
      simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and]
      omega
  · exact fun he => g.2.2 (congrArg Sigma.fst he)

/-- Every side occurrence of `C` other than the two occurrences of `d` is a side occurrence of the
merged complex. -/
theorem exists_mergeFacesCornerOrigin_eq {c : C.Corner}
    (h₁ : c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) (h₂ : c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) :
    ∃ c', C.mergeFacesCornerOrigin g₁ g₂ c' = c := by
  obtain ⟨g, k⟩ := c
  have := C.sides_pos g₁
  have := C.sides_pos g₂
  have hk := k.2
  by_cases hg₁ : g = g₁
  · subst hg₁
    rw [prevCorner_mk_zero] at h₁
    have hk' : (k : ℕ) < C.sides g - 1 := by
      by_contra hk'
      exact h₁ (Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega))))
    exact ⟨⟨none, ⟨k, by simp only [mergeFacesSides]; omega⟩⟩, by
      rw [mergeFacesCornerOrigin_none_of_lt hk']⟩
  by_cases hg₂ : g = g₂
  · subst hg₂
    have hk0 : (k : ℕ) ≠ 0 := fun hk0 => h₂ (Sigma.ext rfl (heq_of_eq (Fin.ext hk0)))
    refine ⟨⟨none, ⟨k + C.sides g₁ - 2, by simp only [mergeFacesSides]; omega⟩⟩, ?_⟩
    rw [mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega)]
    exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega)))
  · exact ⟨⟨some ⟨g, hg₁, hg₂⟩, k⟩, rfl⟩

namespace IsMergeable

variable (h : C.IsMergeable g₁ g₂)
include h

/-- The sides of the merged complex do not run along the edge of `d`. -/
theorem toGeomEdge_outgoing_mergeFacesCornerOrigin_ne (c) :
    C.graph.toGeomEdge (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c)) ≠
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := fun he =>
  (h.eq_or_eq_of_toGeomEdge_eq _ he).elim (mergeFacesCornerOrigin_ne_prevCorner h.ne c)
    (mergeFacesCornerOrigin_ne_mk_zero h.ne c)

end IsMergeable

/-! ### The merged complex -/

variable (C) in
/-- The dart of `C.graph.deleteEdge d` along which a side of a face of the merged complex is
attached. -/
def mergeFacesSide (h : C.IsMergeable g₁ g₂) (g : Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂})
    (k : Fin (C.mergeFacesSides g₁ g₂ g)) :
    (C.graph.deleteEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)).E :=
  ⟨C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨g, k⟩),
    h.toGeomEdge_outgoing_mergeFacesCornerOrigin_ne _⟩

/-- The positions of `X` in the merged face are followed by the next side of `g₁`; the last
position of `X` is followed by the start of `Y`, at the source of `d`. -/
private theorem tgt_outgoing_mergeFacesCornerOrigin_of_lt (h : C.IsMergeable g₁ g₂)
    {k : Fin (C.mergeFacesSides g₁ g₂ none)} (hk : (k : ℕ) < C.sides g₁ - 1) :
    C.graph.tgt (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩)) =
      C.graph.src (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, finRotate _ k⟩)) := by
  have hr := Fin.coe_finRotate_eq_ite k
  have hN : C.mergeFacesSides g₁ g₂ none = C.sides g₁ + C.sides g₂ - 2 := rfl
  have := C.sides_pos g₁
  have := C.sides_pos g₂
  have hd := h.outgoing_eq
  rw [incoming_mk_zero, outgoing_def] at hd
  rw [mergeFacesCornerOrigin_none_of_lt hk, outgoing_def]
  by_cases hk1 : (k : ℕ) + 1 < C.sides g₁ - 1
  · rw [mergeFacesCornerOrigin_none_of_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
      outgoing_def]
    exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)
  rw [C.tgt_side_eq_src_side (f := g₁) (j := ⟨C.sides g₁ - 1, by omega⟩)
    (by dsimp only; split_ifs <;> omega)]
  by_cases hY : (k : ℕ) + 1 = C.sides g₁ + C.sides g₂ - 2
  · -- `Y` is empty: `g₂ = d⁻¹` is a monogon, so `d` is a loop, and the next position is `0`.
    have h₂ : C.sides g₂ = 1 := by omega
    rw [mergeFacesCornerOrigin_none_of_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
      outgoing_def, ← C.graph.tgt_rev, ← hd, C.tgt_side_eq_src_side_of_sides_eq_one h₂, hd,
      SerreGraph.src_rev]
    exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)
  · rw [mergeFacesCornerOrigin_none_of_not_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
      outgoing_def, ← C.graph.tgt_rev, ← hd]
    exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)

/-- The positions of `Y` in the merged face are followed by the next side of `g₂`; the last one is
followed by the start of `X`, at the target of `d`. -/
private theorem tgt_outgoing_mergeFacesCornerOrigin_of_not_lt (h : C.IsMergeable g₁ g₂)
    {k : Fin (C.mergeFacesSides g₁ g₂ none)} (hk : ¬(k : ℕ) < C.sides g₁ - 1) :
    C.graph.tgt (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, k⟩)) =
      C.graph.src (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨none, finRotate _ k⟩)) := by
  have hr := Fin.coe_finRotate_eq_ite k
  have hN : C.mergeFacesSides g₁ g₂ none = C.sides g₁ + C.sides g₂ - 2 := rfl
  have := C.sides_pos g₁
  have := C.sides_pos g₂
  have : (k : ℕ) < C.sides g₁ + C.sides g₂ - 2 := k.2
  have hd := h.outgoing_eq
  rw [incoming_mk_zero, outgoing_def] at hd
  rw [mergeFacesCornerOrigin_none_of_not_lt hk, outgoing_def]
  by_cases hX : (k : ℕ) + 1 = C.sides g₁ + C.sides g₂ - 2
  · rw [C.tgt_side_eq_src_side (j := ⟨0, C.sides_pos g₂⟩) (by dsimp only; split_ifs <;> omega),
      hd, SerreGraph.src_rev]
    by_cases h₁ : 1 < C.sides g₁
    · -- the next position is the start of `X`
      rw [mergeFacesCornerOrigin_none_of_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
        outgoing_def]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)
    · -- `X` is empty: `g₁ = d` is a monogon, so `d` is a loop
      rw [mergeFacesCornerOrigin_none_of_not_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
        outgoing_def, C.tgt_side_eq_src_side_of_sides_eq_one (f := g₁) (by omega),
        ← C.graph.tgt_rev, ← hd]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)
  · rw [mergeFacesCornerOrigin_none_of_not_lt (k := finRotate _ k) (by split_ifs at hr <;> omega),
      outgoing_def]
    exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)

/-- The sides of the faces of the merged complex form closed dart sequences. -/
private theorem tgt_outgoing_mergeFacesCornerOrigin (h : C.IsMergeable g₁ g₂)
    (g : Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂}) (k : Fin (C.mergeFacesSides g₁ g₂ g)) :
    C.graph.tgt (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨g, k⟩)) =
      C.graph.src (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ ⟨g, finRotate _ k⟩)) := by
  obtain _ | g := g
  · by_cases hk : (k : ℕ) < C.sides g₁ - 1
    exacts [tgt_outgoing_mergeFacesCornerOrigin_of_lt h hk,
      tgt_outgoing_mergeFacesCornerOrigin_of_not_lt h hk]
  · rw [mergeFacesCornerOrigin_some, mergeFacesCornerOrigin_some, outgoing_def, outgoing_def]
    exact C.tgt_side g.1 k

variable (C) in
/-- The polygonal complex obtained from `C` by merging the faces `g₁ = X d` and `g₂ = d⁻¹ Y` along
the last side `d` of `g₁`: the edge of `d` is deleted, and the two faces are replaced by the face
`none` attached along `X Y`. It is reducible, so that its one-skeleton and its faces are seen to be
`C.graph.deleteEdge d` and `Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂}`. -/
abbrev mergeFaces (h : C.IsMergeable g₁ g₂) : PolygonalComplex.{u, v, w} where
  graph := C.graph.deleteEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
  Face := Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂}
  sides := C.mergeFacesSides g₁ g₂
  sides_pos g := by
    obtain _ | g := g
    exacts [Nat.sub_pos_of_lt h.two_lt_sides_add_sides, C.sides_pos g.1]
  side := C.mergeFacesSide h
  tgt_side g k := by exact tgt_outgoing_mergeFacesCornerOrigin h g k

variable (h : C.IsMergeable g₁ g₂)

/-- Merging two faces of a complex with finitely many faces gives finitely many faces. -/
instance [Finite C.Face] : Finite (C.mergeFaces h).Face :=
  inferInstanceAs (Finite (Option {g : C.Face // g ≠ g₁ ∧ g ≠ g₂}))

/-! ### Side occurrences -/

/-- The dart of a side occurrence of the merged complex is the dart of the side occurrence of `C`
it comes from. -/
@[simp] theorem coe_outgoing_mergeFaces (c : (C.mergeFaces h).Corner) :
    ((C.mergeFaces h).outgoing c).1 = C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c) := by
  rw [outgoing_def]
  rfl

/-- The side occurrences of `C` are those of `C.mergeFaces h` together with the two occurrences of
the deleted edge: `Sum.inr true` is the last side `d` of `g₁` and `Sum.inr false` is the first side
`d⁻¹` of `g₂`. -/
noncomputable def mergeFacesCornerEquiv : (C.mergeFaces h).Corner ⊕ Bool ≃ C.Corner := by
  refine Equiv.ofBijective (Sum.elim (C.mergeFacesCornerOrigin g₁ g₂)
    fun b => cond b (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)
    ⟨(mergeFacesCornerOrigin_injective h.ne).sumElim (fun b b' hb => ?_) fun c b => ?_,
      fun c => ?_⟩
  · have hne : C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ :=
      fun he => h.ne (by simpa using congrArg Sigma.fst he)
    cases b <;> cases b' <;> first | rfl | exact absurd hb hne | exact absurd hb.symm hne
  · cases b
    exacts [mergeFacesCornerOrigin_ne_mk_zero h.ne c, mergeFacesCornerOrigin_ne_prevCorner h.ne c]
  · by_cases h₁ : c = C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩
    · exact ⟨.inr true, h₁.symm⟩
    by_cases h₂ : c = ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩
    · exact ⟨.inr false, h₂.symm⟩
    obtain ⟨c', hc'⟩ := exists_mergeFacesCornerOrigin_eq h₁ h₂
    exact ⟨.inl c', hc'⟩

@[simp] theorem mergeFacesCornerEquiv_inl (c : (C.mergeFaces h).Corner) :
    C.mergeFacesCornerEquiv h (.inl c) = C.mergeFacesCornerOrigin g₁ g₂ c :=
  (rfl)

@[simp] theorem mergeFacesCornerEquiv_inr (b : Bool) :
    C.mergeFacesCornerEquiv h (.inr b) =
      cond b (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ :=
  (rfl)

/-- A corner of the merged complex sits at the vertex of the corner of `C` it comes from. -/
@[simp] theorem cornerVertex_mergeFaces (c : (C.mergeFaces h).Corner) :
    (C.mergeFaces h).cornerVertex c = C.cornerVertex (C.mergeFacesCornerOrigin g₁ g₂ c) := by
  rw [← src_outgoing, ← src_outgoing, ← coe_outgoing_mergeFaces h c]

/-- Away from the two corners where `X` and `Y` meet, the corner preceding a corner of the merged
complex comes from the corner preceding the corner of `C` it comes from. These two corners are the
first corner `⟨g₁, 0⟩` of `X` and the corner `nextCorner ⟨g₂, 0⟩` of `g₂ = d⁻¹ Y` following
`d⁻¹`. -/
theorem mergeFacesCornerOrigin_prevCorner (c : (C.mergeFaces h).Corner)
    (h₁ : C.mergeFacesCornerOrigin g₁ g₂ c ≠ ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    (h₂ : C.mergeFacesCornerOrigin g₁ g₂ c ≠ C.nextCorner ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) :
    C.mergeFacesCornerOrigin g₁ g₂ ((C.mergeFaces h).prevCorner c) =
      C.prevCorner (C.mergeFacesCornerOrigin g₁ g₂ c) := by
  obtain ⟨_ | g, k⟩ := c
  · have := C.sides_pos g₁
    have hN : (C.mergeFaces h).sides none = C.sides g₁ + C.sides g₂ - 2 := rfl
    have hk : (k : ℕ) < C.sides g₁ + C.sides g₂ - 2 := k.2
    by_cases hk1 : (k : ℕ) < C.sides g₁ - 1
    · rw [mergeFacesCornerOrigin_none_of_lt hk1] at h₁ ⊢
      have hk0 : (k : ℕ) ≠ 0 := fun h0 => h₁ (Sigma.ext rfl (heq_of_eq (Fin.ext h0)))
      rw [(C.mergeFaces h).prevCorner_mk_of_ne_zero (i := ⟨k - 1, by omega⟩) hk0 rfl,
        mergeFacesCornerOrigin_none_of_lt (by dsimp only; omega),
        C.prevCorner_mk_of_ne_zero (i := ⟨k - 1, by omega⟩) hk0 rfl]
    · rw [mergeFacesCornerOrigin_none_of_not_lt hk1] at h₂ ⊢
      have hk2 : C.sides g₁ ≤ k := by
        by_contra hlt
        rw [nextCorner_def] at h₂
        refine h₂ (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
        have h0 := Fin.coe_finRotate_eq_ite (⟨0, C.sides_pos g₂⟩ : Fin (C.sides g₂))
        dsimp only at h0 ⊢
        split_ifs at h0 <;> omega
      rw [(C.mergeFaces h).prevCorner_mk_of_ne_zero (i := ⟨k - 1, by omega⟩) (by omega) rfl,
        mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega),
        C.prevCorner_mk_of_ne_zero (i := ⟨k + 1 - C.sides g₁, by omega⟩) (by dsimp only; omega)
          (by dsimp only; omega)]
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega)))
  · rw [prevCorner_def, prevCorner_def, mergeFacesCornerOrigin_some, mergeFacesCornerOrigin_some]

/-- Away from the two corners where `X` and `Y` meet, a corner of the merged complex has the
incoming side of the corner of `C` it comes from. -/
theorem coe_incoming_mergeFaces (c : (C.mergeFaces h).Corner)
    (h₁ : C.mergeFacesCornerOrigin g₁ g₂ c ≠ ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    (h₂ : C.mergeFacesCornerOrigin g₁ g₂ c ≠ C.nextCorner ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) :
    ((C.mergeFaces h).incoming c).1 = C.incoming (C.mergeFacesCornerOrigin g₁ g₂ c) := by
  rw [(C.mergeFaces h).incoming_eq_outgoing_prevCorner c, coe_outgoing_mergeFaces,
    mergeFacesCornerOrigin_prevCorner h c h₁ h₂,
    ← C.incoming_eq_outgoing_prevCorner (C.mergeFacesCornerOrigin g₁ g₂ c)]

/-- Two sides of the merged complex are attached along the same dart exactly when the sides of `C`
they come from are. -/
theorem outgoing_mergeFaces_eq_outgoing_iff {c c' : (C.mergeFaces h).Corner} :
    (C.mergeFaces h).outgoing c' = (C.mergeFaces h).outgoing c ↔
      C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c') =
        C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c) := by
  rw [Subtype.ext_iff, coe_outgoing_mergeFaces, coe_outgoing_mergeFaces]

/-- Two sides of the merged complex are attached along mutually reverse darts exactly when the
sides of `C` they come from are. -/
theorem outgoing_mergeFaces_eq_rev_iff {c c' : (C.mergeFaces h).Corner} :
    (C.mergeFaces h).outgoing c' = (C.mergeFaces h).graph.rev ((C.mergeFaces h).outgoing c) ↔
      C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c') =
        C.graph.rev (C.outgoing (C.mergeFacesCornerOrigin g₁ g₂ c)) := by
  rw [Subtype.ext_iff, coe_outgoing_mergeFaces, ← coe_outgoing_mergeFaces h c]

/-! ### Side counts, link degrees and the Euler characteristic -/

/-- The side occurrences of `C.mergeFaces h` attached along a remaining dart `e` are those of `C`
attached along `e`. -/
private noncomputable def outgoingFiberMergeFacesEquiv (e : (C.mergeFaces h).graph.E) :
    {c : (C.mergeFaces h).Corner // (C.mergeFaces h).outgoing c = e} ≃
      {c : C.Corner // C.outgoing c = e.1} := by
  refine Equiv.ofBijective (fun c => ⟨C.mergeFacesCornerOrigin g₁ g₂ c.1, by
    rw [← coe_outgoing_mergeFaces h, c.2]⟩) ⟨fun c c' hc => ?_, fun ⟨c, hc⟩ => ?_⟩
  · exact Subtype.ext (mergeFacesCornerOrigin_injective h.ne (congrArg Subtype.val hc))
  · have h₁ : c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ := by
      rintro rfl
      exact e.2 (by rw [← hc, ← incoming_eq_outgoing_prevCorner])
    have h₂ : c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ := by
      rintro rfl
      exact e.2 (by rw [← hc, h.outgoing_eq, SerreGraph.toGeomEdge_rev])
    obtain ⟨c', rfl⟩ := exists_mergeFacesCornerOrigin_eq h₁ h₂
    exact ⟨⟨c', Subtype.ext ((coe_outgoing_mergeFaces h c').trans hc)⟩, rfl⟩

/-- Merging two faces does not change the number of face sides attached along a remaining dart. -/
@[simp] theorem sideCount_mergeFaces (e : (C.mergeFaces h).graph.E) :
    (C.mergeFaces h).sideCount e = C.sideCount e.1 := by
  rw [sideCount_def, sideCount_def]
  exact Nat.card_congr (C.outgoingFiberMergeFacesEquiv h e)

/-- Merging two faces does not change the link degree of a remaining germ. -/
@[simp] theorem linkDegree_mergeFaces (e : (C.mergeFaces h).graph.E) :
    (C.mergeFaces h).linkDegree e = C.linkDegree e.1 := by
  rw [linkDegree_eq_natCard_sum, linkDegree_eq_natCard_sum]
  exact Nat.card_congr ((C.outgoingFiberMergeFacesEquiv h _).sumCongr
    (C.outgoingFiberMergeFacesEquiv h e))

/-- Merging two faces removes one face. -/
theorem card_face_mergeFaces_add_one [Finite C.Face] :
    Nat.card (C.mergeFaces h).Face + 1 = Nat.card C.Face := by
  classical
  have e : {g' : {g // g ≠ g₁} // g' ≠ ⟨g₂, h.ne.symm⟩} ≃ {g // g ≠ g₁ ∧ g ≠ g₂} :=
    (Equiv.subtypeEquivRight fun _ => not_congr Subtype.ext_iff).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ≠ g₁) (· ≠ g₂))
  have h₁ : Nat.card (C.mergeFaces h).Face = Nat.card {g // g ≠ g₁ ∧ g ≠ g₂} + 1 :=
    Finite.card_option
  have h₂ : Nat.card {g // g ≠ g₁} = Nat.card {g // g ≠ g₁ ∧ g ≠ g₂} + 1 := by
    rw [← Nat.card_congr e, ← Finite.card_option,
      Nat.card_congr (Equiv.optionSubtypeNe (⟨g₂, h.ne.symm⟩ : {g // g ≠ g₁}))]
  have h₃ : Nat.card C.Face = Nat.card {g // g ≠ g₁} + 1 := by
    rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe g₁)]
  omega

/-- Merging two faces does not change the Euler characteristic: it removes one edge and one face. -/
@[simp] theorem eulerChar_mergeFaces [Finite C.graph.GeomEdge] [Finite C.Face] :
    (C.mergeFaces h).eulerChar = C.eulerChar := by
  rw [eulerChar_def, eulerChar_def,
    ← C.graph.card_deleteEdge_geomEdge_add_one (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩),
    ← card_face_mergeFaces_add_one h]
  push_cast
  ring

/-! ### Orientability -/

variable {h} in
/-- Merging two faces of an orientable complex gives an orientable complex: the merged face takes
the common orientation of the two faces, which are oriented alike since they traverse `d` in
opposite directions. -/
theorem IsOrientable.mergeFaces (hC : C.IsOrientable) : (C.mergeFaces h).IsOrientable := by
  obtain ⟨σ, hσ⟩ := C.isOrientable_iff_forall_outgoing.1 hC
  have hD : C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ :=
    fun he => h.ne (by simpa using congrArg Sigma.fst he)
  have hs : σ g₁ = σ g₂ := by
    have := (hσ _ _ hD).2 (h.outgoing_eq.trans (by rw [incoming_eq_outgoing_prevCorner]))
    rwa [prevCorner_fst] at this
  have hσ' (c : (C.mergeFaces h).Corner) :
      Option.elim c.1 (σ g₁) (fun g => σ g.1) = σ (C.mergeFacesCornerOrigin g₁ g₂ c).1 := by
    obtain ⟨_ | g, k⟩ := c
    · rcases mergeFacesCornerOrigin_none_fst k with h' | h' <;> simp [h', hs]
    · rfl
  refine (C.mergeFaces h).isOrientable_iff_forall_outgoing.2
    ⟨fun g => Option.elim g (σ g₁) (fun g => σ g.1), fun c c' hne => ?_⟩
  dsimp only
  rw [hσ' c, hσ' c', outgoing_mergeFaces_eq_outgoing_iff, outgoing_mergeFaces_eq_rev_iff]
  exact hσ _ _ fun he => hne (mergeFacesCornerOrigin_injective h.ne he)

omit h in
/-- Two distinct side occurrences of `C`, one of them along the edge of `d`, are not attached
along the same dart: they would be the occurrences `d` and `d⁻¹`. -/
private theorem IsMergeable.outgoing_ne_of_toGeomEdge_eq (h : C.IsMergeable g₁ g₂) {c c' : C.Corner}
    (hne : c ≠ c') (hc : C.graph.toGeomEdge (C.outgoing c) =
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)) :
    C.outgoing c' ≠ C.outgoing c := by
  intro he
  have hd : C.outgoing (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) ≠
      C.outgoing ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ := by
    rw [h.outgoing_eq, ← incoming_eq_outgoing_prevCorner]
    exact (C.graph.rev_ne _).symm
  rcases h.eq_or_eq_of_toGeomEdge_eq c hc with rfl | rfl <;>
    rcases h.eq_or_eq_of_toGeomEdge_eq c' ((congrArg C.graph.toGeomEdge he).trans hc) with rfl | rfl
  exacts [hne rfl, hd he.symm, hd he, hne rfl]

omit h in
/-- A side occurrence of `C` off the edge of `d` is a side occurrence of the merged complex. -/
private theorem IsMergeable.exists_mergeFacesCornerOrigin_eq (h : C.IsMergeable g₁ g₂)
    {c : C.Corner} (hc : C.graph.toGeomEdge (C.outgoing c) ≠
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)) :
    ∃ x, C.mergeFacesCornerOrigin g₁ g₂ x = c :=
  PolygonalComplex.exists_mergeFacesCornerOrigin_eq
    (fun he => hc (by rw [he, incoming_eq_outgoing_prevCorner]))
    fun he => hc (by rw [he, h.outgoing_eq, SerreGraph.toGeomEdge_rev])

variable {h} in
/-- If the complex obtained by merging two faces is orientable, so is the original complex: the two
faces take the orientation of the merged face. -/
theorem IsOrientable.of_mergeFaces (hM : (C.mergeFaces h).IsOrientable) : C.IsOrientable := by
  classical
  obtain ⟨σ', hσ'⟩ := (C.mergeFaces h).isOrientable_iff_forall_outgoing.1 hM
  let σ : C.Face → Bool := fun g => if hg : g ≠ g₁ ∧ g ≠ g₂ then σ' (some ⟨g, hg⟩) else σ' none
  have hσ (c : (C.mergeFaces h).Corner) : σ (C.mergeFacesCornerOrigin g₁ g₂ c).1 = σ' c.1 := by
    obtain ⟨_ | g, k⟩ := c
    · rcases mergeFacesCornerOrigin_none_fst k with h' | h' <;> simp [σ, h']
    · simp [σ, g.2]
  have hσd {c : C.Corner} (hc : C.graph.toGeomEdge (C.outgoing c) =
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)) : σ c.1 = σ' none := by
    rcases h.eq_or_eq_of_toGeomEdge_eq c hc with rfl | rfl <;> simp [σ]
  refine C.isOrientable_iff_forall_outgoing.2 ⟨σ, fun c c' hne => ?_⟩
  by_cases hc : C.graph.toGeomEdge (C.outgoing c) =
    C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
  · exact ⟨fun he => absurd he (h.outgoing_ne_of_toGeomEdge_eq hne hc),
      fun he => by rw [hσd hc, hσd (by rw [he, SerreGraph.toGeomEdge_rev, hc])]⟩
  obtain ⟨x, rfl⟩ := h.exists_mergeFacesCornerOrigin_eq hc
  refine ⟨fun he => ?_, fun he => ?_⟩
  · obtain ⟨x', rfl⟩ := h.exists_mergeFacesCornerOrigin_eq (by rwa [he])
    rw [hσ, hσ]
    exact (hσ' x x' fun hx => hne (congrArg _ hx)).1 ((outgoing_mergeFaces_eq_outgoing_iff h).2 he)
  · obtain ⟨x', rfl⟩ :=
      h.exists_mergeFacesCornerOrigin_eq (by rwa [he, SerreGraph.toGeomEdge_rev])
    rw [hσ, hσ]
    exact (hσ' x x' fun hx => hne (congrArg _ hx)).2 ((outgoing_mergeFaces_eq_rev_iff h).2 he)

/-- Merging two faces does not change orientability. -/
@[simp] theorem isOrientable_mergeFaces_iff : (C.mergeFaces h).IsOrientable ↔ C.IsOrientable :=
  ⟨IsOrientable.of_mergeFaces, fun hC => hC.mergeFaces⟩

/-! ### Merging the two faces of a split face -/

variable (C) in
/-- The two new faces `a₀ ⋯ aₚ₋₁ d` and `d⁻¹ aₚ ⋯ aₙ₋₁` of a split face can be merged along `d`. -/
theorem isMergeable_splitFace (f : C.Face) (p : Fin (C.sides f)) :
    (C.splitFace f p).IsMergeable (.inr true) (.inr false) where
  ne := by simp
  two_lt_sides_add_sides := by
    have := p.2
    simp only [splitFaceSides]
    omega
  outgoing_eq := by
    rw [outgoing_splitFace_inr_false_zero, incoming_splitFace_inr_true_zero]
    rfl
  eq_or_eq_of_toGeomEdge_eq c hc := by
    rw [incoming_splitFace_inr_true_zero, eq_comm, SerreGraph.toGeomEdge_eq_toGeomEdge_iff,
      SerreGraph.addEdge_rev_inr, Bool.not_true] at hc
    have hinj := C.splitFaceCornerOrigin_injective f p
    rcases hc with hc | hc
    · refine .inl (hinj ((outgoing_splitFace_eq_inr_iff.1 hc).trans
        (outgoing_splitFace_eq_inr_iff.1 ?_).symm))
      rw [← incoming_eq_outgoing_prevCorner, incoming_splitFace_inr_true_zero]
    · exact .inr (hinj ((outgoing_splitFace_eq_inr_iff.1 hc).trans
        (outgoing_splitFace_eq_inr_iff.1 (outgoing_splitFace_inr_false_zero C f p)).symm))

variable (C) (f : C.Face) (p : Fin (C.sides f))

/-- Merging the two faces of a split face gives back the faces of the original complex: the merged
face is the split face, and the other faces are the faces of `C` other than the split face. -/
noncomputable def mergeFacesSplitFaceFaceEquiv :
    ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Face ≃ C.Face := by
  refine Equiv.ofBijective (fun g => g.elim f fun g => Sum.elim Subtype.val (fun _ => f) g.1)
    ⟨fun a b hab => ?_, fun g => ?_⟩
  · rcases a with _ | ⟨a | a, ha⟩ <;> rcases b with _ | ⟨b | b, hb⟩
    all_goals first
      | rfl
      | (cases a <;> simp at ha; done)
      | (cases b <;> simp at hb; done)
      | exact absurd hab.symm b.2
      | exact absurd hab a.2
      | (simp only [Option.some.injEq, Subtype.mk.injEq, Sum.inl.injEq]; exact Subtype.ext hab)
  · by_cases hg : g = f
    · exact ⟨none, hg.symm⟩
    · exact ⟨some ⟨.inl ⟨g, hg⟩, by simp⟩, rfl⟩

@[simp] theorem mergeFacesSplitFaceFaceEquiv_none : C.mergeFacesSplitFaceFaceEquiv f p none = f :=
  (rfl)

@[simp] theorem mergeFacesSplitFaceFaceEquiv_some_inl (g : {g : C.Face // g ≠ f})
    (hg : (.inl g : (C.splitFace f p).Face) ≠ .inr true ∧
      (.inl g : (C.splitFace f p).Face) ≠ .inr false) :
    C.mergeFacesSplitFaceFaceEquiv f p (some ⟨.inl g, hg⟩) = g.1 :=
  (rfl)

/-- Merging the two faces of a split face gives back the numbers of sides of the faces. -/
theorem sides_mergeFacesSplitFaceFaceEquiv
    (g : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Face) :
    C.sides (C.mergeFacesSplitFaceFaceEquiv f p g) =
      ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).sides g := by
  rcases g with _ | ⟨_ | b, hb⟩
  · have := p.2
    have e : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).sides none =
        (p + 1) + (C.sides f - p + 1) - 2 := rfl
    rw [mergeFacesSplitFaceFaceEquiv_none, e]
    omega
  · rfl
  · cases b <;> simp at hb

/-- Merging the two faces of a split face gives back the side occurrences of `C`, at the same
positions of corresponding faces. -/
noncomputable def mergeFacesSplitFaceCornerEquiv :
    ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Corner ≃ C.Corner :=
  Equiv.sigmaCongr (C.mergeFacesSplitFaceFaceEquiv f p) fun g =>
    finCongr (C.sides_mergeFacesSplitFaceFaceEquiv f p g).symm

@[simp] theorem mergeFacesSplitFaceCornerEquiv_fst
    (c : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Corner) :
    (C.mergeFacesSplitFaceCornerEquiv f p c).1 = C.mergeFacesSplitFaceFaceEquiv f p c.1 :=
  (rfl)

@[simp] theorem coe_mergeFacesSplitFaceCornerEquiv_snd
    (c : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Corner) :
    ((C.mergeFacesSplitFaceCornerEquiv f p c).2 : ℕ) = c.2 :=
  (rfl)

/-- Merging the two faces of a split face gives back `C`: corresponding side occurrences are
attached along corresponding darts, where the darts of the merged complex are those of `C` by
`SerreGraph.deleteEdgeAddEdgeEquiv`. -/
theorem outgoing_mergeFacesSplitFaceCornerEquiv
    (c : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Corner) :
    C.outgoing (C.mergeFacesSplitFaceCornerEquiv f p c) =
      C.graph.deleteEdgeAddEdgeEquiv (C.incoming_splitFace_inr_true_zero f p)
        (((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).outgoing c) := by
  apply Sum.inl_injective
  rw [SerreGraph.inl_deleteEdgeAddEdgeEquiv, coe_outgoing_mergeFaces, outgoing_splitFace]
  obtain ⟨_ | ⟨_ | g, hg⟩, k⟩ := c
  · have e : C.splitFaceSides f p (.inr true) = p + 1 := rfl
    by_cases hkp : (k : ℕ) < p
    · rw [mergeFacesCornerOrigin_none_of_lt (by simpa using hkp),
        splitFaceCornerOrigin_inr_true_of_lt hkp]
      rfl
    · rw [mergeFacesCornerOrigin_none_of_not_lt (by simpa using hkp),
        splitFaceCornerOrigin_inr_false_of_ne_zero (by dsimp only; omega), Sum.map_inl]
      refine congrArg (fun c => Sum.inl (C.outgoing c)) (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
      rw [coe_mergeFacesSplitFaceCornerEquiv_snd]
      dsimp only
      omega
  · rw [mergeFacesCornerOrigin_some, splitFaceCornerOrigin_inl]
    rfl
  · cases g <;> simp at hg

/-- A corner which lies on the face of `c'`, at the position following that of `c` along a face with
the same number of sides as the face of `c'`, is the corner following `c'` when `c'` is at the
position of `c`. -/
private theorem eq_nextCorner_of_coe_snd {D E : PolygonalComplex.{u, v, w}} {c : D.Corner}
    {c' x : E.Corner} (hfst : x.1 = c'.1) (hs : E.sides c'.1 = D.sides c.1)
    (hx : (x.2 : ℕ) = (D.nextCorner c).2) (hc' : (c'.2 : ℕ) = c.2) : x = E.nextCorner c' := by
  obtain ⟨g, k⟩ := c'
  obtain ⟨g', k'⟩ := x
  obtain rfl : g' = g := hfst
  rw [nextCorner_def]
  refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
  rw [nextCorner_def] at hx
  have h₁ := Fin.coe_finRotate_eq_ite c.2
  have h₂ := Fin.coe_finRotate_eq_ite k
  dsimp only at hx hc' hs ⊢
  split_ifs at h₁ h₂ <;> omega

/-- Merging the two faces of a split face gives back `C`: the isomorphism keeps the orientation and
the starting point of every face, and is the identity on vertices. -/
noncomputable def mergeFacesSplitFaceIso :
    ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Iso C where
  graph := C.graph.deleteEdgeAddEdgeIso (C.incoming_splitFace_inr_true_zero f p)
  faceEquiv := C.mergeFacesSplitFaceFaceEquiv f p
  flip _ := false
  sideEquiv := C.mergeFacesSplitFaceCornerEquiv f p
  sideEquiv_apply_fst _ := rfl
  sideEquiv_nextCorner c := eq_nextCorner_of_coe_snd (by simp)
    (C.sides_mergeFacesSplitFaceFaceEquiv f p c.1) (coe_mergeFacesSplitFaceCornerEquiv_snd _ _ _ _)
    (coe_mergeFacesSplitFaceCornerEquiv_snd _ _ _ _)
  outgoing_sideEquiv c := by
    rw [Bool.cond_false, SerreGraph.deleteEdgeAddEdgeIso_equivE]
    exact C.outgoing_mergeFacesSplitFaceCornerEquiv f p c

@[simp] theorem mergeFacesSplitFaceIso_graph :
    (C.mergeFacesSplitFaceIso f p).graph =
      C.graph.deleteEdgeAddEdgeIso (C.incoming_splitFace_inr_true_zero f p) :=
  (rfl)

@[simp] theorem mergeFacesSplitFaceIso_faceEquiv :
    (C.mergeFacesSplitFaceIso f p).faceEquiv = C.mergeFacesSplitFaceFaceEquiv f p :=
  (rfl)

@[simp] theorem mergeFacesSplitFaceIso_flip
    (g : ((C.splitFace f p).mergeFaces (C.isMergeable_splitFace f p)).Face) :
    (C.mergeFacesSplitFaceIso f p).flip g = false :=
  (rfl)

@[simp] theorem mergeFacesSplitFaceIso_sideEquiv :
    (C.mergeFacesSplitFaceIso f p).sideEquiv = C.mergeFacesSplitFaceCornerEquiv f p :=
  (rfl)

/-! ### Splitting a merged face -/

variable {C} (h₂ : 1 < C.sides g₂)

/-- Splitting the merged face `X Y` of `C.mergeFaces h` at the corner where `Y` starts gives back
the faces of `C`: the two new faces are `g₁` and `g₂`. -/
noncomputable def splitFaceMergeFacesFaceEquiv :
    ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Face ≃ C.Face := by
  refine Equiv.ofBijective (Sum.elim (fun g => g.1.elim g₁ Subtype.val) fun b => cond b g₁ g₂)
    ⟨fun a b hab => ?_, fun g => ?_⟩
  · rcases a with ⟨_ | a, ha⟩ | _ | _ <;> rcases b with ⟨_ | b, hb⟩ | _ | _
    all_goals first
      | rfl
      | exact absurd rfl ha
      | exact absurd rfl hb
      | (simp only [Sum.inl.injEq, Subtype.mk.injEq, Option.some.injEq]; exact Subtype.ext hab)
      | exact absurd hab a.2.1
      | exact absurd hab a.2.2
      | exact absurd hab.symm b.2.1
      | exact absurd hab.symm b.2.2
      | exact absurd hab h.ne
      | exact absurd hab.symm h.ne
  · by_cases hg₁ : g = g₁
    · exact ⟨.inr true, hg₁.symm⟩
    by_cases hg₂ : g = g₂
    · exact ⟨.inr false, hg₂.symm⟩
    exact ⟨.inl ⟨some ⟨g, hg₁, hg₂⟩, Option.some_ne_none _⟩, rfl⟩

@[simp] theorem splitFaceMergeFacesFaceEquiv_inl_some (g : {g : C.Face // g ≠ g₁ ∧ g ≠ g₂})
    (hg : some g ≠ none) : C.splitFaceMergeFacesFaceEquiv h h₂ (.inl ⟨some g, hg⟩) = g.1 :=
  (rfl)

@[simp] theorem splitFaceMergeFacesFaceEquiv_inr (b : Bool) :
    C.splitFaceMergeFacesFaceEquiv h h₂ (.inr b) = cond b g₁ g₂ :=
  (rfl)

/-- Splitting a merged face gives back the numbers of sides of the faces. -/
theorem sides_splitFaceMergeFacesFaceEquiv
    (g : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Face) :
    C.sides (C.splitFaceMergeFacesFaceEquiv h h₂ g) =
      ((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).sides g := by
  have := C.sides_pos g₁
  rcases g with ⟨_ | g, hg⟩ | _ | _
  · exact absurd rfl hg
  · rfl
  · have e : ((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).sides (.inr false) =
        (C.sides g₁ + C.sides g₂ - 2) - (C.sides g₁ - 1) + 1 := rfl
    rw [splitFaceMergeFacesFaceEquiv_inr, e, Bool.cond_false]
    omega
  · have e : ((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).sides (.inr true) =
        C.sides g₁ - 1 + 1 := rfl
    rw [splitFaceMergeFacesFaceEquiv_inr, e, Bool.cond_true]
    omega

/-- Splitting a merged face gives back the side occurrences of `C`, at the same positions of
corresponding faces. -/
noncomputable def splitFaceMergeFacesCornerEquiv :
    ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Corner ≃ C.Corner :=
  Equiv.sigmaCongr (C.splitFaceMergeFacesFaceEquiv h h₂) fun g =>
    finCongr (C.sides_splitFaceMergeFacesFaceEquiv h h₂ g).symm

@[simp] theorem splitFaceMergeFacesCornerEquiv_fst
    (c : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Corner) :
    (C.splitFaceMergeFacesCornerEquiv h h₂ c).1 = C.splitFaceMergeFacesFaceEquiv h h₂ c.1 :=
  (rfl)

@[simp] theorem coe_splitFaceMergeFacesCornerEquiv_snd
    (c : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Corner) :
    ((C.splitFaceMergeFacesCornerEquiv h h₂ c).2 : ℕ) = c.2 :=
  (rfl)

/-- The second side of `g₂ = d⁻¹ Y` starts at the source of `d`. -/
private theorem src_side_one_eq (h : C.IsMergeable g₁ g₂) (h₂ : 1 < C.sides g₂) :
    C.graph.src (C.side g₂ ⟨1, h₂⟩) = C.graph.src (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  rw [← C.tgt_side_eq_src_side (i := ⟨0, C.sides_pos g₂⟩) (by dsimp only; split_ifs <;> omega),
    ← outgoing_def _ ⟨_, _⟩, h.outgoing_eq, SerreGraph.tgt_rev]

/-- The side of the merged face at the position where `Y` starts is the second side of `g₂`, which
starts at the source of `d`. -/
theorem src_mergeFacesSide_sides_sub_one :
    C.graph.src ((C.mergeFaces h).side none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).1 =
        C.graph.src (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  have := C.sides_pos g₁
  rw [← outgoing_def _ ⟨_, _⟩, coe_outgoing_mergeFaces,
    mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega), outgoing_def,
    ← src_side_one_eq h h₂]
  exact congrArg (fun j => C.graph.src (C.side g₂ j)) (Fin.ext (by dsimp only; omega))

/-- The side of the merged face at the position `0` starts at the target of `d`. -/
theorem src_mergeFacesSide_zero :
    C.graph.src ((C.mergeFaces h).side none ⟨0, (C.mergeFaces h).sides_pos none⟩).1 =
      C.graph.tgt (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  have := C.sides_pos g₁
  rw [← outgoing_def _ ⟨_, _⟩, coe_outgoing_mergeFaces]
  by_cases h₁ : 1 < C.sides g₁
  · rw [mergeFacesCornerOrigin_none_of_lt (k := ⟨0, (C.mergeFaces h).sides_pos none⟩)
        (by dsimp only; omega), outgoing_def, incoming_mk_zero,
      C.tgt_side_eq_src_side (i := ⟨C.sides g₁ - 1, by omega⟩) (j := ⟨0, C.sides_pos g₁⟩)
        (by dsimp only; split_ifs <;> omega)]
  · -- `X` is empty, so `g₁ = d` is a monogon and `d` is a loop
    have h₂ : 1 < C.sides g₂ := by
      have := h.two_lt_sides_add_sides
      omega
    rw [mergeFacesCornerOrigin_none_of_not_lt (k := ⟨0, (C.mergeFaces h).sides_pos none⟩)
        (by dsimp only; omega), outgoing_def, incoming_mk_zero,
      C.tgt_side_eq_src_side_of_sides_eq_one (f := g₁) (by omega), ← incoming_mk_zero,
      ← src_side_one_eq h h₂]
    exact congrArg (fun j => C.graph.src (C.side g₂ j)) (Fin.ext (by dsimp only; omega))

/-- Splitting a merged face gives back the sources of `C`: the darts of the split complex are
those of `C` by `SerreGraph.deleteEdgeSumEquiv`, and the new edge runs along the deleted one. -/
theorem src_deleteEdgeSumEquiv_splitFaceMergeFaces
    (e : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).graph.E) :
    C.graph.src (C.graph.deleteEdgeSumEquiv _ e) =
      ((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).graph.src e :=
  SerreGraph.src_deleteEdgeSumEquiv (src_mergeFacesSide_sides_sub_one h h₂)
    (src_mergeFacesSide_zero h) e

/-- The sides of the face `d'⁻¹ Y` of a split merged face are those of `g₂ = d⁻¹ Y`. -/
private theorem outgoing_splitFaceMergeFacesCornerEquiv_inr_false
    (k : Fin (C.sides g₁ + C.sides g₂ - 2 - (C.sides g₁ - 1) + 1)) :
    C.outgoing (C.splitFaceMergeFacesCornerEquiv h h₂ ⟨.inr false, k⟩) =
      C.graph.deleteEdgeSumEquiv _ (((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).outgoing ⟨.inr false, k⟩) := by
  have := C.sides_pos g₁
  have := k.2
  rw [outgoing_splitFace]
  by_cases hk : (k : ℕ) = 0
  · rw [splitFaceCornerOrigin_inr_false_of_eq_zero hk, Sum.map_inr, id,
      SerreGraph.deleteEdgeSumEquiv_inr, Bool.cond_false, ← h.outgoing_eq]
    refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
    rw [coe_splitFaceMergeFacesCornerEquiv_snd]
    exact hk
  · rw [splitFaceCornerOrigin_inr_false_of_ne_zero hk, Sum.map_inl,
      SerreGraph.deleteEdgeSumEquiv_inl, coe_outgoing_mergeFaces,
      mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega)]
    refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
    rw [coe_splitFaceMergeFacesCornerEquiv_snd]
    dsimp only
    omega

/-- The sides of the face `X d'` of a split merged face are those of `g₁ = X d`. -/
private theorem outgoing_splitFaceMergeFacesCornerEquiv_inr_true (k : Fin (C.sides g₁ - 1 + 1)) :
    C.outgoing (C.splitFaceMergeFacesCornerEquiv h h₂ ⟨.inr true, k⟩) =
      C.graph.deleteEdgeSumEquiv _ (((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).outgoing ⟨.inr true, k⟩) := by
  have := k.2
  rw [outgoing_splitFace]
  by_cases hk : (k : ℕ) < C.sides g₁ - 1
  · rw [splitFaceCornerOrigin_inr_true_of_lt hk, Sum.map_inl,
      SerreGraph.deleteEdgeSumEquiv_inl, coe_outgoing_mergeFaces,
      mergeFacesCornerOrigin_none_of_lt hk]
    refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
    rw [coe_splitFaceMergeFacesCornerEquiv_snd]
  · rw [splitFaceCornerOrigin_inr_true_of_not_lt hk, Sum.map_inr, id,
      SerreGraph.deleteEdgeSumEquiv_inr, Bool.cond_true, incoming_mk_zero, ← outgoing_def _ ⟨_, _⟩]
    refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
    rw [coe_splitFaceMergeFacesCornerEquiv_snd]
    dsimp only
    omega

/-- Splitting a merged face gives back `C`: corresponding side occurrences are attached along
corresponding darts. -/
theorem outgoing_splitFaceMergeFacesCornerEquiv
    (c : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Corner) :
    C.outgoing (C.splitFaceMergeFacesCornerEquiv h h₂ c) =
      C.graph.deleteEdgeSumEquiv _ (((C.mergeFaces h).splitFace none
        ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).outgoing c) := by
  obtain ⟨⟨_ | g, hg⟩ | _ | _, k⟩ := c
  · exact absurd rfl hg
  · rw [outgoing_splitFace, splitFaceCornerOrigin_inl, Sum.map_inl,
      SerreGraph.deleteEdgeSumEquiv_inl, coe_outgoing_mergeFaces, mergeFacesCornerOrigin_some]
    rfl
  · exact outgoing_splitFaceMergeFacesCornerEquiv_inr_false h h₂ k
  · exact outgoing_splitFaceMergeFacesCornerEquiv_inr_true h h₂ k

/-- Splitting the merged face `X Y` of `C.mergeFaces h` at the corner where `Y` starts gives back
`C`: the isomorphism keeps the orientation and the starting point of every face, and is the identity
on vertices. -/
noncomputable def splitFaceMergeFacesIso :
    ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Iso C where
  graph := C.graph.addEdgeDeleteEdgeIso (src_mergeFacesSide_sides_sub_one h h₂)
    (src_mergeFacesSide_zero h)
  faceEquiv := C.splitFaceMergeFacesFaceEquiv h h₂
  flip _ := false
  sideEquiv := C.splitFaceMergeFacesCornerEquiv h h₂
  sideEquiv_apply_fst _ := rfl
  sideEquiv_nextCorner c := eq_nextCorner_of_coe_snd (by simp)
    (C.sides_splitFaceMergeFacesFaceEquiv h h₂ c.1) (coe_splitFaceMergeFacesCornerEquiv_snd _ _ _)
    (coe_splitFaceMergeFacesCornerEquiv_snd _ _ _)
  outgoing_sideEquiv c := by
    rw [Bool.cond_false, SerreGraph.addEdgeDeleteEdgeIso_equivE]
    exact outgoing_splitFaceMergeFacesCornerEquiv h h₂ c

@[simp] theorem splitFaceMergeFacesIso_graph :
    (C.splitFaceMergeFacesIso h h₂).graph = C.graph.addEdgeDeleteEdgeIso
      (src_mergeFacesSide_sides_sub_one h h₂) (src_mergeFacesSide_zero h) :=
  (rfl)

@[simp] theorem splitFaceMergeFacesIso_faceEquiv :
    (C.splitFaceMergeFacesIso h h₂).faceEquiv = C.splitFaceMergeFacesFaceEquiv h h₂ :=
  (rfl)

@[simp] theorem splitFaceMergeFacesIso_flip
    (g : ((C.mergeFaces h).splitFace none
      ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩).Face) :
    (C.splitFaceMergeFacesIso h h₂).flip g = false :=
  (rfl)

@[simp] theorem splitFaceMergeFacesIso_sideEquiv :
    (C.splitFaceMergeFacesIso h h₂).sideEquiv = C.splitFaceMergeFacesCornerEquiv h h₂ :=
  (rfl)

end PolygonalComplex

end TauCeti
