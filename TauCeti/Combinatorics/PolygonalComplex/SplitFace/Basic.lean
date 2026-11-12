/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.AddEdge
public import TauCeti.Combinatorics.PolygonalComplex.Basic
public import Mathlib.Basic.Finite.Sum
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring

/-!
# Splitting a face of a polygonal complex

Splitting a face `f` with sides `a₀ ⋯ aₙ₋₁` of a polygonal complex at the corner `p` cuts the
polygon along a new side `d` running from the corner `p` to the corner `0`: the face is replaced
by the two faces `a₀ ⋯ aₚ₋₁ d` and `d⁻¹ aₚ ⋯ aₙ₋₁`. This is the second of the two elementary
subdivisions of Gallier and Xu, the operation (P2), which is the two-dimensional cutting of
Seifert and Threlfall. For `p = 0` the first face is the monogon `d` and the new edge is a loop.

The one-skeleton of `C.splitFace f p` is `C.graph.addEdge _ _`, with the new dart `Sum.inr true`
for `d` and `Sum.inr false` for its reverse. Its faces are the faces of `C` other than `f`,
together with `Sum.inr true` for `a₀ ⋯ aₚ₋₁ d` and `Sum.inr false` for `d⁻¹ aₚ ⋯ aₙ₋₁`. The new
dart and the new faces are fresh by construction. The side occurrences of the new complex are
those of `C` together with the two occurrences of the new edge
(`PolygonalComplex.splitFaceCornerEquiv`), one on each of the two new faces.

The move keeps the incidence counts: the old darts keep their side counts and link degrees, and
each of the two new darts lies on exactly one face side, so the new germs have degree two. It adds
one edge and one face, so the Euler characteristic is unchanged, and it does not change
orientability: the two new faces are oriented compatibly along the new edge exactly when they
come from one orientation of the split face.

## Main definitions

* `TauCeti.PolygonalComplex.splitFace`: the complex obtained by splitting a face.
* `TauCeti.PolygonalComplex.splitFaceCornerOrigin`, `TauCeti.PolygonalComplex.splitFaceCornerEquiv`:
  the side occurrences of the new complex are those of the old one and the two occurrences of the
  new edge.
* `TauCeti.PolygonalComplex.splitFaceOriginFace`: the face of the old complex containing a face of
  the new one.

## Main results

* `TauCeti.PolygonalComplex.sideCount_splitFace_inl`,
  `TauCeti.PolygonalComplex.sideCount_splitFace_inr`: the old darts keep their side counts, and
  each of the two new darts lies on exactly one face side.
* `TauCeti.PolygonalComplex.linkDegree_splitFace_inl`,
  `TauCeti.PolygonalComplex.linkDegree_splitFace_inr`: the old germs keep their link degrees, and
  the new germs have degree two.
* `TauCeti.PolygonalComplex.eulerChar_splitFace`: the Euler characteristic is unchanged.
* `TauCeti.PolygonalComplex.isOrientable_splitFace_iff`: orientability is unchanged.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P2).
* H. Seifert, W. Threlfall, *A Textbook of Topology*, Academic Press, 1980, Chapter VI, §37.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w}) (f : C.Face) (p : Fin (C.sides f))

/-! ### The split complex -/

/-- The numbers of sides of the faces of `C.splitFace f p`: the faces other than `f` keep their
sides, the face `a₀ ⋯ aₚ₋₁ d` has `p + 1` sides and the face `d⁻¹ aₚ ⋯ aₙ₋₁` has `n - p + 1`.
It is reducible, so that the positions along the faces of `C.splitFace f p` are indices in these
explicit ranges. -/
abbrev splitFaceSides : {g : C.Face // g ≠ f} ⊕ Bool → ℕ
  | .inl g => C.sides g.1
  | .inr true => p + 1
  | .inr false => C.sides f - p + 1

theorem splitFaceSides_pos (g : {g : C.Face // g ≠ f} ⊕ Bool) : 0 < C.splitFaceSides f p g := by
  obtain g | _ | _ := g
  exacts [C.sides_pos g.1, Nat.succ_pos _, Nat.succ_pos _]

/-- The side occurrence of `C`, or the new dart, at a position along a face of `C.splitFace f p`.
On the face `a₀ ⋯ aₚ₋₁ d` the positions before `p` are the sides `a₀, …, aₚ₋₁` of `f` and the
position `p` is the new dart `d`, namely `Sum.inr true`. On the face `d⁻¹ aₚ ⋯ aₙ₋₁` the position
`0` is the reverse `Sum.inr false` of the new dart and the position `k + 1` is the side `aₚ₊ₖ` of
`f`. -/
def splitFaceCornerOrigin :
    (Σ g : {g : C.Face // g ≠ f} ⊕ Bool, Fin (C.splitFaceSides f p g)) → C.Corner ⊕ Bool
  | ⟨.inl g, k⟩ => .inl ⟨g.1, k⟩
  | ⟨.inr true, k⟩ => if h : (k : ℕ) < p then .inl ⟨f, ⟨k, h.trans p.2⟩⟩ else .inr true
  | ⟨.inr false, k⟩ => if (k : ℕ) = 0 then .inr false else
      .inl ⟨f, ⟨p + k - 1, by have := k.2; have := p.2; simp only [splitFaceSides] at *; omega⟩⟩

/-- The dart of `C.splitFace f p` along which a side of one of its faces is attached. -/
def splitFaceSide (g : {g : C.Face // g ≠ f} ⊕ Bool) (k : Fin (C.splitFaceSides f p g)) :
    C.graph.E ⊕ Bool :=
  Sum.map C.outgoing id (C.splitFaceCornerOrigin f p ⟨g, k⟩)

variable {C f p}

@[simp] theorem splitFaceCornerOrigin_inl (g : {g : C.Face // g ≠ f}) (k : Fin (C.sides g.1)) :
    C.splitFaceCornerOrigin f p ⟨.inl g, k⟩ = .inl ⟨g.1, k⟩ := (rfl)

theorem splitFaceCornerOrigin_inr_true_of_lt {k : Fin (p + 1)} (h : (k : ℕ) < p) :
    C.splitFaceCornerOrigin f p ⟨.inr true, k⟩ = .inl ⟨f, ⟨k, h.trans p.2⟩⟩ := by
  simp [splitFaceCornerOrigin, h]

theorem splitFaceCornerOrigin_inr_true_of_not_lt {k : Fin (p + 1)} (h : ¬(k : ℕ) < p) :
    C.splitFaceCornerOrigin f p ⟨.inr true, k⟩ = .inr true := by
  simp [splitFaceCornerOrigin, h]

theorem splitFaceCornerOrigin_inr_false_of_eq_zero {k : Fin (C.sides f - p + 1)}
    (h : (k : ℕ) = 0) : C.splitFaceCornerOrigin f p ⟨.inr false, k⟩ = .inr false := by
  simp [splitFaceCornerOrigin, h]

theorem splitFaceCornerOrigin_inr_false_of_ne_zero {k : Fin (C.sides f - p + 1)}
    (h : (k : ℕ) ≠ 0) :
    C.splitFaceCornerOrigin f p ⟨.inr false, k⟩ = .inl ⟨f, ⟨p + k - 1, by omega⟩⟩ := by
  simp [splitFaceCornerOrigin, h]

theorem splitFaceSide_def (g : {g : C.Face // g ≠ f} ⊕ Bool) (k : Fin (C.splitFaceSides f p g)) :
    C.splitFaceSide f p g k = Sum.map C.outgoing id (C.splitFaceCornerOrigin f p ⟨g, k⟩) := (rfl)

private theorem splitFaceSide_inl (g : {g : C.Face // g ≠ f}) (k : Fin (C.sides g.1)) :
    C.splitFaceSide f p (.inl g) k = .inl (C.side g.1 k) := by
  rw [splitFaceSide_def, splitFaceCornerOrigin_inl, Sum.map_inl, outgoing_def]

private theorem splitFaceSide_true_of_lt {k : Fin (p + 1)} (h : (k : ℕ) < p) :
    C.splitFaceSide f p (.inr true) k = .inl (C.side f ⟨k, h.trans p.2⟩) := by
  rw [splitFaceSide_def, splitFaceCornerOrigin_inr_true_of_lt h, Sum.map_inl, outgoing_def]

private theorem splitFaceSide_true_of_not_lt {k : Fin (p + 1)} (h : ¬(k : ℕ) < p) :
    C.splitFaceSide f p (.inr true) k = .inr true := by
  rw [splitFaceSide_def, splitFaceCornerOrigin_inr_true_of_not_lt h, Sum.map_inr, id]

private theorem splitFaceSide_false_of_eq_zero {k : Fin (C.sides f - p + 1)} (h : (k : ℕ) = 0) :
    C.splitFaceSide f p (.inr false) k = .inr false := by
  rw [splitFaceSide_def, splitFaceCornerOrigin_inr_false_of_eq_zero h, Sum.map_inr, id]

private theorem splitFaceSide_false_of_ne_zero {k : Fin (C.sides f - p + 1)} (h : (k : ℕ) ≠ 0) :
    C.splitFaceSide f p (.inr false) k = .inl (C.side f ⟨p + k - 1, by omega⟩) := by
  rw [splitFaceSide_def, splitFaceCornerOrigin_inr_false_of_ne_zero h, Sum.map_inl, outgoing_def]

variable (C f p)

/-- The sides of the face `a₀ ⋯ aₚ₋₁ d` form a closed dart sequence. -/
private theorem tgt_splitFaceSide_true (k : Fin (p + 1)) :
    (C.graph.addEdge (C.graph.src (C.side f p)) (C.graph.src (C.side f ⟨0, C.sides_pos f⟩))).tgt
        (C.splitFaceSide f p (.inr true) k) =
      (C.graph.addEdge (C.graph.src (C.side f p)) (C.graph.src (C.side f ⟨0, C.sides_pos f⟩))).src
        (C.splitFaceSide f p (.inr true) (finRotate (p + 1) k)) := by
  have hr := Fin.coe_finRotate_eq_ite k
  by_cases hk : (k : ℕ) < p
  · rw [splitFaceSide_true_of_lt hk]
    by_cases hk' : (k : ℕ) + 1 < p
    · rw [splitFaceSide_true_of_lt (by split_ifs at hr <;> omega)]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)
    · rw [splitFaceSide_true_of_not_lt (by split_ifs at hr <;> omega)]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs <;> omega)
  · rw [splitFaceSide_true_of_not_lt hk]
    by_cases hp : 0 < (p : ℕ)
    · rw [splitFaceSide_true_of_lt (by split_ifs at hr <;> omega)]
      exact congrArg (fun j => C.graph.src (C.side f j))
        (Fin.ext (by dsimp only; split_ifs at hr <;> omega))
    · rw [splitFaceSide_true_of_not_lt (by omega)]
      exact congrArg (fun j => C.graph.src (C.side f j)) (Fin.ext (by dsimp only; omega))

/-- The sides of the face `d⁻¹ aₚ ⋯ aₙ₋₁` form a closed dart sequence. -/
private theorem tgt_splitFaceSide_false (k : Fin (C.sides f - p + 1)) :
    (C.graph.addEdge (C.graph.src (C.side f p)) (C.graph.src (C.side f ⟨0, C.sides_pos f⟩))).tgt
        (C.splitFaceSide f p (.inr false) k) =
      (C.graph.addEdge (C.graph.src (C.side f p)) (C.graph.src (C.side f ⟨0, C.sides_pos f⟩))).src
        (C.splitFaceSide f p (.inr false) (finRotate (C.sides f - p + 1) k)) := by
  have hr := Fin.coe_finRotate_eq_ite k
  have hp := p.2
  by_cases hk : (k : ℕ) = 0
  · rw [splitFaceSide_false_of_eq_zero hk,
      splitFaceSide_false_of_ne_zero (by split_ifs at hr <;> omega)]
    exact congrArg (fun j => C.graph.src (C.side f j))
      (Fin.ext (by dsimp only; split_ifs at hr <;> omega))
  · rw [splitFaceSide_false_of_ne_zero hk]
    by_cases hk' : (k : ℕ) + 1 = C.sides f - p + 1
    · rw [splitFaceSide_false_of_eq_zero (by split_ifs at hr; omega)]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs <;> omega)
    · rw [splitFaceSide_false_of_ne_zero (by split_ifs at hr; omega)]
      exact C.tgt_side_eq_src_side (by dsimp only; split_ifs at hr ⊢ <;> omega)

/-- The polygonal complex obtained from `C` by splitting the face `f = a₀ ⋯ aₙ₋₁` at its corner
`p`, along a new edge from the corner `p` to the corner `0`. The new dart `Sum.inr true` runs from
the start of `aₚ` to the start of `a₀`. The faces are those of `C` other than `f`, the face
`Sum.inr true` attached along `a₀ ⋯ aₚ₋₁` followed by the new dart, and the face `Sum.inr false`
attached along the reverse of the new dart followed by `aₚ ⋯ aₙ₋₁`. It is reducible, so that its
one-skeleton and its faces are seen to be `C.graph.addEdge _ _` and
`{g : C.Face // g ≠ f} ⊕ Bool`. -/
abbrev splitFace : PolygonalComplex.{u, v, w} where
  graph := C.graph.addEdge (C.graph.src (C.side f p)) (C.graph.src (C.side f ⟨0, C.sides_pos f⟩))
  Face := {g : C.Face // g ≠ f} ⊕ Bool
  sides := C.splitFaceSides f p
  sides_pos := C.splitFaceSides_pos f p
  side := C.splitFaceSide f p
  tgt_side g k := by
    obtain g | _ | _ := g
    · rw [splitFaceSide_inl, splitFaceSide_inl]
      exact C.tgt_side g.1 k
    · exact C.tgt_splitFaceSide_false f p k
    · exact C.tgt_splitFaceSide_true f p k

/-- Splitting a face of a complex with finitely many faces gives finitely many faces. -/
instance [Finite C.Face] : Finite (C.splitFace f p).Face :=
  inferInstanceAs (Finite ({g : C.Face // g ≠ f} ⊕ Bool))

/-! ### Side occurrences -/

/-- The dart of a side occurrence of `C.splitFace f p` is the dart of the side occurrence of `C`
it comes from, or the new dart. -/
theorem outgoing_splitFace (c : (C.splitFace f p).Corner) :
    (C.splitFace f p).outgoing c = Sum.map C.outgoing id (C.splitFaceCornerOrigin f p c) :=
  (C.splitFace f p).outgoing_def c

variable {C f p} in
/-- A side of `C.splitFace f p` is attached along an old dart `e` exactly when it comes from a
side of `C` attached along `e`. -/
theorem outgoing_splitFace_eq_inl_iff {c : (C.splitFace f p).Corner} {e : C.graph.E} :
    (C.splitFace f p).outgoing c = .inl e ↔
      ∃ c₀, C.splitFaceCornerOrigin f p c = .inl c₀ ∧ C.outgoing c₀ = e := by
  rw [outgoing_splitFace]
  rcases C.splitFaceCornerOrigin f p c with c₀ | b <;> simp

variable {C f p} in
/-- A side of `C.splitFace f p` is attached along one of the two new darts exactly when it is the
corresponding occurrence of the new edge. -/
theorem outgoing_splitFace_eq_inr_iff {c : (C.splitFace f p).Corner} {b : Bool} :
    (C.splitFace f p).outgoing c = .inr b ↔ C.splitFaceCornerOrigin f p c = .inr b := by
  rw [outgoing_splitFace]
  rcases C.splitFaceCornerOrigin f p c with c₀ | b' <;> simp

/-- The new dart is the last side of the face `a₀ ⋯ aₚ₋₁ d`. -/
theorem outgoing_splitFace_inr_true_last :
    (C.splitFace f p).outgoing ⟨.inr true, ⟨p, Nat.lt_succ_self _⟩⟩ = .inr true :=
  outgoing_splitFace_eq_inr_iff.2 (splitFaceCornerOrigin_inr_true_of_not_lt (lt_irrefl _))

/-- The reverse of the new dart is the first side of the face `d⁻¹ aₚ ⋯ aₙ₋₁`. -/
theorem outgoing_splitFace_inr_false_zero :
    (C.splitFace f p).outgoing ⟨.inr false, ⟨0, Nat.succ_pos _⟩⟩ = .inr false :=
  outgoing_splitFace_eq_inr_iff.2 (splitFaceCornerOrigin_inr_false_of_eq_zero rfl)

/-- The side occurrence of `C.splitFace f p` coming from a side occurrence of `C`, and the two
occurrences of the new edge: the side `aₖ` of `f` is the side `k` of the face `a₀ ⋯ aₚ₋₁ d` if
`k < p` and the side `k - p + 1` of the face `d⁻¹ aₚ ⋯ aₙ₋₁` otherwise. -/
def splitFaceCornerOfOrigin [DecidableEq C.Face] : C.Corner ⊕ Bool → (C.splitFace f p).Corner
  | .inl ⟨g, k⟩ => if h : g = f then
      if hk : (k : ℕ) < p then ⟨.inr true, ⟨k, Nat.lt_succ_of_lt hk⟩⟩
      else ⟨.inr false, ⟨k - p + 1, by
        subst h; exact Nat.succ_lt_succ (Nat.sub_lt_sub_right (not_lt.1 hk) k.2)⟩⟩
    else ⟨.inl ⟨g, h⟩, k⟩
  | .inr true => ⟨.inr true, ⟨p, Nat.lt_succ_self _⟩⟩
  | .inr false => ⟨.inr false, ⟨0, Nat.succ_pos _⟩⟩

variable {C f p} in
theorem splitFaceCornerOrigin_splitFaceCornerOfOrigin [DecidableEq C.Face] (x : C.Corner ⊕ Bool) :
    C.splitFaceCornerOrigin f p (C.splitFaceCornerOfOrigin f p x) = x := by
  obtain ⟨g, k⟩ | _ | _ := x
  · by_cases hg : g = f
    · subst hg
      by_cases hk : (k : ℕ) < p
      · simp only [splitFaceCornerOfOrigin, hk, ↓reduceDIte]
        exact splitFaceCornerOrigin_inr_true_of_lt hk
      · simp only [splitFaceCornerOfOrigin, hk, ↓reduceDIte]
        rw [splitFaceCornerOrigin_inr_false_of_ne_zero (Nat.succ_ne_zero _)]
        exact congrArg (fun j => (Sum.inl ⟨g, j⟩ : C.Corner ⊕ Bool))
          (Fin.ext (by dsimp only; omega))
    · simp [splitFaceCornerOfOrigin, hg]
  · exact splitFaceCornerOrigin_inr_false_of_eq_zero rfl
  · exact splitFaceCornerOrigin_inr_true_of_not_lt (lt_irrefl _)

variable {C f p} in
theorem splitFaceCornerOfOrigin_splitFaceCornerOrigin [DecidableEq C.Face]
    (c : (C.splitFace f p).Corner) :
    C.splitFaceCornerOfOrigin f p (C.splitFaceCornerOrigin f p c) = c := by
  obtain ⟨g | _ | _, k⟩ := c
  · simp [splitFaceCornerOfOrigin, g.2]
  · by_cases hk : (k : ℕ) = 0
    · rw [splitFaceCornerOrigin_inr_false_of_eq_zero hk]
      exact congrArg (Sigma.mk _) (Fin.ext hk.symm)
    · rw [splitFaceCornerOrigin_inr_false_of_ne_zero hk]
      have hlt : ¬p + (k : ℕ) - 1 < p := by omega
      simp only [splitFaceCornerOfOrigin, hlt, ↓reduceDIte]
      exact congrArg (Sigma.mk _) (Fin.ext (by dsimp only; omega))
  · have hk2 : (k : ℕ) < p + 1 := k.2
    by_cases hk : (k : ℕ) < p
    · rw [splitFaceCornerOrigin_inr_true_of_lt hk]
      simp [splitFaceCornerOfOrigin, hk]
    · rw [splitFaceCornerOrigin_inr_true_of_not_lt hk]
      exact congrArg (Sigma.mk _) (Fin.ext (by dsimp only; omega))

/-- The side occurrences of `C.splitFace f p` are those of `C` together with the two occurrences
of the new edge: `Sum.inr true` is the last side of the face `a₀ ⋯ aₚ₋₁ d` and `Sum.inr false` is
the first side of the face `d⁻¹ aₚ ⋯ aₙ₋₁`. -/
def splitFaceCornerEquiv [DecidableEq C.Face] : (C.splitFace f p).Corner ≃ C.Corner ⊕ Bool where
  toFun := C.splitFaceCornerOrigin f p
  invFun := C.splitFaceCornerOfOrigin f p
  left_inv := splitFaceCornerOfOrigin_splitFaceCornerOrigin
  right_inv := splitFaceCornerOrigin_splitFaceCornerOfOrigin

@[simp] theorem splitFaceCornerEquiv_apply [DecidableEq C.Face] (c : (C.splitFace f p).Corner) :
    C.splitFaceCornerEquiv f p c = C.splitFaceCornerOrigin f p c := (rfl)

@[simp] theorem splitFaceCornerEquiv_symm_apply [DecidableEq C.Face] (x : C.Corner ⊕ Bool) :
    (C.splitFaceCornerEquiv f p).symm x = C.splitFaceCornerOfOrigin f p x := (rfl)

theorem splitFaceCornerOrigin_injective : Function.Injective (C.splitFaceCornerOrigin f p) := by
  classical exact (C.splitFaceCornerEquiv f p).injective

/-! ### Side counts and link degrees -/

/-- The side occurrences of `C.splitFace f p` attached along an old dart `e` are those of `C`
attached along `e`. -/
private noncomputable def outgoingFiberSplitFaceEquiv (e : C.graph.E) :
    {c : C.Corner // C.outgoing c = e} ≃
      {c : (C.splitFace f p).Corner // (C.splitFace f p).outgoing c = .inl e} := by
  classical
  refine Equiv.ofBijective (fun c => ⟨C.splitFaceCornerOfOrigin f p (.inl c.1),
    outgoing_splitFace_eq_inl_iff.2 ⟨c.1, splitFaceCornerOrigin_splitFaceCornerOfOrigin _, c.2⟩⟩)
    ⟨fun c c' h => ?_, fun ⟨c, hc⟩ => ?_⟩
  · exact Subtype.ext (Sum.inl_injective
      ((C.splitFaceCornerEquiv f p).symm.injective (congrArg Subtype.val h)))
  · obtain ⟨c₀, h₀, he⟩ := outgoing_splitFace_eq_inl_iff.1 hc
    exact ⟨⟨c₀, he⟩, Subtype.ext ((congrArg (C.splitFaceCornerOfOrigin f p) h₀.symm).trans
      (splitFaceCornerOfOrigin_splitFaceCornerOrigin c))⟩

/-- Splitting a face does not change the number of face sides attached along an old dart. -/
@[simp] theorem sideCount_splitFace_inl (e : C.graph.E) :
    (C.splitFace f p).sideCount (.inl e) = C.sideCount e := by
  rw [sideCount_def, sideCount_def]
  exact (Nat.card_congr (C.outgoingFiberSplitFaceEquiv f p e)).symm

/-- Each of the two new darts lies on exactly one face side: the new side occurs once on each of
the two new faces. -/
@[simp] theorem sideCount_splitFace_inr (b : Bool) :
    (C.splitFace f p).sideCount (.inr b) = 1 := by
  classical
  rw [sideCount_def, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun c c' => Subtype.ext (C.splitFaceCornerOrigin_injective f p
      ((outgoing_splitFace_eq_inr_iff.1 c.2).trans (outgoing_splitFace_eq_inr_iff.1 c'.2).symm))⟩,
    ⟨⟨C.splitFaceCornerOfOrigin f p (.inr b), outgoing_splitFace_eq_inr_iff.2
      (splitFaceCornerOrigin_splitFaceCornerOfOrigin _)⟩⟩⟩

/-- Splitting a face does not change the link degree of an old germ. -/
@[simp] theorem linkDegree_splitFace_inl (e : C.graph.E) :
    (C.splitFace f p).linkDegree (.inl e) = C.linkDegree e := by
  rw [linkDegree_eq_natCard_sum, linkDegree_eq_natCard_sum]
  exact (Nat.card_congr ((C.outgoingFiberSplitFaceEquiv f p _).sumCongr
    (C.outgoingFiberSplitFaceEquiv f p e))).symm

/-- Each of the two new germs has degree two in its link: the new edge is interior. -/
@[simp] theorem linkDegree_splitFace_inr (b : Bool) :
    (C.splitFace f p).linkDegree (.inr b) = 2 := by
  have (b' : Bool) :
      Finite {c : (C.splitFace f p).Corner // (C.splitFace f p).outgoing c = .inr b'} :=
    Nat.finite_of_card_ne_zero (by rw [← sideCount_def, sideCount_splitFace_inr]; simp)
  rw [linkDegree_eq_natCard_sum, SerreGraph.addEdge_rev_inr, Nat.card_sum, ← sideCount_def,
    ← sideCount_def, sideCount_splitFace_inr, sideCount_splitFace_inr]

/-! ### Euler characteristic -/

/-- Splitting a face adds one face. -/
theorem card_face_splitFace [Finite C.Face] :
    Nat.card (C.splitFace f p).Face = Nat.card C.Face + 1 := by
  classical
  rw [← Nat.card_congr (Equiv.optionSubtypeNe f), Finite.card_option, Nat.card_sum,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

/-- Splitting a face does not change the Euler characteristic: it adds one edge and one face. -/
@[simp] theorem eulerChar_splitFace [Finite C.graph.GeomEdge] [Finite C.Face] :
    (C.splitFace f p).eulerChar = C.eulerChar := by
  rw [eulerChar_def, eulerChar_def, card_face_splitFace, SerreGraph.card_addEdge_geomEdge]
  push_cast
  ring

/-! ### Orientability -/

/-- The face of `C` containing a face of `C.splitFace f p`. -/
def splitFaceOriginFace : (C.splitFace f p).Face → C.Face
  | .inl g => g.1
  | .inr _ => f

@[simp] theorem splitFaceOriginFace_inl (g : {g : C.Face // g ≠ f}) :
    C.splitFaceOriginFace f p (.inl g) = g.1 := (rfl)

@[simp] theorem splitFaceOriginFace_inr (b : Bool) : C.splitFaceOriginFace f p (.inr b) = f :=
  (rfl)

variable {C f p} in
/-- A side occurrence of `C.splitFace f p` coming from a side occurrence of `C` lies on a face
contained in the face of that occurrence. -/
theorem splitFaceOriginFace_fst_of_eq_inl {c : (C.splitFace f p).Corner} {c₀ : C.Corner}
    (h : C.splitFaceCornerOrigin f p c = .inl c₀) : C.splitFaceOriginFace f p c.1 = c₀.1 := by
  obtain ⟨g | _ | _, k⟩ := c
  · obtain rfl := Sum.inl_injective h
    rfl
  · by_cases hk : (k : ℕ) = 0
    · rw [splitFaceCornerOrigin_inr_false_of_eq_zero hk] at h
      cases h
    · rw [splitFaceCornerOrigin_inr_false_of_ne_zero hk] at h
      obtain rfl := Sum.inl_injective h
      rfl
  · by_cases hk : (k : ℕ) < p
    · rw [splitFaceCornerOrigin_inr_true_of_lt hk] at h
      obtain rfl := Sum.inl_injective h
      rfl
    · rw [splitFaceCornerOrigin_inr_true_of_not_lt hk] at h
      cases h

variable {C f p} in
/-- An occurrence of the new edge lies on a face contained in the split face. -/
theorem splitFaceOriginFace_fst_of_eq_inr {c : (C.splitFace f p).Corner} {b : Bool}
    (h : C.splitFaceCornerOrigin f p c = .inr b) : C.splitFaceOriginFace f p c.1 = f := by
  obtain ⟨g | _, k⟩ := c
  · cases h
  · rfl

variable {C f p} in
/-- The oriented side of a side occurrence of `C.splitFace f p` coming from a side occurrence of
`C`, for orientations agreeing on the two faces. -/
private theorem orientedSide_splitFace_of_eq_inl {σ' : (C.splitFace f p).Face → Bool}
    {σ : C.Face → Bool} {c : (C.splitFace f p).Corner} {c₀ : C.Corner}
    (h : C.splitFaceCornerOrigin f p c = .inl c₀) (hσ : σ' c.1 = σ c₀.1) :
    (C.splitFace f p).orientedSide σ' c = .inl (C.orientedSide σ c₀) := by
  have ho : (C.splitFace f p).outgoing c = .inl (C.outgoing c₀) :=
    outgoing_splitFace_eq_inl_iff.2 ⟨c₀, h, rfl⟩
  rcases hs : σ c₀.1 with _ | _
  · rw [(C.splitFace f p).orientedSide_of_eq_false (hσ.trans hs), C.orientedSide_of_eq_false hs,
      ho, SerreGraph.addEdge_rev_inl]
  · rw [(C.splitFace f p).orientedSide_of_eq_true (hσ.trans hs), C.orientedSide_of_eq_true hs, ho]

variable {C f p} in
/-- The oriented side of an occurrence of the new edge. -/
private theorem orientedSide_splitFace_of_eq_inr {σ' : (C.splitFace f p).Face → Bool}
    {c : (C.splitFace f p).Corner} {b : Bool} (h : C.splitFaceCornerOrigin f p c = .inr b) :
    (C.splitFace f p).orientedSide σ' c = .inr (cond (σ' c.1) b !b) := by
  have ho := outgoing_splitFace_eq_inr_iff.2 h
  rcases hs : σ' c.1 with _ | _
  · rw [(C.splitFace f p).orientedSide_of_eq_false hs, ho, SerreGraph.addEdge_rev_inr,
      Bool.cond_false]
  · rw [(C.splitFace f p).orientedSide_of_eq_true hs, ho, Bool.cond_true]

variable {C} in
/-- Splitting a face of an orientable complex gives an orientable complex: the two new faces
inherit the orientation of the face they come from. -/
theorem IsOrientable.splitFace (h : C.IsOrientable) : (C.splitFace f p).IsOrientable := by
  obtain ⟨σ, hσ⟩ := C.isOrientable_iff.1 h
  have hinj := C.splitFaceCornerOrigin_injective f p
  refine (C.splitFace f p).isOrientable_iff.2
    ⟨σ ∘ C.splitFaceOriginFace f p, fun c c' hne hg => ?_⟩
  rw [outgoing_splitFace, outgoing_splitFace] at hg
  rcases hc : C.splitFaceCornerOrigin f p c with c₀ | b <;>
    rcases hc' : C.splitFaceCornerOrigin f p c' with c₀' | b'
  · rw [hc, hc', Sum.map_inl, Sum.map_inl, SerreGraph.toGeomEdge_addEdge_inl_eq_iff] at hg
    rw [orientedSide_splitFace_of_eq_inl hc (congrArg σ (splitFaceOriginFace_fst_of_eq_inl hc)),
      orientedSide_splitFace_of_eq_inl hc' (congrArg σ (splitFaceOriginFace_fst_of_eq_inl hc')),
      hσ c₀ c₀' (fun h => hne (hinj (hc.trans (h ▸ hc'.symm)))) hg, SerreGraph.addEdge_rev_inl]
  · rw [hc, hc'] at hg
    exact absurd hg (SerreGraph.toGeomEdge_addEdge_inl_ne_inr _ _)
  · rw [hc, hc'] at hg
    exact absurd hg.symm (SerreGraph.toGeomEdge_addEdge_inl_ne_inr _ _)
  · have hb : b ≠ b' := fun h => hne (hinj (hc.trans (h ▸ hc'.symm)))
    rw [orientedSide_splitFace_of_eq_inr hc, orientedSide_splitFace_of_eq_inr hc',
      SerreGraph.addEdge_rev_inr, Function.comp_apply, Function.comp_apply,
      splitFaceOriginFace_fst_of_eq_inr hc, splitFaceOriginFace_fst_of_eq_inr hc']
    cases b <;> cases b' <;> cases σ f <;> simp_all

variable {C f p} in
private theorem splitFaceCornerOfOrigin_ne [DecidableEq C.Face] {x y : C.Corner ⊕ Bool}
    (h : x ≠ y) : C.splitFaceCornerOfOrigin f p x ≠ C.splitFaceCornerOfOrigin f p y :=
  fun hxy => h ((C.splitFaceCornerEquiv f p).symm.injective hxy)

variable {C f p} in
/-- An orientation of `C.splitFace f p` compatible along the new edge orients the two new faces
alike. -/
private theorem orientation_inr_false_eq_inr_true {σ' : (C.splitFace f p).Face → Bool}
    (hσ' : ∀ c c' : (C.splitFace f p).Corner, c ≠ c' →
      (C.splitFace f p).graph.toGeomEdge ((C.splitFace f p).outgoing c) =
        (C.splitFace f p).graph.toGeomEdge ((C.splitFace f p).outgoing c') →
      (C.splitFace f p).orientedSide σ' c' =
        (C.splitFace f p).graph.rev ((C.splitFace f p).orientedSide σ' c)) :
    σ' (.inr false) = σ' (.inr true) := by
  classical
  have hd : (Sum.inr (cond (σ' (.inr false)) false true) : C.graph.E ⊕ Bool) =
      .inr !(cond (σ' (.inr true)) true false) := by
    have := hσ' _ _ (splitFaceCornerOfOrigin_ne (x := .inr true) (y := .inr false) (by simp)) (by
      rw [outgoing_splitFace, outgoing_splitFace, splitFaceCornerOrigin_splitFaceCornerOfOrigin,
        splitFaceCornerOrigin_splitFaceCornerOfOrigin]
      exact ((C.splitFace f p).graph.toGeomEdge_rev (.inr true)).symm)
    rwa [orientedSide_splitFace_of_eq_inr (splitFaceCornerOrigin_splitFaceCornerOfOrigin _),
      orientedSide_splitFace_of_eq_inr (splitFaceCornerOrigin_splitFaceCornerOfOrigin _),
      SerreGraph.addEdge_rev_inr] at this
  cases h1 : σ' (.inr true) <;> cases h2 : σ' (.inr false) <;> simp [h1, h2] at hd ⊢

variable {C f p} in
/-- If the complex obtained by splitting a face is orientable, so is the original complex: the two
new faces are oriented compatibly along the new edge, and the face they come from takes their
common orientation. -/
theorem IsOrientable.of_splitFace (h : (C.splitFace f p).IsOrientable) : C.IsOrientable := by
  classical
  obtain ⟨σ', hσ'⟩ := (C.splitFace f p).isOrientable_iff.1 h
  have hs := orientation_inr_false_eq_inr_true hσ'
  let σ : C.Face → Bool := fun g => if hg : g = f then σ' (.inr true) else σ' (.inl ⟨g, hg⟩)
  have hσ : ∀ g', σ' g' = σ (C.splitFaceOriginFace f p g') := by
    rintro (g | _ | _)
    · simp [σ, g.2]
    · simp [σ, hs]
    · simp [σ]
  refine C.isOrientable_iff.2 ⟨σ, fun c₀ c₀' hc hg => ?_⟩
  have h₀ := splitFaceCornerOrigin_splitFaceCornerOfOrigin (f := f) (p := p) (.inl c₀)
  have h₀' := splitFaceCornerOrigin_splitFaceCornerOfOrigin (f := f) (p := p) (.inl c₀')
  have := hσ' _ _ (splitFaceCornerOfOrigin_ne (f := f) (p := p) (x := .inl c₀) (y := .inl c₀')
    (by simpa using hc)) (by
    rw [outgoing_splitFace, outgoing_splitFace, h₀, h₀']
    exact SerreGraph.toGeomEdge_addEdge_inl_eq_iff.2 hg)
  rw [orientedSide_splitFace_of_eq_inl h₀
      ((hσ _).trans (congrArg σ (splitFaceOriginFace_fst_of_eq_inl h₀))),
    orientedSide_splitFace_of_eq_inl h₀'
      ((hσ _).trans (congrArg σ (splitFaceOriginFace_fst_of_eq_inl h₀'))),
    SerreGraph.addEdge_rev_inl] at this
  exact Sum.inl_injective this

/-- Splitting a face does not change orientability. -/
@[simp] theorem isOrientable_splitFace_iff : (C.splitFace f p).IsOrientable ↔ C.IsOrientable :=
  ⟨IsOrientable.of_splitFace, IsOrientable.splitFace f p⟩

end PolygonalComplex

end TauCeti
