/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.Group.Conj
public import TauCeti.GroupTheory.FreeGroup.Reduce

import Mathlib.Tactic.Group

/-!
# Conjugacy and cyclic rotation in free groups

Rotating a word conjugates the free-group element it represents. Together with Mathlib's
explicit cyclic-reduction conjugator, this relates rotation of cyclic reductions to
conjugacy of the original elements.

Conversely, two cyclically reduced words represent conjugate elements only if they are
rotations of each other. This gives the classical conjugacy criterion in free groups: `x` and
`y` are conjugate exactly when the cyclic reductions of their reduced words are cyclic
rotations of each other.

## Main results

* `FreeGroup.IsCyclicallyReduced.rotate`: rotations of cyclically reduced words are cyclically
  reduced.
* `FreeGroup.isConj_mk_iff_isRotated`: cyclically reduced words represent conjugate elements
  exactly when they are rotations of each other.
* `FreeGroup.isConj_iff_isRotated_reduceCyclically`: the conjugacy criterion for elements of a
  free group.

The explicit cyclic-reduction conjugator uses Mathlib's
`FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically` from
`Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`.

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter I.
-/

public section

namespace FreeGroup

variable {α : Type*}

namespace IsCyclicallyReduced

/-- Moving the first letter of a cyclically reduced word to its end gives a cyclically reduced
word. -/
private theorem append_singleton_of_cons {a : α × Bool} {L : List (α × Bool)}
    (h : IsCyclicallyReduced (a :: L)) : IsCyclicallyReduced (L ++ [a]) := by
  rcases L with _ | ⟨b, L⟩
  · simp
  obtain ⟨hred, hcyc⟩ := h
  rw [isReduced_cons_cons] at hred
  refine ⟨List.isChain_append.mpr ⟨hred.2, IsReduced.singleton, fun x hx y hy => ?_⟩,
    fun x hx y hy => ?_⟩
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hcyc x (by simpa [List.getLast?_cons] using hx) a rfl
  · simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    simp only [List.getLast?_append, List.getLast?_singleton, Option.mem_def, Option.some_or,
      Option.some.injEq] at hx
    subst hx hy
    exact hred.1

/-- A rotation of a cyclically reduced word is cyclically reduced. -/
theorem rotate {L : List (α × Bool)} (h : IsCyclicallyReduced L) (n : ℕ) :
    IsCyclicallyReduced (L.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate]
    rcases hL : L.rotate n with _ | ⟨a, L'⟩
    · simp
    · rw [hL] at ih
      simpa using append_singleton_of_cons ih

end IsCyclicallyReduced

/-- Cyclic reducedness is invariant under cyclic rotation. -/
theorem _root_.List.IsRotated.isCyclicallyReduced_iff {L L' : List (α × Bool)} (h : L ~r L') :
    IsCyclicallyReduced L ↔ IsCyclicallyReduced L' := by
  refine ⟨fun hL => ?_, fun hL' => ?_⟩
  · obtain ⟨n, rfl⟩ := h
    exact hL.rotate n
  · obtain ⟨n, rfl⟩ := h.symm
    exact hL'.rotate n

/-- A rotation of a word is cyclically reduced exactly when the word is. -/
@[simp]
theorem isCyclicallyReduced_rotate {L : List (α × Bool)} {n : ℕ} :
    IsCyclicallyReduced (L.rotate n) ↔ IsCyclicallyReduced L :=
  (List.IsRotated.forall L n).isCyclicallyReduced_iff

/-- Rotating a word is conjugation by the inverse of its initial segment. -/
theorem conj_mk_rotate (u : List (α × Bool)) (n : ℕ) :
    (mk (u.take (n % u.length)))⁻¹ * mk u * mk (u.take (n % u.length)) =
      mk (u.rotate n) := by
  let p := u.take (n % u.length)
  let q := u.drop (n % u.length)
  have hu : u = p ++ q := (List.take_append_drop _ _).symm
  have hv : u.rotate n = q ++ p := List.rotate_eq_drop_append_take_mod
  calc
    _ = (mk p)⁻¹ * (mk p * mk q) * mk p := by rw [mul_mk, ← hu]
    _ = mk q * mk p := by rw [inv_mul_cancel_left]
    _ = mk (u.rotate n) := by rw [hv, ← mul_mk]

/-- Two words related by a cyclic rotation represent conjugate elements of a free group.
The words need not be reduced. -/
theorem isConj_mk_of_isRotated {u v : List (α × Bool)} (h : u.IsRotated v) :
    IsConj (mk u) (mk v) := by
  obtain ⟨n, rfl⟩ := h
  exact isConj_iff.mpr ⟨(mk (u.take (n % u.length)))⁻¹,
    by simpa only [inv_inv] using conj_mk_rotate u n⟩

/-- The cyclic reduction of any word has an explicit group conjugator. -/
theorem mk_conjugator_mul_mk_reduceCyclically (L : List (α × Bool)) [DecidableEq α] :
    mk (reduceCyclically.conjugator L) *
        mk (reduceCyclically L) *
        (mk (reduceCyclically.conjugator L))⁻¹ = mk L := by
  rw [inv_mk, mul_mk, mul_mk, reduceCyclically.conj_conjugator_reduceCyclically]

/-- The element of any word is conjugate to the element of its cyclic reduction. -/
theorem isConj_mk_reduceCyclically (L : List (α × Bool)) [DecidableEq α] :
    IsConj (mk L) (mk (reduceCyclically L)) := by
  apply IsConj.symm
  exact isConj_iff.mpr ⟨mk (reduceCyclically.conjugator L),
    mk_conjugator_mul_mk_reduceCyclically L⟩

/-- Elements whose cyclic reductions differ by a rotation are conjugate. -/
theorem isConj_of_isRotated_reduceCyclically [DecidableEq α] {x y : FreeGroup α}
    (h : (reduceCyclically x.toWord).IsRotated (reduceCyclically y.toWord)) :
    IsConj x y := by
  simpa only [mk_toWord] using
    (isConj_mk_reduceCyclically x.toWord).trans <|
      (isConj_mk_of_isRotated h).trans (isConj_mk_reduceCyclically y.toWord).symm

/-- A word of the form `w L w⁻¹` with `w` nonempty is not cyclically reduced: its first letter
cancels against its last. -/
theorem not_isCyclicallyReduced_append_append_invRev {w : List (α × Bool)} (hw : w ≠ [])
    (L : List (α × Bool)) : ¬IsCyclicallyReduced (w ++ L ++ invRev w) := by
  obtain ⟨f, w₁, rfl⟩ := List.exists_cons_of_ne_nil hw
  intro h
  have hlast : (f :: w₁ ++ L ++ invRev (f :: w₁)).getLast? = some (f.1, !f.2) := by
    rw [invRev_cons, ← List.append_assoc,
      show invRev [f] = [(f.1, !f.2)] by simp [invRev], List.getLast?_concat]
  simpa using h.2 _ hlast f (by simp)

/-- If conjugating the element of a cyclically reduced word `u` by the element of a reduced word
`w` gives the element of a cyclically reduced word `v`, then `u` and `v` are rotations of each
other. -/
private theorem isRotated_of_mk_mul_mk_mul_inv_eq {w u v : List (α × Bool)}
    (hw : IsReduced w) (hu : IsCyclicallyReduced u) (hv : IsCyclicallyReduced v)
    (h : mk w * mk u * (mk w)⁻¹ = mk v) : u ~r v := by
  -- Induct on `w` from the right. The last letter `l` of `w` either cancels against an end of
  -- `u`, and conjugating by `l` rotates `u`, or nothing cancels, and then `v` would be the reduced
  -- word `w u w⁻¹`, which is not cyclically reduced.
  induction w using List.reverseRecOn generalizing u with
  | nil =>
    rw [← one_eq_mk, one_mul, inv_one, mul_one] at h
    rw [hu.isReduced.eq_of_mk_eq hv.isReduced h]
  | append_singleton w l ih =>
    have hw' : IsReduced w := hw.infix ⟨[], [l], by simp⟩
    have hconj : mk w * (mk [l] * mk u * (mk [l])⁻¹) * (mk w)⁻¹ = mk v := by
      rw [← h, ← mul_mk]
      group
    rcases u.eq_nil_or_concat' with rfl | ⟨u₀, c, rfl⟩
    · rw [← one_eq_mk, mul_one, mul_inv_cancel, one_eq_mk] at h
      rw [IsReduced.nil.eq_of_mk_eq hv.isReduced h]
    by_cases hhead : (u₀ ++ [c]).head? = some (l.1, !l.2)
    · -- The first letter of `u` cancels against `l`: conjugating by `l` rotates `u` once.
      obtain ⟨u₁, hu₁⟩ := List.head?_eq_some_iff.mp hhead
      have hrot : u₀ ++ [c] ~r u₁ ++ [(l.1, !l.2)] := by
        rw [hu₁]
        exact (List.isRotated_concat _ _).symm
      refine hrot.trans (ih hw' (hrot.isCyclicallyReduced_iff.mp hu) ?_)
      have e₁ : mk ((l.1, !l.2) :: u₁) = (mk [l])⁻¹ * mk u₁ := by
        rw [inv_mk_singleton, mul_mk, List.singleton_append]
      have e₂ : mk (u₁ ++ [(l.1, !l.2)]) = mk u₁ * (mk [l])⁻¹ := by
        rw [inv_mk_singleton, mul_mk]
      rw [← hconj, hu₁, e₁, e₂]
      group
    by_cases hlast : c = l
    · -- The last letter of `u` cancels against `l⁻¹`: conjugating by `l` rotates `u` back once.
      subst hlast
      have hrot : u₀ ++ [c] ~r c :: u₀ := List.isRotated_concat _ _
      refine hrot.trans (ih hw' (hrot.isCyclicallyReduced_iff.mp hu) ?_)
      have e : mk (c :: u₀) = mk [c] * mk u₀ := by
        rw [mul_mk, List.singleton_append]
      rw [← hconj, e, ← mul_mk]
      group
    -- Nothing cancels, so the conjugate is the reduced word `w l u l⁻¹ w⁻¹`, which is not
    -- cyclically reduced.
    exfalso
    have hred : IsReduced (w ++ [l] ++ (u₀ ++ [c]) ++ invRev (w ++ [l])) :=
      hw.append_append_invRev hu.isReduced (by simp) (by simpa using hhead)
        (by simpa [eq_comm] using hlast)
    have hv' := hv.isReduced.eq_of_mk_eq hred <| by
      rw [← h, inv_mk, mul_mk, mul_mk]
    exact not_isCyclicallyReduced_append_append_invRev (by simp) (u₀ ++ [c]) (hv' ▸ hv)

/-- Two cyclically reduced words represent conjugate elements of a free group exactly when they
are cyclic rotations of each other. -/
theorem isConj_mk_iff_isRotated {u v : List (α × Bool)}
    (hu : IsCyclicallyReduced u) (hv : IsCyclicallyReduced v) :
    IsConj (mk u) (mk v) ↔ u ~r v := by
  classical
  refine ⟨fun h => ?_, isConj_mk_of_isRotated⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← mk_toWord (x := g)] at hg
  exact isRotated_of_mk_mul_mk_mul_inv_eq isReduced_toWord hu hv hg

/-- **Conjugacy criterion in free groups.** Two elements of a free group are conjugate exactly
when the cyclic reductions of their reduced words are cyclic rotations of each other. -/
theorem isConj_iff_isRotated_reduceCyclically [DecidableEq α] {x y : FreeGroup α} :
    IsConj x y ↔ (reduceCyclically x.toWord).IsRotated (reduceCyclically y.toWord) := by
  refine ⟨fun h => ?_, isConj_of_isRotated_reduceCyclically⟩
  rw [← isConj_mk_iff_isRotated (reduceCyclically.isCyclicallyReduced isReduced_toWord)
    (reduceCyclically.isCyclicallyReduced isReduced_toWord)]
  rw [← mk_toWord (x := x), ← mk_toWord (x := y)] at h
  exact ((isConj_mk_reduceCyclically x.toWord).symm.trans h).trans
    (isConj_mk_reduceCyclically y.toWord)

/-- For any letters `a` and `b`, the elements `a b` and `a b⁻¹` of a free group are not
conjugate: the homomorphism to `Multiplicative ℤ` sending every generator to `ofAdd 1` maps them
to `ofAdd 2` and `ofAdd 0`. -/
theorem not_isConj_of_mul_of_of_mul_inv_of (a b : α) :
    ¬IsConj (of a * of b) (of a * (of b)⁻¹) := by
  intro h
  have := (FreeGroup.lift fun _ => Multiplicative.ofAdd (1 : ℤ)).map_isConj h
  rw [isConj_iff_eq] at this
  simp [← ofAdd_add] at this

end FreeGroup
