/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Conway

/-!
# The Seifert-matrix Alexander polynomial of a closed braid word

Seifert's algorithm on the closure of a braid word `w` on `n` strands gives the canonical Seifert
surface, with Seifert matrix `TauCeti.BraidWord.seifertMatrix w`. This surface is connected exactly
when every level `0, …, n - 2` carries a letter of `w`, and then the Conway-normalized Alexander
polynomial of the closure, in the square root `s` of the Alexander variable, is
`det(s V - s⁻¹ Vᵀ)` (`Matrix.seifertConwayDeterminant`). Otherwise the closure is a split link and
the polynomial is `0`. This is `TauCeti.BraidWord.seifertAlexander w`.

It does not depend on the word representing a braid: Artin relations change the Seifert matrix by
relabellings and unimodular congruences, and free cancellation by an elementary enlargement, or by
a zero row and column when it joins two components of the canonical surface. Cyclic rotation and
Markov stabilization keep it too, and it satisfies the Conway skein relation
`Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`.

## Main definitions

* `TauCeti.BraidWord.seifertAlexander`: the Seifert-matrix Alexander polynomial of the closure of
  a braid word.

## Main results

* `TauCeti.BraidWord.seifertAlexander_eq_of_toBraid_eq`: it only depends on the braid.
* `TauCeti.BraidWord.seifertAlexander_rotate` and `TauCeti.BraidWord.seifertAlexander_stabilize`:
  it is unchanged by cyclic rotation and Markov stabilization.
* `TauCeti.BraidWord.seifertAlexander_strandIncl` and `TauCeti.BraidWord.seifertAlexander_nil_one`:
  it vanishes once an uncrossed strand is added, and is `1` on the unknot.
* `TauCeti.BraidWord.seifertAlexander_skein`: it satisfies the Conway skein relation.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8, Theorem 8.6 (the Conway-normalized skein relation).
-/

public section

namespace TauCeti

open BraidGroup LaurentPolynomial Matrix

namespace BraidWord

variable {n : ℕ} {w w' : BraidWord n}

/-- The **Seifert-matrix Alexander polynomial** of the closure of a braid word, in the square root
`s` of the Alexander variable: `det(s V - s⁻¹ Vᵀ)` for the Seifert matrix `V` of the canonical
Seifert surface when every level carries a letter, so that this surface is connected, and `0`
otherwise, when the closure is a split link. It only depends on the braid the word represents
(`TauCeti.BraidWord.seifertAlexander_eq_of_toBraid_eq`). -/
noncomputable def seifertAlexander (w : BraidWord n) : ℤ[T;T⁻¹] :=
  if ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i then w.seifertMatrix.seifertConwayDeterminant else 0

/-- The defining case split of the Seifert-matrix Alexander polynomial. -/
theorem seifertAlexander_def (w : BraidWord n) :
    w.seifertAlexander =
      if ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i then w.seifertMatrix.seifertConwayDeterminant
      else 0 :=
  (rfl)

/-- If every level carries a letter, the Seifert-matrix Alexander polynomial is the Seifert
determinant of the canonical Seifert surface. -/
theorem seifertAlexander_of_forall (h : ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i) :
    w.seifertAlexander = w.seifertMatrix.seifertConwayDeterminant :=
  ite_eq_left h

/-- If some level carries no letter, the closure is split and its Seifert-matrix Alexander
polynomial vanishes. -/
theorem seifertAlexander_eq_zero_of_not_exists {i : Fin (n - 1)} (h : ¬∃ x ∈ w, x.1 = i) :
    w.seifertAlexander = 0 :=
  ite_eq_right fun h' ↦ h (h' i)

/-- Words using the same levels whose Seifert determinants agree when every level is used have the
same Seifert-matrix Alexander polynomial. -/
private theorem seifertAlexander_eq_of_exists_iff
    (hlevel : ∀ i : Fin (n - 1), (∃ x ∈ w, x.1 = i) ↔ ∃ x ∈ w', x.1 = i)
    (hdet : (∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i) →
      w.seifertMatrix.seifertConwayDeterminant = w'.seifertMatrix.seifertConwayDeterminant) :
    w.seifertAlexander = w'.seifertAlexander := by
  by_cases h : ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i
  · rw [seifertAlexander_of_forall h, seifertAlexander_of_forall fun i ↦ (hlevel i).1 (h i),
      hdet h]
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [seifertAlexander_eq_zero_of_not_exists hi,
      seifertAlexander_eq_zero_of_not_exists (mt (hlevel i).2 hi)]

/-- An Artin relation step keeps the Seifert-matrix Alexander polynomial. -/
theorem seifertAlexander_eq_of_artinStep (h : ArtinStep w w') :
    w.seifertAlexander = w'.seifertAlexander := by
  refine seifertAlexander_eq_of_exists_iff (fun l ↦ ?_)
    fun _ ↦ seifertConwayDeterminant_seifertMatrix_eq_of_artinStep h
  cases h <;> simp only [List.mem_append, List.mem_cons] <;> grind

/-- Inserting an inverse pair of letters keeps the Seifert-matrix Alexander polynomial. -/
theorem seifertAlexander_insert (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertAlexander = (u ++ v).seifertAlexander := by
  by_cases hi : ∃ x ∈ u ++ v, x.1 = i
  · refine seifertAlexander_eq_of_exists_iff (fun l ↦ ?_)
      fun _ ↦ seifertConwayDeterminant_seifertMatrix_insert u v i ε hi
    obtain ⟨y, hy, hyi⟩ := hi
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    grind
  · -- the inserted pair joins two components of the canonical surface
    rw [seifertAlexander_eq_zero_of_not_exists hi, seifertAlexander_def,
      seifertConwayDeterminant_seifertMatrix_insert_eq_zero_of_not_exists u v i ε hi, ite_self]

/-- A free insertion or deletion of an inverse pair keeps the Seifert-matrix Alexander
polynomial. -/
theorem FreeCancelStep.seifertAlexander_eq (h : FreeCancelStep w w') :
    w.seifertAlexander = w'.seifertAlexander := by
  cases h with
  | insert u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact (seifertAlexander_insert u v i ε).symm
  | delete u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact seifertAlexander_insert u v i ε

/-- Braid words connected by Artin relations and free cancellation have the same Seifert-matrix
Alexander polynomial. -/
theorem WordEquiv.seifertAlexander_eq (h : WordEquiv w w') :
    w.seifertAlexander = w'.seifertAlexander :=
  WordEquiv.induction seifertAlexander_eq_of_artinStep FreeCancelStep.seifertAlexander_eq
    (fun _ ↦ rfl) (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih') h

/-- **The Seifert-matrix Alexander polynomial depends only on the braid.** -/
theorem seifertAlexander_eq_of_toBraid_eq (h : w.toBraid = w'.toBraid) :
    w.seifertAlexander = w'.seifertAlexander :=
  (toBraid_eq_iff_wordEquiv.mp h).seifertAlexander_eq

/-- Cyclically rotating a braid word keeps the Seifert-matrix Alexander polynomial. -/
@[simp]
theorem seifertAlexander_rotate (w : BraidWord n) (k : ℕ) :
    seifertAlexander (n := n) (w.rotate k) = w.seifertAlexander :=
  seifertAlexander_eq_of_exists_iff (fun _ ↦ by simp only [List.mem_rotate])
    fun _ ↦ seifertConwayDeterminant_seifertMatrix_rotate w k

/-- Markov stabilization keeps the Seifert-matrix Alexander polynomial. -/
@[simp]
theorem seifertAlexander_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    (w.stabilize ε).seifertAlexander = w.seifertAlexander := by
  have hlevel : (∀ i : Fin (n + 1), ∃ x ∈ w.stabilize ε, x.1 = i) ↔
      ∀ i : Fin n, ∃ x ∈ w, x.1 = i := by
    refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
    · obtain ⟨x, hx, hxi⟩ := h i.castSucc
      simp only [stabilize_def, strandIncl_def, List.mem_append, List.mem_map,
        List.mem_singleton] at hx
      rcases hx with ⟨y, hy, rfl⟩ | rfl
      · exact ⟨y, hy, Fin.castSucc_injective _ hxi⟩
      · exact absurd hxi (Fin.castSucc_ne_last i).symm
    · induction i using Fin.lastCases with
      | last => exact ⟨(Fin.last n, ε), by simp [stabilize_def], rfl⟩
      | cast i =>
        obtain ⟨y, hy, rfl⟩ := h i
        exact ⟨(y.1.castSucc, y.2), by simp [stabilize_def, strandIncl_def, hy], rfl⟩
  by_cases h : ∀ i : Fin n, ∃ x ∈ w, x.1 = i
  · rw [seifertAlexander_of_forall (w := w) h,
      seifertAlexander_of_forall (w := w.stabilize ε) (hlevel.2 h),
      seifertConwayDeterminant_seifertMatrix_stabilize]
  · obtain ⟨i, hi⟩ := not_forall.1 (mt hlevel.1 h)
    obtain ⟨j, hj⟩ := not_forall.1 h
    rw [seifertAlexander_eq_zero_of_not_exists (w := w.stabilize ε) (i := i) hi,
      seifertAlexander_eq_zero_of_not_exists (w := w) (i := j) hj]

/-- A word with an uncrossed strand added closes to a split link: its Seifert-matrix Alexander
polynomial vanishes. -/
@[simp]
theorem seifertAlexander_strandIncl (w : BraidWord (n + 1)) : w.strandIncl.seifertAlexander = 0 :=
  seifertAlexander_eq_zero_of_not_exists (i := Fin.last n) fun ⟨x, hx, hxi⟩ ↦ by
    rw [strandIncl_def] at hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact Fin.castSucc_ne_last _ hxi

/-- The empty word on one strand closes to the unknot, whose Seifert-matrix Alexander polynomial
is `1`. -/
@[simp]
theorem seifertAlexander_nil_one : seifertAlexander ([] : BraidWord 1) = 1 := by
  have : IsEmpty (seifertLoops ([] : BraidWord 1)) :=
    ⟨fun p ↦ by simpa using ((mem_seifertLoops _).1 p.2).snd_lt_length⟩
  rw [seifertAlexander_of_forall fun i ↦ i.elim0, seifertConwayDeterminant_of_isEmpty]

/-- **The Conway skein relation for the Seifert-matrix Alexander polynomial of a closed braid.**
The closures of `u σᵢ v`, `u σᵢ⁻¹ v` and `u v` satisfy `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`. -/
theorem seifertAlexander_skein (u v : BraidWord n) (i : Fin (n - 1)) :
    (u ++ (i, 1) :: v).seifertAlexander - (u ++ (i, -1) :: v).seifertAlexander =
      (T (-1) - T 1) * (u ++ v).seifertAlexander := by
  by_cases hi : ∃ x ∈ u ++ v, x.1 = i
  · -- all three words use the same levels
    have hlevel (ε : ℤˣ) (l : Fin (n - 1)) :
        (∃ x ∈ u ++ (i, ε) :: v, x.1 = l) ↔ ∃ x ∈ u ++ v, x.1 = l := by
      obtain ⟨y, hy, hyi⟩ := hi
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      grind
    by_cases h : ∀ l : Fin (n - 1), ∃ x ∈ u ++ v, x.1 = l
    · rw [seifertAlexander_of_forall h, seifertAlexander_of_forall fun l ↦ (hlevel 1 l).2 (h l),
        seifertAlexander_of_forall fun l ↦ (hlevel (-1) l).2 (h l),
        seifertConwayDeterminant_seifertMatrix_skein u v i hi]
    · obtain ⟨l, hl⟩ := not_forall.1 h
      rw [seifertAlexander_eq_zero_of_not_exists hl,
        seifertAlexander_eq_zero_of_not_exists (mt (hlevel 1 l).1 hl),
        seifertAlexander_eq_zero_of_not_exists (mt (hlevel (-1) l).1 hl), sub_zero, mul_zero]
  · -- the changed letter is alone on its level, so its sign does not matter
    rw [seifertAlexander_eq_zero_of_not_exists hi, mul_zero, sub_eq_zero]
    refine seifertAlexander_eq_of_exists_iff (fun l ↦ ?_) fun _ ↦
      seifertConwayDeterminant_seifertMatrix_append_cons_of_not_exists u v i 1 (-1) hi
    simp only [List.mem_append, List.mem_cons]
    grind

end BraidWord

end TauCeti
