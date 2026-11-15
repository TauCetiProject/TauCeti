/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence
public import TauCeti.KnotTheory.BraidWord.FreeCancellation.SeifertMatrix
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.BraidRelation
public import TauCeti.KnotTheory.SeifertMatrix.Polynomial.Conway

import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Conway

/-!
# The Conway polynomial from a braid word

Seifert's algorithm gives a possibly disconnected surface for the closure of a braid word.
Its matrix alone forgets the number of components of that surface: for instance the empty
word on two strands has an empty matrix, just like the unknot. To obtain a link invariant,
use the matrix's Conway polynomial only when every level carries a letter, and zero otherwise.
The former condition says that the chain of Seifert discs is connected; in the latter case
the closure is split.

`TauCeti.BraidWord.conwayPolynomial` incorporates this correction and is unchanged by Artin
relations and free cancellation. Consequently any word representing the same braid computes
the same polynomial. On an unused level, inserting an inverse pair can join components of
the surface, but then the new Seifert matrix has a zero row and column, so its polynomial
vanishes. This case is essential for word independence.

The polynomial satisfies the Conway skein relation `∇₊ - ∇₋ = z ∇₀` for every crossing of the
word (`TauCeti.BraidWord.conwayPolynomial_skein`). When the changed letter is alone on its level,
both sides vanish: the smoothed word leaves that level unused, and the sign of a lone letter only
relabels the Seifert matrix.

The construction uses the canonical matrices and their elementary changes from
`TauCeti.KnotTheory.BraidWord.SeifertMatrix.Equivalence`, and the matrix polynomial from
`TauCeti.KnotTheory.SeifertMatrix.Polynomial.Conway`. Word independence lets the polynomial
descend to braids (see `TauCeti.KnotTheory.Markov.Conway`).

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapters 6 and 8
  (Seifert matrices and the Conway polynomial).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1
  (the Artin presentation).
-/

public noncomputable section

open scoped Polynomial

namespace TauCeti.BraidWord

open KnotTheory Matrix

variable {n : ℕ}

/-- Inserting an inverse pair on a level already used preserves the Conway polynomial of the
canonical Seifert matrix, including when the matrix has odd size. -/
theorem conwayPolynomial_seifertMatrix_insert (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (h : ∃ x ∈ u ++ v, x.1 = i) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.conwayPolynomial =
      (u ++ v).seifertMatrix.conwayPolynomial := by
  apply Matrix.conwayPolynomial_eq_of_alexander_eq
  · have hc := card_seifertLoops_insert u v i ε h
    omega
  · exact alexander_seifertMatrix_insert u v i ε h

/-- An inverse pair on an unused level creates a zero row and column, hence a vanishing
Conway polynomial, rather than preserving the determinant of the disconnected surface. -/
theorem conwayPolynomial_seifertMatrix_insert_of_not_exists (u v : BraidWord n)
    (i : Fin (n - 1)) (ε : ℤˣ) (h : ¬∃ x ∈ u ++ v, x.1 = i) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.conwayPolynomial = 0 := by
  obtain ⟨e, he⟩ := exists_seifertMatrix_insert_eq_fromBlocks u v i ε h
  apply Eq.symm
  apply (Matrix.conwayPolynomial_eq_iff _ _).mpr
  rw [Polynomial.eval₂_zero, ← Matrix.seifertConwayDeterminant_submatrix_equiv_self _ e, he,
    Matrix.seifertConwayDeterminant_def]
  symm
  apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
  rintro (j | j) <;> simp

/-- The Conway polynomial computed from a braid word on at least one strand. If its canonical
Seifert surface is disconnected (some level is unused), the closure is split and the value is
zero; otherwise use the polynomial of its Seifert matrix, with variable `z = s⁻¹ - s`. -/
def conwayPolynomial (w : BraidWord (n + 1)) : ℤ[X] :=
  if ∀ i, ∃ x ∈ w, x.1 = i then w.seifertMatrix.conwayPolynomial else 0

/-- The connected-surface and disconnected-surface cases of the braid-word algorithm. -/
theorem conwayPolynomial_def (w : BraidWord (n + 1)) :
    w.conwayPolynomial =
      if ∀ i, ∃ x ∈ w, x.1 = i then w.seifertMatrix.conwayPolynomial else 0 := (rfl)

/-- If all levels are used, the word polynomial is the Conway polynomial of its Seifert matrix. -/
theorem conwayPolynomial_of_forall (w : BraidWord (n + 1))
    (h : ∀ i, ∃ x ∈ w, x.1 = i) :
    w.conwayPolynomial = w.seifertMatrix.conwayPolynomial := by
  rw [conwayPolynomial_def, ite_eq_left h]

/-- A word omitting a level has zero Conway polynomial. -/
theorem conwayPolynomial_of_not_exists (w : BraidWord (n + 1)) (i : Fin (n + 1 - 1))
    (h : ¬∃ x ∈ w, x.1 = i) : w.conwayPolynomial = 0 := by
  have hn : ¬∀ i, ∃ x ∈ w, x.1 = i := fun hw => h (hw i)
  rw [conwayPolynomial_def, ite_eq_right hn]

/-- Agreement on whether all levels occur, together with matrix-polynomial agreement in that
case, implies agreement of the corrected word polynomials, even across different strand counts. -/
theorem conwayPolynomial_eq_of_forall_mem_map_iff {m : ℕ}
    {w : BraidWord (n + 1)} {w' : BraidWord (m + 1)}
    (hs : (∀ i, i ∈ w.map Prod.fst) ↔ ∀ i, i ∈ w'.map Prod.fst)
    (hM : (∀ i, ∃ x ∈ w, x.1 = i) →
      w.seifertMatrix.conwayPolynomial = w'.seifertMatrix.conwayPolynomial) :
    w.conwayPolynomial = w'.conwayPolynomial := by
  simp only [List.mem_map] at hs
  simp only [conwayPolynomial_def, hs]
  split_ifs with h
  · exact hM (hs.mpr h)
  · rfl

/-- Inserting or deleting an adjacent inverse pair preserves the corrected word polynomial. -/
theorem conwayPolynomial_insert (u v : BraidWord (n + 1)) (i : Fin (n + 1 - 1)) (ε : ℤˣ) :
    (u ++ (i, ε) :: (i, -ε) :: v).conwayPolynomial = (u ++ v).conwayPolynomial := by
  by_cases h : ∃ x ∈ u ++ v, x.1 = i
  · apply conwayPolynomial_eq_of_forall_mem_map_iff
    · have hi := List.mem_map.mpr h
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      grind
    · exact fun _ ↦ conwayPolynomial_seifertMatrix_insert u v i ε h
  · rw [conwayPolynomial_of_not_exists (u ++ v) i h, conwayPolynomial_def,
      conwayPolynomial_seifertMatrix_insert_of_not_exists u v i ε h]
    simp

/-- A free insertion or deletion preserves the corrected Conway polynomial. -/
theorem FreeCancelStep.conwayPolynomial_eq {w w' : BraidWord (n + 1)}
    (h : FreeCancelStep w w') : w.conwayPolynomial = w'.conwayPolynomial := by
  cases h with
  | insert u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact (conwayPolynomial_insert u v i ε).symm
  | delete u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact conwayPolynomial_insert u v i ε

/-- An Artin relation preserves the corrected Conway polynomial. -/
theorem conwayPolynomial_eq_of_artinStep {w w' : BraidWord (n + 1)} (h : ArtinStep w w') :
    w.conwayPolynomial = w'.conwayPolynomial := by
  apply conwayPolynomial_eq_of_forall_mem_map_iff
  · cases h <;>
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] <;> grind only
  · intro _
    obtain ⟨e, P, hP, he⟩ := exists_seifertMatrix_of_artinStep h
    rw [he, Matrix.conwayPolynomial_congruence_submatrix_equiv_of_det_sq_eq_one _ e
      (Int.isUnit_sq hP)]

/-- Equivalent words compute the same Conway polynomial. -/
theorem WordEquiv.conwayPolynomial_eq {w w' : BraidWord (n + 1)} (h : WordEquiv w w') :
    w.conwayPolynomial = w'.conwayPolynomial :=
  h.induction conwayPolynomial_eq_of_artinStep FreeCancelStep.conwayPolynomial_eq
    (fun _ => rfl) (fun _ ih => ih.symm) (fun _ _ ih ih' => ih.trans ih')

/-- The corrected Conway polynomial depends only on the represented braid, not on its word. -/
theorem conwayPolynomial_eq_of_toBraid_eq {w w' : BraidWord (n + 1)}
    (h : w.toBraid = w'.toBraid) : w.conwayPolynomial = w'.conwayPolynomial :=
  (toBraid_eq_iff_wordEquiv.mp h).conwayPolynomial_eq

/-- Moving the first letter to the end preserves the corrected Conway polynomial. -/
theorem conwayPolynomial_append_singleton (x : Fin (n + 1 - 1) × ℤˣ)
    (v : BraidWord (n + 1)) : (v ++ [x]).conwayPolynomial =
      conwayPolynomial (n := n) (x :: v) := by
  apply conwayPolynomial_eq_of_forall_mem_map_iff
  · simp [or_comm]
  · intro _
    obtain ⟨e, P, hP, he⟩ := exists_seifertMatrix_append_singleton x v
    rw [he, Matrix.conwayPolynomial_congruence_submatrix_equiv_of_det_sq_eq_one _ e
      (Int.isUnit_sq hP)]

/-- Cyclic rotation preserves the corrected Conway polynomial. -/
@[simp]
theorem conwayPolynomial_rotate (w : BraidWord (n + 1)) (k : ℕ) :
    (conwayPolynomial (n := n) (w.rotate k)) = w.conwayPolynomial :=
  List.apply_rotate_of_append_singleton conwayPolynomial conwayPolynomial_append_singleton w k

/-- Either sign of Markov stabilization preserves the corrected Conway polynomial. -/
@[simp]
theorem conwayPolynomial_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    (w.stabilize ε).conwayPolynomial = w.conwayPolynomial := by
  apply conwayPolynomial_eq_of_forall_mem_map_iff
  · -- Normalize the strand-index arithmetic before decomposing the finite index type.
    change (∀ i : Fin (n + 1), i ∈ (w.stabilize ε).map Prod.fst) ↔
      ∀ i : Fin n, i ∈ w.map Prod.fst
    rw [Fin.forall_iff_castSucc]
    simp [stabilize_def, strandIncl_def, List.mem_map, eq_comm]
  · intro _
    obtain ⟨e, he⟩ := exists_seifertMatrix_stabilize w ε
    rw [he, Matrix.conwayPolynomial_submatrix_equiv_self]

/-- The empty one-strand word is the unknot, whereas empty words on more strands are unlinks. -/
@[simp]
theorem conwayPolynomial_nil : conwayPolynomial (n := n) [] = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
    rw [conwayPolynomial_of_forall _ (fun i => Fin.elim0 i)]
    simpa using Matrix.conwayPolynomial_of_isEmpty (seifertMatrix (n := 1) [])
  | succ n =>
    rw [conwayPolynomial_of_not_exists _ ⟨0, by omega⟩ (by simp)]
    simp

/-- A word with an uncrossed strand added closes to a split link, of Conway polynomial zero. -/
@[simp]
theorem conwayPolynomial_strandIncl (w : BraidWord (n + 1)) : w.strandIncl.conwayPolynomial = 0 :=
  conwayPolynomial_of_not_exists _ (Fin.last n) fun ⟨x, hx, hxi⟩ ↦ by
    rw [strandIncl_def] at hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact Fin.castSucc_ne_last _ hxi

/-- **The Conway skein relation for braid words.** The closures of `u σᵢ v`, `u σᵢ⁻¹ v` and
`u v` satisfy `∇₊ - ∇₋ = z ∇₀`. -/
theorem conwayPolynomial_skein (u v : BraidWord (n + 1)) (i : Fin (n + 1 - 1)) :
    (u ++ (i, 1) :: v).conwayPolynomial - (u ++ (i, -1) :: v).conwayPolynomial =
      Polynomial.X * (u ++ v).conwayPolynomial := by
  by_cases hi : ∃ x ∈ u ++ v, x.1 = i
  · -- All three words use the same levels.
    have hlevel (ε : ℤˣ) (l : Fin (n + 1 - 1)) :
        (∃ x ∈ u ++ (i, ε) :: v, x.1 = l) ↔ ∃ x ∈ u ++ v, x.1 = l := by
      obtain ⟨y, hy, hyi⟩ := hi
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      grind
    by_cases h : ∀ l, ∃ x ∈ u ++ v, x.1 = l
    · rw [conwayPolynomial_of_forall _ h,
        conwayPolynomial_of_forall _ fun l ↦ (hlevel 1 l).2 (h l),
        conwayPolynomial_of_forall _ fun l ↦ (hlevel (-1) l).2 (h l)]
      apply LaurentPolynomial.eval₂_C_T_neg_sub_T_injective
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Matrix.eval₂_C_conwayPolynomial]
      exact seifertConwayDeterminant_seifertMatrix_skein u v i hi
    · obtain ⟨l, hl⟩ := not_forall.1 h
      rw [conwayPolynomial_of_not_exists _ l hl,
        conwayPolynomial_of_not_exists _ l (mt (hlevel 1 l).1 hl),
        conwayPolynomial_of_not_exists _ l (mt (hlevel (-1) l).1 hl), sub_zero, mul_zero]
  · -- The changed letter is alone on its level, so its sign only relabels the Seifert matrix.
    rw [conwayPolynomial_of_not_exists _ i hi, mul_zero, sub_eq_zero]
    apply conwayPolynomial_eq_of_forall_mem_map_iff
    · simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    · intro _
      obtain ⟨e, he⟩ := exists_seifertMatrix_append_cons_of_not_exists u v i 1 (-1) hi
      rw [he, Matrix.conwayPolynomial_submatrix_equiv_self]

/-- The right-handed trefoil, presented as the closure of `σ₀³`, has polynomial `1 + X²`. -/
@[simp]
theorem conwayPolynomial_trefoil :
    conwayPolynomial (n := 1) [(0, 1), (0, 1), (0, 1)] = 1 + Polynomial.X ^ 2 := by
  rw [conwayPolynomial_of_forall _ (by decide)]
  obtain ⟨e, he⟩ := seifertMatrix_trefoil
  rw [← Matrix.conwayPolynomial_submatrix_equiv_self _ e, he,
    Matrix.conwayPolynomial_transpose, KnotTheory.conwayPolynomial_trefoilSeifertMatrix]

end TauCeti.BraidWord
