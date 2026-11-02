/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.ArtinEquivalence
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
public import TauCeti.KnotTheory.SeifertMatrix.Conway

import TauCeti.Data.List.Rotate
import TauCeti.KnotTheory.BraidWord.FreeCancellation.SeifertMatrix
import TauCeti.KnotTheory.BraidWord.SeifertMatrix.BraidRelation

/-!
# The Conway skein relation for the Seifert determinant of a closed braid

For a braid word `w`, Seifert's algorithm on its closure gives the canonical Seifert surface whose
Seifert matrix is `TauCeti.BraidWord.seifertMatrix w`, and `Δ(w) = det(s V - s⁻¹ Vᵀ)` is its
half-power Seifert determinant `Matrix.seifertConwayDeterminant`, with `s` the square root of the
Alexander variable. This file proves that `Δ` satisfies the oriented Conway skein relation on
braid words: changing one letter `σᵢ` to `σᵢ⁻¹` and deleting it give the three closures of a
skein triple, and

`Δ(u σᵢ v) - Δ(u σᵢ⁻¹ v) = (s⁻¹ - s) Δ(u v)`

whenever the level `i` already carries a letter of `u v`
(`TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_skein`). This is the relation that
the normalized Burau invariant satisfies (`TauCeti.MarkovBraid.normalizedBurauAlexander_skein`),
so it is the Seifert-matrix side of the comparison of the two routes to the Alexander polynomial
of a closed braid, carried out in `TauCeti.KnotTheory.BraidWord.SeifertMatrix.Burau`.

That comparison also needs `Δ` to be compatible with the moves relating braid words and with
Markov stabilization, and these are recorded here as well. An Artin relation changes the Seifert
matrix by a unimodular congruence, so it keeps `Δ`; inserting an inverse pair `σᵢ^ε σᵢ^(-ε)` keeps
`Δ` on a level already in use, where the matrix changes by an elementary enlargement, and makes it
vanish on an unused level, where the matrix gains a zero row and column. Stabilization, and
prepending a letter alone on its level, add a band but no loop, so they keep `Δ`.

The proof first moves the changed letter to the end of the word. Cyclic rotation cuts the same
closed braid at another place and changes the Seifert matrix by a unimodular congruence
(`TauCeti.BraidWord.exists_seifertMatrix_append_singleton`), so it keeps `Δ`
(`TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_rotate`). For a letter `σᵢ^ε` at the end
of the word `v σᵢ^ε`, the canonical surface is that of `v` with one more band, and the loops are
those of `v` together with the loop `α` through the last letter of level `i` in `v` and the new
band. The sign `ε` of the new band enters the Seifert matrix only through the diagonal entry at
`α`, which drops by one when `ε` goes from `-1` to `1`, and deleting the row and column of `α`
leaves the Seifert matrix of `v`. The skein calculation for a single diagonal entry
(`Matrix.seifertConwayDeterminant_add_diagonal_single`) then gives the relation.

The hypothesis on the level cannot be dropped. On two strands, `σ₁` and `σ₁⁻¹` both have the empty
Seifert matrix and determinant `1`, as does the empty word, whose canonical surface consists of two
disjoint discs: the left side of the relation vanishes and the right side does not.

## Main results

* `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_rotate`: cyclic rotation of a braid
  word keeps the Seifert determinant.
* `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_eq_of_artinStep`,
  `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_insert` and
  `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_insert_eq_zero`: Artin relations and
  free insertion on a level in use keep the Seifert determinant; free insertion on an unused level
  makes it vanish.
* `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_stabilize` and
  `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_cons_of_forall_ne`: so do Markov
  stabilization and prepending a letter alone on its level.
* `TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_skein`: the Seifert determinant of
  closed braids satisfies the Conway skein relation.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8, Theorem 8.6 (the Conway-normalized skein relation).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 3 (the Burau representation and the Alexander polynomial of a closed braid).
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory LaurentPolynomial Matrix

variable {n : ℕ}

/-! ### Cyclic rotation -/

/-- Moving the first letter of a braid word to the end keeps the Seifert determinant. -/
theorem seifertConwayDeterminant_seifertMatrix_append_singleton (x : Fin (n - 1) × ℤˣ)
    (v : BraidWord n) :
    (v ++ [x]).seifertMatrix.seifertConwayDeterminant =
      (seifertMatrix (n := n) (x :: v)).seifertConwayDeterminant := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_append_singleton x v
  rw [h, seifertConwayDeterminant_submatrix_equiv_self,
    seifertConwayDeterminant_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP)]

/-- Cyclically rotating a braid word keeps the Seifert determinant. -/
@[simp]
theorem seifertConwayDeterminant_seifertMatrix_rotate (w : BraidWord n) (k : ℕ) :
    (seifertMatrix (n := n) (w.rotate k)).seifertConwayDeterminant =
      w.seifertMatrix.seifertConwayDeterminant :=
  List.apply_rotate_of_append_singleton
    (fun w : BraidWord n ↦ w.seifertMatrix.seifertConwayDeterminant)
    seifertConwayDeterminant_seifertMatrix_append_singleton w k

/-! ### Artin relations, free cancellation and stabilization -/

section Moves

/-- An Artin relation step keeps the Seifert determinant. -/
theorem seifertConwayDeterminant_seifertMatrix_eq_of_artinStep {w w' : BraidWord n}
    (h : ArtinStep w w') :
    w.seifertMatrix.seifertConwayDeterminant = w'.seifertMatrix.seifertConwayDeterminant := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_of_artinStep h
  rw [h, seifertConwayDeterminant_submatrix_equiv_self,
    seifertConwayDeterminant_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP)]

variable (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)

/-- Inserting an inverse pair of letters on a level already in use keeps the Seifert determinant:
the Seifert matrix changes by an elementary enlargement, up to a unimodular congruence. -/
theorem seifertConwayDeterminant_seifertMatrix_insert (h : ∃ x ∈ u ++ v, x.1 = i) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.seifertConwayDeterminant =
      (u ++ v).seifertMatrix.seifertConwayDeterminant := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨ι, P, η, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeRow u v i h
    rw [← seifertConwayDeterminant_enlargeRow _ η, ← hPV,
      seifertConwayDeterminant_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP),
      seifertConwayDeterminant_submatrix_equiv_self]
  · obtain ⟨ι, P, ξ, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeColumn u v i h
    rw [neg_neg, ← seifertConwayDeterminant_enlargeColumn _ ξ, ← hPV,
      seifertConwayDeterminant_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP),
      seifertConwayDeterminant_submatrix_equiv_self]

/-- Inserting an inverse pair of letters on an unused level gives Seifert determinant zero: the
Seifert matrix only gains a zero row and column. -/
theorem seifertConwayDeterminant_seifertMatrix_insert_eq_zero (h : ¬∃ x ∈ u ++ v, x.1 = i) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.seifertConwayDeterminant = 0 := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_insert_eq_fromBlocks u v i ε h
  rw [← seifertConwayDeterminant_submatrix_equiv_self _ ι, hι,
    seifertConwayDeterminant_fromBlocks_zero, seifertConwayDeterminant_zero, mul_zero]

end Moves

/-- Markov stabilization keeps the Seifert determinant. -/
@[simp]
theorem seifertConwayDeterminant_seifertMatrix_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    (w.stabilize ε).seifertMatrix.seifertConwayDeterminant =
      w.seifertMatrix.seifertConwayDeterminant := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_stabilize w ε
  rw [hι, seifertConwayDeterminant_submatrix_equiv_self]

/-- Prepending a letter alone on its level keeps the Seifert determinant: its band closes up no
loop. -/
theorem seifertConwayDeterminant_seifertMatrix_cons_of_forall_ne (x : Fin (n - 1) × ℤˣ)
    (v : BraidWord n) (h : ∀ y ∈ v, y.1 ≠ x.1) :
    (seifertMatrix (n := n) (x :: v)).seifertConwayDeterminant =
      v.seifertMatrix.seifertConwayDeterminant := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_append_singleton_of_forall_ne v x h
  rw [← seifertConwayDeterminant_seifertMatrix_append_singleton, hι,
    seifertConwayDeterminant_submatrix_equiv_self]

/-! ### Appending a letter -/

section Append

variable {v : BraidWord n} {i : Fin (n - 1)} {t : ℕ} (ht : t < v.length)
  (htl : v.levelAt t = some (i : ℕ)) (htg : ∀ k, t < k → v.levelAt k ≠ some (i : ℕ))
include ht htl htg

/-- The last letter of level `i` in `v` and an appended letter of level `i` span a loop. -/
private theorem isSeifertLoop_append_singleton_last (ε : ℤˣ) :
    (v ++ [(i, ε)]).IsSeifertLoop (t, v.length) := by
  refine (isSeifertLoop_iff _).2 ⟨ht, by simp, ?_, fun k hk hk' ↦ ?_⟩
  · simp only
    rw [levelAt_append_singleton_length, levelAt_append_singleton_of_lt v _ ht, htl]
  · simp only at hk hk'
    rw [levelAt_append_singleton_of_lt v _ hk, levelAt_append_singleton_of_lt v _ ht, htl]
    exact htg k hk'

/-- Every loop of `v ++ [(i, ε)]` is a loop of `v` or the loop through the appended letter. -/
private theorem IsSeifertLoop.append_singleton_cases {ε : ℤˣ} {c : ℕ × ℕ}
    (hc : (v ++ [(i, ε)]).IsSeifertLoop c) : c.2 < v.length ∨ c = (t, v.length) := by
  obtain ⟨h12, h2, hl, hb⟩ := (isSeifertLoop_iff _).1 hc
  simp only [List.length_append, List.length_singleton] at h2
  rcases Nat.lt_or_ge c.2 v.length with h | h
  · exact Or.inl h
  · right
    have h2' : c.2 = v.length := by omega
    have h1 : c.1 < v.length := h2' ▸ h12
    rw [h2', levelAt_append_singleton_length, levelAt_append_singleton_of_lt v _ h1] at hl
    have hle : c.1 ≤ t := not_lt.1 fun hlt ↦ htg _ hlt hl.symm
    have hge : t ≤ c.1 := not_lt.1 fun hlt ↦ hb t (h2' ▸ ht) hlt (by
      rw [levelAt_append_singleton_of_lt v _ ht, levelAt_append_singleton_of_lt v _ h1, htl,
        ← hl])
    exact Prod.ext (le_antisymm hle hge) h2'

/-- The loop through the appended letter, read as a loop of `v ++ [(i, ε)]`. -/
private def lastLoop (ε : ℤˣ) : (v ++ [(i, ε)]).seifertLoops :=
  ⟨(t, v.length), (mem_seifertLoops _).2 (isSeifertLoop_append_singleton_last ht htl htg ε)⟩

/-- A loop other than the loop through the appended letter ends before it. -/
private theorem snd_lt_length_of_ne_lastLoop {ε : ℤˣ} {c : (v ++ [(i, ε)]).seifertLoops}
    (hc : c ≠ lastLoop ht htl htg ε) : c.1.2 < v.length :=
  (((mem_seifertLoops _).1 c.2).append_singleton_cases ht htl htg).resolve_right
    fun h ↦ hc (Subtype.ext h)

/-- **Changing the sign of the appended letter.** Going from `σᵢ⁻¹` to `σᵢ` at the end of the word
changes the Seifert matrix only in the diagonal entry of the loop through the appended letter,
which drops by one. -/
private theorem seifertMatrix_append_singleton_one_submatrix :
    (v ++ [(i, 1)]).seifertMatrix.submatrix
        (Equiv.subtypeEquivRight (mem_seifertLoops_append_singleton_iff v i (-1) 1))
        (Equiv.subtypeEquivRight (mem_seifertLoops_append_singleton_iff v i (-1) 1)) =
      (v ++ [(i, -1)]).seifertMatrix + diagonal (Pi.single (lastLoop ht htl htg (-1)) (-1)) := by
  ext a b
  obtain ⟨⟨a₁, a₂⟩, ha⟩ := a
  obtain ⟨⟨b₁, b₂⟩, hb⟩ := b
  have hα : ((⟨(a₁, a₂), ha⟩ : (v ++ [(i, -1)]).seifertLoops) = lastLoop ht htl htg (-1)) ↔
      a₂ = v.length := by
    refine ⟨fun h ↦ congrArg (fun c : (v ++ [(i, -1)]).seifertLoops ↦ c.1.2) h, fun h ↦ ?_⟩
    rcases ((mem_seifertLoops _).1 ha).append_singleton_cases ht htl htg with h' | h'
    · exact absurd h (Nat.ne_of_lt h')
    · exact Subtype.ext h'
  obtain ⟨ha12, ha2, -, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 ha)
  obtain ⟨hb12, hb2, -, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hb)
  simp only [List.length_append, List.length_singleton] at ha2 hb2
  have ha1 : a₁ < v.length := by omega
  have hb1 : b₁ < v.length := by omega
  simp only [submatrix_apply, Matrix.add_apply, diagonal_apply, seifertMatrix_apply,
    EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, Prod.mk.injEq,
    Equiv.subtypeEquivRight_apply_coe, levelAt_append_singleton,
    signAt_append_singleton_of_lt v (i, 1) ha1, signAt_append_singleton_of_lt v (i, -1) ha1,
    signAt_append_singleton, Units.val_one, Units.val_neg]
  by_cases hab : a₁ = b₁ ∧ a₂ = b₂
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [and_self, ite_true, Pi.single_apply, hα]
    by_cases h2 : a₂ = v.length
    · rcases signAt_eq_one_or_eq_neg_one v ha1 with hs | hs <;> simp [h2, hs]
    · simp [h2]
  · simp only [hab, ite_false, add_zero]
    -- the sign of the appended letter only enters through a band shared at position `a₂ = b₁`
    rcases eq_or_ne a₂ b₁ with rfl | h
    · simp [hb1.ne]
    · simp [h]

/-- Deleting the row and column of the loop through the appended letter leaves the loops of `v`. -/
private def lastLoopComplEquiv (ε : ℤˣ) :
    {c : (v ++ [(i, ε)]).seifertLoops // c ≠ lastLoop ht htl htg ε} ≃ v.seifertLoops where
  toFun c := ⟨c.1.1, (mem_seifertLoops _).2 ((isSeifertLoop_append_singleton_iff v _
    (snd_lt_length_of_ne_lastLoop ht htl htg c.2)).1 ((mem_seifertLoops _).1 c.1.2))⟩
  invFun d := by
    have hd := (mem_seifertLoops _).1 d.2
    have hd2 : d.1.2 < v.length := ((isSeifertLoop_iff _).1 hd).2.1
    refine ⟨⟨d.1, (mem_seifertLoops _).2 ((isSeifertLoop_append_singleton_iff v _ hd2).2 hd)⟩,
      fun h ↦ ?_⟩
    have : d.1.2 = v.length := congrArg (fun c : (v ++ [(i, ε)]).seifertLoops ↦ c.1.2) h
    omega
  left_inv _ := rfl
  right_inv _ := rfl

/-- The minor of the Seifert matrix of `v ++ [(i, ε)]` away from the loop through the appended
letter is the Seifert matrix of `v`. -/
private theorem seifertMatrix_append_singleton_submatrix_ne (ε : ℤˣ) :
    (v ++ [(i, ε)]).seifertMatrix.submatrix
        ((↑) : {c // c ≠ lastLoop ht htl htg ε} → _) (↑) =
      v.seifertMatrix.submatrix (lastLoopComplEquiv ht htl htg ε)
        (lastLoopComplEquiv ht htl htg ε) := by
  ext a b
  have ha2 := snd_lt_length_of_ne_lastLoop ht htl htg a.2
  have hb2 := snd_lt_length_of_ne_lastLoop ht htl htg b.2
  have ha1 : a.1.1.1 < v.length :=
    ((isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 a.1.2)).1.trans ha2
  have hb1 : b.1.1.1 < v.length :=
    ((isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 b.1.2)).1.trans hb2
  simp only [submatrix_apply, seifertMatrix_apply, lastLoopComplEquiv, Equiv.coe_fn_mk,
    Subtype.ext_iff, levelAt_append_singleton_of_lt v _ ha1, levelAt_append_singleton_of_lt v _ hb1,
    signAt_append_singleton_of_lt v _ ha1, signAt_append_singleton_of_lt v _ ha2]

/-- **The skein relation for an appended letter.** -/
private theorem seifertConwayDeterminant_seifertMatrix_append_skein :
    (v ++ [(i, 1)]).seifertMatrix.seifertConwayDeterminant -
        (v ++ [(i, -1)]).seifertMatrix.seifertConwayDeterminant =
      (T (-1) - T 1) * v.seifertMatrix.seifertConwayDeterminant := by
  have he := seifertConwayDeterminant_submatrix_equiv_self (seifertMatrix (n := n) (v ++ [(i, 1)]))
    (Equiv.subtypeEquivRight (mem_seifertLoops_append_singleton_iff v i (-1) 1))
  rw [seifertMatrix_append_singleton_one_submatrix ht htl htg] at he
  rw [← he,
    seifertConwayDeterminant_add_diagonal_single,
    seifertMatrix_append_singleton_submatrix_ne ht htl htg,
    seifertConwayDeterminant_submatrix_equiv_self, map_neg, map_one]
  ring

end Append

/-! ### The skein relation -/

/-- **The Conway skein relation for the Seifert determinant of a closed braid.** If the level `i`
carries a letter of `u ++ v`, then the Seifert determinants `Δ = det(s V - s⁻¹ Vᵀ)` of the closures
of `u σᵢ v`, `u σᵢ⁻¹ v` and `u v` satisfy `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`. -/
theorem seifertConwayDeterminant_seifertMatrix_skein (u v : BraidWord n) (i : Fin (n - 1))
    (h : ∃ x ∈ u ++ v, x.1 = i) :
    (u ++ (i, 1) :: v).seifertMatrix.seifertConwayDeterminant -
        (u ++ (i, -1) :: v).seifertMatrix.seifertConwayDeterminant =
      (T (-1) - T 1) * (u ++ v).seifertMatrix.seifertConwayDeterminant := by
  -- rotate the changed letter to the end of the word
  have hrot (ε : ℤˣ) : (u ++ (i, ε) :: v).rotate (u ++ [(i, ε)]).length = v ++ u ++ [(i, ε)] := by
    rw [show u ++ (i, ε) :: v = (u ++ [(i, ε)]) ++ v by simp, List.rotate_append_length_eq,
      List.append_assoc]
  have h' : ∃ x ∈ v ++ u, (x.1 : ℕ) = i := by
    obtain ⟨x, hx, hxi⟩ := h
    exact ⟨x, List.mem_append.2 ((List.mem_append.1 hx).symm), congrArg Fin.val hxi⟩
  obtain ⟨t, ht, htl, htg⟩ := exists_last_levelAt (v ++ u) h'
  rw [← seifertConwayDeterminant_seifertMatrix_rotate (u ++ (i, 1) :: v), hrot,
    ← seifertConwayDeterminant_seifertMatrix_rotate (u ++ (i, -1) :: v), hrot,
    ← seifertConwayDeterminant_seifertMatrix_rotate (u ++ v) u.length,
    List.rotate_append_length_eq]
  exact seifertConwayDeterminant_seifertMatrix_append_skein ht htl htg

end BraidWord

end TauCeti
