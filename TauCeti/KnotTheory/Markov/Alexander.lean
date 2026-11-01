/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Conway
public import TauCeti.KnotTheory.Burau.Normalization
public import TauCeti.KnotTheory.Markov.Basic
import TauCeti.KnotTheory.Burau.Skein
import TauCeti.KnotTheory.Markov.Skein

/-!
# The Seifert and Burau routes to the Alexander polynomial of a closed braid agree

There are two classical ways to compute the Conway-normalized Alexander polynomial of the closure of
a braid, written in the square root `s` of the Alexander variable `t`.

* **From a Seifert surface.** Seifert's algorithm on the closure of a braid word `w` gives the
  canonical Seifert surface, with Seifert matrix `V = TauCeti.BraidWord.seifertMatrix w`, and the
  polynomial is `det(s V - s⁻¹ Vᵀ)` (`Matrix.seifertConwayDeterminant`). This requires the surface
  to be connected, which happens exactly when every level `0, …, n - 2` carries a letter of `w`.
  Otherwise the closure is a split link and the polynomial is `0`. This is
  `TauCeti.BraidWord.seifertAlexander w`.
* **From the Burau representation.** The corner minor of `burau β - 1`, evaluated at `t = s²` and
  multiplied by the exact Markov normalization `(-1)^p s^(-e-p)`, for `p + 1` strands and exponent
  sum `e` (`TauCeti.MarkovBraid.normalizedBurauAlexander`).

The Seifert route does not depend on the word representing a braid: Artin relations, cyclic
rotation and stabilization change the Seifert matrix by relabellings and unimodular congruences,
and free cancellation by an elementary enlargement, or by a zero row and column when it joins two
components of the canonical surface. So it defines `TauCeti.MarkovBraid.seifertAlexander` on
braids, constant on Markov equivalence classes (`TauCeti.MarkovEquiv.seifertAlexander_eq`). Both
routes satisfy the Conway skein relation `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`, vanish on braids with an
uncrossed strand, whose closures are split, and take the value `1` on the trivial braid on one
strand, whose closure is the unknot. A Markov invariant with these three properties is determined
(`TauCeti.MarkovBraid.eq_of_skein`), so the two routes agree for every braid and every unit `s` of
every commutative ring
(`TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`).

## Main definitions

* `TauCeti.BraidWord.seifertAlexander`: the Seifert-matrix Alexander polynomial of the closure of
  a braid word.
* `TauCeti.MarkovBraid.seifertAlexander`: the same polynomial for a braid, read from any word
  representing it.

## Main results

* `TauCeti.MarkovEquiv.seifertAlexander_eq`: it is a Markov invariant.
* `TauCeti.MarkovBraid.seifertAlexander_skein`: it satisfies the Conway skein relation.
* `TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`: **the Seifert-matrix
  and Burau routes to the Alexander polynomial of a closed braid agree.**

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8, Theorem 8.6 (the Conway-normalized skein characterization).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 3 (the Burau representation and the Alexander polynomial of a closed braid).
-/

public section

namespace TauCeti

open BraidGroup BraidWord KnotTheory LaurentPolynomial Matrix

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
theorem seifertAlexander_of_not_exists {i : Fin (n - 1)} (h : ¬∃ x ∈ w, x.1 = i) :
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
    rw [seifertAlexander_of_not_exists hi, seifertAlexander_of_not_exists (mt (hlevel i).2 hi)]

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
    rw [seifertAlexander_of_not_exists hi, seifertAlexander_def,
      seifertConwayDeterminant_seifertMatrix_insert_of_not_exists u v i ε hi, ite_self]

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
    rw [seifertAlexander_of_not_exists (w := w.stabilize ε) (i := i) hi,
      seifertAlexander_of_not_exists (w := w) (i := j) hj]

/-- A word with an uncrossed strand added closes to a split link: its Seifert-matrix Alexander
polynomial vanishes. -/
@[simp]
theorem seifertAlexander_strandIncl (w : BraidWord (n + 1)) : w.strandIncl.seifertAlexander = 0 :=
  seifertAlexander_of_not_exists (i := Fin.last n) fun ⟨x, hx, hxi⟩ ↦ by
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
      rw [seifertAlexander_of_not_exists hl, seifertAlexander_of_not_exists (mt (hlevel 1 l).1 hl),
        seifertAlexander_of_not_exists (mt (hlevel (-1) l).1 hl), sub_zero, mul_zero]
  · -- the changed letter is alone on its level, so its sign does not matter
    rw [seifertAlexander_of_not_exists hi, mul_zero, sub_eq_zero]
    refine seifertAlexander_eq_of_exists_iff (fun l ↦ ?_) fun _ ↦
      seifertConwayDeterminant_seifertMatrix_append_cons_of_not_exists u v i 1 (-1) hi
    simp only [List.mem_append, List.mem_cons]
    grind

end BraidWord

namespace MarkovBraid

variable {n : ℕ}

/-- The **Seifert-matrix Alexander polynomial** of the closure of a braid, in the square root `s`
of the Alexander variable: the polynomial `TauCeti.BraidWord.seifertAlexander` of any word
representing the braid (`TauCeti.MarkovBraid.seifertAlexander_eq_of_toBraid_eq`). It agrees with
the normalized Burau invariant
(`TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`). -/
noncomputable def seifertAlexander (β : MarkovBraid) : ℤ[T;T⁻¹] :=
  (toBraid_surjective β.braid).choose.seifertAlexander

/-- The Seifert-matrix Alexander polynomial of a braid is computed by any word representing it. -/
theorem seifertAlexander_eq_of_toBraid_eq {β : MarkovBraid}
    {w : BraidWord (β.predStrands + 1)} (hw : w.toBraid = β.braid) :
    β.seifertAlexander = w.seifertAlexander :=
  BraidWord.seifertAlexander_eq_of_toBraid_eq
    ((toBraid_surjective β.braid).choose_spec.trans hw.symm)

/-- The Seifert-matrix Alexander polynomial of the braid represented by a word is that of the
word. -/
@[simp]
theorem seifertAlexander_mk (w : BraidWord (n + 1)) :
    seifertAlexander ⟨n, w.toBraid⟩ = w.seifertAlexander :=
  seifertAlexander_eq_of_toBraid_eq (β := ⟨n, w.toBraid⟩) rfl

/-- The trivial braid on one strand closes to the unknot, of Seifert-matrix Alexander
polynomial `1`. -/
@[simp]
theorem seifertAlexander_one_strand : seifertAlexander ⟨0, 1⟩ = 1 := by
  rw [seifertAlexander_eq_of_toBraid_eq (β := ⟨0, 1⟩) (w := []) toBraid_nil,
    seifertAlexander_nil_one]

/-- Adding an uncrossed strand makes the Seifert-matrix Alexander polynomial vanish: the closure
becomes split. -/
@[simp]
theorem seifertAlexander_strandIncl (b : BraidGroup (n + 1)) :
    seifertAlexander ⟨n + 1, strandIncl b⟩ = 0 := by
  obtain ⟨w, rfl⟩ := toBraid_surjective b
  rw [← toBraid_strandIncl, seifertAlexander_mk, BraidWord.seifertAlexander_strandIncl]

/-- **The Conway skein relation for the Seifert-matrix Alexander polynomial of a closed braid.**
Changing one crossing of a braid from positive to negative, and smoothing it, give the three
closures of a skein triple, and `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`. -/
theorem seifertAlexander_skein (b c : BraidGroup (n + 1)) (i : Fin n) :
    seifertAlexander ⟨n, b * sigma (n := n + 1) i * c⟩ -
        seifertAlexander ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ =
      (T (-1) - T 1) * seifertAlexander ⟨n, b * c⟩ := by
  obtain ⟨u, rfl⟩ := toBraid_surjective b
  obtain ⟨v, rfl⟩ := toBraid_surjective c
  have hw (ε : ℤˣ) : toBraid (u ++ ((i, ε) :: v : BraidWord (n + 1))) =
      u.toBraid * sigma (n := n + 1) i ^ (ε : ℤ) * v.toBraid := by
    rw [toBraid_append, toBraid_cons, mul_assoc]
  rw [seifertAlexander_eq_of_toBraid_eq (β := ⟨n, _⟩) ((hw 1).trans (by simp)),
    seifertAlexander_eq_of_toBraid_eq (β := ⟨n, _⟩) ((hw (-1)).trans (by simp)),
    ← toBraid_append, seifertAlexander_mk, BraidWord.seifertAlexander_skein]

end MarkovBraid

/-- A single Markov move does not change the Seifert-matrix Alexander polynomial. -/
theorem IsMarkovMove.seifertAlexander_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) :
    β.seifertAlexander = γ.seifertAlexander := by
  cases h with
  | conj b c =>
    -- Conjugation by a word `u` is undone by rotating `u` to the end of the word.
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    obtain ⟨u, rfl⟩ := toBraid_surjective c
    let uInv : BraidWord _ := u.reverse.map fun x ↦ (x.1, -x.2)
    have huInv : uInv.toBraid = u.toBraid⁻¹ := toBraid_reverse_map_neg u
    have hrot := BraidWord.seifertAlexander_rotate (u ++ (w ++ uInv)) u.length
    rw [List.rotate_append_length_eq] at hrot
    rw [MarkovBraid.seifertAlexander_mk,
      MarkovBraid.seifertAlexander_eq_of_toBraid_eq (w := u ++ (w ++ uInv))
        (by rw [toBraid_append, toBraid_append, huInv, mul_assoc]), ← hrot]
    exact BraidWord.seifertAlexander_eq_of_toBraid_eq
      (by rw [toBraid_append, toBraid_append, huInv, inv_mul_cancel_right])
  | stabilize b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [MarkovBraid.seifertAlexander_eq_of_toBraid_eq (w := w.stabilize 1) (by simp),
      BraidWord.seifertAlexander_stabilize, MarkovBraid.seifertAlexander_mk]
  | stabilizeInv b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [MarkovBraid.seifertAlexander_eq_of_toBraid_eq (w := w.stabilize (-1)) (by simp),
      BraidWord.seifertAlexander_stabilize, MarkovBraid.seifertAlexander_mk]

/-- **The Seifert-matrix Alexander polynomial is a Markov invariant.** By Markov's theorem, it is
an invariant of the oriented link obtained by closing the braid. -/
theorem MarkovEquiv.seifertAlexander_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.seifertAlexander = γ.seifertAlexander :=
  h.induction (fun hmove ↦ hmove.seifertAlexander_eq) (fun _ ↦ rfl)
    (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

namespace MarkovBraid

/-- **The Seifert-matrix and Burau routes to the Alexander polynomial of a closed braid agree.**
For every braid `β` and every unit `s` of a commutative ring, the normalized Burau invariant at `s`
is the Seifert-matrix Alexander polynomial evaluated at `s`. Both are Markov invariants satisfying
the Conway skein relation, vanishing on split closures and equal to `1` on the unknot. -/
theorem normalizedBurauAlexander_eq_eval₂_seifertAlexander {R : Type*} [CommRing R]
    (β : MarkovBraid) (s : Rˣ) :
    β.normalizedBurauAlexander s = eval₂ (Int.castRingHom R) s β.seifertAlexander := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 (((s⁻¹ : Rˣ) : R) - s) 0
    (F := fun β ↦ β.normalizedBurauAlexander s)
    (G := fun β ↦ eval₂ (Int.castRingHom R) s β.seifertAlexander)
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun _ _ h ↦ by rw [h.seifertAlexander_eq]) (fun n c i ↦ ?_) (fun n c i ↦ ?_)
    (fun n b ↦ by simp) (fun n b ↦ by simp) (by simp)) β
  · simpa using normalizedBurauAlexander_skein 1 c i s
  · have h := congrArg (eval₂ (Int.castRingHom R) s) (seifertAlexander_skein 1 c i)
    simp only [one_mul, map_sub, map_mul, eval₂_T, _root_.zpow_neg_one, zpow_one] at h
    simpa using h

end MarkovBraid

end TauCeti
