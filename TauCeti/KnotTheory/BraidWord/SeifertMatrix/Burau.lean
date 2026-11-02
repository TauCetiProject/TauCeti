/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
public import TauCeti.KnotTheory.Burau.Normalization
public import TauCeti.KnotTheory.SeifertMatrix.Conway

import TauCeti.KnotTheory.BraidWord.Equivalence
import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Conway
import TauCeti.KnotTheory.Burau.Skein
import TauCeti.KnotTheory.Markov.Skein
import TauCeti.KnotTheory.SeifertMatrix.Polynomial.Conway

/-!
# The Seifert-matrix and Burau routes to the Alexander polynomial of a closed braid agree

There are two algorithms in Tau Ceti for the Alexander polynomial of the closure of a braid. The
first reads a Seifert matrix off the canonical Seifert surface that Seifert's algorithm builds on
the closure of a braid word `w` (`TauCeti.BraidWord.seifertMatrix`) and takes the half-power
Seifert determinant `Δ(w) = det(s V - s⁻¹ Vᵀ)` (`Matrix.seifertConwayDeterminant`). The second takes
the corner minor of the Burau matrix of the braid, with its exact Markov normalization
(`TauCeti.MarkovBraid.normalizedBurauAlexander`). This file proves that they agree: if every level
of `w` carries a letter, so that the canonical surface is connected, then `Δ(w)` evaluated at any
unit `s` of any commutative ring is the normalized Burau invariant of the braid `w` represents at
`s` (`TauCeti.BraidWord.eval₂_seifertConwayDeterminant_seifertMatrix_eq_normalizedBurauAlexander`).
For a Seifert matrix of even size, as for a knot, `Δ(w)` at `s` is the Conway-normalized Alexander
polynomial of the Seifert matrix at `s²`, so the two routes give the same Alexander polynomial
(`TauCeti.BraidWord.eval₂_alexander_seifertMatrix_eq_normalizedBurauAlexander`). If some level
carries no letter, the closure is a split link and the normalized Burau invariant vanishes
(`TauCeti.BraidWord.normalizedBurauAlexander_toBraid_eq_zero`).

The proof is the skein-theoretic characterization of `TauCeti.MarkovBraid.eq_of_skein`: a Markov
invariant satisfying the Conway skein relation and vanishing when an uncrossed strand is added is
determined by its value on the trivial braid on one strand. On the Seifert side, the invariant
of a braid is `Δ(w)` for any word `w` representing it if every level of `w` carries a letter, and
`0` otherwise, matching the vanishing of the Conway polynomial on split links. It is well defined
because Artin relations change the Seifert matrix by a unimodular congruence, and free insertion
of an inverse pair by an elementary enlargement on a level in use, while on an unused level it
creates a zero row and column. Cyclic rotation and stabilization keep `Δ`, which gives Markov
invariance. The skein relation is
`TauCeti.BraidWord.seifertConwayDeterminant_seifertMatrix_skein` when the changed letter shares
its level with another letter; otherwise the letter closes up no loop, so the two sides of the
relation are equal and the smoothed word has an unused level.

## Main results

* `TauCeti.BraidWord.eval₂_seifertConwayDeterminant_seifertMatrix_eq_normalizedBurauAlexander`:
  the Seifert determinant of a braid word using every level is the normalized Burau invariant.
* `TauCeti.BraidWord.eval₂_alexander_seifertMatrix_eq_normalizedBurauAlexander`: for a Seifert
  matrix of even size, the Alexander polynomial of the Seifert matrix at `s²` is the normalized
  Burau invariant at `s`.
* `TauCeti.BraidWord.normalizedBurauAlexander_toBraid_eq_zero`: the normalized Burau invariant of
  a braid word with an unused level vanishes.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 6 and 8
  (Seifert matrices, the Conway polynomial and its skein relation).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 3 (the Burau representation and the Alexander polynomial of a closed braid).
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory LaurentPolynomial BraidGroup

variable {n : ℕ}

/-! ### The Seifert determinant of a word, set to zero on unused levels -/

/-- The Seifert determinant of the canonical Seifert surface of the closure of `w` if every level
carries a letter, so that the surface is connected, and `0` otherwise. -/
private noncomputable def connectedSeifertDet (w : BraidWord n) : ℤ[T;T⁻¹] :=
  if ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i then w.seifertMatrix.seifertConwayDeterminant else 0

private theorem connectedSeifertDet_of_forall (w : BraidWord n)
    (h : ∀ i : Fin (n - 1), ∃ x ∈ w, x.1 = i) :
    connectedSeifertDet w = w.seifertMatrix.seifertConwayDeterminant :=
  ite_eq_left h

private theorem connectedSeifertDet_of_exists (w : BraidWord n)
    (h : ∃ i : Fin (n - 1), ∀ x ∈ w, x.1 ≠ i) : connectedSeifertDet w = 0 :=
  ite_eq_right fun hall ↦ by
    obtain ⟨i, hi⟩ := h
    obtain ⟨x, hx, hxi⟩ := hall i
    exact hi x hx hxi

private theorem connectedSeifertDet_congr {w w' : BraidWord n}
    (hlevel : ∀ i : Fin (n - 1), (∃ x ∈ w, x.1 = i) ↔ ∃ x ∈ w', x.1 = i)
    (hdet : w.seifertMatrix.seifertConwayDeterminant =
      w'.seifertMatrix.seifertConwayDeterminant) :
    connectedSeifertDet w = connectedSeifertDet w' := by
  simp only [connectedSeifertDet, hlevel, hdet]

private theorem connectedSeifertDet_eq_of_artinStep {w w' : BraidWord n} (h : ArtinStep w w') :
    connectedSeifertDet w = connectedSeifertDet w' := by
  -- an Artin relation step keeps the set of letters
  have hmem : ∀ x, x ∈ w ↔ x ∈ w' := by
    cases h <;> simp only [List.mem_append, List.mem_cons] <;> tauto
  exact connectedSeifertDet_congr (fun i ↦ by simp only [hmem])
    (seifertConwayDeterminant_seifertMatrix_eq_of_artinStep h)

private theorem connectedSeifertDet_insert (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ) :
    connectedSeifertDet (u ++ (i, ε) :: (i, -ε) :: v) = connectedSeifertDet (u ++ v) := by
  by_cases h : ∃ x ∈ u ++ v, x.1 = i
  · refine connectedSeifertDet_congr (fun l ↦ ⟨?_, ?_⟩)
      (seifertConwayDeterminant_seifertMatrix_insert u v i ε h)
    · rintro ⟨x, hx, rfl⟩
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact ⟨x, List.mem_append_left _ hx, rfl⟩
      · exact h
      · exact h
      · exact ⟨x, List.mem_append_right _ hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto, rfl⟩
  · rw [connectedSeifertDet_of_exists (u ++ v) ⟨i, fun x hx hxi ↦ h ⟨x, hx, hxi⟩⟩,
      connectedSeifertDet]
    split_ifs
    · exact seifertConwayDeterminant_seifertMatrix_insert_eq_zero u v i ε h
    · rfl

private theorem connectedSeifertDet_eq_of_toBraid_eq {w w' : BraidWord n}
    (h : w.toBraid = w'.toBraid) : connectedSeifertDet w = connectedSeifertDet w' := by
  refine WordEquiv.induction (motive := fun w w' ↦ connectedSeifertDet w = connectedSeifertDet w')
    connectedSeifertDet_eq_of_artinStep (fun hc ↦ ?_) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih') (toBraid_eq_iff_wordEquiv.mp h)
  cases hc with
  | insert u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact (connectedSeifertDet_insert u v i ε).symm
  | delete u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact connectedSeifertDet_insert u v i ε

private theorem connectedSeifertDet_rotate (w : BraidWord n) (k : ℕ) :
    connectedSeifertDet (w.rotate k) = connectedSeifertDet w :=
  connectedSeifertDet_congr (fun i ↦ by simp only [List.mem_rotate])
    (seifertConwayDeterminant_seifertMatrix_rotate w k)

private theorem connectedSeifertDet_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    connectedSeifertDet (w.stabilize ε) = connectedSeifertDet w := by
  -- the levels in use after stabilization are the old ones and the new top level
  have hlevel : (∀ i : Fin (n + 1), ∃ x ∈ w.stabilize ε, x.1 = i) ↔
      ∀ i : Fin n, ∃ x ∈ w, x.1 = i := by
    simp only [stabilize_def, strandIncl_def, List.mem_append, List.mem_map, List.mem_singleton]
    constructor
    · intro hall i
      obtain ⟨x, hx | rfl, hxi⟩ := hall i.castSucc
      · obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, hy, Fin.castSucc_injective _ hxi⟩
      · exact absurd hxi (Fin.castSucc_lt_last i).ne'
    · intro hall i
      induction i using Fin.lastCases with
      | last => exact ⟨_, Or.inr rfl, rfl⟩
      | cast j =>
        obtain ⟨y, hy, hyj⟩ := hall j
        exact ⟨_, Or.inl ⟨y, hy, rfl⟩, by rw [hyj]⟩
  unfold connectedSeifertDet
  rw [seifertConwayDeterminant_seifertMatrix_stabilize]
  -- the levels of `BraidWord (n + 2)` and `BraidWord (n + 1)` are `Fin (n + 2 - 1)` and
  -- `Fin (n + 1 - 1)`, which reduce to the `Fin (n + 1)` and `Fin n` of `hlevel`
  exact if_congr hlevel rfl rfl

/-! ### The Seifert determinant of a braid -/

variable {R : Type*} [CommRing R]

/-- The Seifert determinant of a braid at a unit `s`, read off any word representing it, and `0`
when that word has an unused level. -/
private noncomputable def markovSeifertDet (s : Rˣ) (β : MarkovBraid) : R :=
  eval₂ (Int.castRingHom R) s (connectedSeifertDet (toBraid_surjective β.braid).choose)

private theorem markovSeifertDet_eq (s : Rˣ) {b : BraidGroup (n + 1)} {w : BraidWord (n + 1)}
    (hw : w.toBraid = b) :
    markovSeifertDet s ⟨n, b⟩ = eval₂ (Int.castRingHom R) s (connectedSeifertDet w) := by
  rw [markovSeifertDet, connectedSeifertDet_eq_of_toBraid_eq
    ((toBraid_surjective b).choose_spec.trans hw.symm)]

private theorem markovSeifertDet_mk (s : Rˣ) (w : BraidWord (n + 1)) :
    markovSeifertDet s ⟨n, w.toBraid⟩ = eval₂ (Int.castRingHom R) s (connectedSeifertDet w) :=
  markovSeifertDet_eq s rfl

private theorem markovSeifertDet_eq_of_isMarkovMove (s : Rˣ) {β γ : MarkovBraid}
    (h : IsMarkovMove β γ) : markovSeifertDet s β = markovSeifertDet s γ := by
  cases h with
  | conj b c =>
    -- conjugation by a word `u` is undone by rotating `u` to the end of the word
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    obtain ⟨u, rfl⟩ := toBraid_surjective c
    let uInv : BraidWord _ := u.reverse.map fun x ↦ (x.1, -x.2)
    have huInv : uInv.toBraid = u.toBraid⁻¹ := toBraid_reverse_map_neg u
    have hrot := connectedSeifertDet_rotate (u ++ (w ++ uInv)) u.length
    rw [List.rotate_append_length_eq] at hrot
    rw [markovSeifertDet_mk, markovSeifertDet_eq (w := u ++ (w ++ uInv)) s
      (by rw [toBraid_append, toBraid_append, huInv, mul_assoc]), ← hrot]
    exact congrArg _ (connectedSeifertDet_eq_of_toBraid_eq
      (by rw [toBraid_append, toBraid_append, huInv, inv_mul_cancel_right]))
  | stabilize b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [markovSeifertDet_eq (w := w.stabilize 1) s (by simp), connectedSeifertDet_stabilize,
      markovSeifertDet_mk]
  | stabilizeInv b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [markovSeifertDet_eq (w := w.stabilize (-1)) s (by simp), connectedSeifertDet_stabilize,
      markovSeifertDet_mk]

private theorem markovSeifertDet_skein (s : Rˣ) (n : ℕ) (c : BraidGroup (n + 1)) (i : Fin n) :
    ((1 : Rˣ) : R) • markovSeifertDet s ⟨n, sigma (n := n + 1) i * c⟩ -
        (↑(1 : Rˣ)⁻¹ : R) • markovSeifertDet s ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
      (((s⁻¹ : Rˣ) : R) - s) • markovSeifertDet s ⟨n, c⟩ := by
  obtain ⟨v, rfl⟩ := toBraid_surjective c
  rw [markovSeifertDet_eq (w := ((i, 1) :: v : BraidWord (n + 1))) s
      (by rw [toBraid_cons]; simp),
    markovSeifertDet_eq (w := ((i, -1) :: v : BraidWord (n + 1))) s (by rw [toBraid_cons]; simp),
    markovSeifertDet_mk]
  simp only [inv_one, Units.val_one, smul_eq_mul, one_mul]
  by_cases hi : ∃ x ∈ v, x.1 = i
  · -- the level `i` is in use in all three words, and the skein relation for `Δ` applies
    have hlevel (ε : ℤˣ) (l : Fin n) :
        (∃ x ∈ ((i, ε) :: v : BraidWord (n + 1)), x.1 = l) ↔ ∃ x ∈ v, x.1 = l := by
      simp only [List.mem_cons, exists_eq_or_imp]
      exact ⟨fun h ↦ h.elim (fun h ↦ h ▸ hi) id, Or.inr⟩
    simp only [connectedSeifertDet, hlevel]
    split_ifs
    · have hskein := seifertConwayDeterminant_seifertMatrix_skein [] v i (by simpa using hi)
      simp only [List.nil_append] at hskein
      rw [← map_sub, hskein, map_mul, map_sub, eval₂_T, eval₂_T, zpow_neg_one, zpow_one]
    · simp
  · -- the letter `σᵢ^{±1}` is alone on its level: it closes up no loop, and `v` has an unused level
    have hne : ∀ ε : ℤˣ, ∀ y ∈ v, y.1 ≠ ((i, ε) : Fin (n + 1 - 1) × ℤˣ).1 :=
      fun _ y hy hyi ↦ hi ⟨y, hy, hyi⟩
    rw [connectedSeifertDet_of_exists v ⟨i, fun x hx hxi ↦ hi ⟨x, hx, hxi⟩⟩, map_zero, mul_zero,
      sub_eq_zero]
    refine congrArg _ (connectedSeifertDet_congr (fun l ↦ by simp only [List.mem_cons,
      exists_eq_or_imp]) ?_)
    rw [seifertConwayDeterminant_seifertMatrix_cons_of_forall_ne _ v (hne 1),
      seifertConwayDeterminant_seifertMatrix_cons_of_forall_ne _ v (hne (-1))]

private theorem markovSeifertDet_strandIncl (s : Rˣ) (n : ℕ) (b : BraidGroup (n + 1)) :
    markovSeifertDet s ⟨n + 1, BraidGroup.strandIncl b⟩ = (0 : R) • markovSeifertDet s ⟨n, b⟩ := by
  obtain ⟨w, rfl⟩ := toBraid_surjective b
  -- the new top level of `w.strandIncl` carries no letter
  have hlast : ∀ x ∈ w.strandIncl, x.1 ≠ Fin.last n := fun x hx ↦ by
    rw [strandIncl_def, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (Fin.castSucc_lt_last _).ne
  rw [zero_smul, markovSeifertDet_eq (w := w.strandIncl) s (toBraid_strandIncl w),
    connectedSeifertDet_of_exists _ ⟨Fin.last n, hlast⟩, map_zero]

private theorem markovSeifertDet_one_strand (s : Rˣ) : markovSeifertDet s ⟨0, 1⟩ = 1 := by
  have : IsEmpty (seifertLoops (n := 1) []) :=
    ⟨fun c ↦ by simpa using ((mem_seifertLoops _).1 c.2).snd_lt_length⟩
  rw [markovSeifertDet_eq (w := []) s toBraid_nil,
    connectedSeifertDet_of_forall _ fun i ↦ i.elim0, Matrix.seifertConwayDeterminant_of_isEmpty,
    map_one]

/-- The Seifert determinant of a braid is its normalized Burau invariant: both are Markov
invariants satisfying the Conway skein relation, vanishing on adding an uncrossed strand and equal
to `1` on the trivial braid on one strand. -/
private theorem markovSeifertDet_eq_normalizedBurauAlexander (s : Rˣ) (β : MarkovBraid) :
    markovSeifertDet s β = β.normalizedBurauAlexander s :=
  congrFun (MarkovBraid.eq_of_skein (R := R) (M := R) 1 (((s⁻¹ : Rˣ) : R) - s) 0
    (fun _ _ h ↦ h.induction (fun hmove ↦ markovSeifertDet_eq_of_isMarkovMove s hmove)
      (fun _ ↦ rfl) (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih'))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s) (markovSeifertDet_skein s)
    (fun n c i ↦ by
      simpa using MarkovBraid.normalizedBurauAlexander_skein (1 : BraidGroup (n + 1)) c i s)
    (markovSeifertDet_strandIncl s) (fun _ _ ↦ by simp)
    (by rw [markovSeifertDet_one_strand, MarkovBraid.normalizedBurauAlexander_one_strand])) β

/-! ### Comparison of the two algorithms -/

/-- **The Seifert-matrix and Burau routes to the Alexander invariant of a closed braid agree.** If
every level of the braid word `w` carries a letter, so that the canonical Seifert surface of its
closure is connected, the Seifert determinant `det(s V - s⁻¹ Vᵀ)` of its Seifert matrix `V`,
evaluated at any unit `s` of a commutative ring, is the normalized Burau invariant of the braid
that `w` represents. -/
theorem eval₂_seifertConwayDeterminant_seifertMatrix_eq_normalizedBurauAlexander
    (w : BraidWord (n + 1)) (hw : ∀ i : Fin n, ∃ x ∈ w, x.1 = i) (s : Rˣ) :
    eval₂ (Int.castRingHom R) s w.seifertMatrix.seifertConwayDeterminant =
      MarkovBraid.normalizedBurauAlexander ⟨n, w.toBraid⟩ s := by
  rw [← connectedSeifertDet_of_forall w hw, ← markovSeifertDet_mk,
    markovSeifertDet_eq_normalizedBurauAlexander]

/-- **The Alexander polynomial of the Seifert matrix of a closed braid is its normalized Burau
invariant.** If every level of `w` carries a letter and the Seifert matrix has even size, as for a
braid closing up to a knot, the Conway-normalized Alexander polynomial of the Seifert matrix at
`s²` is the normalized Burau invariant at `s`. -/
theorem eval₂_alexander_seifertMatrix_eq_normalizedBurauAlexander (w : BraidWord (n + 1))
    (hw : ∀ i : Fin n, ∃ x ∈ w, x.1 = i) (heven : Even w.seifertLoops.card) (s : Rˣ) :
    eval₂ (Int.castRingHom R) (s ^ 2) (alexander w.seifertMatrix) =
      MarkovBraid.normalizedBurauAlexander ⟨n, w.toBraid⟩ s := by
  rw [← Matrix.eval₂_conwayPolynomial_eq_alexander _ (by rwa [Fintype.card_coe]),
    Matrix.eval₂_conwayPolynomial, ← Matrix.eval₂_seifertConwayDeterminant,
    eval₂_seifertConwayDeterminant_seifertMatrix_eq_normalizedBurauAlexander w hw]

/-- **Split closures have vanishing normalized Burau invariant.** If some level of the braid word
`w` carries no letter, the closure of `w` is a split link, and the normalized Burau invariant of
the braid it represents vanishes. -/
theorem normalizedBurauAlexander_toBraid_eq_zero (w : BraidWord (n + 1))
    (hw : ∃ i : Fin n, ∀ x ∈ w, x.1 ≠ i) (s : Rˣ) :
    MarkovBraid.normalizedBurauAlexander ⟨n, w.toBraid⟩ s = 0 := by
  rw [← markovSeifertDet_eq_normalizedBurauAlexander, markovSeifertDet_mk,
    connectedSeifertDet_of_exists w hw, map_zero]

end BraidWord

end TauCeti
