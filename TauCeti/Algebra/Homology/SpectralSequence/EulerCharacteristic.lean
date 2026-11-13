/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.HomologicalComplex
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

/-!
# Euler characteristic of pages of spectral sequences

In a spectral sequence `(E_r)` of modules over a ring `R`, each page `E_r` is a homological complex
whose homology is isomorphic to `E_{r+1}`. Whenever a differential vector `u = (u₁, u₂)` has odd
total degree `u₁ + u₂`, the total-degree sign `(p, q) ↦ (-1)^(p + q)` alternates along the
differentials of `E_r` and does not depend on the page index `r`: for cohomological and homological
spectral sequences with `u = (r, 1 - r)`, one has `r + (1 - r) = 1`.

Combining this sign convention with `HomologicalComplex.eulerChar_eq_homologyEulerChar` gives
invariance of the Euler characteristic across the pages of a finitely supported spectral sequence:

* `ComplexShape.eulerCharSignsUp'Sub`, `ComplexShape.eulerCharSignsDown'Sub`,
  `ComplexShape.eulerCharSignsSpectralSequenceNat`,
  `ComplexShape.eulerCharSignsSpectralSequenceFin`: total-degree alternating signs on the page
  shapes of cohomological and homological spectral sequences, built from the odd-total-degree
  constructors `ComplexShape.EulerCharSigns.ofUp'Odd` and companions.
* `CategoryTheory.SpectralSequence.finite_page_X_of_le`: over a Noetherian ring, finite generation
  at `pq` propagates from `E_r` to `E_{r'}` for `r ≤ r'`.
* `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_succ` and
  `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`: Euler characteristic invariance across
  one step (needing no Noetherian hypothesis) and across arbitrarily many pages (over a Noetherian
  ring with rank--nullity).

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
* John McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Exercise 1.1.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace ComplexShape

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on `ComplexShape.up' u` for any
shift `u : ℤ × ℤ` of odd total degree `u.1 + u.2`. -/
@[instance_reducible]
def EulerCharSigns.ofUp'Odd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (up' u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq'.1 + pq'.2 = (pq.1 + pq.2) + (u.1 + u.2) := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp at h1 h2
      lia
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- The sign at `pq` under `ComplexShape.EulerCharSigns.ofUp'Odd` is `(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem EulerCharSigns.ofUp'Odd_χ {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) (pq : ℤ × ℤ) :
    (EulerCharSigns.ofUp'Odd hu).χ pq = (pq.1 + pq.2).negOnePow :=
  (rfl)

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on `ComplexShape.down' u` for
any shift `u : ℤ × ℤ` of odd total degree `u.1 + u.2`. -/
@[instance_reducible]
def EulerCharSigns.ofDown'Odd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (down' u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq.1 + pq.2 = (pq'.1 + pq'.2) + (u.1 + u.2) := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp at h1 h2
      lia
    have hneg : (pq.1 + pq.2).negOnePow = -(pq'.1 + pq'.2).negOnePow := by
      rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]
    rw [hneg, neg_neg]

/-- The sign at `pq` under `ComplexShape.EulerCharSigns.ofDown'Odd` is `(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem EulerCharSigns.ofDown'Odd_χ {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) (pq : ℤ × ℤ) :
    (EulerCharSigns.ofDown'Odd hu).χ pq = (pq.1 + pq.2).negOnePow :=
  (rfl)

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on
`ComplexShape.spectralSequenceNat u` for any shift `u : ℤ × ℤ` of odd total degree. -/
@[instance_reducible]
def EulerCharSigns.ofSpectralSequenceNatOdd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (spectralSequenceNat u).EulerCharSigns where
  χ pq := ((pq.1 : ℤ) + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : (pq'.1 : ℤ) + pq'.2 = ((pq.1 : ℤ) + pq.2) + (u.1 + u.2) := by
      rw [← h.1, ← h.2]
      ring
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- The sign at `pq` under `ComplexShape.EulerCharSigns.ofSpectralSequenceNatOdd` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem EulerCharSigns.ofSpectralSequenceNatOdd_χ {u : ℤ × ℤ} (hu : Odd (u.1 + u.2))
    (pq : ℕ × ℕ) :
    (EulerCharSigns.ofSpectralSequenceNatOdd hu).χ pq = ((pq.1 : ℤ) + pq.2).negOnePow :=
  (rfl)

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on
`ComplexShape.spectralSequenceFin l u` for any shift `u : ℤ × ℤ` of odd total degree. -/
@[instance_reducible]
def EulerCharSigns.ofSpectralSequenceFinOdd {l : ℕ} {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (spectralSequenceFin l u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq'.1 + pq'.2 = (pq.1 + pq.2) + (u.1 + u.2) := by
      rw [← h.1, ← h.2]
      ring
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- The sign at `pq` under `ComplexShape.EulerCharSigns.ofSpectralSequenceFinOdd` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem EulerCharSigns.ofSpectralSequenceFinOdd_χ {l : ℕ} {u : ℤ × ℤ} (hu : Odd (u.1 + u.2))
    (pq : ℤ × Fin l) :
    (EulerCharSigns.ofSpectralSequenceFinOdd hu).χ pq = (pq.1 + pq.2).negOnePow :=
  (rfl)

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a cohomological spectral sequence. -/
instance eulerCharSignsUp'Sub (r : ℤ) :
    (up' (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofUp'Odd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.up' (r, 1 - r)` is `(-1)^(pq.1 + pq.2)`. -/
@[simp high]
theorem χ_up'_sub (r : ℤ) (pq : ℤ × ℤ) :
    (up' (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow :=
  EulerCharSigns.ofUp'Odd_χ _ pq

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a homological spectral sequence. -/
instance eulerCharSignsDown'Sub (r : ℤ) :
    (down' (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofDown'Odd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.down' (r, 1 - r)` is `(-1)^(pq.1 + pq.2)`. -/
@[simp high]
theorem χ_down'_sub (r : ℤ) (pq : ℤ × ℤ) :
    (down' (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow :=
  EulerCharSigns.ofDown'Odd_χ _ pq

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a first-quadrant cohomological
spectral sequence indexed by `ℕ × ℕ`. -/
instance eulerCharSignsSpectralSequenceNat (r : ℤ) :
    (spectralSequenceNat (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofSpectralSequenceNatOdd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.spectralSequenceNat (r, 1 - r)` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp high]
theorem χ_spectralSequenceNat (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat (r, 1 - r)).χ pq = ((pq.1 : ℤ) + pq.2).negOnePow :=
  EulerCharSigns.ofSpectralSequenceNatOdd_χ _ pq

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a bounded-row cohomological spectral
sequence indexed by `ℤ × Fin l`. -/
instance eulerCharSignsSpectralSequenceFin (l : ℕ) (r : ℤ) :
    (spectralSequenceFin l (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofSpectralSequenceFinOdd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.spectralSequenceFin l (r, 1 - r)` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp high]
theorem χ_spectralSequenceFin (l : ℕ) (r : ℤ) (pq : ℤ × Fin l) :
    (spectralSequenceFin l (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow :=
  EulerCharSigns.ofSpectralSequenceFinOdd_χ _ pq

end ComplexShape

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [Ring R] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- **Finite generation propagates to later pages.** Over a Noetherian ring, if `(E.page r).X pq` is
finitely generated, then `(E.page r').X pq` is finitely generated for every `r' ≥ r`. -/
theorem finite_page_X_of_le [IsNoetherianRing R] {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    [h : Module.Finite R ((E.page r).X pq)] (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ s hrs ih =>
    have : Module.Finite R ((E.page s (hr.trans hrs)).X pq) := ih
    exact ((E.page s (hr.trans hrs)).finite_homology pq).equiv
      (E.iso s (s + 1) pq rfl (hr.trans hrs)).toLinearEquiv

/-- **One-step Euler characteristic invariance.** Over a ring with rank--nullity, if page `s` has
finitely generated terms, finitely many nonzero objects, and the same alternating signs as page
`s + 1`, then `(E.page s).eulerChar = (E.page (s + 1)).eulerChar`. -/
theorem eulerChar_page_eq_of_succ [StrongRankCondition R] [HasRankNullity.{v} R]
    {s : ℤ} (hs : r₀ ≤ s) [(c s).EulerCharSigns] [(c (s + 1)).EulerCharSigns]
    [∀ pq, Module.Finite R ((E.page s hs).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page s hs).X pq)}.Finite)
    (hχ : ∀ pq, (c s).χ pq = (c (s + 1)).χ pq := by simp) :
    (E.page s hs).eulerChar = (E.page (s + 1) (Int.le_add_one hs)).eulerChar := by
  rw [(E.page s hs).eulerChar_eq_homologyEulerChar hfin]
  exact finsum_congr fun pq ↦ by
    rw [hχ pq, (E.iso s (s + 1) pq rfl hs).toLinearEquiv.finrank_eq]

/-- **Invariance of the Euler characteristic across pages of a spectral sequence.** Over a
Noetherian ring satisfying rank--nullity, if page `r` has finitely generated terms and finitely many
nonzero objects, and all pages carry the same alternating signs, then every later page `r' ≥ r` has
the same Euler characteristic as page `r`. -/
theorem eulerChar_page_eq_of_le [IsNoetherianRing R] [HasRankNullity.{v} R]
    [∀ s, (c s).EulerCharSigns] {r : ℤ} (hr : r₀ ≤ r)
    [∀ pq, Module.Finite R ((E.page r).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page r).X pq)}.Finite)
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ s s' pq, (c s).χ pq = (c s').χ pq := by simp) :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ s hrs ih =>
    have : ∀ pq, Module.Finite R ((E.page s (hr.trans hrs)).X pq) :=
      fun _ ↦ E.finite_page_X_of_le hr s hrs
    rw [← E.eulerChar_page_eq_of_succ (hr.trans hrs)
      (E.finite_not_isZero_page_X_of_le hr hfin s hrs) (fun pq ↦ hχ s (s + 1) pq), ih]

end CategoryTheory.SpectralSequence
