/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.HomologicalComplex
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.Algebra.Homology.SpectralSequence.ModuleCat

/-!
# Euler characteristic of pages of spectral sequences

In a spectral sequence `(E_r)` of modules over a ring `R`, each page `E_r` is a homological complex
whose homology is isomorphic to `E_{r+1}`. Whenever a differential vector `u = (u₁, u₂)` has odd
total degree `u₁ + u₂`, the total-degree sign `(p, q) ↦ (-1)^(p + q)` alternates along the
differentials of `E_r` and does not depend on the page index `r`: in particular, for cohomological
spectral sequences with `u = (r, 1 - r)` one has `r + (1 - r) = 1`.

Combining this sign convention with `HomologicalComplex.eulerChar_eq_homologyEulerChar` gives
invariance of the Euler characteristic across the pages of a finitely supported spectral sequence:

* `ComplexShape.EulerCharSigns.ofUp'Odd` and `ComplexShape.eulerCharSignsUp'Sub`: total-degree
  alternating signs `(p, q) ↦ (-1)^(p + q)` on `ComplexShape.up' u` for odd `u.1 + u.2` and on the
  cohomological spectral sequence page shapes `(r, 1 - r)`.
* `CategoryTheory.SpectralSequence.eulerChar_page_add_one`,
  `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le_of_finite`, and
  `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`: Euler characteristic invariance across
  one step, across a finite interval `r ≤ s < r'`, and across arbitrarily many pages. All three
  assume finite support on the starting page and adjacent sign agreement (`(c s).χ = (c (s + 1)).χ`)
  across the step or interval; for one step finite generation is needed only on the source page `s`,
  across `[r, r')` on every page in that interval, and across arbitrarily many pages via Noetherian
  terms on page `r` over a ring satisfying the strong rank condition and rank--nullity.

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

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a cohomological spectral sequence with
differential bidegree `(r, 1 - r)`. -/
instance eulerCharSignsUp'Sub (r : ℤ) :
    (up' (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofUp'Odd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.up' (r, 1 - r)` is `(-1)^(pq.1 + pq.2)`. -/
@[simp high]
theorem χ_up'_sub (r : ℤ) (pq : ℤ × ℤ) :
    (up' (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow :=
  EulerCharSigns.ofUp'Odd_χ _ pq

/-- At a position `pq` of total degree `pq.1 + pq.2 = -n`, the alternating sign on
`ComplexShape.up' (r, 1 - r)` is `(-1 : ℤ) ^ n`. -/
theorem coe_χ_up'_sub_of_add_eq_neg (r : ℤ) {pq : ℤ × ℤ} {n : ℕ} (h : pq.1 + pq.2 = -(n : ℤ)) :
    ((up' (r, 1 - r)).χ pq : ℤ) = (-1 : ℤ) ^ n := by
  rw [χ_up'_sub, h, Int.negOnePow_neg, Int.coe_negOnePow_natCast]

end ComplexShape

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [Ring R] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- **One-step Euler characteristic invariance.** Over a ring satisfying the strong rank condition
and rank--nullity, if page `s` has finitely generated terms, finitely many nonzero objects, and the
same alternating signs as page `s + 1`, then `(E.page (s + 1)).eulerChar = (E.page s).eulerChar`. -/
theorem eulerChar_page_add_one [StrongRankCondition R] [HasRankNullity.{v} R]
    {s : ℤ} (hs : r₀ ≤ s) [(c s).EulerCharSigns] [(c (s + 1)).EulerCharSigns]
    [∀ pq, Module.Finite R ((E.page s hs).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page s hs).X pq)}.Finite)
    (hχ : ∀ pq, (c s).χ pq = (c (s + 1)).χ pq := by simp) :
    (E.page (s + 1) (Int.le_add_one hs)).eulerChar = (E.page s hs).eulerChar := by
  rw [(E.page s hs).eulerChar_eq_homologyEulerChar hfin]
  exact finsum_congr fun pq ↦ by
    rw [hχ pq, (E.iso s (s + 1) pq rfl hs).toLinearEquiv.finrank_eq]

/-- **Invariance of the Euler characteristic across finitely many pages of a spectral sequence.**
Over a ring satisfying the strong rank condition and rank--nullity, if page `r` has finitely many
nonzero objects and every page `s` in `[r, r')` has finitely generated terms and the same
alternating signs as page `s + 1`, then `(E.page r').eulerChar = (E.page r).eulerChar`. -/
theorem eulerChar_page_eq_of_le_of_finite [StrongRankCondition R] [HasRankNullity.{v} R]
    {r : ℤ} (hr : r₀ ≤ r)
    (hfin : {pq : κ | ¬ IsZero ((E.page r).X pq)}.Finite)
    (r' : ℤ) (hrr' : r ≤ r')
    [hsigns : ∀ s : Set.Icc r r', (c s.val).EulerCharSigns]
    (hmem : ∀ s (hs : r ≤ s), s < r' → ∀ pq,
      Module.Finite R ((E.page s (hr.trans hs)).X pq))
    (hχ : ∀ s (hs : r ≤ s) (hs' : s < r'), ∀ pq,
      (letI := hsigns ⟨s, hs, Int.le_of_lt hs'⟩; (c s).χ pq) =
        (letI := hsigns ⟨s + 1, Int.le_add_one hs, hs'⟩; (c (s + 1)).χ pq) := by simp) :
    (letI := hsigns ⟨r', hrr', le_rfl⟩; (E.page r' (hr.trans hrr')).eulerChar) =
      (letI := hsigns ⟨r, le_rfl, hrr'⟩; (E.page r).eulerChar) := by
  revert hsigns hmem hχ
  induction r', hrr' using Int.leInduction with
  | base => intros; rfl
  | succ s hrs ih =>
    intro hsigns hmem hχ
    have : ∀ pq, Module.Finite R ((E.page s (hr.trans hrs)).X pq) :=
      hmem s hrs (Int.lt_succ s)
    let _ : (c s).EulerCharSigns := hsigns ⟨s, hrs, Int.le_add_one le_rfl⟩
    let _ : (c (s + 1)).EulerCharSigns := hsigns ⟨s + 1, Int.le_add_one hrs, le_rfl⟩
    have hstep := E.eulerChar_page_add_one (hr.trans hrs)
      (E.finite_not_isZero_page_X_of_le hr hfin s hrs) (hχ s hrs (Int.lt_succ s))
    have hih := @ih
      (fun t ↦ hsigns ⟨t.val, t.property.1, le_trans t.property.2 (Int.le_add_one le_rfl)⟩)
      (fun t ht hts ↦ hmem t ht (lt_trans hts (Int.lt_succ s)))
      (fun t ht hts ↦ hχ t ht (lt_trans hts (Int.lt_succ s)))
    exact hstep.trans hih

/-- **Invariance of the Euler characteristic across pages of a spectral sequence.** Over a ring
satisfying the strong rank condition and rank--nullity, if page `r` has Noetherian terms (for
instance if `R` is a Noetherian ring and page `r` has finitely generated terms) and finitely many
nonzero objects, and adjacent pages `s` and `s + 1` in `[r, r')` carry the same alternating signs,
then `(E.page r').eulerChar = (E.page r).eulerChar`. -/
theorem eulerChar_page_eq_of_le [StrongRankCondition R] [HasRankNullity.{v} R]
    {r : ℤ} (hr : r₀ ≤ r)
    [∀ pq, IsNoetherian R ((E.page r).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page r).X pq)}.Finite)
    (r' : ℤ) (hrr' : r ≤ r')
    [hsigns : ∀ s : Set.Icc r r', (c s.val).EulerCharSigns]
    (hχ : ∀ s (hs : r ≤ s) (hs' : s < r'), ∀ pq,
      (letI := hsigns ⟨s, hs, Int.le_of_lt hs'⟩; (c s).χ pq) =
        (letI := hsigns ⟨s + 1, Int.le_add_one hs, hs'⟩; (c (s + 1)).χ pq) := by simp) :
    (letI := hsigns ⟨r', hrr', le_rfl⟩; (E.page r' (hr.trans hrr')).eulerChar) =
      (letI := hsigns ⟨r, le_rfl, hrr'⟩; (E.page r).eulerChar) :=
  E.eulerChar_page_eq_of_le_of_finite hr hfin r' hrr'
    (fun s hs _ _ ↦ E.finite_page_X_of_le hr s hs) hχ

end CategoryTheory.SpectralSequence
