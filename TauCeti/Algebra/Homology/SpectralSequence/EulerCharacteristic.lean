/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ComplexShape
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
import Mathlib.Order.SuccPred.Int
import TauCeti.Algebra.Homology.SpectralObject.Finrank
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
import TauCeti.Algebra.Homology.SpectralSequence.ModuleCat

/-!
# Euler characteristic of spectral sequences and filtered abutments

Let `E` be a spectral sequence of `R`-modules. Because each page `E_{r+1}` is isomorphic to the
homology of `E_r`, cardinal rank does not increase across pages
(`TauCeti.Algebra.Homology.SpectralSequence.ModuleCat`,
`CategoryTheory.SpectralSequence.rank_page_X_le_of_le`).

When `R` satisfies `HasRankNullity` (for instance a division ring or a commutative domain such as
`ℤ`, with no Noetherianity hypothesis) and the alternating signs `(c s).χ` are independent of the
page `s`, Euler–Poincaré for arbitrary complex shapes
(`HomologicalComplex.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology_of_rank_lt_aleph0`) shows
that the Euler characteristic `(E.page r).eulerChar` is constant across all pages `r' ≥ r` once
page `r` has finite support and terms of finite cardinal rank
(`CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le_of_rank_lt_aleph0`, specialized to
finitely generated terms under `StrongRankCondition` in
`CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le` and to cohomological spectral sequences in
`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le_of_rank_lt_aleph0` and
`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le`).

On the abutment side, `TauCeti.Algebra.Homology.SpectralObject.Finrank` supplies finite
generation and rank additivity for finitely filtered abutments of spectral objects of modules.
Combining strong convergence on a finite box of bidegrees with total-degree alternating signs
equates `(E.page r).eulerChar` with the alternating sum of the ranks of `X.abutment`
(`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment`).

## Main results

* `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le_of_rank_lt_aleph0`,
  `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`,
  `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le_of_rank_lt_aleph0`, and
  `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le`: invariance of the Euler
  characteristic across pages of a spectral sequence without Noetherianity.
* `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment`: the Euler
  characteristic of a converged page equals the alternating sum of the ranks of the abutment.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II, §3.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 1.15 and Chapter 2.
-/

public section

open CategoryTheory Limits Module Cardinal

universe u v

namespace CategoryTheory.SpectralSequence

section EulerChar

section RankLtAleph0

variable {R : Type u} [Ring R] [HasRankNullity.{v} R]
  {κ : Type*} {c : ℤ → ComplexShape κ} [∀ r, (c r).EulerCharSigns] {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over any ring satisfying `HasRankNullity`, if page `r` of a spectral sequence vanishes outside
`s : Finset κ`, has terms of finite cardinal rank on `s`, and the Euler characteristic signs
`(c t).χ` agree on `s` for `r ≤ t ≤ r'`, then the alternating sum of ranks over `s` on page `r'`
equals that on page `r`. -/
theorem sum_eulerCharSigns_finrank_page_X_eq_of_le_of_rank_lt_aleph0 {r : ℤ} (hr : r₀ ≤ r)
    {s : Finset κ} (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hrank : ∀ pq ∈ s, Module.rank R ((E.page r).X pq) < ℵ₀)
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    ∑ pq ∈ s, ((c r').χ pq : ℤ) * finrank R ((E.page r' (hr.trans hrr')).X pq) =
      ∑ pq ∈ s, ((c r).χ pq : ℤ) * finrank R ((E.page r).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ t hrt ih =>
    have hstep :=
      HomologicalComplex.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology_of_rank_lt_aleph0
        (E.page t (hr.trans hrt))
        (fun pq hpq ↦ E.isZero_page_X_of_le hr (hs pq hpq) t hrt)
        (fun pq hpq ↦ (E.rank_page_X_le_of_le hr t hrt).trans_lt (hrank pq hpq))
    rw [← ih (fun u hru hut ↦ hχ u hru (hut.trans (Int.le_add_one le_rfl))), hstep]
    refine Finset.sum_congr rfl fun pq hpq ↦ ?_
    rw [hχ (t + 1) (Int.le_add_one hrt) le_rfl pq hpq,
      hχ t hrt (Int.le_add_one le_rfl) pq hpq,
      (E.iso t (t + 1) pq rfl (hr.trans hrt)).toLinearEquiv.finrank_eq]

/-- **Page invariance of the Euler characteristic of a spectral sequence (finite rank).** Under the
hypotheses of `sum_eulerCharSigns_finrank_page_X_eq_of_le_of_rank_lt_aleph0`,
`(E.page r').eulerChar = (E.page r).eulerChar` for every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le_of_rank_lt_aleph0 {r : ℤ} (hr : r₀ ≤ r) {s : Finset κ}
    (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hrank : ∀ pq ∈ s, Module.rank R ((E.page r).X pq) < ℵ₀)
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar := by
  rw [(E.page r' (hr.trans hrr')).eulerChar_eq_sum_of_forall_notMem
      (fun pq hpq ↦ E.isZero_page_X_of_le hr (hs pq hpq) r' hrr'),
    (E.page r).eulerChar_eq_sum_of_forall_notMem hs]
  exact E.sum_eulerCharSigns_finrank_page_X_eq_of_le_of_rank_lt_aleph0 hr hs hrank r' hrr' hχ

end RankLtAleph0

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]
  {κ : Type*} {c : ℤ → ComplexShape κ} [∀ r, (c r).EulerCharSigns] {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over a ring satisfying `StrongRankCondition` and `HasRankNullity`, if page `r` of a spectral
sequence vanishes outside `s : Finset κ`, has finitely generated terms on `s`, and the Euler
characteristic signs `(c t).χ` agree on `s` for `r ≤ t ≤ r'`, then the alternating sum of ranks
over `s` on page `r'` equals that on page `r`. -/
theorem sum_eulerCharSigns_finrank_page_X_eq_of_le {r : ℤ} (hr : r₀ ≤ r) {s : Finset κ}
    (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    ∑ pq ∈ s, ((c r').χ pq : ℤ) * finrank R ((E.page r' (hr.trans hrr')).X pq) =
      ∑ pq ∈ s, ((c r).χ pq : ℤ) * finrank R ((E.page r).X pq) :=
  E.sum_eulerCharSigns_finrank_page_X_eq_of_le_of_rank_lt_aleph0 hr hs
    (fun pq hpq ↦ have := hfin pq hpq; Module.rank_lt_aleph0 R ((E.page r hr).X pq)) r' hrr' hχ

/-- **Page invariance of the Euler characteristic of a spectral sequence.** Under the hypotheses of
`sum_eulerCharSigns_finrank_page_X_eq_of_le`, `(E.page r').eulerChar = (E.page r).eulerChar` for
every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le {r : ℤ} (hr : r₀ ≤ r) {s : Finset κ}
    (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar :=
  E.eulerChar_page_eq_of_le_of_rank_lt_aleph0 hr hs
    (fun pq hpq ↦ have := hfin pq hpq; Module.rank_lt_aleph0 R ((E.page r hr).X pq)) r' hrr' hχ

end EulerChar

end CategoryTheory.SpectralSequence

namespace CategoryTheory.CohomologicalSpectralSequence

section RankLtAleph0

variable {R : Type u} [Ring R] [HasRankNullity.{v} R]

/-- **Page invariance of the Euler characteristic of a cohomological spectral sequence (finite
rank).** Over any ring satisfying `HasRankNullity`, if page `r` vanishes outside a finite set `s`
of bidegrees and has terms of finite cardinal rank on `s`, then
`(E.page r').eulerChar = (E.page r).eulerChar` for every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le_of_rank_lt_aleph0 {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀) {r : ℤ} (hr : r₀ ≤ r)
    {s : Finset (ℤ × ℤ)} (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hrank : ∀ pq ∈ s, Module.rank R ((E.page r).X pq) < ℵ₀) (r' : ℤ) (hrr' : r ≤ r') :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar :=
  SpectralSequence.eulerChar_page_eq_of_le_of_rank_lt_aleph0 E hr hs hrank r' hrr'
    fun _ _ _ _ _ ↦ by simp

end RankLtAleph0

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- **Page invariance of the Euler characteristic of a cohomological spectral sequence.** Over a
ring satisfying `StrongRankCondition` and `HasRankNullity`, if page `r` vanishes outside a finite
set `s` of bidegrees and has finitely generated terms on `s`, then
`(E.page r').eulerChar = (E.page r).eulerChar` for every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀) {r : ℤ} (hr : r₀ ≤ r)
    {s : Finset (ℤ × ℤ)} (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq)) (r' : ℤ) (hrr' : r ≤ r') :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar :=
  SpectralSequence.eulerChar_page_eq_of_le E hr hs hfin r' hrr'
    fun _ _ _ _ _ ↦ by simp

/-- **Euler characteristic of a converged page equals the alternating sum of abutment ranks.**
Suppose page `r` of a cohomological spectral sequence `E` vanishes outside the bidegrees `pq` with
`pq.1 + pq.2 ∈ I` and `pq.2 ∈ Ico a b`, and for each `n ∈ I` and `q ∈ Ico a b` the term
`(E.page r).X (n - q, q)` is finitely generated and isomorphic to the graded piece
`cokernel (X.abutmentFiltrationMap q n)` of a filtration of `X.abutment` that starts at `0` at `a`
and is exhaustive at `b`. Then `(E.page r).eulerChar` equals
`∑ n ∈ I, (-1)^n * finrank R (X.abutment n)`. -/
theorem eulerChar_page_eq_sum_abutment {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀)
    (X : Abelian.SpectralObject (ModuleCat.{v} R) EInt)
    {r : ℤ} (hr : r₀ ≤ r) (I : Finset ℤ) {a b : ℤ} (hab : a ≤ b)
    (ha : ∀ n ∈ I, IsZero (X.abutmentFiltration a n))
    (hb : ∀ n ∈ I, IsIso (X.abutmentFiltrationι b n))
    (hzero : ∀ pq : ℤ × ℤ, ¬ (pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico a b) →
      IsZero ((E.page r).X pq))
    (hfin : ∀ n ∈ I, ∀ q ∈ Finset.Ico a b, Module.Finite R ((E.page r).X (n - q, q)))
    (hiso : ∀ n ∈ I, ∀ q ∈ Finset.Ico a b,
      Nonempty (((E.page r).X (n - q, q)) ≅ cokernel (X.abutmentFiltrationMap q n))) :
    (E.page r).eulerChar = ∑ n ∈ I, (n.negOnePow : ℤ) * finrank R (X.abutment n) := by
  let s : Finset (ℤ × ℤ) := (I ×ˢ Finset.Ico a b).image fun nq ↦ (nq.1 - nq.2, nq.2)
  have hmem_s (pq : ℤ × ℤ) : pq ∈ s ↔ pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico a b := by
    constructor
    · intro hpq
      rcases Finset.mem_image.1 hpq with ⟨⟨n, q⟩, hnq, rfl⟩
      rw [sub_add_cancel]
      exact Finset.mem_product.1 hnq
    · rintro ⟨hn, hq⟩
      exact Finset.mem_image.2 ⟨(pq.1 + pq.2, pq.2), Finset.mem_product.2 ⟨hn, hq⟩,
        Prod.ext (add_sub_cancel_right pq.1 pq.2) rfl⟩
  rw [(E.page r).eulerChar_eq_sum_of_forall_notMem
      fun pq hpq ↦ hzero pq ((hmem_s pq).not.1 hpq)]
  rw [Finset.sum_image (by
    rintro ⟨n₁, q₁⟩ _ ⟨n₂, q₂⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    lia)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hcok (q : ℤ) (hq : q ∈ Finset.Ico a b) :
      Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n)) :=
    have := hfin n hn q hq
    .equiv (hiso n hn q hq).some.toLinearEquiv
  rw [X.finrank_abutment_eq_sum_Ico hab (ha n hn) (hb n hn) hcok, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  simp only [ComplexShape.eulerCharSignsCohomologicalSpectralSequence_χ, sub_add_cancel,
    (hiso n hn q hq).some.toLinearEquiv.finrank_eq]

end CategoryTheory.CohomologicalSpectralSequence
