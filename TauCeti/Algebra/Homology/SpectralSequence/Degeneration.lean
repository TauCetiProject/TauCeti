/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.SerreClass

/-!
# Vanishing and survival of objects on later pages of a spectral sequence

Each page of a spectral sequence is the homology of the previous one, so its objects are
subquotients of the objects of every earlier page. Hence an object which vanishes on some page
vanishes on every later page (`CategoryTheory.SpectralSequence.isZero_page_X_of_le`).

Conversely, suppose that on the page `r` every object joined to the position `pq` by a
differential of some later page vanishes. Then on every later page both differentials at `pq`
vanish, because their other ends are already zero, so the object at `pq` is its own homology and
survives unchanged to every page `r' ≥ r`
(`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero`). This is how sparseness of an early
page, for instance a lacunary pattern of nonzero total degrees, makes a spectral sequence
degenerate: all differentials from the page `r` on vanish
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`).

For a cohomological spectral sequence starting on the page `2`, whose differentials on the page
`r` go from `(p, q)` to `(p + r, q - r + 1)` and so raise the total degree `p + q` by one, this
gives the lacunary degeneration: if of any two positions of the page `2` whose total degrees differ
by one at least one carries the zero object, every differential from the page `2` on vanishes
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_isZero_or_isZero`), and every object of the
page `2` survives unchanged to every later page
(`CategoryTheory.SpectralSequence.nonempty_page_X_iso_page_two_X_of_isZero_or_isZero`).

## Main results

* `CategoryTheory.SpectralSequence.isZero_page_X_of_le`: a zero object stays zero on later pages.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`: a differential of a later page between
  positions one of which is zero on an earlier page vanishes.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero_page`,
  `CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero`: the differentials at a
  position whose neighbours vanish are zero on a later page, or on all later pages.
* `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero`: an object whose neighbours vanish
  survives unchanged to all later pages, with
  `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero_self` and
  `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero_add_one`;
  `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT` is the same up to a given page, when
  the neighbours joined by the differentials of the later pages need not vanish, with
  `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT_self` and
  `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT_add_one`.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_isZero_or_isZero` and
  `CategoryTheory.SpectralSequence.nonempty_page_X_iso_page_two_X_of_isZero_or_isZero`: lacunary
  degeneration of a cohomological spectral sequence starting on the page `2`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §1.2, the objects of later pages as subquotients of those of earlier pages.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence C c r₀)

/-- **Zero objects stay zero.** If the object at `pq` vanishes on the page `r`, it vanishes on
every later page `r' ≥ r`, since each page is the homology of the previous one. This is
`CategoryTheory.SpectralSequence.prop_page_X_of_le` for the Serre class of zero objects. -/
lemma isZero_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (h : IsZero ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r') : IsZero ((E.page r' (hr.trans hrr')).X pq) :=
  E.prop_page_X_of_le IsZero hr h r' hrr'

/-- **Differentials into or out of zero objects vanish on later pages.** If the source or the
target of a differential of the page `r' ≥ r` is zero on the page `r`, the differential is zero. -/
lemma page_d_eq_zero_of_le {r : ℤ} (hr : r₀ ≤ r) {pq pq' : κ}
    (h : IsZero ((E.page r).X pq) ∨ IsZero ((E.page r).X pq')) (r' : ℤ) (hrr' : r ≤ r') :
    (E.page r' (hr.trans hrr')).d pq pq' = 0 := by
  rcases h with h | h
  · exact (E.isZero_page_X_of_le hr h r' hrr').eq_of_src _ _
  · exact (E.isZero_page_X_of_le hr h r' hrr').eq_of_tgt _ _

/-- **The differentials of one page at a position with vanishing neighbours vanish.** Suppose that
on the page `r` every object joined to the position `pq` by a differential of the page `s ≥ r` is
zero. Then both differentials of the page `s` at `pq` vanish: either their other end is zero, or
the shape forbids them. -/
lemma page_d_eq_zero_of_forall_isZero_page {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (s : ℤ) (hrs : r ≤ s)
    (h : ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    {i j : κ} (hij : i = pq ∨ j = pq) :
    (E.page s (hr.trans hrs)).d i j = 0 := by
  by_cases hrel : (c s).Rel i j
  · rcases hij with rfl | rfl
    · exact E.page_d_eq_zero_of_le hr (Or.inr (h j (Or.inl hrel))) s hrs
    · exact E.page_d_eq_zero_of_le hr (Or.inl (h i (Or.inr hrel))) s hrs
  · exact (E.page s (hr.trans hrs)).shape i j hrel

/-- **Differentials at a position with vanishing neighbours vanish.** Suppose that on the page `r`
every object joined to the position `pq` by a differential of some page `s ≥ r` is zero. Then on
every page `s ≥ r` both differentials at `pq` vanish: either their other end is zero, or the shape
forbids them. -/
lemma page_d_eq_zero_of_forall_isZero {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    (s : ℤ) (hrs : r ≤ s) {i j : κ} (hij : i = pq ∨ j = pq) :
    (E.page s (hr.trans hrs)).d i j = 0 :=
  E.page_d_eq_zero_of_forall_isZero_page hr s hrs (h s hrs) hij

/-- **Objects with vanishing neighbours survive up to a page.** Suppose that on the page `r` every
object joined to the position `pq` by a differential of a page `s` with `r ≤ s < r'` is zero. Then
the object at `pq` on the page `r'` is isomorphic to the object at `pq` on the page `r`: on each
page in between, both differentials at `pq` vanish
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero_page`), so the object is its own
homology. Nothing is assumed about the differentials of the page `r'` and the later ones, which may
be nonzero at `pq`. The isomorphism is built page by page, see
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT_self` and
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT_add_one`. -/
noncomputable def pageXIsoOfLEOfIsZeroOfLT {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (r' : ℤ) (hrr' : r ≤ r')
    (h : ∀ s, r ≤ s → s < r' → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq →
      IsZero ((E.page r).X pq')) :
    (E.page r' (hr.trans hrr')).X pq ≅ (E.page r).X pq :=
  Int.leInduction (motive := fun r' hrr' ↦ (∀ s, r ≤ s → s < r' → ∀ pq',
      (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq')) →
      ((E.page r' (hr.trans hrr')).X pq ≅ (E.page r).X pq))
    (fun _ ↦ Iso.refl _)
    (fun s hrs e h ↦ (E.iso s (s + 1) pq rfl (hr.trans hrs)).symm ≪≫
      ((E.page s (hr.trans hrs)).isoHomologyπ _ pq rfl
        (E.page_d_eq_zero_of_forall_isZero_page hr s hrs (h s hrs (by lia))
          (Or.inr rfl))).symm ≪≫
      (E.page s (hr.trans hrs)).iCyclesIso pq _ rfl
        (E.page_d_eq_zero_of_forall_isZero_page hr s hrs (h s hrs (by lia)) (Or.inl rfl)) ≪≫
      e fun t ht hts ↦ h t ht (by lia))
    r' hrr' h

/-- On the page `r` itself, `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT` is the
identity. -/
@[simp]
lemma pageXIsoOfLEOfIsZeroOfLT_self {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → s < r → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq →
      IsZero ((E.page r).X pq')) :
    E.pageXIsoOfLEOfIsZeroOfLT hr r le_rfl h = Iso.refl _ := by
  rw [pageXIsoOfLEOfIsZeroOfLT, Int.leInduction_base]

/-- From the page `s` to the page `s + 1`,
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT` identifies the object at `pq` with its
homology on the page `s`, which is the object itself since both differentials at `pq` vanish. -/
lemma pageXIsoOfLEOfIsZeroOfLT_add_one {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (s : ℤ) (hrs : r ≤ s)
    (h : ∀ t, r ≤ t → t < s + 1 → ∀ pq', (c t).Rel pq pq' ∨ (c t).Rel pq' pq →
      IsZero ((E.page r).X pq')) :
    E.pageXIsoOfLEOfIsZeroOfLT hr (s + 1) (Int.le_add_one hrs) h =
      (E.iso s (s + 1) pq rfl (hr.trans hrs)).symm ≪≫
        ((E.page s (hr.trans hrs)).isoHomologyπ _ pq rfl
          (E.page_d_eq_zero_of_forall_isZero_page hr s hrs (h s hrs (by lia))
            (Or.inr rfl))).symm ≪≫
        (E.page s (hr.trans hrs)).iCyclesIso pq _ rfl
          (E.page_d_eq_zero_of_forall_isZero_page hr s hrs (h s hrs (by lia)) (Or.inl rfl)) ≪≫
        E.pageXIsoOfLEOfIsZeroOfLT hr s hrs fun t ht hts ↦ h t ht (by lia) := by
  rw [pageXIsoOfLEOfIsZeroOfLT, Int.leInduction_add_one]
  rfl

/-- **Objects with vanishing neighbours survive.** Suppose that on the page `r` every object
joined to the position `pq` by a differential of some page `s ≥ r` is zero. Then the object at
`pq` on every later page `r' ≥ r` is isomorphic to the object at `pq` on the page `r`. This is
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT`, whose hypothesis now holds up to every
page; see `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero_self` and
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero_add_one`. -/
noncomputable def pageXIsoOfLEOfIsZero {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    (r' : ℤ) (hrr' : r ≤ r') : (E.page r' (hr.trans hrr')).X pq ≅ (E.page r).X pq :=
  E.pageXIsoOfLEOfIsZeroOfLT hr r' hrr' fun s hs _ ↦ h s hs

/-- On the page `r` itself, `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero` is the
identity. -/
@[simp]
lemma pageXIsoOfLEOfIsZero_self {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq')) :
    E.pageXIsoOfLEOfIsZero hr h r le_rfl = Iso.refl _ :=
  E.pageXIsoOfLEOfIsZeroOfLT_self hr _

/-- From the page `s` to the page `s + 1`,
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZero` identifies the object at `pq` with its
homology on the page `s`, which is the object itself since both differentials at `pq` vanish. -/
lemma pageXIsoOfLEOfIsZero_add_one {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    (s : ℤ) (hrs : r ≤ s) :
    E.pageXIsoOfLEOfIsZero hr h (s + 1) (Int.le_add_one hrs) =
      (E.iso s (s + 1) pq rfl (hr.trans hrs)).symm ≪≫
        ((E.page s (hr.trans hrs)).isoHomologyπ _ pq rfl
          (E.page_d_eq_zero_of_forall_isZero hr h s hrs (Or.inr rfl))).symm ≪≫
        (E.page s (hr.trans hrs)).iCyclesIso pq _ rfl
          (E.page_d_eq_zero_of_forall_isZero hr h s hrs (Or.inl rfl)) ≪≫
        E.pageXIsoOfLEOfIsZero hr h s hrs :=
  E.pageXIsoOfLEOfIsZeroOfLT_add_one hr s hrs _

section Cohomological

variable (E : SpectralSequence C (fun r ↦ ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) 2)

/-- **Lacunary degeneration.** If of any two positions of the page `2` of a cohomological spectral
sequence whose total degrees differ by one at least one carries the zero object, every
differential on every page `r ≥ 2` vanishes, since a differential raises the total degree by
one. -/
lemma page_d_eq_zero_of_isZero_or_isZero
    (h : ∀ pq pq' : ℤ × ℤ, pq.1 + pq.2 + 1 = pq'.1 + pq'.2 →
      IsZero ((E.page 2).X pq) ∨ IsZero ((E.page 2).X pq'))
    (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) : (E.page r hr).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
  · exact E.page_d_eq_zero_of_le le_rfl
      (h pq pq' (Abelian.SpectralObject.coreE₂Cohomological.hc r pq pq' hrel hr)) r hr
  · exact HomologicalComplex.shape _ _ _ hrel

/-- **Survival in the lacunary case.** Let `pq` be a position of the page `2` of a cohomological
spectral sequence. If for every position `pq'` whose total degree differs by one from that of `pq`
the object at `pq` or the object at `pq'` vanishes on the page `2`, then on every page `r ≥ 2` the
object at `pq` is isomorphic to the object at `pq` on the page `2`. -/
lemma nonempty_page_X_iso_page_two_X_of_isZero_or_isZero {pq : ℤ × ℤ}
    (h : ∀ pq' : ℤ × ℤ, pq.1 + pq.2 + 1 = pq'.1 + pq'.2 ∨ pq'.1 + pq'.2 + 1 = pq.1 + pq.2 →
      IsZero ((E.page 2).X pq) ∨ IsZero ((E.page 2).X pq'))
    (r : ℤ) (hr : 2 ≤ r) : Nonempty ((E.page r hr).X pq ≅ (E.page 2).X pq) := by
  by_cases hpq : IsZero ((E.page 2).X pq)
  · exact ⟨(E.isZero_page_X_of_le le_rfl hpq r hr).iso hpq⟩
  -- Otherwise every object joined to `pq` by a differential vanishes, so `pq` survives.
  refine ⟨E.pageXIsoOfLEOfIsZero le_rfl (fun s hs pq' hpq' ↦ (h pq' ?_).resolve_left hpq) r hr⟩
  exact hpq'.imp (fun hrel ↦ Abelian.SpectralObject.coreE₂Cohomological.hc s _ _ hrel hs)
    (fun hrel ↦ Abelian.SpectralObject.coreE₂Cohomological.hc s _ _ hrel hs)

end Cohomological

end CategoryTheory.SpectralSequence
