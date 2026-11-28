/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Stabilization.Basic

/-!
# Degeneration of spectral sequences

A spectral sequence `E : SpectralSequence C c r₀` **degenerates at page `s`** (`s ≥ r₀`) if every
differential on every page `r ≥ s` vanishes (`CategoryTheory.SpectralSequence.DegeneratesAt`). This
implies stabilization at every position from page `s`
(`CategoryTheory.SpectralSequence.DegeneratesAt.stabilizesAt`), and is invariant under isomorphisms
of spectral sequences (`CategoryTheory.SpectralSequence.degeneratesAt_iff_of_iso`).

For a cohomological spectral sequence starting on the page `2`, whose differentials on the page
`r` go from `(p, q)` to `(p + r, q - r + 1)` and so raise the total degree `p + q` by one, this
gives lacunary degeneration: if of any two positions of the page `2` whose total degrees differ
by one at least one carries the zero object, every differential from the page `2` on vanishes
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_isZero_or_isZero`), and every object of the
page `2` survives unchanged to every later page
(`CategoryTheory.SpectralSequence.nonempty_page_X_iso_page_two_X_of_isZero_or_isZero`).

## Main results

* `CategoryTheory.SpectralSequence.DegeneratesAt`: degeneration from page `s` onward, with
  `DegeneratesAt.mono`, `DegeneratesAt.stabilizesAt`, `degeneratesAt_iff_forall_stabilizesAt`, and
  `degeneratesAt_iff_of_iso`.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero_page`: the differentials at a
  position whose neighbours vanish are zero on a later page.
* `CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT`: an object whose neighbours vanish up
  to a given page survives unchanged to that page, with
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

section Degeneration

/-- A spectral sequence `E` **degenerates at page `s`** (`s ≥ r₀`) if every differential of every
page `r ≥ s` vanishes. -/
structure DegeneratesAt (E : SpectralSequence C c r₀) (s : ℤ) : Prop where
  /-- The degeneration page `s` is at least the starting page `r₀`. -/
  le : r₀ ≤ s
  /-- Every differential on every page `r ≥ s` vanishes. -/
  d_eq_zero : ∀ r (hsr : s ≤ r) (i j : κ), (E.page r (le.trans hsr)).d i j = 0

lemma DegeneratesAt.mono {E : SpectralSequence C c r₀} {s s' : ℤ} (h : E.DegeneratesAt s)
    (hss' : s ≤ s') : E.DegeneratesAt s' where
  le := h.le.trans hss'
  d_eq_zero r hs'r i j := h.d_eq_zero r (hss'.trans hs'r) i j

lemma DegeneratesAt.stabilizesAt {E : SpectralSequence C c r₀} {s : ℤ} (h : E.DegeneratesAt s)
    (pq : κ) : E.StabilizesAt pq s where
  le := h.le
  dFrom_eq_zero r hsr := h.d_eq_zero r hsr pq _
  dTo_eq_zero r hsr := h.d_eq_zero r hsr _ pq

lemma degeneratesAt_iff_forall_stabilizesAt (E : SpectralSequence C c r₀) (s : ℤ) :
    E.DegeneratesAt s ↔ r₀ ≤ s ∧ ∀ pq, E.StabilizesAt pq s := by
  refine ⟨fun h ↦ ⟨h.le, h.stabilizesAt⟩, fun ⟨hs, h⟩ ↦ ⟨hs, fun r hsr i j ↦ ?_⟩⟩
  exact ((E.page r (hs.trans hsr)).dFrom_eq_zero_iff i).1 ((h i).dFrom_eq_zero r hsr) j

/-- Degeneration at page `s` is invariant under isomorphisms of spectral sequences. -/
theorem degeneratesAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (s : ℤ) :
    E.DegeneratesAt s ↔ E'.DegeneratesAt s := by
  constructor <;> intro h <;> refine ⟨h.le, fun r hsr i j ↦ ?_⟩
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) i j).1 (h.d_eq_zero r hsr i j)
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) i j).2 (h.d_eq_zero r hsr i j)

end Degeneration

section BoundedSurvival

variable (E : SpectralSequence C c r₀)

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

end BoundedSurvival

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
  refine ⟨(E.pageXIsoOfStabilizesAt (E.stabilizesAt_of_forall_isZero le_rfl
    fun s hs pq' hpq' ↦ (h pq' ?_).resolve_left hpq) r hr).symm⟩
  exact hpq'.imp (fun hrel ↦ Abelian.SpectralObject.coreE₂Cohomological.hc s _ _ hrel hs)
    (fun hrel ↦ Abelian.SpectralObject.coreE₂Cohomological.hc s _ _ hrel hs)

end Cohomological

end CategoryTheory.SpectralSequence
