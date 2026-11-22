/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.SerreClass

/-!
# Vanishing and survival of objects on later pages of a spectral sequence

Each page of a spectral sequence is the homology of the previous one, so its objects are
subquotients of the objects of every earlier page. Hence an object which vanishes on some page
vanishes on every later page (`CategoryTheory.SpectralSequence.isZero_page_X_of_le`).

Conversely, when a spectral sequence stabilizes at a position `pq` from a page `s`
(`CategoryTheory.SpectralSequence.StabilizesAt`), meaning that every differential leaving or
entering `pq` on pages `r ≥ s` vanishes, the object at `pq` is its own homology at each step
(`CategoryTheory.SpectralSequence.pageXStepIso`) and survives unchanged to every later page `r ≥ s`
(`CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt`). In particular, if on the page `r`
every object joined to `pq` by a differential of some later page vanishes, then the spectral
sequence stabilizes at `pq` from page `r`
(`CategoryTheory.SpectralSequence.stabilizesAt_of_forall_isZero`). This is how sparseness of an
early page, for instance a lacunary pattern of nonzero total degrees, makes a spectral sequence
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
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero`: the differentials at a
  position whose neighbours vanish are zero on all later pages.
* `CategoryTheory.SpectralSequence.StabilizesAt`,
  `CategoryTheory.SpectralSequence.pageXStepIso`, and
  `CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt`: canonical survival isomorphisms at a
  stabilizing position, with `CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt_self` and
  `CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt_add_one`.
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

/-- **Differentials at a position with vanishing neighbours vanish.** Suppose that on the page `r`
every object joined to the position `pq` by a differential of some page `s ≥ r` is zero. Then on
every page `s ≥ r` both differentials at `pq` vanish: either their other end is zero, or the shape
forbids them. -/
lemma page_d_eq_zero_of_forall_isZero {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    (s : ℤ) (hrs : r ≤ s) {i j : κ} (hij : i = pq ∨ j = pq) :
    (E.page s (hr.trans hrs)).d i j = 0 := by
  by_cases hrel : (c s).Rel i j
  · rcases hij with rfl | rfl
    · exact E.page_d_eq_zero_of_le hr (Or.inr (h s hrs j (Or.inl hrel))) s hrs
    · exact E.page_d_eq_zero_of_le hr (Or.inl (h s hrs i (Or.inr hrel))) s hrs
  · exact (E.page s (hr.trans hrs)).shape i j hrel

/-- A spectral sequence `E` **stabilizes at `pq` from page `s`** (`s ≥ r₀`) if on every page
`r ≥ s`, both the differential leaving `pq` and the differential entering `pq` vanish. -/
structure StabilizesAt (pq : κ) (s : ℤ) : Prop where
  /-- The stabilization page `s` is at least the starting page `r₀`. -/
  le : r₀ ≤ s
  /-- Every differential leaving `pq` on pages `r ≥ s` vanishes. -/
  dFrom_eq_zero : ∀ r (hsr : s ≤ r), (E.page r (le.trans hsr)).dFrom pq = 0
  /-- Every differential entering `pq` on pages `r ≥ s` vanishes. -/
  dTo_eq_zero : ∀ r (hsr : s ≤ r), (E.page r (le.trans hsr)).dTo pq = 0

lemma StabilizesAt.mono {E : SpectralSequence C c r₀} {pq : κ} {s s' : ℤ}
    (h : E.StabilizesAt pq s) (hss' : s ≤ s') : E.StabilizesAt pq s' where
  le := h.le.trans hss'
  dFrom_eq_zero r hs'r := h.dFrom_eq_zero r (hss'.trans hs'r)
  dTo_eq_zero r hs'r := h.dTo_eq_zero r (hss'.trans hs'r)

/-- If the object at `pq` vanishes on page `s`, then `E` stabilizes at `pq` from page `s`. -/
lemma stabilizesAt_of_isZero_page_X {s : ℤ} (hs : r₀ ≤ s) {pq : κ}
    (h : IsZero ((E.page s hs).X pq)) : E.StabilizesAt pq s :=
  ⟨hs, fun r hsr ↦ E.page_d_eq_zero_of_le hs (Or.inl h) r hsr,
    fun r hsr ↦ E.page_d_eq_zero_of_le hs (Or.inr h) r hsr⟩

/-- If on page `s` every object joined to `pq` by a differential of some page `r ≥ s` vanishes,
then `E` stabilizes at `pq` from page `s`. -/
lemma stabilizesAt_of_forall_isZero {s : ℤ} (hs : r₀ ≤ s) {pq : κ}
    (h : ∀ r, s ≤ r → ∀ pq', (c r).Rel pq pq' ∨ (c r).Rel pq' pq → IsZero ((E.page s hs).X pq')) :
    E.StabilizesAt pq s :=
  ⟨hs, fun r hsr ↦ E.page_d_eq_zero_of_forall_isZero hs h r hsr (Or.inl rfl),
    fun r hsr ↦ E.page_d_eq_zero_of_forall_isZero hs h r hsr (Or.inr rfl)⟩

/-- The canonical one-step isomorphism `(E.page r hr).X pq ≅ (E.page (r + 1) _).X pq` when both
the entering and leaving differentials at `pq` on page `r` vanish. -/
noncomputable def pageXStepIso (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hdTo : (E.page r hr).dTo pq = 0) (hdFrom : (E.page r hr).dFrom pq = 0) :
    (E.page r hr).X pq ≅ (E.page (r + 1) (Int.le_add_one hr)).X pq :=
  (E.page r hr).XIsoHomologyOfDEqZero pq hdTo hdFrom ≪≫ E.iso r (r + 1) pq rfl hr

@[reassoc, simp]
lemma pageXStepIso_hom (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hdTo : (E.page r hr).dTo pq = 0) (hdFrom : (E.page r hr).dFrom pq = 0) :
    (E.pageXStepIso pq r hr hdTo hdFrom).hom =
      ((E.page r hr).XIsoHomologyOfDEqZero pq hdTo hdFrom).hom ≫
        (E.iso r (r + 1) pq rfl hr).hom :=
  by simp [pageXStepIso]

/-- **Canonical stabilization isomorphism.** If `E` stabilizes at `pq` from page `s`, then the
composites of the homology isomorphisms yield canonical isomorphisms
`(E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq` for all `r ≥ s`. -/
noncomputable def pageXIsoOfStabilizesAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    (E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq :=
  Int.leInduction
    (motive := fun r hsr ↦ (E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq)
    (Iso.refl _)
    (fun r hsr e ↦
      e ≪≫ E.pageXStepIso pq r (h.le.trans hsr) (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr))
    r hsr

@[simp]
lemma pageXIsoOfStabilizesAt_self {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) :
    E.pageXIsoOfStabilizesAt h s le_rfl = Iso.refl _ :=
  Int.leInduction_base _ _

lemma pageXIsoOfStabilizesAt_add_one {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.pageXIsoOfStabilizesAt h (r + 1) (Int.le_add_one hsr) =
      E.pageXIsoOfStabilizesAt h r hsr ≪≫
        E.pageXStepIso pq r (h.le.trans hsr) (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr) :=
  Int.leInduction_add_one _ _ r hsr

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
