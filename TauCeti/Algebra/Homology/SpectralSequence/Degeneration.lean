/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.SerreClass
public import TauCeti.Algebra.Homology.SpectralSequence.Tower

/-!
# Vanishing and survival of objects on later pages of a spectral sequence

Each page of a spectral sequence is the homology of the previous one, so its objects are
subquotients of the objects of every earlier page. Hence an object which vanishes on some page
vanishes on every later page (`CategoryTheory.SpectralSequence.isZero_page_X_of_le`).

Conversely, suppose that on the page `r` every object joined to the position `pq` by a
differential of some later page vanishes. Then on every later page both differentials at `pq`
vanish, because their other ends are already zero, so `E` stabilises at `pq` from page `r`
(`CategoryTheory.SpectralSequence.stabilisesAt_of_forall_isZero`), and
`CategoryTheory.SpectralSequence.pageXIsoOfStabilises` identifies the object at `pq` across all
pages `r' ≥ r`. This is how sparseness of an early page, for instance a lacunary pattern of
nonzero total degrees, makes a spectral sequence degenerate: all differentials from the page `r`
on vanish (`CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`).

## Main results

* `CategoryTheory.SpectralSequence.isZero_page_X_of_le`: a zero object stays zero on later pages.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`: a differential of a later page between
  positions one of which is zero on an earlier page vanishes.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_forall_isZero`: the differentials at a
  position whose neighbours vanish are zero on all later pages.
* `CategoryTheory.SpectralSequence.stabilisesAt_of_forall_isZero`: an object whose neighbours
  vanish stabilises from page `r`.

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

/-- **Objects with vanishing neighbours stabilise.** Suppose that on the page `r` every object
joined to the position `pq` by a differential of some page `s ≥ r` is zero. Then `E` stabilises
at `pq` from page `r` (`CategoryTheory.SpectralSequence.StabilisesAt`), so
`CategoryTheory.SpectralSequence.pageXIsoOfStabilises` identifies `(E.page r).X pq` with
`(E.page r').X pq` for every `r' ≥ r`. -/
lemma stabilisesAt_of_forall_isZero {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq')) :
    E.StabilisesAt pq r hr :=
  (E.stabilisesAt_iff_forall_d_eq_zero pq r hr).mpr fun s hrs _pq' ↦
    ⟨E.page_d_eq_zero_of_forall_isZero hr h s hrs (Or.inl rfl),
     E.page_d_eq_zero_of_forall_isZero hr h s hrs (Or.inr rfl)⟩

end CategoryTheory.SpectralSequence
