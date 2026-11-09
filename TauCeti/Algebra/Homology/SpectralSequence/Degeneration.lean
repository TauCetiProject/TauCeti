/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Vanishing and survival of objects on later pages of a spectral sequence

Each page of a spectral sequence is the homology of the previous one, so its objects are
subquotients of the objects of every earlier page. Hence an object which vanishes on some page
vanishes on every later page (`CategoryTheory.SpectralSequence.isZero_page_X_of_le`).

Conversely, suppose that on the page `r` every object joined to the position `pq` by a
differential of some later page vanishes. Then on every later page both differentials at `pq`
vanish, because their other ends are already zero, so the object at `pq` is its own homology and
survives unchanged to every page `r' ≥ r`
(`CategoryTheory.SpectralSequence.nonempty_page_X_iso_of_le`). This is how sparseness of an early
page, for instance two nonzero rows far apart or a lacunary pattern of nonzero total degrees,
makes a spectral sequence degenerate: all differentials from the page `r` on vanish
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`).

## Main results

* `CategoryTheory.SpectralSequence.isZero_page_X_of_le`: a zero object stays zero on later pages.
* `CategoryTheory.SpectralSequence.page_d_eq_zero_of_le`: a differential of a later page between
  positions one of which is zero on an earlier page vanishes.
* `CategoryTheory.SpectralSequence.nonempty_page_X_iso_of_le`: an object whose neighbours vanish
  survives unchanged to all later pages.

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
every later page `r' ≥ r`, since each page is the homology of the previous one. -/
lemma isZero_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (h : IsZero ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r') : IsZero ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ r' hrr' ih =>
    exact (E.iso r' (r' + 1) pq rfl (hr.trans hrr')).isZero_iff.1
      (((E.page r' (hr.trans hrr')).sc pq).isZero_homology_of_isZero_X₂ ih)

/-- **Differentials into or out of zero objects vanish on later pages.** If the source or the
target of a differential of the page `r' ≥ r` is zero on the page `r`, the differential is zero. -/
lemma page_d_eq_zero_of_le {r : ℤ} (hr : r₀ ≤ r) {pq pq' : κ}
    (h : IsZero ((E.page r).X pq) ∨ IsZero ((E.page r).X pq')) (r' : ℤ) (hrr' : r ≤ r') :
    (E.page r' (hr.trans hrr')).d pq pq' = 0 := by
  rcases h with h | h
  · exact (E.isZero_page_X_of_le hr h r' hrr').eq_of_src _ _
  · exact (E.isZero_page_X_of_le hr h r' hrr').eq_of_tgt _ _

/-- **Objects with vanishing neighbours survive.** Suppose that on the page `r` every object
joined to the position `pq` by a differential of some page `s ≥ r` is zero. Then the object at
`pq` on every later page `r' ≥ r` is isomorphic to the object at `pq` on the page `r`: on each
page in between, both differentials at `pq` vanish, so the object is its own homology. -/
lemma nonempty_page_X_iso_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : ∀ s, r ≤ s → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → IsZero ((E.page r).X pq'))
    (r' : ℤ) (hrr' : r ≤ r') : Nonempty ((E.page r' (hr.trans hrr')).X pq ≅ (E.page r).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact ⟨Iso.refl _⟩
  | succ s hrs ih =>
    obtain ⟨e⟩ := ih
    let K := E.page s (hr.trans hrs)
    -- Both differentials at `pq` vanish: either their other end is zero, or the shape forbids
    -- them.
    have hd {i j : κ} (hij : i = pq ∨ j = pq) : K.d i j = 0 := by
      by_cases hrel : (c s).Rel i j
      · rcases hij with rfl | rfl
        · exact E.page_d_eq_zero_of_le hr (Or.inr (h s hrs j (Or.inl hrel))) s hrs
        · exact E.page_d_eq_zero_of_le hr (Or.inl (h s hrs i (Or.inr hrel))) s hrs
      · exact K.shape i j hrel
    exact ⟨(E.iso s (s + 1) pq rfl (hr.trans hrs)).symm ≪≫
      (K.isoHomologyπ _ pq rfl (hd (Or.inr rfl))).symm ≪≫
        K.iCyclesIso pq _ rfl (hd (Or.inl rfl)) ≪≫ e⟩

end CategoryTheory.SpectralSequence
