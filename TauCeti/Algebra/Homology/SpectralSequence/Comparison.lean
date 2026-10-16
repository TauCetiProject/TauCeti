/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Comparison of spectral sequences on later pages

A morphism `f : E ⟶ E'` of spectral sequences commutes with the identifications of the homology
of a page with the next page. Hence if `f` is an isomorphism on every object of the `r`th page,
it is an isomorphism on the homology of the `r`th page, so on every object of the `(r + 1)`st
page, and, by induction, on every object of every page `r' ≥ r`.

## Main results

* `CategoryTheory.SpectralSequence.Hom.isIso_hom_f_of_le`: the comparison on later pages.
-/

public section

namespace CategoryTheory.SpectralSequence.Hom

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {E E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- A morphism of spectral sequences which is an isomorphism on every object of the `r`th page is
an isomorphism on every object of every page `r' ≥ r`. -/
lemma isIso_hom_f_of_le (r : ℤ) (hr : r₀ ≤ r) (h : ∀ pq, IsIso ((f.hom r hr).f pq))
    (r' : ℤ) (hrr' : r ≤ r') (pq : κ) :
    IsIso ((f.hom r' (hr.trans hrr')).f pq) := by
  induction r', hrr' using Int.leInduction generalizing pq with
  | base => exact h pq
  | succ r' hrr' ih =>
    have := HomologicalComplex.Hom.isIso_of_components (f.hom r' (hr.trans hrr'))
    rw [(Iso.eq_inv_comp _).mpr (f.comm r' (r' + 1) pq rfl (hr.trans hrr')).symm]
    infer_instance

end CategoryTheory.SpectralSequence.Hom
