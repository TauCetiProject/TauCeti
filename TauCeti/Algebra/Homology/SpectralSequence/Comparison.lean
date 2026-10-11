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

* `CategoryTheory.SpectralSequence.Hom.isIso_hom_f_of_le`: a morphism of spectral sequences which
  is an isomorphism on every object of the `r`th page is an isomorphism on every object of every
  later page.
-/

public section

namespace CategoryTheory.SpectralSequence.Hom

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {E E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- A morphism of spectral sequences which is an isomorphism on every object of the `r`th page is
an isomorphism on every object of the `(r + 1)`st page. -/
lemma isIso_hom_f_succ (r : ℤ) (hr : r₀ ≤ r) (hr' : r₀ ≤ r + 1)
    (h : ∀ pq, IsIso ((f.hom r hr).f pq)) (pq : κ) :
    IsIso ((f.hom (r + 1) hr').f pq) := by
  have := HomologicalComplex.Hom.isIso_of_components (f.hom r hr)
  rw [(Iso.eq_inv_comp _).mpr (f.comm r (r + 1) pq rfl hr).symm]
  infer_instance

/-- A morphism of spectral sequences which is an isomorphism on every object of the `r`th page is
an isomorphism on every object of every page `r' ≥ r`. -/
lemma isIso_hom_f_of_le (r : ℤ) (hr : r₀ ≤ r) (h : ∀ pq, IsIso ((f.hom r hr).f pq))
    (r' : ℤ) (hrr' : r ≤ r') (pq : κ) :
    IsIso ((f.hom r' (hr.trans hrr')).f pq) := by
  induction r', hrr' using Int.leInduction generalizing pq with
  | base => exact h pq
  | succ r' hrr' ih => exact f.isIso_hom_f_succ r' (hr.trans hrr') _ ih pq

end CategoryTheory.SpectralSequence.Hom
