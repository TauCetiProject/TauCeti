/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Isomorphisms of spectral sequences

The components of an isomorphism `e : E ≅ E'` of spectral sequences at each position of each page
are inverse to each other (`CategoryTheory.SpectralSequence.hom_inv_id_hom_f`,
`CategoryTheory.SpectralSequence.inv_hom_id_hom_f`).
-/

public section

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {E E' : SpectralSequence C c r₀}

/-- The component of `e.hom` at `pq` on the page `r` followed by that of `e.inv` is the
identity. -/
@[reassoc (attr := simp)]
lemma hom_inv_id_hom_f (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (e.hom.hom r hr).f pq ≫ (e.inv.hom r hr).f pq = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, ← comp_hom _ _ r hr, e.hom_inv_id, id_hom,
    HomologicalComplex.id_f]

/-- The component of `e.inv` at `pq` on the page `r` followed by that of `e.hom` is the
identity. -/
@[reassoc (attr := simp)]
lemma inv_hom_id_hom_f (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (e.inv.hom r hr).f pq ≫ (e.hom.hom r hr).f pq = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, ← comp_hom _ _ r hr, e.inv_hom_id, id_hom,
    HomologicalComplex.id_f]

end CategoryTheory.SpectralSequence
