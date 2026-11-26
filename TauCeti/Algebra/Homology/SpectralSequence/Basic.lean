/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Isomorphisms and rebased spectral sequences

The components of an isomorphism `e : E ≅ E'` of spectral sequences at each position of each page
are inverse to each other (`CategoryTheory.SpectralSequence.hom_inv_id_hom_f`,
`CategoryTheory.SpectralSequence.inv_hom_id_hom_f`).

A spectral sequence `E` starting on page `r₀` can be restricted to start on any later page `s ≥ r₀`
(`CategoryTheory.SpectralSequence.fromPage`), preserving all pages and homology identifications from
`s` on, functorially (`CategoryTheory.SpectralSequence.fromPageFunctor`).
-/

public section

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Iso

variable {E E' : SpectralSequence C c r₀}

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

end Iso

section FromPage

/-- Restrict a spectral sequence starting on page `r₀` to start on a later page `s ≥ r₀`,
keeping all pages from `s` onward unchanged. -/
abbrev fromPage (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) : SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

@[simp]
lemma fromPage_page (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.fromPage s hs).page r hr = E.page r (hs.trans hr) :=
  (rfl)

@[simp]
lemma fromPage_iso (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) (r r' : ℤ) (pq : κ)
    (hrr' : r + 1 = r') (hr : s ≤ r) :
    (E.fromPage s hs).iso r r' pq hrr' hr = E.iso r r' pq hrr' (hs.trans hr) :=
  (rfl)

/-- The morphism between restricted spectral sequences induced by a morphism `f : E ⟶ E'`. -/
@[expose]
def fromPageMap {E E' : SpectralSequence C c r₀} (s : ℤ) (hs : r₀ ≤ s) (f : E ⟶ E') :
    E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
lemma fromPageMap_hom {E E' : SpectralSequence C c r₀} (s : ℤ) (hs : r₀ ≤ s) (f : E ⟶ E')
    (r : ℤ) (hr : s ≤ r) :
    (fromPageMap s hs f).hom r hr = f.hom r (hs.trans hr) :=
  (rfl)

@[simp]
lemma fromPageMap_id (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) :
    fromPageMap s hs (𝟙 E) = 𝟙 (E.fromPage s hs) :=
  rfl

@[simp]
lemma fromPageMap_comp {E E' E'' : SpectralSequence C c r₀} (s : ℤ) (hs : r₀ ≤ s)
    (f : E ⟶ E') (g : E' ⟶ E'') :
    fromPageMap s hs (f ≫ g) = fromPageMap s hs f ≫ fromPageMap s hs g :=
  rfl

variable (C c r₀) in
/-- Restricting spectral sequences from page `r₀` to start on page `s ≥ r₀`, as a functor. -/
@[expose, simps]
def fromPageFunctor (s : ℤ) (hs : r₀ ≤ s) : SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := fromPageMap s hs f

end FromPage

end CategoryTheory.SpectralSequence
