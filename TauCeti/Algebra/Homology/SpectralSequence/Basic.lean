/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Morphisms, isomorphisms, and rebased spectral sequences

The components of an isomorphism `e : E ≅ E'` of spectral sequences at each position of each page
are inverse to each other (`CategoryTheory.SpectralSequence.hom_inv_id_hom_f`,
`CategoryTheory.SpectralSequence.inv_hom_id_hom_f`). A morphism of spectral sequences also commutes
with the inverses of the isomorphisms between the homology of a page and the next page
(`CategoryTheory.SpectralSequence.Hom.hom_f_comp_iso_inv`).

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

/-- A morphism of spectral sequences commutes with the inverses of the isomorphisms between the
homology of a page and the next page: this is the inverse form of `Hom.comm`. -/
@[reassoc]
lemma Hom.hom_f_comp_iso_inv (f : E ⟶ E') (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia)
    (hr : r₀ ≤ r := by lia) :
    (f.hom r').f pq ≫ (E'.iso r r' pq hrr' hr).inv =
      (E.iso r r' pq hrr' hr).inv ≫ HomologicalComplex.homologyMap (f.hom r hr) pq := by
  rw [Iso.comp_inv_eq, Category.assoc, f.comm r r' pq hrr' hr, Iso.inv_hom_id_assoc]

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
  (rfl)

@[simp]
lemma fromPageMap_comp {E E' E'' : SpectralSequence C c r₀} (s : ℤ) (hs : r₀ ≤ s)
    (f : E ⟶ E') (g : E' ⟶ E'') :
    fromPageMap s hs (f ≫ g) = fromPageMap s hs f ≫ fromPageMap s hs g :=
  (rfl)

@[simp]
lemma fromPageMap_self {E E' : SpectralSequence C c r₀} (f : E ⟶ E') :
    fromPageMap r₀ le_rfl f = f :=
  (rfl)

@[simp]
lemma fromPageMap_fromPageMap {E E' : SpectralSequence C c r₀} {s t : ℤ}
    (hs : r₀ ≤ s) (hst : s ≤ t) (f : E ⟶ E') :
    fromPageMap t hst (fromPageMap s hs f) = fromPageMap t (hs.trans hst) f :=
  (rfl)

variable (C c r₀) in
/-- Restricting spectral sequences from page `r₀` to start on page `s ≥ r₀`, as a functor. -/
def fromPageFunctor (s : ℤ) (hs : r₀ ≤ s) : SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := fromPageMap s hs f

@[simp]
lemma fromPageFunctor_obj (s : ℤ) (hs : r₀ ≤ s) (E : SpectralSequence C c r₀) :
    (fromPageFunctor C c r₀ s hs).obj E = E.fromPage s hs :=
  (rfl)

@[simp]
lemma fromPageFunctor_map {E E' : SpectralSequence C c r₀} (s : ℤ) (hs : r₀ ≤ s) (f : E ⟶ E') :
    (fromPageFunctor C c r₀ s hs).map f =
      eqToHom (fromPageFunctor_obj s hs E) ≫ fromPageMap s hs f ≫
        eqToHom (fromPageFunctor_obj s hs E').symm := by
  change fromPageMap s hs f = eqToHom rfl ≫ fromPageMap s hs f ≫ eqToHom rfl
  simp

@[simp]
lemma fromPageFunctor_self :
    fromPageFunctor C c r₀ r₀ le_rfl = 𝟭 (SpectralSequence C c r₀) :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ f ↦ by
    change fromPageMap r₀ le_rfl f = eqToHom rfl ≫ f ≫ eqToHom rfl
    simp)

@[simp]
lemma fromPageFunctor_comp_fromPageFunctor {s t : ℤ} (hs : r₀ ≤ s) (hst : s ≤ t) :
    fromPageFunctor C c r₀ s hs ⋙ fromPageFunctor C c s t hst =
      fromPageFunctor C c r₀ t (hs.trans hst) :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ f ↦ by
    change fromPageMap t hst (fromPageMap s hs f) =
      eqToHom rfl ≫ fromPageMap t (hs.trans hst) f ≫ eqToHom rfl
    simp)

end FromPage

end CategoryTheory.SpectralSequence
