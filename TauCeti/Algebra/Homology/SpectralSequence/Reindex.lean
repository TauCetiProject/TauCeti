/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective

/-!
# Reindexing spectral sequences

A spectral sequence `E` with pages `E_r` indexed by `κ`, whose differentials on page `r` follow
the complex shape `c r`, can be read in other coordinates. Given a shift `d : ℤ` of the page
numbers and a bijection `f : κ' ≃ κ` of the index types which identifies the shape `c' r` with
`c (r + d)` for every `r`, the **reindexed spectral sequence** `E.reindex d f hf hd` has page `r`
equal to page `r + d` of `E`, with its object at `i : κ'` the object of `E` at `f i`
(`CategoryTheory.SpectralSequence.reindex_page_X`) and the same differentials
(`CategoryTheory.SpectralSequence.reindex_page_d`). Morphisms of spectral sequences are
reindexed componentwise (`CategoryTheory.SpectralSequence.reindexFunctor`).

This is how one spectral sequence is written in the indexing conventions of different sources:
for instance the spectral sequence of a filtered cochain complex, which Mathlib numbers so that
its first page is page `2` and its objects sit at bidegrees adapted to the spectral object it
comes from, is turned into the classical homological or cohomological `E₁` spectral sequence of
the filtration by an affine bijection of `ℤ × ℤ` and a page shift by `1`.

The pages are the restrictions of the pages of `E` along the embeddings of complex shapes defined
by `f` (`ComplexShape.Embedding.mk'`). These embeddings are surjective, so the comparison of the
homology of a page with the next page is `HomologicalComplex.restrictionHomologyIsoOfSurjective`
followed by that of `E`.

## Main definitions

* `CategoryTheory.SpectralSequence.reindex`: the reindexed spectral sequence.
* `CategoryTheory.SpectralSequence.reindexFunctor`: reindexing as a functor.
-/

public section

open CategoryTheory

namespace CategoryTheory.SpectralSequence

variable {C : Type*} [Category* C] [Abelian C] {κ κ' : Type*} {c : ℤ → ComplexShape κ}
  {c' : ℤ → ComplexShape κ'} {r₀ r₀' : ℤ} (d : ℤ) (f : κ' ≃ κ)
  (hf : ∀ r i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j)) (hd : r₀ ≤ r₀' + d)

/-- The **reindexed spectral sequence**: page `r` is page `r + d` of `E`, with its object at
`i : κ'` the object of `E` at `f i`. Here `f : κ' ≃ κ` identifies the complex shape `c' r` of the
`r`th page with the complex shape `c (r + d)` of the `(r + d)`th page of `E`. -/
@[expose]
noncomputable def reindex (E : SpectralSequence C c r₀) : SpectralSequence C c' r₀' where
  page r hr := (E.page (r + d)).restriction (ComplexShape.Embedding.mk' _ _ f f.injective (hf r))
  iso r r' j hrr' hr :=
    (E.page (r + d)).restrictionHomologyIsoOfSurjective _ f.surjective j (f j) rfl ≪≫
      E.iso (r + d) (r' + d) (f j)

variable (E : SpectralSequence C c r₀)

@[simp]
lemma reindex_page_X (r : ℤ) (hr : r₀' ≤ r) (j : κ') :
    ((E.reindex d f hf hd).page r hr).X j = (E.page (r + d)).X (f j) :=
  (rfl)

@[simp]
lemma reindex_page_d (r : ℤ) (hr : r₀' ≤ r) (i j : κ') :
    ((E.reindex d f hf hd).page r hr).d i j = (E.page (r + d)).d (f i) (f j) :=
  (rfl)

lemma reindex_iso (r r' : ℤ) (j : κ') (hrr' : r + 1 = r') (hr : r₀' ≤ r) :
    (E.reindex d f hf hd).iso r r' j hrr' hr =
      (E.page (r + d)).restrictionHomologyIsoOfSurjective
          (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)) f.surjective j (f j) rfl ≪≫
        E.iso (r + d) (r' + d) (f j) :=
  (rfl)

/-- The object at `j` of page `r` of the reindexed spectral sequence is the object at `f j` of
page `r + d` of `E`. -/
noncomputable def reindexPageXIso (r r' : ℤ) (hr : r₀' ≤ r) (hr' : r + d = r') (j : κ')
    (i : κ) (hj : f j = i) :
    ((E.reindex d f hf hd).page r hr).X j ≅ (E.page r').X i :=
  eqToIso (by subst hr' hj; rfl)

variable {E} {E' E'' : SpectralSequence C c r₀}

/-- The square expressing that the morphism of restricted pages induced by `φ` commutes with the
comparisons of the homology of a page with the next page of the reindexed spectral sequences. -/
lemma homologyMap_restrictionMap_comp_iso_hom (φ : E ⟶ E') (r r' : ℤ) (j : κ')
    (hrr' : r + 1 = r') (hr : r₀' ≤ r) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap (φ.hom (r + d))
        (ComplexShape.Embedding.mk' _ _ f f.injective (hf r))) j ≫
      ((E'.page (r + d)).restrictionHomologyIsoOfSurjective
          (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)) f.surjective j (f j) rfl ≪≫
        E'.iso (r + d) (r' + d) (f j)).hom =
    ((E.page (r + d)).restrictionHomologyIsoOfSurjective
          (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)) f.surjective j (f j) rfl ≪≫
        E.iso (r + d) (r' + d) (f j)).hom ≫ (φ.hom (r' + d)).f (f j) := by
  have := HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
    (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)) f.surjective (φ.hom (r + d)) j (f j) rfl
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, reassoc_of% this,
    φ.comm (r + d) (r' + d) (f j) (by lia) (by lia)]

/-- The morphism of reindexed spectral sequences induced by a morphism of spectral sequences. -/
@[expose]
noncomputable def reindexMap (φ : E ⟶ E') : E.reindex d f hf hd ⟶ E'.reindex d f hf hd where
  hom r hr := HomologicalComplex.restrictionMap (φ.hom (r + d))
    (ComplexShape.Embedding.mk' _ _ f f.injective (hf r))
  comm r r' j hrr' hr := homologyMap_restrictionMap_comp_iso_hom d f hf hd φ r r' j hrr' hr

@[simp]
lemma reindexMap_hom_f (φ : E ⟶ E') (r : ℤ) (hr : r₀' ≤ r) (j : κ') :
    ((reindexMap d f hf hd φ).hom r hr).f j = (φ.hom (r + d)).f (f j) :=
  (rfl)

variable (C c' r₀')

/-- Reindexing spectral sequences, as a functor. -/
@[expose, simps]
noncomputable def reindexFunctor : SpectralSequence C c r₀ ⥤ SpectralSequence C c' r₀' where
  obj E := E.reindex d f hf hd
  map φ := reindexMap d f hf hd φ

end CategoryTheory.SpectralSequence
