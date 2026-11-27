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
(`CategoryTheory.SpectralSequence.reindex_page_d`; read through the identifications
`CategoryTheory.SpectralSequence.reindexPageXIso` of the objects, this is
`CategoryTheory.SpectralSequence.reindex_page_d_eq`). Morphisms of spectral sequences are
reindexed componentwise (`CategoryTheory.SpectralSequence.reindexFunctor`).

This is how one spectral sequence is written in the indexing conventions of different sources:
for instance the spectral sequence of a filtered cochain complex, which Mathlib numbers so that
its first page is page `2` and its objects sit at bidegrees adapted to the spectral object it
comes from, is turned into the classical homological or cohomological `E₁` spectral sequence of
the filtration by an affine bijection of `ℤ × ℤ` and a page shift by `1`.

The pages are the restrictions of the pages of `E` along the embeddings of complex shapes defined
by `f` (`ComplexShape.Embedding.mk'`). These embeddings are surjective, so the comparison of the
homology of a page with the next page is `HomologicalComplex.restrictionHomologyIsoOfSurjective`
followed by that of `E`; on cycles, it sends the class of a cycle at `j` to the class of the same
cycle at `f j` (`CategoryTheory.SpectralSequence.liftCycles_homologyπ_reindex_iso_hom`).

## Main definitions

* `CategoryTheory.SpectralSequence.reindex`: the reindexed spectral sequence.
* `CategoryTheory.SpectralSequence.reindexFunctor`: reindexing as a functor.

A page shift `d` with `r₀ ≤ r₀' + d` may also drop pages: for `d = 0` and `f` the identity,
`E.reindex 0 (Equiv.refl κ) _ hd` keeps the pages `r ≥ r₀'` of `E`. The induced morphisms only see
those pages (`CategoryTheory.SpectralSequence.reindexMap_congr`), so morphisms of spectral sequences
that agree from page `r₀'` on are identified.
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

/-- Under the identifications `CategoryTheory.SpectralSequence.reindexPageXIso` of its objects, the
differentials of the reindexed spectral sequence are those of `E`. -/
lemma reindex_page_d_eq (r r' : ℤ) (hr : r₀' ≤ r) (hr' : r + d = r') (i j : κ') (a b : κ)
    (ha : f i = a) (hb : f j = b) :
    ((E.reindex d f hf hd).page r hr).d i j =
      (E.reindexPageXIso d f hf hd r r' hr hr' i a ha).hom ≫ (E.page r').d a b ≫
        (E.reindexPageXIso d f hf hd r r' hr hr' j b hb).inv := by
  subst hr' ha hb
  rw [reindexPageXIso, reindexPageXIso, eqToIso.hom, eqToIso.inv]
  exact (conj_eqToHom_iff_heq' _ _ _ _).2 .rfl

/-- At the page `r + d` of `E` and the index `f j`, the identification `reindexPageXIso` of the
object at `j` of page `r` of the reindexed spectral sequence is the identity. -/
@[simp]
lemma reindexPageXIso_hom_self (r : ℤ) (hr : r₀' ≤ r) (j : κ') :
    (E.reindexPageXIso d f hf hd r (r + d) hr rfl j (f j) rfl).hom = 𝟙 _ := by
  rw [reindexPageXIso, eqToIso.hom]
  exact eqToHom_refl _ _

/-- The computation of `liftCycles_homologyπ_reindex_iso_hom` on the pages `r + d` and `r' + d`
of `E`, at the index `f j`, where the identifications `reindexPageXIso` are identities. -/
@[reassoc]
private lemma liftCycles_homologyπ_reindex_iso_hom_aux {A : C} (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀' ≤ r) (j k : κ') (hk : (c' r).next j = k) (x : A ⟶ (E.page (r + d)).X (f j))
    (hx : x ≫ ((E.reindex d f hf hd).page r hr).d j k = 0) :
    ((E.reindex d f hf hd).page r hr).liftCycles x k hk hx ≫
        ((E.reindex d f hf hd).page r hr).homologyπ j ≫
        ((E.reindex d f hf hd).iso r r' j hrr' hr).hom =
      (E.page (r + d)).liftCycles x (f k)
          (by rw [← hk]
              exact (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)).next_f_of_surjective
                f.surjective j) hx ≫
        (E.page (r + d)).homologyπ (f j) ≫ (E.iso (r + d) (r' + d) (f j)).hom := by
  rw [reindex_iso, Iso.trans_hom]
  -- The pages of the reindexed spectral sequence are the restrictions of the pages of `E`.
  exact (HomologicalComplex.liftCycles_homologyπ_restrictionHomologyIsoOfSurjective_hom_assoc
    (ComplexShape.Embedding.mk' _ _ f f.injective (hf r)) f.surjective (E.page (r + d)) j (f j)
    rfl x k hk hx _).trans
      (by
        simp [HomologicalComplex.restrictionXIso]
        -- The two sides differ only in the proofs that `x` is a cycle: one is stated with the
        -- differential of the restriction, the other with that of `E.page (r + d)`, and these
        -- agree by definition of `HomologicalComplex.restriction` (`reindex_page_d`).
        rfl)

/-- On cycles, the identification of the homology of page `r` of the reindexed spectral sequence
with page `r'` is that of `E` on pages `s = r + d` and `s' = r' + d`: through the identifications
`reindexPageXIso` of the objects, the class of a cycle `x` at `j` is sent to the image of the class
of the same cycle at `i = f j`. -/
@[reassoc]
lemma liftCycles_homologyπ_reindex_iso_hom {A : C} (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀' ≤ r) (s s' : ℤ) (hs : r + d = s) (hs' : r' + d = s') (j k : κ') (i l : κ)
    (hk : (c' r).next j = k) (hi : f j = i) (hl : (c s).next i = l)
    (x : A ⟶ ((E.reindex d f hf hd).page r hr).X j)
    (hx : x ≫ ((E.reindex d f hf hd).page r hr).d j k = 0) :
    ((E.reindex d f hf hd).page r hr).liftCycles x k hk hx ≫
        ((E.reindex d f hf hd).page r hr).homologyπ j ≫
        ((E.reindex d f hf hd).iso r r' j hrr' hr).hom ≫
        (E.reindexPageXIso d f hf hd r' s' (by lia) hs' j i hi).hom =
      (E.page s).liftCycles (x ≫ (E.reindexPageXIso d f hf hd r s hr hs j i hi).hom) l hl
          (by
            have hkl : f k = l := by
              rw [← hl, ← hk, ← hi, ← hs]
              exact ((ComplexShape.Embedding.mk' _ _ f f.injective (hf r)).next_f_of_surjective
                f.surjective j).symm
            rw [Category.assoc, ← cancel_mono (E.reindexPageXIso d f hf hd r s hr hs k l hkl).inv,
              Category.assoc, Category.assoc, Limits.zero_comp,
              ← E.reindex_page_d_eq d f hf hd r s hr hs j k i l hi hkl, hx]) ≫
        (E.page s).homologyπ i ≫ (E.iso s s' i (by lia) (by lia)).hom := by
  subst hs hs' hi hl
  rw [liftCycles_homologyπ_reindex_iso_hom_aux_assoc d f hf hd E r r' hrr' hr j k hk x hx]
  -- With these indices, the identifications `reindexPageXIso` are identities by definition.
  rw [reindexPageXIso_hom_self]
  refine (Category.comp_id _).trans ?_
  congr 1
  rw [← cancel_mono ((E.page (r + d)).iCycles (f j)), HomologicalComplex.liftCycles_i,
    reindexPageXIso_hom_self]
  exact (HomologicalComplex.liftCycles_i _ _ _ _ _).trans (Category.comp_id x).symm

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
noncomputable def reindexMap (φ : E ⟶ E') : E.reindex d f hf hd ⟶ E'.reindex d f hf hd where
  hom r hr := HomologicalComplex.restrictionMap (φ.hom (r + d))
    (ComplexShape.Embedding.mk' _ _ f f.injective (hf r))
  comm r r' j hrr' hr := homologyMap_restrictionMap_comp_iso_hom d f hf hd φ r r' j hrr' hr

@[simp]
lemma reindexMap_hom_f (φ : E ⟶ E') (r : ℤ) (hr : r₀' ≤ r) (j : κ') :
    ((reindexMap d f hf hd φ).hom r hr).f j = (φ.hom (r + d)).f (f j) :=
  (rfl)

/-- Under the identifications `CategoryTheory.SpectralSequence.reindexPageXIso` of its objects, the
morphism of reindexed spectral sequences induced by `φ` is `φ` itself. -/
@[reassoc]
lemma reindexMap_hom_f_comp_reindexPageXIso_hom (φ : E ⟶ E') (r r' : ℤ) (hr : r₀' ≤ r)
    (hr' : r + d = r') (j : κ') (i : κ) (hj : f j = i) :
    ((reindexMap d f hf hd φ).hom r hr).f j ≫
        (E'.reindexPageXIso d f hf hd r r' hr hr' j i hj).hom =
      (E.reindexPageXIso d f hf hd r r' hr hr' j i hj).hom ≫ (φ.hom r' (by lia)).f i := by
  subst hr' hj
  -- Both identifications are `eqToHom` of an equality of definitionally equal objects.
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The morphism of reindexed spectral sequences induced by `φ` only depends on the pages `r + d`
of `φ` with `r₀' ≤ r`, the pages that the reindexed spectral sequences keep. -/
lemma reindexMap_congr {φ φ' : E ⟶ E'} (h : ∀ r (hr : r₀' ≤ r), φ.hom (r + d) = φ'.hom (r + d)) :
    reindexMap d f hf hd φ = reindexMap d f hf hd φ' := by
  ext r hr j
  rw [reindexMap_hom_f, reindexMap_hom_f, h r hr]

/-- Reindexing the identity morphism gives the identity morphism. -/
@[simp]
lemma reindexMap_id : reindexMap d f hf hd (𝟙 E) = 𝟙 _ :=
  (rfl)

/-- Reindexing a composite of morphisms gives the composite of the reindexed morphisms. -/
@[simp, reassoc]
lemma reindexMap_comp (φ : E ⟶ E') (ψ : E' ⟶ E'') :
    reindexMap d f hf hd (φ ≫ ψ) = reindexMap d f hf hd φ ≫ reindexMap d f hf hd ψ :=
  (rfl)

variable (C c' r₀')

/-- Reindexing spectral sequences, as a functor. -/
@[expose, simps]
noncomputable def reindexFunctor : SpectralSequence C c r₀ ⥤ SpectralSequence C c' r₀' where
  obj E := E.reindex d f hf hd
  map φ := reindexMap d f hf hd φ

end CategoryTheory.SpectralSequence
