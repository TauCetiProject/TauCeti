/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import TauCeti.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# The hypercohomology spectral sequence of a homological functor

Let `X` be an object of the derived category `D(C)` of an abelian category, and let
`H : D(C) ⥤ A` be a homological functor to an abelian category, with its shift sequence
`n ↦ H.shift n`. The spectral object `(t.spectralObject X).mapHomologicalFunctor H` of the
truncations of `X` for the canonical t-structure (see
`TauCeti.CategoryTheory.Triangulated.TStructure.SpectralObject`) has the `E₂` spectral sequence

`E₂^{p,q} = (H.shift p).obj (Hᵠ(X)[0]) ⇒ (H.shift (p + q)).obj X`,

where `Hᵠ(X)[0]` is the `q`th cohomology object of `X` placed in degree `0`
(`DerivedCategory.spectralSequenceFirstPageXIso`): the truncation `τ_{≥q} τ_{<q+1} X` is
`Hᵠ(X)` placed in degree `q` (`DerivedCategory.truncGETruncLTIsoSingleFunctor`), which is the
shift by `-q` of `Hᵠ(X)[0]`. For `H = Hom(Z, -)` the object `(H.shift p).obj (M[0])` is
`Hom(Z, M[p])`, that is `Extᵖ(Z, M)` when `Z` is an object of `C` placed in degree `0`, and the
spectral sequence is the hypercohomology spectral sequence `Extᵖ(Z, Hᵠ(X)) ⇒ Ext^{p+q}(Z, X)`.
When `X` is `≥ 0` and `H` vanishes on the objects `≥ 1`, as for `Hom(Z, -)` with `Z` in degree
`0`, the spectral object is first quadrant
(`CategoryTheory.Triangulated.TStructure.isFirstQuadrant_mapHomologicalFunctor_spectralObject`), so
that the filtration of the abutment `(H.shift n).obj X` is finite and the pages stabilize to its
graded pieces.

## Main definitions and results

* `DerivedCategory.spectralSequenceFirstPageXIso`: the objects of the first page, and
  `DerivedCategory.spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom`: their
  naturality in `X`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.7, for the hypercohomology spectral sequence `(Rᵖ F)(Hᵠ(K)) ⇒ R^{p+q} F(K)`.
* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
-/

public section

open CategoryTheory Triangulated Abelian.SpectralObject

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {A : Type*} [Category* A] [Abelian A] (H : DerivedCategory C ⥤ A) [H.IsHomological]
  [H.ShiftSequence ℤ] (X : DerivedCategory C)

/-- The object at `(p, q)` on the first page (numbered `2`) of the spectral sequence of the
truncations of `X` under a homological functor `H` is `(H.shift p).obj (Hᵠ(X)[0])`, the value of
`H.shift p` on the `q`th cohomology of `X` placed in degree `0`. -/
noncomputable def spectralSequenceFirstPageXIso (p q : ℤ) :
    ((((TStructure.t.spectralObject X).mapHomologicalFunctor H).spectralSequence
      coreE₂Cohomological).page 2).X ⟨p, q⟩ ≅
      (H.shift p).obj ((singleFunctor C 0).obj ((homologyFunctor C q).obj X)) :=
  ((TStructure.t.spectralObject X).mapHomologicalFunctor H).spectralSequenceFirstPageXIso
      coreE₂Cohomological (⟨p, q⟩ : ℤ × ℤ) q (q + 1 : ℤ) rfl rfl (p + q) rfl ≪≫
    (H.shift (p + q)).mapIso (truncGETruncLTIsoSingleFunctor X q) ≪≫
    (H.shift (p + q)).mapIso (((singleFunctors C).shiftIso (-q) q 0 (by lia)).app _).symm ≪≫
    (H.shiftIso (-q) (p + q) p (by lia)).app _

/-- The identification `spectralSequenceFirstPageXIso` of the first page is natural in `X`: the
morphism of spectral sequences induced by `f : X ⟶ X'` is, at `(p, q)`, the value of `H.shift p`
on the map `Hᵠ(f)` placed in degree `0`. -/
@[reassoc]
lemma spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom {X X' : DerivedCategory C}
    (f : X ⟶ X') (p q : ℤ) :
    spectralSequencePageXMap coreE₂Cohomological
        ((Triangulated.SpectralObject.mapHomologicalFunctorFunctor H EInt).map
          (TStructure.t.spectralObjectFunctor.map f)) 2 le_rfl ⟨p, q⟩ ≫
        (spectralSequenceFirstPageXIso H X' p q).hom =
      (spectralSequenceFirstPageXIso H X p q).hom ≫
        (H.shift p).map ((singleFunctor C 0).map ((homologyFunctor C q).map f)) := by
  simp only [spectralSequenceFirstPageXIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [Abelian.SpectralObject.spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom_assoc
    (X := (TStructure.t.spectralObject X).mapHomologicalFunctor H)
    (Y := (TStructure.t.spectralObject X').mapHomologicalFunctor H)]
  congr 1
  -- The component of the morphism of spectral objects induced by `f` on `H^{p+q}(q ≤ q + 1)` is
  -- the value of `H.shift (p + q)` on the map induced on `τ_{≥q} τ_{<q+1}`.
  dsimp
  rw [← Functor.map_comp_assoc, truncGETruncLTIsoSingleFunctor_hom_naturality,
    Functor.map_comp_assoc]
  congr 1
  rw [← Functor.map_comp_assoc, NatTrans.naturality, Functor.map_comp_assoc]
  congr 1
  exact H.shiftIso_hom_naturality _ _ _ _ _

end DerivedCategory
