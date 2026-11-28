/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.CategoryTheory.Sites.QuotientSheaf.Represented

/-!
# Representable quotient sheaves of schemes

Let `s t : R ⟶ U` be a pre-relation of schemes and `q : U ⟶ M` an invariant morphism. If
`h_U ⟶ h_M` and `h_R ⟶ h_U ×_{h_M} h_U` are fppf locally surjective, then the quotient sheaf `U/R`
is the representable sheaf `h_M` (Stacks, Lemma 39.20.3 (03C5)). Since `Spaces.quotientSheaf` is
the general quotient sheaf at `J := Scheme.fppfTopology`, this isomorphism is
`TauCeti.CategoryTheory.quotientSheaf.isoOfIsLocallySurjective` applied directly.

The main instance is an fppf covering `q : U ⟶ M` (flat, locally of finite presentation and
surjective) with its kernel pair `R = U ×_M U`: then `h_R ⟶ h_U ×_{h_M} h_U` is an isomorphism and
`h_U ⟶ h_M` is fppf locally surjective, so `U/(U ×_M U) ≅ h_M`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf.kernelPairIso`: for an fppf covering
  `q : U ⟶ M`, the quotient sheaf of the kernel pair of `q` is `h_M`.
* `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf.sigmaDescIdKernelPairIso`: the quotient sheaf
  of the kernel pair of the fold map `∐_{i : ι} U ⟶ U`, for a nonempty index type `ι`, is `h_U`.

## References

* [Stacks Project, Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {R U M : Scheme.{u}} {s t : R ⟶ U}

/-- For an fppf covering `q : U ⟶ M` (flat, locally of finite presentation and surjective), the
factorisation of `q` through the quotient sheaf of its kernel pair `U ×_M U ⇉ U` is an
isomorphism. -/
instance quotientSheaf.isIso_desc_kernelPair (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    IsIso (TauCeti.CategoryTheory.quotientSheaf.desc
      (Scheme.fppfTopology.uliftYoneda.{u + 1}.map q)
      (TauCeti.CategoryTheory.quotientSheaf.uliftYoneda_map_condition
        (pullback.condition (f := q) (g := q)))) :=
  TauCeti.CategoryTheory.quotientSheaf.isIso_desc_kernelPair q
    (Precoverage.generate_mem_toGrothendieck q.singleton_mem_fppfPrecoverage)

/-- For an fppf covering `q : U ⟶ M` (flat, locally of finite presentation and surjective), the
quotient sheaf of the kernel pair `U ×_M U ⇉ U` is the representable sheaf `h_M`. -/
noncomputable def quotientSheaf.kernelPairIso (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    quotientSheaf (pullback.snd q q) (pullback.fst q q) ≅
      Scheme.fppfTopology.uliftYoneda.{u + 1}.obj M :=
  asIso (TauCeti.CategoryTheory.quotientSheaf.desc
    (Scheme.fppfTopology.uliftYoneda.{u + 1}.map q)
    (TauCeti.CategoryTheory.quotientSheaf.uliftYoneda_map_condition
      (pullback.condition (f := q) (g := q))))

/-- The forward map of `quotientSheaf.kernelPairIso q` is the factorisation of `h_U ⟶ h_M`
through the quotient sheaf of the kernel pair of `q`. -/
theorem quotientSheaf.kernelPairIso_hom (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    (quotientSheaf.kernelPairIso q).hom = TauCeti.CategoryTheory.quotientSheaf.desc
      (Scheme.fppfTopology.uliftYoneda.{u + 1}.map q)
      (TauCeti.CategoryTheory.quotientSheaf.uliftYoneda_map_condition
        (pullback.condition (f := q) (g := q))) :=
  (rfl)

/-- The projection onto the quotient sheaf of the kernel pair of `q`, followed by
`quotientSheaf.kernelPairIso q`, is the map `h_U ⟶ h_M` induced by `q`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_kernelPairIso_hom (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology (pullback.snd q q)
        (pullback.fst q q) ≫ (quotientSheaf.kernelPairIso q).hom =
      Scheme.fppfTopology.uliftYoneda.{u + 1}.map q :=
  TauCeti.CategoryTheory.quotientSheaf.π_desc _ _

/-- The map `h_U ⟶ h_M` induced by `q`, followed by the inverse of
`quotientSheaf.kernelPairIso q`, is the projection onto the quotient sheaf of the kernel pair. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_kernelPairIso_inv (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.map q ≫ (quotientSheaf.kernelPairIso q).inv =
      TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology (pullback.snd q q)
        (pullback.fst q q) :=
  (Iso.comp_inv_eq _).2 (quotientSheaf.π_kernelPairIso_hom q).symm

section Fold

variable (U) (ι : Type*) [Small.{u} ι] [Nonempty ι]

/-- For a nonempty index type `ι`, the quotient sheaf of the kernel pair of the fold map
`∐_{i : ι} U ⟶ U` is `h_U` (for `ι` with two elements, `(U ⊔ U)/(fold kernel pair) ≅ h_U`). -/
noncomputable def quotientSheaf.sigmaDescIdKernelPairIso :
    quotientSheaf (pullback.snd (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U))
        (pullback.fst (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U)) ≅
      Scheme.fppfTopology.uliftYoneda.{u + 1}.obj U :=
  quotientSheaf.kernelPairIso _

/-- The projection onto the quotient sheaf of the kernel pair of the fold map, followed by
`quotientSheaf.sigmaDescIdKernelPairIso U ι`, is the map `h_{∐ U} ⟶ h_U` induced by the fold
map. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_sigmaDescIdKernelPairIso_hom :
    TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology
        (pullback.snd (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U))
        (pullback.fst (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U)) ≫
        (quotientSheaf.sigmaDescIdKernelPairIso U ι).hom =
      Scheme.fppfTopology.uliftYoneda.{u + 1}.map (Sigma.desc fun _ : ι ↦ 𝟙 U) :=
  quotientSheaf.π_kernelPairIso_hom _

/-- The map `h_{∐ U} ⟶ h_U` induced by the fold map, followed by the inverse of
`quotientSheaf.sigmaDescIdKernelPairIso U ι`, is the projection onto the quotient sheaf of the
kernel pair of the fold map. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_sigmaDescIdKernelPairIso_inv :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.map (Sigma.desc fun _ : ι ↦ 𝟙 U) ≫
        (quotientSheaf.sigmaDescIdKernelPairIso U ι).inv =
      TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology
        (pullback.snd (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U))
        (pullback.fst (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U)) :=
  (Iso.comp_inv_eq _).2 (quotientSheaf.π_sigmaDescIdKernelPairIso_hom U ι).symm

end Fold

end TauCeti.AlgebraicGeometry.Spaces
