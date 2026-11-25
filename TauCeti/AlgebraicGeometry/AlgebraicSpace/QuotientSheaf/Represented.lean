/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf
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
* `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf.foldKernelPairIso`: the quotient sheaf of the
  kernel pair of the fold map `∐_{i : ι} U ⟶ U`, for a nonempty index type `ι`, is `h_U`.

## References

* [Stacks Project, Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {R U M : Scheme.{u}} {s t : R ⟶ U}

/-- The singleton sieve of an fppf covering morphism `q : U ⟶ M` covers `M` for the fppf
topology. -/
theorem generate_singleton_mem_fppfTopology (q : U ⟶ M) [Flat q] [LocallyOfFinitePresentation q]
    [Surjective q] : Sieve.generate (Presieve.singleton q) ∈ Scheme.fppfTopology M :=
  Precoverage.generate_mem_toGrothendieck q.singleton_mem_fppfPrecoverage

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
    (generate_singleton_mem_fppfTopology q)

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

/-- The projection onto the quotient sheaf of the kernel pair of `q`, followed by
`quotientSheaf.kernelPairIso q`, is the map `h_U ⟶ h_M` induced by `q`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_kernelPairIso_hom (q : U ⟶ M) [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology (pullback.snd q q)
        (pullback.fst q q) ≫ (quotientSheaf.kernelPairIso q).hom =
      Scheme.fppfTopology.uliftYoneda.{u + 1}.map q :=
  TauCeti.CategoryTheory.quotientSheaf.π_desc _ _

section Fold

variable (U) (ι : Type) [Nonempty ι]

/-- The fold map `∐_{i : ι} U ⟶ U` is locally of finite presentation. -/
instance locallyOfFinitePresentation_sigmaDesc_id :
    LocallyOfFinitePresentation (Sigma.desc fun _ : ι ↦ 𝟙 U) :=
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The fold map `∐_{i : ι} U ⟶ U` is surjective for a nonempty index type `ι`. -/
instance surjective_sigmaDesc_id : Surjective (Sigma.desc fun _ : ι ↦ 𝟙 U) :=
  Surjective.sigmaDesc_of_union_range_eq_univ <| by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨i, x, rfl⟩

/-- For a nonempty index type `ι`, the quotient sheaf of the kernel pair of the fold map
`∐_{i : ι} U ⟶ U` is `h_U` (for `ι` with two elements, `(U ⊔ U)/(fold kernel pair) ≅ h_U`, a
SchemeAndStackFoundations §1.6 Check). -/
noncomputable def quotientSheaf.foldKernelPairIso :
    quotientSheaf (pullback.snd (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U))
        (pullback.fst (Sigma.desc fun _ : ι ↦ 𝟙 U) (Sigma.desc fun _ : ι ↦ 𝟙 U)) ≅
      Scheme.fppfTopology.uliftYoneda.{u + 1}.obj U :=
  quotientSheaf.kernelPairIso _

end Fold

end TauCeti.AlgebraicGeometry.Spaces
