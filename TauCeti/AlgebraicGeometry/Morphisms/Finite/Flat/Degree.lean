/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# The rank of a finite flat morphism is the degree of its function-field extension

For a finite flat affine morphism with integral target, the rank at every target point equals
the dimension after passing to compatible fraction rings. When the source is also integral,
these fraction rings are fields, and the dimension is the function-field extension degree.

Globally, let `f : X ⟶ Y` be a finite flat dominant morphism of integral schemes, and
`f^* : K(Y) ⟶ K(X)` its pullback of rational functions
(`AlgebraicGeometry.Scheme.Hom.functionFieldMap`). Then the rank of `f` at every point of `Y` is
the degree `[K(X) : f^* K(Y)]`. In particular the rank is constant, with no noetherian or finite
presentation hypothesis. For instance, a finite dominant morphism from an integral scheme to an
integral curve smooth over a field is flat
(`AlgebraicGeometry.Scheme.Hom.flat_of_isDominant_of_smooth`), so its constant fibre length is
the degree of its function-field extension.

The local rank is Mathlib's `Scheme.Hom.finrank`. Its affine formula reduces the result to
Mathlib's fibre-rank calculation for finite flat modules and the invariance of dimension under
passage to fraction rings. The global statement restricts `f` over an affine open of `Y`, whose
preimage is affine because `f` is finite. Both coordinate rings are domains whose fraction
fields are the function fields, and `f^*` extends the map of coordinate rings.

The degree is stated as the dimension of `K(X)` over the subfield `f^* K(Y)`, as for the degree
of an isogeny of Weierstrass curves (`TauCeti.Isogeny.degree`). This avoids putting an algebra
structure on `K(X)` over `K(Y)`, which would clash with `Algebra.id` for an endomorphism.

## Main results

* `TauCeti.AlgebraicGeometry.finrank_SpecMap_eq_finrank_fractionRing`: the affine statement, for
  any compatible fraction rings.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_fieldRange_functionFieldMap`: the rank of a
  finite flat dominant morphism of integral schemes is the degree `[K(X) : f^* K(Y)]` at every
  point.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA).
-/

public section

open AlgebraicGeometry

universe u v w

namespace TauCeti.AlgebraicGeometry

/-- The rank of a finite flat affine morphism with integral target is the dimension after
passing to fraction rings. If `S` is a domain, `K` and `L` are fields and this is the degree
of the induced function-field extension. The scalar towers record compatibility with the
map of coordinate rings. -/
theorem finrank_SpecMap_eq_finrank_fractionRing
    {R S : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [CommRing S]
    [CommRing K] [CommRing L] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra R L] [Module K L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L] [Module.Flat R S] [Module.Finite R S]
    (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank p = Module.finrank K L := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  exact ((Module.rankAtStalk_eq p).trans p.asIdeal.finrank_fiber_eq_finrank).trans
    (IsFractionRing.finrank_eq R K S L).symm

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

/-- **The rank of a finite flat morphism is its function-field degree.** For a finite flat
dominant morphism `f : X ⟶ Y` of integral schemes, the rank of `f` at every point of `Y` is the
degree `[K(X) : f^* K(Y)]` of the function field of `X` over the image of the pullback of
rational functions `f^*` (`Scheme.Hom.functionFieldMap`). In particular the rank is constant. -/
theorem Scheme.Hom.finrank_eq_finrank_fieldRange_functionFieldMap (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsFinite f] [Flat f] [IsDominant f] (y : Y) :
    f.finrank y = Module.finrank f.functionFieldMap.hom.fieldRange X.functionField := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  -- Over `U`, the morphism `f` is the spectrum of the finite flat map of coordinate rings `φ`.
  have : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.Finite := by
    rw [← f.app_eq_appLE]; exact f.finite_app U hU
  have : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.Flat := f.flat_appLE hU hV le_rfl
  set φ := f.appLE U (f ⁻¹ᵁ U) le_rfl
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [f.finrank_fromSpec_eq_finrank_SpecMap_appLE hU p]
  -- The coordinate rings are domains with fraction fields `K(Y)` and `K(X)`, and `f^*` extends
  -- `φ`.
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X _ hV
  algebraize [φ.hom, f.functionFieldMap.hom]
  let : Algebra Γ(Y, U) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp φ.hom).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, U) Y.functionField X.functionField := .of_algebraMap_eq fun a ↦ by
    have := congr($(f.germToFunctionField_functionFieldMap U).hom a)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.app_eq_appLE] at this
    exact this.symm
  -- `φ` is the `algebraMap` of the algebra structure it defines, so `Spec.map φ` is the morphism
  -- of the affine statement.
  refine (TauCeti.AlgebraicGeometry.finrank_SpecMap_eq_finrank_fractionRing
    (K := Y.functionField) (L := X.functionField) p).trans ?_
  exact Algebra.finrank_eq_of_equiv_equiv f.functionFieldMap.hom.rangeRestrictFieldEquiv
    (.refl _) (by ext; simp [Subfield.algebraMap_ofSubfield, RingHom.algebraMap_toAlgebra])

end AlgebraicGeometry
