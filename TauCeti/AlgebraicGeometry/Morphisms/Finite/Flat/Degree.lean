/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.AlgebraicGeometry.Morphisms.Affine.Degree

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

The local rank is Mathlib's `Scheme.Hom.finrank`. Over an affine open `U` of `Y`, whose preimage
is affine because `f` is finite, Mathlib's fibre-rank calculation for finite flat modules over a
domain identifies it with the rank of `Γ(X, f⁻¹ U)` over `Γ(Y, U)`. For any dominant affine
morphism of integral schemes, flat or not, that rank is `[K(X) : f^* K(Y)]`
(`AlgebraicGeometry.Scheme.Hom.finrank_appLE_eq_finrank_fieldRange_functionFieldMap`): both
coordinate rings are domains whose fraction fields are the function fields, and `f^*` extends the
map of coordinate rings.

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
  -- Over `U`, the morphism `f` is the spectrum of the map of coordinate rings `φ`.
  set φ := f.appLE U (f ⁻¹ᵁ U) le_rfl
  have H : IsPullback (Spec.map φ) hV.fromSpec hU.fromSpec f :=
    IsOpenImmersion.isPullback _ _ _ _ (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
      (by rw [hU.opensRange_fromSpec, hV.opensRange_fromSpec])
  have hfin : IsFinite (Spec.map φ) := MorphismProperty.of_isPullback H.flip ‹_›
  have hflat : Flat (Spec.map φ) := MorphismProperty.of_isPullback H.flip ‹_›
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [← finrank_of_isPullback _ _ _ _ H.flip,
    ← f.finrank_appLE_eq_finrank_fieldRange_functionFieldMap hU]
  algebraize [φ.hom]
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by rwa [IsFinite.SpecMap_iff] at hfin
  have : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by rwa [Flat.SpecMap_iff] at hflat
  have : p.asIdeal.IsPrime := p.isPrime
  -- `φ` is the `algebraMap` of the algebra structure it defines, so `Spec.map φ` is the morphism
  -- whose rank at `p` is the rank of the fibre of `Γ(X, f⁻¹ U)`, constant over the domain
  -- `Γ(Y, U)`.
  exact (Scheme.Hom.finrank_SpecMap_algebraMap _ _ p).trans
    ((Module.rankAtStalk_eq p).trans (Ideal.finrank_fiber_eq_finrank p.asIdeal))

end AlgebraicGeometry
