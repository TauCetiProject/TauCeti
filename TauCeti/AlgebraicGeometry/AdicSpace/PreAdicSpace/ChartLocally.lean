/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap

/-!
# Morphisms of pre-adic spaces chart-locally induced by morphisms of Huber pairs

Given a property `Q` of morphisms of Huber pairs, a morphism `f : X ⟶ Y` of pre-adic spaces is
*chart-locally `Q`* when every point of `X` has an open neighbourhood `U` mapped by `f` into an
open `V ⊆ Y` such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and
Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of Huber
pairs `(A, A⁺) → (B, B⁺)` satisfying `Q`. This is the shape of Wedhorn's Definition 8.48 and of
Huber's definition of adic morphisms (Huber 1994, §3); the name follows Mathlib's
`AlgebraicGeometry.affineLocally` for schemes.

The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs needs the structure
presheaf of `Spa(B, B⁺)` to be a sheaf, which is part of the data of the definition.

## Main definitions

* `TauCeti.PreAdicSpace.chartLocally`: the morphisms chart-locally induced by morphisms of Huber
  pairs satisfying a given property.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.48.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

open ValuationSpectrum

/-- A morphism `f : X ⟶ Y` of pre-adic spaces is *chart-locally `Q`*, for a property `Q` of
morphisms of Huber pairs, when every point `x` of `X` has an open neighbourhood `U`, mapped by `f`
into an open `V` of `Y`, together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and
Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf, a morphism
`φ : (A, A⁺) → (B, B⁺)` satisfying `Q`, and isomorphisms identifying `X` restricted to `U` with
`Spa(B, B⁺)` and `Y` restricted to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism
induced by `φ`. -/
def chartLocally
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop) :
    MorphismProperty PreAdicSpace.{u} := fun X Y f ↦
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : Q φ)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.ofRestrict _ ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.ofRestrict _

/-- Unfolding lemma for `TauCeti.PreAdicSpace.chartLocally`. -/
theorem chartLocally_iff
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    {X Y : PreAdicSpace.{u}} (f : X ⟶ Y) : chartLocally Q f ↔
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.ofRestrict _ ≫ f =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.ofRestrict _ :=
  Iff.rfl

end PreAdicSpace

end TauCeti

end
