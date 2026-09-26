/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Singular cohomology with local coefficients

Let `L` be a local coefficient system of `R`-modules on a space `X` and let `M` be an `R`-module.
Applying `Hom(-, M)` to the singular chains of `X` twisted by `L` gives the twisted singular
cochain complex: in degree `n` it is the module of morphisms from the twisted `n`-chains to `M`,
and its differential is precomposition with the twisted singular boundary.  Its cohomology is the
singular cohomology of `X` with coefficients in `L` and values in `M`.  As for untwisted singular
cohomology, the cochain groups are modules over any ring `k` acting linearly on `R`-modules: `ℤ`
always, and `R` itself when `R` is commutative.

Since the twisted `n`-chains are the coproduct over the singular `n`-simplices `σ` of the fibre of
`L` at the initial vertex of `σ`, a twisted `n`-cochain is a family of morphisms `L(σ(0)) ⟶ M`,
one for each singular `n`-simplex.  So this is cohomology with coefficients in the dual of `L`,
which is the form in which cap products pair cohomology against homology twisted by the
orientation system of a manifold.

Everything is functorial: a morphism of local coefficient systems `L ⟶ K` induces a cochain map
from the cochains twisted by `K` to those twisted by `L`, a continuous map `f : X ⟶ Y` induces a
cochain map from the cochains of `Y` twisted by `L` to those of `X` twisted by the pullback
system, and for a constant system the construction returns ordinary singular cohomology.

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedCochainComplex` and
  `TauCeti.LocalCoefficientSystem.twistedCohomology`: the twisted singular cochain complex and its
  cohomology.
* `TauCeti.LocalCoefficientSystem.twistedCochainComplexCoefficientMap` and
  `TauCeti.LocalCoefficientSystem.twistedCohomologyCoefficientMap`: change of local coefficient
  system.
* `TauCeti.LocalCoefficientSystem.twistedCochainComplexMap` and
  `TauCeti.LocalCoefficientSystem.twistedCohomologyMap`: the maps induced by a continuous map.
* `TauCeti.LocalCoefficientSystem.twistedCohomologyConstantIso`: for a constant system, twisted
  cohomology is ordinary singular cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapters VII--VIII.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M : ModuleCat.{max v w} R) {X : TopCat.{v}}

section Definition

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The singular cochain complex of `X` with coefficients in the local coefficient system `L` and
values in `M`: in degree `n`, the `k`-module of morphisms from the twisted singular `n`-chains
of `X` to `M`. -/
abbrev twistedCochainComplex : CochainComplex (ModuleCat.{max v w} k) ℕ :=
  L.twistedChainComplex.linearYonedaObj k M

/-- The singular cohomology of `X` in degree `n` with coefficients in the local coefficient
system `L` and values in `M`. -/
abbrev twistedCohomology (n : ℕ) : ModuleCat.{max v w} k :=
  (L.twistedCochainComplex k M).homology n

end Definition

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

/-- The cochain map induced by a morphism of local coefficient systems: precomposition with the
induced morphism of twisted chains. -/
abbrev twistedCochainComplexCoefficientMap (η : L ⟶ K) :
    K.twistedCochainComplex k M ⟶ L.twistedCochainComplex k M :=
  (ChainComplex.linearYonedaFunctor k M).map (twistedChainComplexCoefficientMap η).op

/-- The degree-`n` component of the cochain map induced by a morphism of local coefficient
systems acts by precomposition. -/
@[simp]
lemma twistedCochainComplexCoefficientMap_f_apply (η : L ⟶ K) (n : ℕ)
    (g : (K.twistedCochainComplex k M).X n) :
    (twistedCochainComplexCoefficientMap k M η).f n g =
      (twistedChainComplexCoefficientMap η).f n ≫ g := (rfl)

@[simp]
lemma twistedCochainComplexCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedCochainComplexCoefficientMap k M (𝟙 L) = 𝟙 _ :=
  (congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

@[reassoc]
lemma twistedCochainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedCochainComplexCoefficientMap k M (η ≫ θ) =
      twistedCochainComplexCoefficientMap k M θ ≫ twistedCochainComplexCoefficientMap k M η :=
  (congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexCoefficientMap_comp η θ)).trans
    (CategoryTheory.Functor.map_comp _ _ _)

/-- The map on twisted cohomology induced by a morphism of local coefficient systems. -/
abbrev twistedCohomologyCoefficientMap (η : L ⟶ K) (n : ℕ) :
    K.twistedCohomology k M n ⟶ L.twistedCohomology k M n :=
  HomologicalComplex.homologyMap (twistedCochainComplexCoefficientMap k M η) n

@[simp]
lemma twistedCohomologyCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (n : ℕ) : twistedCohomologyCoefficientMap k M (𝟙 L) n = 𝟙 _ :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (twistedCochainComplexCoefficientMap_id k M L)).trans (CategoryTheory.Functor.map_id _ _)

@[reassoc]
lemma twistedCohomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (n : ℕ) :
    twistedCohomologyCoefficientMap k M (η ≫ θ) n =
      twistedCohomologyCoefficientMap k M θ n ≫ twistedCohomologyCoefficientMap k M η n :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (twistedCochainComplexCoefficientMap_comp k M η θ)).trans
    (CategoryTheory.Functor.map_comp _ _ _)

end Coefficients

section Map

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- The cochain map induced by a continuous map `f : X ⟶ Y`, from the cochains of `Y` twisted by
`L` to the cochains of `X` twisted by the pullback of `L` along `f`. -/
abbrev twistedCochainComplexMap :
    L.twistedCochainComplex k M ⟶ ((pullback f.hom).obj L).twistedCochainComplex k M :=
  (ChainComplex.linearYonedaFunctor k M).map (twistedChainComplexMap f L).op

/-- The degree-`n` component of the cochain map induced by a continuous map acts by precomposition
with the induced morphism of twisted chains. -/
@[simp]
lemma twistedCochainComplexMap_f_apply (n : ℕ) (g : (L.twistedCochainComplex k M).X n) :
    (twistedCochainComplexMap k M f L).f n g = (twistedChainComplexMap f L).f n ≫ g := (rfl)

/-- The map on twisted cohomology induced by a continuous map. -/
abbrev twistedCohomologyMap (n : ℕ) :
    L.twistedCohomology k M n ⟶ ((pullback f.hom).obj L).twistedCohomology k M n :=
  HomologicalComplex.homologyMap (twistedCochainComplexMap k M f L) n

end Map

section MapCoefficient

variable {Y : TopCat.{v}} (f : X ⟶ Y) {L K : LocalCoefficientSystem.{u, v, max v w} R Y}

/-- The cochain map induced by a continuous map is natural in the coefficient system. -/
@[reassoc]
lemma twistedCochainComplexMap_naturality (η : L ⟶ K) :
    twistedCochainComplexCoefficientMap k M η ≫ twistedCochainComplexMap k M f L =
      twistedCochainComplexMap k M f K ≫
        twistedCochainComplexCoefficientMap k M ((pullback f.hom).map η) :=
  ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
      (twistedChainComplexMap_naturality f η)).trans
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

/-- The map induced on twisted cohomology by a continuous map is natural in the coefficient
system. -/
@[reassoc]
lemma twistedCohomologyMap_naturality (η : L ⟶ K) (n : ℕ) :
    twistedCohomologyCoefficientMap k M η n ≫ twistedCohomologyMap k M f L n =
      twistedCohomologyMap k M f K n ≫
        twistedCohomologyCoefficientMap k M ((pullback f.hom).map η) n :=
  ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
      (twistedCochainComplexMap_naturality k M f η)).trans
      ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _))

end MapCoefficient

section MapComp

variable {Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The identity map induces on twisted cochains the map coming from the identification of a
coefficient system with its pullback along the identity. -/
@[simp]
lemma twistedCochainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedCochainComplexMap k M (𝟙 X) L =
      twistedCochainComplexCoefficientMap k M ((pullbackIdIso X).hom.app L) :=
  congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k M).map (Opposite.op φ))
    (twistedChainComplexMap_id L)

/-- A composite of continuous maps induces on twisted cochains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated pullback. -/
@[simp, reassoc]
lemma twistedCochainComplexMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    twistedCochainComplexMap k M (f ≫ g) L =
      twistedCochainComplexMap k M g L ≫
        twistedCochainComplexMap k M f ((pullback g.hom).obj L) ≫
          twistedCochainComplexCoefficientMap k M ((pullbackCompIso f.hom g.hom).hom.app L) := by
  simp only [twistedCochainComplexMap, twistedChainComplexMap_comp, op_comp,
    twistedCochainComplexCoefficientMap, Category.assoc]
  exact ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).trans
    (congrArg ((ChainComplex.linearYonedaFunctor k M).map _ ≫ ·)
      ((ChainComplex.linearYonedaFunctor k M).map_comp _ _))

/-- The cohomology form of `twistedCochainComplexMap_id`. -/
@[simp]
lemma twistedCohomologyMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (n : ℕ) :
    twistedCohomologyMap k M (𝟙 X) L n =
      twistedCohomologyCoefficientMap k M ((pullbackIdIso X).hom.app L) n :=
  congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
    (twistedCochainComplexMap_id k M L)

/-- The cohomology form of `twistedCochainComplexMap_comp`. -/
@[simp, reassoc]
lemma twistedCohomologyMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) (n : ℕ) :
    twistedCohomologyMap k M (f ≫ g) L n =
      twistedCohomologyMap k M g L n ≫ twistedCohomologyMap k M f ((pullback g.hom).obj L) n ≫
        twistedCohomologyCoefficientMap k M ((pullbackCompIso f.hom g.hom).hom.app L) n := by
  rw [twistedCohomologyMap, twistedCochainComplexMap_comp]
  exact ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _).trans
    (congrArg ((HomologicalComplex.homologyFunctor _ _ n).map _ ≫ ·)
      ((HomologicalComplex.homologyFunctor _ _ n).map_comp _ _))

end MapComp

section Constant

variable (X) (N : ModuleCat.{max v w} R)

/-- For a constant local coefficient system, the twisted cochain complex is the ordinary singular
cochain complex with the same coefficient module. -/
def twistedCochainComplexConstantIso :
    ((constantFunctor X).obj N).twistedCochainComplex k M ≅ X.singularCochainComplex N k M :=
  ((ChainComplex.linearYonedaFunctor k M).mapIso (twistedChainComplexConstantIso X N).op).symm

@[simp]
lemma twistedCochainComplexConstantIso_hom :
    (twistedCochainComplexConstantIso k M X N).hom =
      (ChainComplex.linearYonedaFunctor k M).map
        (twistedChainComplexConstantIso X N).inv.op := (rfl)

@[simp]
lemma twistedCochainComplexConstantIso_inv :
    (twistedCochainComplexConstantIso k M X N).inv =
      (ChainComplex.linearYonedaFunctor k M).map
        (twistedChainComplexConstantIso X N).hom.op := (rfl)

/-- For a constant local coefficient system, twisted cohomology is ordinary singular
cohomology. -/
def twistedCohomologyConstantIso (n : ℕ) :
    ((constantFunctor X).obj N).twistedCohomology k M n ≅ X.singularCohomology N k M n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (twistedCochainComplexConstantIso k M X N)

@[simp]
lemma twistedCohomologyConstantIso_hom (n : ℕ) :
    (twistedCohomologyConstantIso k M X N n).hom =
      HomologicalComplex.homologyMap (twistedCochainComplexConstantIso k M X N).hom n := (rfl)

@[simp]
lemma twistedCohomologyConstantIso_inv (n : ℕ) :
    (twistedCohomologyConstantIso k M X N n).inv =
      HomologicalComplex.homologyMap (twistedCochainComplexConstantIso k M X N).inv n := (rfl)

end Constant

end LocalCoefficientSystem

end TauCeti
