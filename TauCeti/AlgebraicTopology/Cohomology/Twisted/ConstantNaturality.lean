/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic

/-!
# Naturality of the constant-coefficient comparison for singular cohomology

The comparison between cohomology with a constant local system and ordinary singular
cohomology commutes with continuous maps. The pullback of the constant system is identified
with the constant system on the source. This gives the map-level comparison needed when
cohomology with local coefficients is specialized to ordinary cohomology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  {X Y : TopCat.{v}} (f : X ⟶ Y) (N : ModuleCat.{max v w} R)

/-- The constant-system comparison of cochain complexes commutes with a continuous map,
after identifying the pullback of a constant system with the constant system on the source. -/
@[reassoc]
lemma twistedCochainComplexConstantIso_hom_space_naturality :
    twistedCochainComplexMap k M f ((constantFunctor Y).obj N) ≫
        twistedCochainComplexCoefficientMap k M (pullbackConstantIso f.hom N).inv ≫
          (twistedCochainComplexConstantIso k M X N).hom =
      (twistedCochainComplexConstantIso k M Y N).hom ≫
        TopCat.singularCochainComplexMap f := by
  let F : (ChainComplex (ModuleCat.{max v w} R) ℕ)ᵒᵖ ⥤
      CochainComplex (ModuleCat.{max v w} k) ℕ := ChainComplex.linearYonedaFunctor k M
  let iX := twistedChainComplexConstantIso X N
  let iY := twistedChainComplexConstantIso Y N
  let c := twistedChainComplexCoefficientIso (pullbackConstantIso f.hom N)
  have h := twistedChainComplexConstantIso_hom_space_naturality f N
  have h' : iX.inv ≫ c.inv ≫ twistedChainComplexMap f ((constantFunctor Y).obj N) =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj N).map f ≫
        iY.inv := by
    calc
      iX.inv ≫ c.inv ≫ twistedChainComplexMap f ((constantFunctor Y).obj N) =
          iX.inv ≫ c.inv ≫ twistedChainComplexMap f ((constantFunctor Y).obj N) ≫
            iY.hom ≫ iY.inv := by simp
      _ = iX.inv ≫ c.inv ≫ c.hom ≫ iX.hom ≫
            ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj N).map
              f ≫ iY.inv := by
          have hc := congrArg (fun q => iX.inv ≫ c.inv ≫ q ≫ iY.inv) h
          dsimp only [iX, iY, c] at hc ⊢
          simpa only [Category.assoc, twistedChainComplexCoefficientIso_hom] using hc
      _ = ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj N).map
            f ≫ iY.inv := by simp
  have hF := congrArg (fun g => F.map g.op) h'
  dsimp only [F] at hF
  dsimp only [iX, iY, c] at hF
  simp only [op_comp, Functor.map_comp] at hF
  rw [TauCeti.singularChainComplexFunctor_obj_map N f] at hF
  simp only [twistedCochainComplexMap,
    twistedCochainComplexCoefficientMap, twistedCochainComplexConstantIso_hom,
    twistedChainComplexCoefficientIso_inv, TopCat.singularCochainComplexMap,
    Category.assoc] at hF ⊢
  exact hF

/-- The constant-system comparison on cohomology is natural in the space. -/
@[reassoc]
lemma twistedCohomologyConstantIso_hom_space_naturality (n : ℕ) :
    twistedCohomologyMap k M f ((constantFunctor Y).obj N) n ≫
        twistedCohomologyCoefficientMap k M (pullbackConstantIso f.hom N).inv n ≫
          (twistedCohomologyConstantIso k M X N n).hom =
      (twistedCohomologyConstantIso k M Y N n).hom ≫
        TopCat.singularCohomologyMap f n := by
  have h := twistedCochainComplexConstantIso_hom_space_naturality k M f N
  have hH := congrArg (fun g => HomologicalComplex.homologyMap g n) h
  simpa only [HomologicalComplex.homologyMap_comp, Category.assoc,
    twistedCohomologyMap, twistedCohomologyCoefficientMap,
    twistedCohomologyConstantIso_hom, TopCat.singularCohomologyMap] using hH

end TauCeti.LocalCoefficientSystem
