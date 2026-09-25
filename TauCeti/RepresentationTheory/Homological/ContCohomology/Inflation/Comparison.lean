/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ComparisonDegreeTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# Explicit inflation is canonical inflation

For a normal subgroup `N` of a topological group `G` and a discrete `G`-module `M`, inflation
exists twice. On the explicit low-degree complex it is `TauCeti.ContCohomology.explicitInfl0`,
`explicitInfl1` and `explicitInfl2`: pullback along `G → G ⧸ N` paired with the inclusion
`M ^ N ↪ M`. On Mathlib's continuous cohomology it is `TauCeti.ContinuousCohomology.infl`, whose
source is the cohomology of the canonical `N`-invariants `TopRep.quotientToInvariants X N` of
`X = ofDiscreteModule ℤ G M`. The coefficient dictionary `TauCeti.ofDiscreteModuleQuotient`
identifies the explicit fixed-point module `M ^ N`, as a discrete `G ⧸ N`-module, with those
canonical invariants.

This file proves that the comparison isomorphisms between the explicit and the canonical models
carry the first inflation to the second, in degrees `0`, `1` and `2`. The input is a single
identity of coefficient morphisms, `ofDiscreteModulePair_quotientMk_subtype`: the canonical
inflation pair, read through the dictionary, is the compatible pair of explicit inflation. It
turns canonical inflation after the dictionary into a single compatible-pair pullback in every
degree (`coeffMap_ofDiscreteModuleQuotient_comp_infl`), and the naturality of each low-degree
comparison in compatible pairs then gives the transport squares.

## Main results

* `TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl`: in every degree, canonical
  inflation after the dictionary morphism is the pullback along the explicit inflation pair.
* `TauCeti.ContCohomology.explicitH0Iso_infl`, `explicitIso_infl` and `explicitIso_infl2`: the
  comparison isomorphisms in degrees `0`, `1` and `2` carry explicit inflation to canonical
  inflation.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2 for the
  comparison of inhomogeneous and homogeneous cochains, and Ch. I, §5 for inflation.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- **The inflation pair through the dictionary.** Composing the dictionary morphism
`M ^ N ⟶ (ofDiscreteModule ℤ G M)ᴺ` with the inclusion of the canonical invariants gives the
compatible pair of explicit inflation: the quotient map `G → G ⧸ N` with the inclusion
`M ^ N ↪ M`. -/
theorem ofDiscreteModulePair_quotientMk_subtype :
    ofDiscreteModulePair (ContinuousMonoidHom.quotientMk N : G →* G ⧸ N)
        (FixedPoints.addSubgroup N M).subtype.toIntLinearMap
        (fun g m ↦ subtype_quotientMk_smul G M N g m) =
      (TopRep.resFunctor (ContinuousMonoidHom.quotientMk N : G →* G ⧸ N)).map
          (ofDiscreteModuleQuotient G M N) ≫
        TopRep.quotientToInvariantsι (ofDiscreteModule ℤ G M) N :=
  -- Evaluating the restricted morphism and the invariants inclusion reduces to the
  -- underlying coefficient of `ofDiscreteModuleQuotient`.
  ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun m ↦ ofDiscreteModuleQuotient_apply G M N m

variable [IsTopologicalGroup G]

/-- **Canonical inflation on the dictionary.** In every degree, the canonical inflation map of
`ofDiscreteModule ℤ G M`, precomposed with the coefficient map of the dictionary morphism
`ofDiscreteModuleQuotient`, is the pullback along the compatible pair of explicit inflation. -/
@[reassoc]
theorem coeffMap_ofDiscreteModuleQuotient_comp_infl (n : ℕ) :
    TauCeti.ContinuousCohomology.coeffMap (ofDiscreteModuleQuotient G M N) n ≫
        TauCeti.ContinuousCohomology.infl N (ofDiscreteModule ℤ G M) n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.quotientMk N)
        (ofDiscreteModulePair (ContinuousMonoidHom.quotientMk N : G →* G ⧸ N)
          (FixedPoints.addSubgroup N M).subtype.toIntLinearMap
          (fun g m ↦ subtype_quotientMk_smul G M N g m)) n := by
  rw [TauCeti.ContinuousCohomology.coeffMap_def, TauCeti.ContinuousCohomology.infl_def,
    ofDiscreteModulePair_quotientMk_subtype]
  refine (_root_.ContinuousCohomology.map_comp
    (X := ofDiscreteModule ℤ (G ⧸ N) (FixedPoints.addSubgroup N M))
    (Y := TopRep.quotientToInvariants (ofDiscreteModule ℤ G M) N) (Z := ofDiscreteModule ℤ G M)
    (ContinuousMonoidHom.id (G ⧸ N)) (ContinuousMonoidHom.quotientMk N)
    (ofDiscreteModuleQuotient G M N) (TopRep.quotientToInvariantsι (ofDiscreteModule ℤ G M) N)
    n).symm.trans ?_
  -- `map_comp` produces the composite `id.comp (quotientMk N)`, which is `quotientMk N` by `rfl`.
  exact TauCeti.ContinuousCohomology.map_congr rfl HEq.rfl n

/-- **Transport of inflation in degree zero.** The degree-zero comparison carries explicit
inflation to canonical inflation, read through the dictionary morphism
`ofDiscreteModuleQuotient`. -/
@[simp]
theorem explicitH0Iso_infl
    (x : H0 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    TauCeti.ContinuousCohomology.infl N (ofDiscreteModule ℤ G M) 0
        (TauCeti.ContinuousCohomology.coeffMap (ofDiscreteModuleQuotient G M N) 0
          ((explicitH0IsoContinuousCohomology (G ⧸ N) (FixedPoints.addSubgroup N M)).hom x)) =
      (explicitH0IsoContinuousCohomology G M).hom (explicitInfl0 G M N x) := by
  rw [← ConcreteCategory.comp_apply, coeffMap_ofDiscreteModuleQuotient_comp_infl,
    explicitInfl0_eq_explicitMap0]
  simpa only [ContinuousMonoidHom.coe_quotientMk] using
    (explicitH0Iso_map (G ⧸ N) (FixedPoints.addSubgroup N M) G M
      (ContinuousMonoidHom.quotientMk N) (FixedPoints.addSubgroup N M).subtype
      (subtype_quotientMk_smul G M N) x)

variable [ContinuousSMul G M] [CompactSpace G]

/-- **Transport of inflation in degree one.** The degree-one comparison carries explicit
inflation to canonical inflation, read through the dictionary morphism
`ofDiscreteModuleQuotient`. -/
@[simp]
theorem explicitIso_infl
    (x : DiscreteH1 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    TauCeti.ContinuousCohomology.infl N (ofDiscreteModule ℤ G M) 1
        (TauCeti.ContinuousCohomology.coeffMap (ofDiscreteModuleQuotient G M N) 1
          ((explicitH1IsoContinuousCohomology (G ⧸ N) (FixedPoints.addSubgroup N M)).hom x)) =
      (explicitH1IsoContinuousCohomology G M).hom
        ((discreteH1Equiv G M).symm
          (explicitInfl1 G M N (discreteH1Equiv (G ⧸ N) (FixedPoints.addSubgroup N M) x))) := by
  rw [← ConcreteCategory.comp_apply, coeffMap_ofDiscreteModuleQuotient_comp_infl,
    explicitInfl1_eq_explicitMap1]
  exact explicitIso_map (G ⧸ N) (FixedPoints.addSubgroup N M) G M
    (ContinuousMonoidHom.quotientMk N) (FixedPoints.addSubgroup N M).subtype
    (subtype_quotientMk_smul G M N) x

/-- **Transport of inflation in degree two.** The degree-two comparison carries explicit
inflation to canonical inflation, read through the dictionary morphism
`ofDiscreteModuleQuotient`. -/
@[simp]
theorem explicitIso_infl2
    (x : DiscreteH2 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    TauCeti.ContinuousCohomology.infl N (ofDiscreteModule ℤ G M) 2
        (TauCeti.ContinuousCohomology.coeffMap (ofDiscreteModuleQuotient G M N) 2
          ((explicitH2IsoContinuousCohomology (G ⧸ N) (FixedPoints.addSubgroup N M)).hom x)) =
      (explicitH2IsoContinuousCohomology G M).hom
        ((discreteH2Equiv G M).symm
          (explicitInfl2 G M N (discreteH2Equiv (G ⧸ N) (FixedPoints.addSubgroup N M) x))) := by
  rw [← ConcreteCategory.comp_apply, coeffMap_ofDiscreteModuleQuotient_comp_infl,
    explicitInfl2_eq_explicitMap2]
  exact explicitIso_map2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M
    (ContinuousMonoidHom.quotientMk N) (FixedPoints.addSubgroup N M).subtype
    (subtype_quotientMk_smul G M N) x

end TauCeti.ContCohomology
