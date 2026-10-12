/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Theorem
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DiscreteGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.AllDegreeColimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The third cohomology of a class formation vanishes

For a class formation with module `A` on a profinite group `G`, Tate's theorem
`TauCeti.ClassFieldTheory.ClassFormation.tateIso` at degree `1` identifies the third cohomology of
every finite normal layer `V ◁ U` with the first cohomology of its Galois group in trivial integral
coefficients,

```text
H³(U ⧸ V, A^V) ≅ H-hat^3(U ⧸ V, A^V) ≅ H-hat^1(U ⧸ V, ℤ) = Hom(U ⧸ V, ℤ) = 0,
```

which vanishes because the Galois group is finite (`ClassFormation.subsingleton_H3`). Continuous
cohomology being the colimit of the cohomology of the finite quotients `G ⧸ V`, each of which is
the cohomology of the layer `V ◁ G`, the continuous third cohomology `H³(G, A)` vanishes as well
(`ClassFormation.subsingleton_continuousCohomology_three`). For the local class formation this is
the vanishing of `H³(G_K, (Kˢ)ˣ)`, the input to the cohomological dimension of the absolute Galois
group of a local field.

## Main results

* `TauCeti.ClassFieldTheory.ClassFormation.subsingleton_H3`: `H³` of every layer of a class
  formation vanishes.
* `TauCeti.ClassFieldTheory.ClassFormation.subsingleton_continuousCohomology_three`: the continuous
  `H³(G, A)` of the module of a class formation vanishes.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J.-P. Serre, *Local Fields*, Chapter XI, §3, and *Galois Cohomology*, Ch. II, §5.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.1.8).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F : Formation G}

attribute [local instance] TopRep.distribMulAction

/-! ### The layer of an open normal subgroup as a finite level -/

section Level

variable (V : OpenNormalSubgroup G)

/-- The level of an open normal subgroup `V` is the subgroup of the module fixed by `V`. -/
private theorem toAddSubgroup_level :
    (F.level V.toOpenSubgroup).toAddSubgroup =
      FixedPoints.addSubgroup V.toSubgroup F.module.V := by
  ext x
  rw [Submodule.mem_toAddSubgroup, Formation.mem_level, FixedPoints.mem_addSubgroup,
    Subtype.forall]
  rfl

/-- The coefficient module of the layer `V ◁ G` is the subgroup of the module fixed by `V`. -/
private def ofOpenNormalRepEquiv :
    ((NormalLayer.ofOpenNormal V).rep F).V ≃ₗ[ℤ] FixedPoints.addSubgroup V.toSubgroup F.module.V :=
  (LinearEquiv.ofEq _ _ (congrArg F.level (NormalLayer.top_ofOpenNormal V))).trans
    (AddEquiv.addSubgroupCongr (toAddSubgroup_level V)).toIntLinearEquiv

/-- `ofOpenNormalRepEquiv` moves no element of the module. -/
private theorem ofOpenNormalRepEquiv_apply_coe (x : ((NormalLayer.ofOpenNormal V).rep F).V) :
    ((ofOpenNormalRepEquiv V x : FixedPoints.addSubgroup V.toSubgroup F.module.V) : F.module.V) =
      ((x : F.level (NormalLayer.ofOpenNormal V).top) : F.toRep.V) := by
  rw [ofOpenNormalRepEquiv, LinearEquiv.trans_apply, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.addSubgroupCongr_apply, LinearEquiv.coe_ofEq_apply]

/-- **The cohomology of the layer `V ◁ G` is that of the finite level `V`**: Mathlib's
`Hⁿ(G ⧸ V, A^V)` of the layer, carried along `NormalLayer.galOfOpenNormalEquiv`, is the group
cohomology of the fixed points of `V` as a module for the finite quotient `G ⧸ V`. -/
private def layerGroupCohomologyIso (n : ℕ) :
    (NormalLayer.ofOpenNormal V).H F n ≅
      groupCohomology (Rep.ofDistribMulAction ℤ (G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup F.module.V)) n :=
  groupCohomology.mapIso (NormalLayer.galOfOpenNormalEquiv V) (ofOpenNormalRepEquiv V)
    (fun g => by
      induction g using QuotientGroup.induction_on with
      | H u =>
        refine LinearMap.ext fun x => Subtype.ext ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, NormalLayer.galOfOpenNormalEquiv_mk]
        -- both sides are `u` acting on the underlying element of `x` in the module
        exact ((ofOpenNormalRepEquiv_apply_coe V _).trans
          ((NormalLayer.rep_ρ_mk_apply_coe _ F u x).trans (Formation.toRep_ρ_apply F u x))).trans
          ((congrArg (F.module.ρ u) (ofOpenNormalRepEquiv_apply_coe V x)).symm.trans
            ((TopRep.distribMulAction_smul F.module u _).symm.trans
              (subtype_quotientMk_smul G F.module.V V.toSubgroup u
                (ofOpenNormalRepEquiv V x)).symm))) n

end Level

namespace ClassFormation

/-- **The third cohomology of every layer of a class formation vanishes.** Tate's isomorphism at
degree `1` identifies `H-hat^3(U ⧸ V, A^V)`, which is `H³(U ⧸ V, A^V)`, with
`H-hat^1(U ⧸ V, ℤ) = Hom(U ⧸ V, ℤ)`, which is zero because `U ⧸ V` is finite. -/
theorem subsingleton_H3 (cf : ClassFormation F) (L : NormalLayer G) : Subsingleton (L.H F 3) := by
  have : Subsingleton (L.TrivialTateH 1) :=
    ModuleCat.subsingleton_of_isZero <|
      (TauCeti.groupCohomology.isZero_H1_of_isTrivial (Rep.trivial ℤ L.Gal ℤ)).of_iso
        ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ L.Gal ℤ))
  have : Subsingleton (L.TateH F (1 + 2)) := (cf.tateIso L 1).symm.injective.subsingleton
  have : Subsingleton (L.TateH F (3 : ℕ)) := this
  exact (L.tateHIsoH F 3).toLinearEquiv.symm.injective.subsingleton

/-- **The continuous third cohomology of a class formation vanishes**: `H³(G, A) = 0` for the
module `A` of a class formation on `G`. Every class is inflated from a finite quotient `G ⧸ V`,
whose third cohomology is that of the layer `V ◁ G`, zero by `subsingleton_H3`. -/
theorem subsingleton_continuousCohomology_three (cf : ClassFormation F) :
    Subsingleton (continuousCohomology 3 F.module) := by
  have := F.smooth.discreteTopology
  have := F.smooth.continuousSMul
  suffices Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G F.module.V)) from
    (ofDiscreteModuleRestrictScalarsIntEquiv F.module 3).symm.injective.subsingleton
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : continuousCohomology 3 (ofDiscreteModule ℤ G F.module.V), x = 0 by
    rw [h x, h y]
  intro x
  -- `x` is inflated from a finite quotient `G ⧸ V`, whose third cohomology vanishes
  obtain ⟨V, z, rfl⟩ := exists_continuousFiniteQuotientComparisonApp_eq x
  have := cf.subsingleton_H3 (NormalLayer.ofOpenNormal V)
  have : Subsingleton (groupCohomology (Rep.ofDistribMulAction ℤ (G ⧸ V.toSubgroup)
      (FixedPoints.addSubgroup V.toSubgroup F.module.V)) 3) :=
    (layerGroupCohomologyIso V 3).toLinearEquiv.symm.injective.subsingleton
  obtain ⟨e⟩ := nonempty_continuousCohomology_addEquiv_groupCohomology (G ⧸ V.toSubgroup)
    (FixedPoints.addSubgroup V.toSubgroup F.module.V) 3
  rw [e.injective.subsingleton.elim z 0, map_zero]

end ClassFormation

end TauCeti.ClassFieldTheory
