/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import TauCeti.GroupTheory.GroupAction.FixedPoints
import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Inflation from a finite normal layer to its ground subgroup

Let `F` be a formation on a profinite group `G` whose coefficient module is read, through an
equivariant additive equivalence `e : M ≃+ A`, on a discrete `G`-module `M`, as for the idele
formation of a number field `K`, whose coefficients are read on the ideles of `Kˢ`. For a finite
normal layer `V ◁ U` of open subgroups of `G`, this file constructs **inflation** from the second
cohomology of the layer to the continuous second cohomology of its ground subgroup,

```text
NormalLayer.explicitInfl2 L e he : H²(U ⧸ V, M^V) → H²(U, M),
```

in the explicit inhomogeneous model of `TauCeti.ContCohomology`. On the class of a layer cocycle
`c` it is the class of the inflated cocycle `(u, v) ↦ c (u V, v V)` (`explicitInfl2_H2π`,
`inflCocycle2_apply`), and it commutes with the refinement of a layer to a smaller top subgroup
(`explicitInfl2_cohomologyInfl`), where the class is read on the common ground subgroup.

Inflation carries the cohomology of the finite layers into continuous cohomology, where the
local–global maps of a number field (localization at the places, corestriction to the ground
field) are defined.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2 L e he`: inflation
  `H²(U ⧸ V, M^V) → H²(U, M)`.
* `TauCeti.ClassFieldTheory.NormalLayer.inflCocycle2 L e he c`: the continuous `2`-cocycle on `U`
  inflated from a layer cocycle `c`.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_H2π`: inflation sends the class of a layer
  cocycle to the class of its inflated cocycle.
* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_cohomologyInfl`: inflation commutes with the
  refinement of layers.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.1) and
  (1.6.7).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

namespace NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G) {F : Formation G}
  {M : Type} [AddCommGroup M] [DistribMulAction G M] (e : M ≃+ F.toRep.V)
  (he : ∀ (g : G) (x : M), e (g • x) = F.toRep.ρ g (e x))

/-- The coefficient module `A^V` of the layer, read in `M` through `e` as the fixed points of the
top subgroup `V`, viewed as a subgroup of the ground subgroup `U`. -/
private def coeffFixedPointsEquiv :
    (L.rep F).V ≃+ FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M where
  toFun x := ⟨e.symm (x : F.level L.top), (FixedPoints.mem_addSubgroup _ _ _).2 fun v =>
    e.injective <| (he _ _).trans <| by
      rw [e.apply_symm_apply]
      exact (Formation.mem_level _).1 x.2 _ (Subgroup.mem_subgroupOf.1 v.2)⟩
  invFun m := ⟨e m, (Formation.mem_level _).2 fun v hv =>
    (he v m).symm.trans <| congrArg e <|
      (FixedPoints.mem_addSubgroup _ _ _).1 m.2 ⟨⟨v, L.top_le_ground hv⟩, hv⟩⟩
  left_inv _ := Subtype.ext (e.apply_symm_apply _)
  right_inv _ := Subtype.ext (e.symm_apply_apply _)
  map_add' _ _ := Subtype.ext (map_add e.symm _ _)

private theorem coeffFixedPointsEquiv_apply_coe (x : (L.rep F).V) :
    (coeffFixedPointsEquiv L e he x : M) = e.symm (x : F.level L.top) :=
  (rfl)

private theorem coeffFixedPointsEquiv_ρ
    (g : L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
    (x : (L.rep F).V) :
    coeffFixedPointsEquiv L e he ((L.rep F).ρ g x) = g • coeffFixedPointsEquiv L e he x := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    refine Subtype.ext ?_
    rw [coeffFixedPointsEquiv_apply_coe, coe_quotient_smul_fixedPoints_addSubgroup,
      coe_smul_fixedPoints_addSubgroup, coeffFixedPointsEquiv_apply_coe, AddEquiv.symm_apply_eq,
      Subgroup.smul_def, he, AddEquiv.apply_symm_apply]
    exact L.rep_ρ_mk_apply_coe _ u x

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The second cohomology of a layer as the explicit `H²` of its finite Galois group, with
coefficients the fixed points of its top subgroup in `M`. -/
private def h2EquivExplicit :
    L.H F 2 ≃+
      H2 (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M) :=
  (groupCohomology.mapIso (MulEquiv.refl L.Gal :
      L.Gal ≃* (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup))
    (coeffFixedPointsEquiv L e he).toIntLinearEquiv
    (fun g => LinearMap.ext fun x => coeffFixedPointsEquiv_ρ L e he g x)
      2).toLinearEquiv.toAddEquiv.trans
    (explicitH2IsoGroupCohomology
      (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M)).symm

/-- **Inflation from a layer to its ground subgroup**: for a finite normal layer `V ◁ U` of a
formation whose coefficient module is read on the discrete module `M` through `e`, the map
`H²(U ⧸ V, M^V) → H²(U, M)` into the continuous cohomology of `U`. On the class of a cocycle `c`
it is the class of `inflCocycle2 L e he c` (`explicitInfl2_H2π`). -/
def explicitInfl2 : L.H F 2 →+ H2 L.ground.toSubgroup M :=
  (ContCohomology.explicitInfl2 L.ground.toSubgroup M
    (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)).comp (h2EquivExplicit L e he).toAddMonoidHom

/-- A layer cocycle, read with values in the fixed points of the top subgroup. -/
private def levelCocycle (c : cocycles₂ (L.rep F)) :
    Z2 (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M) :=
  ⟨fun q => coeffFixedPointsEquiv L e he (c q), mem_Z2_iff.2 ⟨continuous_of_discreteTopology,
    fun g h j => by
      have hc := congrArg (coeffFixedPointsEquiv L e he) ((mem_cocycles₂_iff c).1 c.2 g h j)
      rw [map_add, map_add] at hc
      exact hc.trans (congrArg (· + _) (coeffFixedPointsEquiv_ρ L e he g (c (h, j))))⟩⟩

private theorem h2EquivExplicit_H2π (c : cocycles₂ (L.rep F)) :
    h2EquivExplicit L e he (H2π _ c) = (levelCocycle L e he c : H2 _ _) := by
  refine (AddEquiv.symm_apply_eq _).2 ((groupCohomology.H2π_comp_map_apply _ _ c).trans
    (Eq.trans ?_ (explicitH2IsoGroupCohomology_mk
      (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M) _).symm))
  exact congrArg _ (Subtype.ext (funext fun q =>
    (congrFun (Z2AddEquivCocycles₂_coe _ _ (levelCocycle L e he c)) q).symm))

/-- The **inflated cocycle** of a `2`-cocycle `c` of a layer: the continuous `2`-cocycle
`(u, v) ↦ c (u V, v V)` on the ground subgroup `U`, with values in `M` (`inflCocycle2_apply`).
Its class is `explicitInfl2 L e he [c]` (`explicitInfl2_H2π`). -/
def inflCocycle2 (c : cocycles₂ (L.rep F)) : Z2 L.ground.toSubgroup M :=
  cocyclesMap2 _ _ _ _ (ContinuousMonoidHom.quotientMk _)
    (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M).subtype
    (continuous_fixedPoints_addSubgroup_subtype _ _ _) (subtype_quotientMk_smul _ _ _)
    (levelCocycle L e he c)

omit [ContinuousSMul G M] in
/-- The values of the inflated cocycle are the values of the layer cocycle at the classes of the
two arguments, read in `M`. -/
@[simp]
theorem inflCocycle2_apply (c : cocycles₂ (L.rep F)) (u v : L.ground.toSubgroup) :
    (inflCocycle2 L e he c : L.ground.toSubgroup × L.ground.toSubgroup → M) (u, v) =
      e.symm (c ((u : L.Gal), (v : L.Gal)) : F.level L.top) := by
  rw [inflCocycle2, cocyclesMap2_apply]
  exact coeffFixedPointsEquiv_apply_coe L e he _

/-- **Inflation on cocycle classes**: `explicitInfl2 L e he` sends the class of a layer cocycle `c`
to the class of the inflated cocycle `inflCocycle2 L e he c`. -/
@[simp]
theorem explicitInfl2_H2π (c : cocycles₂ (L.rep F)) :
    L.explicitInfl2 e he (H2π _ c) = (inflCocycle2 L e he c : H2 _ _) := by
  rw [explicitInfl2, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2EquivExplicit_H2π,
    explicitInfl2_mk]
  rfl

/-- **Inflation commutes with refinement of layers**: for a refinement of `V ◁ U` to `V' ◁ U`, the
class inflated from `V' ◁ U` of the refined class is the class inflated from `V ◁ U`, read along
the identification of the two ground subgroups. -/
theorem explicitInfl2_cohomologyInfl {old new : NormalLayer G} (T : LayerRefinement old new)
    (x : old.H F 2) :
    new.explicitInfl2 e he (T.cohomologyInfl F 2 x) =
      explicitMap2 old.ground.toSubgroup M new.ground.toSubgroup M
        (ContinuousMonoidHom.subgroupInclusion T.same_ground_toSubgroup.ge) (AddMonoidHom.id _)
        continuous_id (fun _ _ => rfl) (old.explicitInfl2 e he x) := by
  induction x using H2_induction_on with
  | h c =>
    rw [LayerRefinement.cohomologyInfl_def, H2π_comp_map_apply, explicitInfl2_H2π]
    refine Eq.trans ?_ (congrArg _ (explicitInfl2_H2π old e he c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    refine congrArg _ (Subtype.ext (funext fun p => Eq.trans ?_
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm))
    obtain ⟨u, v⟩ := p
    refine (inflCocycle2_apply new e he _ u v).trans
      (Eq.trans (congrArg _ ?_) (inflCocycle2_apply old e he c _ _).symm)
    exact (T.repHom_hom_apply_coe F _).trans
      (congrArg (fun q => ((c q : F.level old.top) : F.toRep.V))
        (Prod.ext (T.galHom_mk u) (T.galHom_mk v)))

end NormalLayer

end TauCeti.ClassFieldTheory
