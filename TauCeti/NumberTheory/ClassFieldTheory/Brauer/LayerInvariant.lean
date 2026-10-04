/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# The local invariant of a finite normal layer of the units formation

Let `K` be a field with separable closure `Kˢ` and absolute Galois group `G_K`, and let
`V ◁ U` be a finite normal layer of open subgroups of `G_K` in the formation
`TauCeti.ClassFieldTheory.unitsFormation K` of `(Kˢ)ˣ`; in field notation it is the finite
Galois extension `E'/E` of the fixed fields of `U` and `V`. This file carries the second
cohomology `H²(U ⧸ V, ((Kˢ)ˣ)^V)` of the layer into the continuous cohomology
`H²(U, (Kˢ)ˣ)` of the ground subgroup by inflation (`layerInfl`), and, for a nonarchimedean local
field `K`, composes with the local invariant `TauCeti.ClassFieldTheory.subgroupInvMap` of `U` to
obtain the **invariant of the layer**

`inv_{E'/E} : H²(U ⧸ V, ((Kˢ)ˣ)^V) → ℚ/ℤ`

(`layerInv`). This is the invariant map of a layer that the class-formation axioms for
`unitsFormation K` constrain, and this file proves the properties of it that come from Hilbert 90
and from the restriction and corestriction squares of the local invariant:

* it is injective (`layerInv_injective`), because inflation into `H²(U, (Kˢ)ˣ)` is injective by
  Hilbert 90 for `V` (`layerInfl_injective`);
* its values have order dividing the degree `[U : V]` (`degree_nsmul_layerInv`), because
  restriction to `V` kills inflated classes (`explicitMap2_layerInfl_eq_zero`) and multiplies
  the invariant by `[U : V]`;
* restriction to an intermediate ground field multiplies it by the relative degree
  (`layerInv_cohomologyRes`), and inflation to a larger top field does not change it
  (`layerInv_cohomologyInfl`), because inflation into the cohomology of the ground subgroup is
  compatible with both operations on layers (`layerInfl_cohomologyRes`,
  `layerInfl_cohomologyInfl`).

## Main definitions

* `TauCeti.ClassFieldTheory.layerInfl L`: inflation `H²(U ⧸ V, ((Kˢ)ˣ)^V) → H²(U, (Kˢ)ˣ)` from a
  layer of the units formation, for every field `K`.
* `TauCeti.ClassFieldTheory.layerCocycle L c`: the continuous `2`-cocycle on `U` inflated from a
  layer cocycle `c`, which represents `layerInfl L [c]` (`layerInfl_H2π`).
* `TauCeti.ClassFieldTheory.layerInv K L`: the invariant of a layer, for a nonarchimedean local
  field `K`.

## Main results

* `TauCeti.ClassFieldTheory.layerInfl_injective`: inflation from a layer is injective.
* `TauCeti.ClassFieldTheory.layerInv_injective`: the invariant of a layer is injective.
* `TauCeti.ClassFieldTheory.degree_nsmul_layerInv`: the invariant of a layer is killed by its
  degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyRes`: restriction multiplies the invariant by the
  relative degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyInfl`: inflation preserves the invariant.

## Implementation notes

The continuous cohomology of the ground subgroup is that of its underlying subgroup
`L.ground.toSubgroup` of `G_K`, as in `TauCeti.ClassFieldTheory.subgroupInvMap`, and the Galois
group of the layer is read as the quotient of that subgroup by
`L.top.toSubgroup.subgroupOf L.ground.toSubgroup`; this quotient is definitionally the Galois
group `L.Gal` of the layer.

The construction of `layerInfl` follows that of `TauCeti.ClassFieldTheory.layerBrLevelEquiv` and
`TauCeti.ClassFieldTheory.brInfl` in `TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation`,
which inflate from a layer `V ◁ G_K` whose ground is the whole absolute Galois group into
`Br K = H²(G_K, (Kˢ)ˣ)`; this file extends it to layers with an arbitrary open ground subgroup.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter XI, §1 and Chapter XIII, §3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7), for
  the injectivity of inflation in degree two.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open groupCohomology ContCohomology

variable {K : Type} [Field K]

/-! ### Inflation from a layer to its ground subgroup -/

section Inflation

variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- The second cohomology of a layer as the explicit `H²` of its finite Galois group, with
coefficients the fixed points of its top subgroup in `(Kˢ)ˣ`. -/
private def layerH2Equiv :
    L.H (unitsFormation K) 2 ≃+
      H2 (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
          (UnitsCoeff K)) :=
  (groupCohomology.mapIso (MulEquiv.refl L.Gal :
      L.Gal ≃* (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup))
    (layerCoeffEquiv L).toIntLinearEquiv
    (fun g => LinearMap.ext fun x => layerCoeffEquiv_ρ L g x) 2).toLinearEquiv.toAddEquiv.trans
    (explicitH2IsoGroupCohomology
      (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (UnitsCoeff K))).symm

/-- **Inflation from a layer to its ground subgroup**: for a finite normal layer `V ◁ U` of the
formation of units, the map `H²(U ⧸ V, ((Kˢ)ˣ)^V) → H²(U, (Kˢ)ˣ)` into the continuous cohomology
of `U`. It is injective (`layerInfl_injective`), and on the class of a cocycle `c` it is the class
of `layerCocycle L c` (`layerInfl_H2π`). -/
def layerInfl : L.H (unitsFormation K) 2 →+ H2 L.ground.toSubgroup (UnitsCoeff K) :=
  (explicitInfl2 L.ground.toSubgroup (UnitsCoeff K)
    (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)).comp (layerH2Equiv L).toAddMonoidHom

/-- A layer cocycle, read with values in the fixed points of the top subgroup. -/
private def levelCocycle (c : cocycles₂ (L.rep (unitsFormation K))) :
    Z2 (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (UnitsCoeff K)) :=
  ⟨fun q => layerCoeffEquiv L (c q), mem_Z2_iff.2 ⟨continuous_of_discreteTopology,
    fun g h j => by
      have hc := congrArg (layerCoeffEquiv L) ((mem_cocycles₂_iff c).1 c.2 g h j)
      rw [map_add, map_add] at hc
      exact hc.trans (congrArg (· + _) (layerCoeffEquiv_ρ L g (c (h, j))))⟩⟩

private theorem layerH2Equiv_H2π (c : cocycles₂ (L.rep (unitsFormation K))) :
    layerH2Equiv L (H2π _ c) = (levelCocycle L c : H2 _ _) := by
  refine (AddEquiv.symm_apply_eq _).2 ((groupCohomology.H2π_comp_map_apply _ _ c).trans
    (Eq.trans ?_ (explicitH2IsoGroupCohomology_mk
      (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (UnitsCoeff K)) _).symm))
  exact congrArg _ (Subtype.ext (funext fun q =>
    (congrFun (Z2AddEquivCocycles₂_coe _ _ (levelCocycle L c)) q).symm))

/-- The **inflated cocycle** of a `2`-cocycle `c` of a layer: the continuous `2`-cocycle
`(u, v) ↦ c (u V, v V)` on the ground subgroup `U`, with values in `(Kˢ)ˣ`
(`layerCocycle_apply`). Its class is `layerInfl L [c]` (`layerInfl_H2π`). -/
def layerCocycle (c : cocycles₂ (L.rep (unitsFormation K))) :
    Z2 L.ground.toSubgroup (UnitsCoeff K) :=
  cocyclesMap2 _ _ _ _ (ContinuousMonoidHom.quotientMk _)
    (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
      (UnitsCoeff K)).subtype
    (continuous_fixedPoints_addSubgroup_subtype _ _ _) (subtype_quotientMk_smul _ _ _)
    (levelCocycle L c)

/-- The values of the inflated cocycle are the values of the layer cocycle at the classes of the
two arguments. -/
@[simp]
theorem layerCocycle_apply (c : cocycles₂ (L.rep (unitsFormation K)))
    (u v : L.ground.toSubgroup) :
    (layerCocycle L c : L.ground.toSubgroup × L.ground.toSubgroup → UnitsCoeff K) (u, v) =
      (unitsCoeffEquivUnitsFormation K).symm
        (c ((u : L.Gal), (v : L.Gal)) : (unitsFormation K).level L.top) := by
  rw [layerCocycle, cocyclesMap2_apply]
  exact layerCoeffEquiv_apply_coe L _

/-- **Inflation on cocycle classes**: `layerInfl L` sends the class of a layer cocycle `c` to the
class of the inflated cocycle `layerCocycle L c`. -/
@[simp]
theorem layerInfl_H2π (c : cocycles₂ (L.rep (unitsFormation K))) :
    layerInfl L (H2π _ c) = (layerCocycle L c : H2 _ _) := by
  rw [layerInfl, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, layerH2Equiv_H2π,
    explicitInfl2_mk]
  rfl

/-- Hilbert 90 for the top subgroup `V`, read as a subgroup of the ground subgroup `U`. -/
private theorem subsingleton_H1_top :
    Subsingleton (H1 (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (UnitsCoeff K)) := by
  have := subsingleton_H1_unitsCoeff_of_isClosed K L.top.toSubgroup L.top.isClosed
  let φ : (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) ≃ₜ* L.top.toSubgroup :=
    { toMulEquiv := Subgroup.subgroupOfEquivOfLe (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (explicitMap1Equiv _ _ _ _ φ (AddEquiv.refl (UnitsCoeff K)) continuous_id continuous_id
    fun _ _ => rfl).symm.injective.subsingleton

/-- **Inflation from a layer to its ground subgroup is injective**: by Hilbert 90 for the top
subgroup, the transgression into `H²(U ⧸ V, ((Kˢ)ˣ)^V)` vanishes. -/
theorem layerInfl_injective : Function.Injective (layerInfl L) := by
  have := subsingleton_H1_top L
  exact (explicitInfl2_injective_of_subsingleton _ _ _
    (Subgroup.isClosed_of_isOpen _
      (L.ground.toSubgroup.subgroupOf_isOpen L.top.toSubgroup L.top.isOpen))).comp
    (layerH2Equiv L).injective

/-- **Restriction to the top subgroup kills inflated classes**: restricting `layerInfl L x` from
the ground subgroup `U` to the top subgroup `V` gives `0`. -/
@[simp]
theorem explicitMap2_layerInfl_eq_zero (x : L.H (unitsFormation K) 2) :
    explicitMap2 L.ground.toSubgroup (UnitsCoeff K) L.top.toSubgroup (UnitsCoeff K)
      (ContinuousMonoidHom.subgroupInclusion (OpenSubgroup.toSubgroup_le.2 L.top_le_ground))
      (AddMonoidHom.id _) continuous_id (fun _ _ => rfl) (layerInfl L x) = 0 := by
  -- Restriction to `V` as a subgroup of `G_K` is restriction to `V` as a subgroup of `U`, which
  -- kills inflation (`explicitRes2_comp_explicitInfl2`), followed by pullback along
  -- `Subgroup.subgroupOfContinuousMulEquivOfLe`.
  have h0 : explicitRes2 L.ground.toSubgroup (UnitsCoeff K)
      (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (layerInfl L x) = 0 :=
    DFunLike.congr_fun (explicitRes2_comp_explicitInfl2 L.ground.toSubgroup (UnitsCoeff K)
      (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)) (layerH2Equiv L x)
  have h1 := explicitMap2_comp L.ground.toSubgroup (UnitsCoeff K)
    (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (UnitsCoeff K)
    (ContinuousMonoidHom.subgroupSubtype _) (AddMonoidHom.id _) continuous_id
    (id_subgroupSubtype_smul _ _ _) L.top.toSubgroup (UnitsCoeff K)
    ((Subgroup.subgroupOfContinuousMulEquivOfLe
      (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)).symm : _ →ₜ* _)
    (AddMonoidHom.id _) continuous_id fun _ _ => rfl
  rw [← explicitRes2_eq_explicitMap2] at h1
  refine (DFunLike.congr_fun (explicitMap2_congr_of_eq _ _ _ _ _ _ _ _ ?_ ?_) _).trans
    ((DFunLike.congr_fun h1 _).trans ?_)
  · exact ContinuousMonoidHom.ext fun _ => rfl
  · exact AddMonoidHom.ext fun _ => rfl
  · rw [AddMonoidHom.comp_apply, h0, map_zero]

/-- **Inflation commutes with restriction of layers**: for a restriction `V ◁ U' ≤ U` of a layer
`V ◁ U` to an intermediate ground subgroup, inflating the restricted class to `U'` is restricting
the inflated class from `U` to `U'`. -/
theorem layerInfl_cohomologyRes {small big : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRestriction small big) (x : big.H (unitsFormation K) 2) :
    layerInfl small (T.cohomologyRes (unitsFormation K) 2 x) =
      explicitMap2 big.ground.toSubgroup (UnitsCoeff K) small.ground.toSubgroup (UnitsCoeff K)
        (ContinuousMonoidHom.subgroupInclusion T.ground_toSubgroup_le) (AddMonoidHom.id _)
        continuous_id (fun _ _ => rfl) (layerInfl big x) := by
  induction x using H2_induction_on with
  | h c =>
    rw [LayerRestriction.cohomologyRes_def, H2π_comp_map_apply, layerInfl_H2π]
    refine Eq.trans ?_ (congrArg _ (layerInfl_H2π big c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    refine congrArg _ (Subtype.ext (funext fun p => Eq.trans ?_
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm))
    obtain ⟨u, v⟩ := p
    refine (layerCocycle_apply small _ u v).trans
      (Eq.trans (congrArg _ ?_) (layerCocycle_apply big c _ _).symm)
    exact (T.repIso_inv_apply_coe (unitsFormation K) _).trans
      (congrArg (fun q =>
        ((c q : (unitsFormation K).level big.top) : (unitsFormation K).toRep.V))
        (Prod.ext (T.galHom_mk u) (T.galHom_mk v)))

/-- **Inflation commutes with refinement of layers**: for a refinement of `V ◁ U` to `V' ◁ U`, the
class inflated from `V' ◁ U` of the refined class is the class inflated from `V ◁ U`, read along
the identification of the two ground subgroups. -/
theorem layerInfl_cohomologyInfl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (unitsFormation K) 2) :
    layerInfl new (T.cohomologyInfl (unitsFormation K) 2 x) =
      explicitMap2 old.ground.toSubgroup (UnitsCoeff K) new.ground.toSubgroup (UnitsCoeff K)
        (ContinuousMonoidHom.subgroupInclusion T.same_ground_toSubgroup.ge) (AddMonoidHom.id _)
        continuous_id (fun _ _ => rfl) (layerInfl old x) := by
  induction x using H2_induction_on with
  | h c =>
    rw [LayerRefinement.cohomologyInfl_def, H2π_comp_map_apply, layerInfl_H2π]
    refine Eq.trans ?_ (congrArg _ (layerInfl_H2π old c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    refine congrArg _ (Subtype.ext (funext fun p => Eq.trans ?_
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm))
    obtain ⟨u, v⟩ := p
    refine (layerCocycle_apply new _ u v).trans
      (Eq.trans (congrArg _ ?_) (layerCocycle_apply old c _ _).symm)
    exact (T.repHom_hom_apply_coe (unitsFormation K) _).trans
      (congrArg (fun q =>
        ((c q : (unitsFormation K).level old.top) : (unitsFormation K).toRep.V))
        (Prod.ext (T.galHom_mk u) (T.galHom_mk v)))

end Inflation

/-! ### The invariant of a layer of the formation of units of a local field -/

section Invariant

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : NormalLayer (AbsoluteGaloisGroup K))

/-- **The invariant of a layer** `V ◁ U` of the formation of units of a nonarchimedean local
field `K`: inflation `layerInfl` into `H²(U, (Kˢ)ˣ)` followed by the local invariant
`subgroupInvMap` of the open subgroup `U`. In field notation it is the invariant
`inv_{E'/E} : H²(Gal(E'/E), E'ˣ) → ℚ/ℤ` of the finite Galois extension `E'/E` that the layer cuts
out. It is injective (`layerInv_injective`) with values killed by the degree
(`degree_nsmul_layerInv`). -/
def layerInv : L.H (unitsFormation K) 2 →+ AddCircle (1 : ℚ) :=
  (subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).toAddMonoidHom.comp (layerInfl L)

/-- The invariant of a layer is the local invariant of the ground subgroup on the inflated
class. -/
theorem layerInv_apply (x : L.H (unitsFormation K) 2) :
    layerInv K L x = subgroupInvMap K L.ground.toSubgroup L.ground.isOpen (layerInfl L x) :=
  (rfl)

/-- **The invariant of a layer is injective.** -/
theorem layerInv_injective : Function.Injective (layerInv K L) :=
  (subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).injective.comp (layerInfl_injective L)

/-- **The invariant of a layer is killed by its degree**: `[U : V] • inv_{E'/E} x = 0`, so the
invariants of a layer lie in the subgroup of `ℚ/ℤ` of order `[U : V]`. -/
theorem degree_nsmul_layerInv (x : L.H (unitsFormation K) 2) :
    L.degree • layerInv K L x = 0 := by
  rw [layerInv_apply, L.degree_eq_relIndex, ← subgroupInvMap_explicitMap2_subgroupInclusion K
    L.ground.toSubgroup L.top.toSubgroup L.ground.isOpen L.top.isOpen
    (OpenSubgroup.toSubgroup_le.2 L.top_le_ground), explicitMap2_layerInfl_eq_zero, map_zero]

/-- **Restriction multiplies the invariant by the relative degree**: for a restriction of a layer
to an intermediate ground field `E''`, `inv_{E'/E''} (res x) = [E'' : E] • inv_{E'/E} x`. -/
@[simp]
theorem layerInv_cohomologyRes {small big : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRestriction small big) (x : big.H (unitsFormation K) 2) :
    layerInv K small (T.cohomologyRes (unitsFormation K) 2 x) =
      T.relativeDegree • layerInv K big x := by
  rw [layerInv_apply, layerInfl_cohomologyRes, subgroupInvMap_explicitMap2_subgroupInclusion,
    LayerRestriction.relativeDegree_def, layerInv_apply]

/-- **Inflation preserves the invariant**: for a refinement of a layer to a larger top field,
`inv (infl x) = inv x`. -/
@[simp]
theorem layerInv_cohomologyInfl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (unitsFormation K) 2) :
    layerInv K new (T.cohomologyInfl (unitsFormation K) 2 x) = layerInv K old x := by
  rw [layerInv_apply, layerInfl_cohomologyInfl, subgroupInvMap_explicitMap2_subgroupInclusion,
    Subgroup.relIndex_eq_one.2 T.same_ground_toSubgroup.le, one_smul, layerInv_apply]

end Invariant

end TauCeti.ClassFieldTheory
