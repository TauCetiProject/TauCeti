/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Conjugation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.NumberTheory.ClassFieldTheory.Formation.InflationRestriction
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

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
  `layerInfl_cohomologyInfl`);
* its range is exactly the subgroup of `ℚ/ℤ` of order `[U : V]` (`range_layerInv`). Every class
  of `H²(U, (Kˢ)ˣ)` is inflated from a layer `V' ◁ U` with `V' ≤ V` (`exists_layerInfl_eq`), and
  by the inflation-restriction sequence of the refinement `V' ◁ U` of `V ◁ U`
  (`LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`) together with Hilbert 90, a class
  of `V' ◁ U` whose restriction to `V' ◁ V` vanishes comes from `V ◁ U`;
* conjugation by `g : G_K` preserves it (`layerInv_conjugateCohomologyIso`), because inflation
  carries the conjugation of layers to the conjugation `H²(U, (Kˢ)ˣ) → H²(gUg⁻¹, (Kˢ)ˣ)`, which
  preserves the local invariant (`subgroupInvMap_explicitMap2_of_conj`).

## Main definitions

* `TauCeti.ClassFieldTheory.layerInfl L`: inflation `H²(U ⧸ V, ((Kˢ)ˣ)^V) → H²(U, (Kˢ)ˣ)` from a
  layer of the units formation, for every field `K`.
* `TauCeti.ClassFieldTheory.layerCocycle L c`: the continuous `2`-cocycle on `U` inflated from a
  layer cocycle `c`, which represents `layerInfl L [c]` (`layerInfl_H2π`).
* `TauCeti.ClassFieldTheory.layerInv K L`: the invariant of a layer, for a nonarchimedean local
  field `K`.

## Main results

* `TauCeti.ClassFieldTheory.layerInfl_injective`: inflation from a layer is injective.
* `TauCeti.ClassFieldTheory.layerInfl_eq_explicitMap2_layerInfl`: inflation is natural along
  maps of layer cohomology that pull back inflated cocycles along a compatible pair.
* `TauCeti.ClassFieldTheory.exists_layerInfl_eq`: every class of `H²(U, (Kˢ)ˣ)` is inflated from
  a refinement of a given layer over `U`.
* `TauCeti.ClassFieldTheory.layerInv_injective`: the invariant of a layer is injective.
* `TauCeti.ClassFieldTheory.degree_nsmul_layerInv`: the invariant of a layer is killed by its
  degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyRes`: restriction multiplies the invariant by the
  relative degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyInfl`: inflation preserves the invariant.
* `TauCeti.ClassFieldTheory.range_layerInv`: the invariants of a layer form the subgroup of `ℚ/ℤ`
  of order its degree.
* `TauCeti.ClassFieldTheory.layerInv_conjugateCohomologyIso`: conjugation preserves the invariant.

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

open _root_.groupCohomology ContCohomology

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
    (ContinuousMonoidHom.id_subgroupSubtype_smul _ _) L.top.toSubgroup (UnitsCoeff K)
    ((Subgroup.subgroupOfContinuousMulEquivOfLe
      (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)).symm : _ →ₜ* _)
    (AddMonoidHom.id _) continuous_id fun _ _ => rfl
  rw [← explicitRes2_eq_explicitMap2] at h1
  refine (DFunLike.congr_fun (explicitMap2_congr_of_eq _ _ _ _ _ _ _ _ ?_ ?_) _).trans
    ((DFunLike.congr_fun h1 _).trans ?_)
  · exact ContinuousMonoidHom.ext fun _ => rfl
  · exact AddMonoidHom.ext fun _ => rfl
  · simp only [AddMonoidHom.comp_apply, h0, map_zero]

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

/-- **Every class of `H²(U, (Kˢ)ˣ)` is inflated from a refinement of a given layer over `U`.**
For a layer `V ◁ U` and a class `c` in the continuous cohomology of its ground subgroup, there is a
layer `V' ◁ U` with `V' ≤ V` from whose `H²` the class `c` is inflated. The class `c` is read on the
ground subgroup of the refinement, which is `U` again. -/
theorem exists_layerInfl_eq (c : H2 L.ground.toSubgroup (UnitsCoeff K)) :
    ∃ (L' : NormalLayer (AbsoluteGaloisGroup K)) (T : LayerRefinement L L')
      (y : L'.H (unitsFormation K) 2),
      layerInfl L' y =
        explicitMap2 L.ground.toSubgroup (UnitsCoeff K) L'.ground.toSubgroup (UnitsCoeff K)
          (ContinuousMonoidHom.subgroupInclusion T.same_ground_toSubgroup.ge) (AddMonoidHom.id _)
          continuous_id (fun _ _ => rfl) c := by
  -- The class is inflated from a finite quotient `U ⧸ N`; an open normal subgroup `W` of `G_K`
  -- inside both `N` and `V` gives a layer `W ◁ U` refining `V ◁ U` whose quotient refines `U ⧸ N`.
  obtain ⟨N, y, rfl⟩ := exists_explicitInfl2_eq c
  let S : Set (AbsoluteGaloisGroup K) :=
    Subtype.val '' (N : Set L.ground.toSubgroup) ∩ (L.top : Set (AbsoluteGaloisGroup K))
  have hS : IsOpen S := (L.ground.isOpen.isOpenMap_subtype_val _ N.isOpen).inter L.top.isOpen
  have h1 : (1 : AbsoluteGaloisGroup K) ∈ S := ⟨⟨1, N.one_mem, rfl⟩, L.top.one_mem⟩
  -- Destructuring this existence statement directly in `obtain` times out at `whnf`.
  have hW := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  obtain ⟨W, hW⟩ := hW
  have hWV : W.toOpenSubgroup ≤ L.top := fun w hw => (hW hw).2
  let L' : NormalLayer (AbsoluteGaloisGroup K) :=
    { ground := L.ground
      top := W.toOpenSubgroup
      top_le_ground := hWV.trans L.top_le_ground
      normal := Subgroup.normal_subgroupOf }
  let N' : OpenNormalSubgroup L.ground.toSubgroup :=
    { toSubgroup := L'.top.toSubgroup.subgroupOf L.ground.toSubgroup
      isOpen' := L.ground.toSubgroup.subgroupOf_isOpen _ W.isOpen
      isNormal' := L'.normal }
  have hN' : N' ≤ N := fun u hu => by
    obtain ⟨v, hv, hvu⟩ := (hW (Subgroup.mem_subgroupOf.1 hu)).1
    exact Subtype.val_injective hvu ▸ hv
  refine ⟨L', ⟨rfl, hWV⟩,
    (layerH2Equiv L').symm
      (explicitFiniteQuotientTransition2 L.ground.toSubgroup (UnitsCoeff K) N N' hN' y), ?_⟩
  -- `layerInfl L'` is inflation along `U → U ⧸ N'` after `layerH2Equiv L'`, and the class read
  -- on the ground subgroup of `L'`, which is `U` itself, is unchanged.
  simp only [layerInfl, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  refine (congrArg (explicitInfl2 L.ground.toSubgroup (UnitsCoeff K) N'.toSubgroup)
      (AddEquiv.apply_symm_apply _ _)).trans <|
    (explicitInfl2_explicitFiniteQuotientTransition2 hN' y).trans ?_
  exact ((DFunLike.congr_fun (explicitMap2_congr_of_eq _ _ _ _ _ (ContinuousMonoidHom.id _) _
    (AddMonoidHom.id _) (hψ := fun _ _ => rfl) (ContinuousMonoidHom.ext fun _ => rfl) rfl) _).trans
    (DFunLike.congr_fun (explicitMap2_id _ _) _)).symm

/-- **Inflation is natural along maps that pull back inflated cocycles**: let `V ◁ U` be a layer
over `K`, `V' ◁ U'` a layer over a field `K'`, and `(f, φ)` a compatible pair from
`(U, (Kˢ)ˣ)` to `(U', (K'ˢ)ˣ)`. If a map `Ψ` of layer cohomologies sends the class of each layer
cocycle `c` to the class of a layer cocycle whose inflated cocycle is the inflated cocycle of `c`
pulled back along `(f, φ)`, then inflating `Ψ x` to `U'` is pulling back the inflation of `x`. -/
theorem layerInfl_eq_explicitMap2_layerInfl {K' : Type} [Field K']
    {L' : NormalLayer (AbsoluteGaloisGroup K')} (f : L'.ground.toSubgroup →ₜ* L.ground.toSubgroup)
    (φ : UnitsCoeff K →+ UnitsCoeff K') (hφ : ∀ (u : L'.ground.toSubgroup) (m : UnitsCoeff K),
      φ (f u • m) = u • φ m)
    (Ψ : L.H (unitsFormation K) 2 → L'.H (unitsFormation K') 2)
    (hΨ : ∀ c : cocycles₂ (L.rep (unitsFormation K)),
      ∃ c' : cocycles₂ (L'.rep (unitsFormation K')), Ψ (H2π _ c) = H2π _ c' ∧
        layerCocycle L' c' = cocyclesMap2 L.ground.toSubgroup (UnitsCoeff K) L'.ground.toSubgroup
          (UnitsCoeff K') f φ continuous_of_discreteTopology hφ (layerCocycle L c))
    (x : L.H (unitsFormation K) 2) :
    layerInfl L' (Ψ x) =
      explicitMap2 L.ground.toSubgroup (UnitsCoeff K) L'.ground.toSubgroup (UnitsCoeff K') f φ
        continuous_of_discreteTopology hφ (layerInfl L x) := by
  induction x using H2_induction_on with
  | h c =>
    obtain ⟨c', hc, hc'⟩ := hΨ c
    rw [hc, layerInfl_H2π]
    refine Eq.trans ?_ (congrArg _ (layerInfl_H2π L c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    exact congrArg (fun z : Z2 L'.ground.toSubgroup (UnitsCoeff K') =>
      (z : H2 L'.ground.toSubgroup (UnitsCoeff K'))) hc'

/-! ### Inflation and conjugation -/

section Conjugation

variable (g : AbsoluteGaloisGroup K)

/-- Inverse conjugation `v ↦ g⁻¹ v g`, from the ground subgroup `gUg⁻¹` of the conjugate layer to
the ground subgroup `U` of the layer. -/
private def conjugateGroundHom :
    (L.conjugate g).ground.toSubgroup →ₜ* L.ground.toSubgroup where
  toFun v := ⟨g⁻¹ * v * g, (L.mem_ground_conjugate g).1 v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun := ((continuous_mul_const g).comp
    ((continuous_const_mul g⁻¹).comp continuous_subtype_val)).subtype_mk _

/-- Inverse conjugation on underlying elements of `G_K`. -/
private theorem conjugateGroundHom_apply_coe (v : (L.conjugate g).ground.toSubgroup) :
    (conjugateGroundHom L g v : AbsoluteGaloisGroup K) = g⁻¹ * v * g :=
  (rfl)

/-- The action of `g` on `(Kˢ)ˣ` and inverse conjugation form a compatible pair. -/
private theorem conjugateGroundHom_smul (v : (L.conjugate g).ground.toSubgroup)
    (m : UnitsCoeff K) :
    DistribSMul.toAddMonoidHom (UnitsCoeff K) g (conjugateGroundHom L g v • m) =
      v • DistribSMul.toAddMonoidHom (UnitsCoeff K) g m := by
  rw [DistribSMul.toAddMonoidHom_apply, DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def,
    Subgroup.smul_def, conjugateGroundHom_apply_coe, smul_smul, smul_smul]
  congr 1
  group

/-- The ground subgroup of the conjugate layer is the conjugate `gUg⁻¹`. -/
private theorem toSubgroup_ground_conjugate :
    (L.conjugate g).ground.toSubgroup = L.ground.toSubgroup.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, OpenSubgroup.mem_toSubgroup,
    OpenSubgroup.mem_toSubgroup]
  exact L.mem_ground_conjugate g

/-- The coefficient dictionary carries the action of `g` on the formation to its action on
`(Kˢ)ˣ`. -/
private theorem unitsCoeffEquivUnitsFormation_symm_ρ (y : (unitsFormation K).toRep.V) :
    (unitsCoeffEquivUnitsFormation K).symm ((unitsFormation K).toRep.ρ g y) =
      DistribSMul.toAddMonoidHom (UnitsCoeff K) g ((unitsCoeffEquivUnitsFormation K).symm y) := by
  rw [AddEquiv.symm_apply_eq, DistribSMul.toAddMonoidHom_apply, unitsCoeffEquivUnitsFormation_smul,
    AddEquiv.apply_symm_apply]

/-- The inflated cocycle of a layer cocycle pulled back along a pair `(f, φ)` that acts on Galois
groups by inverse conjugation and on coefficients by `g` is the inflated cocycle, pulled back along
inverse conjugation and pushed forward by `g`. -/
private theorem layerCocycle_mapCocycles₂ (f : (L.conjugate g).Gal →* L.Gal)
    (φ : Rep.res f (L.rep (unitsFormation K)) ⟶ (L.conjugate g).rep (unitsFormation K))
    (hf : ∀ w : (L.conjugate g).ground.toSubgroup,
      f (w : (L.conjugate g).Gal) = (conjugateGroundHom L g w : L.Gal))
    (hφ : ∀ x : (L.rep (unitsFormation K)).V, (φ.hom x : (unitsFormation K).toRep.V) =
      (unitsFormation K).toRep.ρ g (x : (unitsFormation K).toRep.V))
    (c : cocycles₂ (L.rep (unitsFormation K))) (p : (L.conjugate g).ground.toSubgroup ×
      (L.conjugate g).ground.toSubgroup) :
    (layerCocycle (L.conjugate g) (mapCocycles₂ f φ c) :
        (L.conjugate g).ground.toSubgroup × (L.conjugate g).ground.toSubgroup → UnitsCoeff K) p =
      DistribSMul.toAddMonoidHom (UnitsCoeff K) g
        ((layerCocycle L c : L.ground.toSubgroup × L.ground.toSubgroup → UnitsCoeff K)
          (conjugateGroundHom L g p.1, conjugateGroundHom L g p.2)) := by
  rw [layerCocycle_apply, layerCocycle_apply, TauCeti.groupCohomology.mapCocycles₂_apply, hφ,
    unitsCoeffEquivUnitsFormation_symm_ρ, hf, hf]

/-- **Inflation commutes with conjugation**: inflating the conjugate of a class to the ground
subgroup `gUg⁻¹` of the conjugate layer is conjugating the inflated class from `U` to `gUg⁻¹`. -/
private theorem layerInfl_conjugateCohomologyIso (x : L.H (unitsFormation K) 2) :
    layerInfl (L.conjugate g) ((L.conjugateCohomologyIso (unitsFormation K) g 2).hom x) =
      explicitMap2 L.ground.toSubgroup (UnitsCoeff K) (L.conjugate g).ground.toSubgroup
        (UnitsCoeff K) (conjugateGroundHom L g) (DistribSMul.toAddMonoidHom (UnitsCoeff K) g)
        continuous_of_discreteTopology (conjugateGroundHom_smul L g) (layerInfl L x) := by
  refine layerInfl_eq_explicitMap2_layerInfl L _ _ _
    (fun y => (L.conjugateCohomologyIso (unitsFormation K) g 2).hom y) (fun c => ?_) x
  refine ⟨?_, ?hcls, ?hcocycle⟩
  case hcls =>
    rw [NormalLayer.conjugateCohomologyIso_def, groupCohomology.mapIso_hom]
    -- Rewriting with `H2π_comp_map_apply` times out here; the term is given explicitly.
    exact groupCohomology.H2π_comp_map_apply (L.conjugateGalEquiv g).symm.toMonoidHom _ c
  case hcocycle =>
    exact Subtype.ext (funext fun p => (layerCocycle_mapCocycles₂ L g _ _
      (fun w => (L.conjugateGalEquiv_symm_mk g w).trans (congrArg QuotientGroup.mk
        (Subtype.ext (L.conjugateGroundEquiv_symm_apply_coe g w))))
      (fun x => L.conjugateCoefficientEquiv_apply_coe (unitsFormation K) g x) c p).trans
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm)

end Conjugation

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

/-- **The invariants of a layer are the subgroup of `ℚ/ℤ` of order its degree**: the range of
`inv_{E'/E}` is the `[E' : E]`-torsion of `ℚ/ℤ`. Together with `layerInv_injective`, this makes
`H²(Gal(E'/E), E'ˣ)` cyclic of order `[E' : E]`. -/
@[simp]
theorem range_layerInv :
    Set.range (layerInv K L) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) L.degree : Set (AddCircle (1 : ℚ))) := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    exact AddSubgroup.torsionBy.nsmul_iff.2 (degree_nsmul_layerInv K L y)
  -- A rational `x` of order dividing `[U : V]` is the invariant of a class of `H²(U, (Kˢ)ˣ)`,
  -- which is inflated from a refinement `V' ◁ U` of the layer.
  obtain ⟨L', T, y, hy⟩ := exists_layerInfl_eq L
    ((subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).symm x)
  have hinv : layerInv K L' y = x := by
    rw [layerInv_apply, hy, subgroupInvMap_explicitMap2_subgroupInclusion K _ _ L.ground.isOpen,
      Subgroup.relIndex_eq_one.2 T.same_ground_toSubgroup.le, one_smul, AddEquiv.apply_symm_apply]
  -- Restricted to the layer of the kernel `V/V'`, the class has invariant `[U : V] • x = 0`.
  have hres : (L'.subgroupRestriction T.galHom.ker).cohomologyRes (unitsFormation K) 2 y = 0 := by
    refine layerInv_injective K _ ?_
    rw [layerInv_cohomologyRes, map_zero, hinv, L'.relativeDegree_subgroupRestriction,
      Subgroup.index_ker, MonoidHom.range_eq_top.2 T.galHom_surjective, Subgroup.card_top,
      ← NormalLayer.degree_eq_natCard_gal]
    exact AddSubgroup.torsionBy.nsmul_iff.1 hx
  -- By the inflation-restriction sequence and Hilbert 90, the class is inflated from `V ◁ U`.
  obtain ⟨z, hz⟩ : y ∈ LinearMap.range (T.cohomologyInfl (unitsFormation K) 2).hom :=
    (T.range_cohomologyInfl_eq_ker_cohomologyRes (unitsFormation K) 1 fun i hi => by
      obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
      exact subsingleton_h1_unitsFormation _).ge hres
  exact ⟨z, (layerInv_cohomologyInfl K T z).symm.trans (congrArg (layerInv K L') hz |>.trans hinv)⟩

/-- **Conjugation preserves the invariant**: for `g : G_K`, the conjugate class in the conjugate
layer `gV ◁ gU` has the same invariant, `inv_{gE'/gE} (g_* x) = inv_{E'/E} x`. -/
@[simp]
theorem layerInv_conjugateCohomologyIso (g : AbsoluteGaloisGroup K)
    (x : L.H (unitsFormation K) 2) :
    layerInv K (L.conjugate g) ((L.conjugateCohomologyIso (unitsFormation K) g 2).hom x) =
      layerInv K L x := by
  rw [layerInv_apply, layerInfl_conjugateCohomologyIso,
    subgroupInvMap_explicitMap2_of_conj K L.ground.toSubgroup (L.conjugate g).ground.toSubgroup
      L.ground.isOpen (L.conjugate g).ground.isOpen g _ (conjugateGroundHom_apply_coe L g)
      (DistribSMul.toAddMonoidHom (UnitsCoeff K) g) (DistribSMul.toAddMonoidHom_apply _ g)
      (toSubgroup_ground_conjugate L g),
    layerInv_apply]

end Invariant

end TauCeti.ClassFieldTheory
