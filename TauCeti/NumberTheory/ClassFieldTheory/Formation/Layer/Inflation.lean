/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import TauCeti.GroupTheory.GroupAction.FixedPoints
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Inflation from a finite normal layer to its ground subgroup

Let `F` be a formation on a profinite group `G` whose coefficient module is read, through an
equivariant additive equivalence `e : M ≃+ A`, on a discrete `G`-module `M`, as for the formation
of units of a field `K`, whose coefficients are read on `(Kˢ)ˣ`, or the idele formation of a number
field `K`, whose coefficients are read on the ideles of `Kˢ`. For a finite normal layer `V ◁ U` of
open subgroups of `G`, this file constructs **inflation** from the second cohomology of the layer
to the continuous second cohomology of its ground subgroup,

```text
NormalLayer.explicitInfl2 L e he : H²(U ⧸ V, M^V) → H²(U, M),
```

in the explicit inhomogeneous model of `TauCeti.ContCohomology`. On the class of a layer cocycle
`c` it is the class of the inflated cocycle `(u, v) ↦ c (u V, v V)` (`explicitInfl2_H2π`,
`inflCocycle2_apply`). It is compatible with the operations on layers: restriction to an
intermediate ground subgroup (`explicitInfl2_cohomologyRes`), refinement to a smaller top subgroup
(`explicitInfl2_cohomologyInfl`), and every map of layer cohomologies that pulls inflated cocycles
back along a compatible pair (`explicitInfl2_eq_explicitMap2_explicitInfl2`). Restriction to the
top subgroup kills inflated classes (`explicitMap2_explicitInfl2_eq_zero`), inflation is injective
when `H¹(V, M)` vanishes (`explicitInfl2_injective_of_subsingleton`), and every class of
`H²(U, M)` is inflated from a refinement of a given layer over `U` (`exists_explicitInfl2_eq`).

Inflation carries the cohomology of the finite layers into continuous cohomology, where the
local invariants and the local–global maps of a number field (localization at the places,
corestriction from the ground subgroup `U` to `G`) are defined.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2 L e he`: inflation
  `H²(U ⧸ V, M^V) → H²(U, M)`.
* `TauCeti.ClassFieldTheory.NormalLayer.inflCocycle2 L e he c`: the continuous `2`-cocycle on `U`
  inflated from a layer cocycle `c`.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_H2π`: inflation sends the class of a layer
  cocycle to the class of its inflated cocycle.
* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_injective_of_subsingleton`: inflation is
  injective when `H¹(V, M)` vanishes.
* `TauCeti.ClassFieldTheory.NormalLayer.explicitMap2_explicitInfl2_eq_zero`: restriction to the
  top subgroup kills inflated classes.
* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_cohomologyRes`,
  `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_cohomologyInfl`: inflation commutes with the
  restriction and the refinement of layers.
* `TauCeti.ClassFieldTheory.NormalLayer.exists_explicitInfl2_eq`: every class of `H²(U, M)` is
  inflated from a refinement of a given layer over `U`.
* `TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2_eq_explicitMap2_explicitInfl2`: inflation is
  natural along maps of layer cohomology that pull back inflated cocycles along a compatible pair.

## Implementation notes

The continuous cohomology of the ground subgroup is that of its underlying subgroup
`L.ground.toSubgroup` of `G`, and the Galois group of the layer is read as the quotient of that
subgroup by `L.top.toSubgroup.subgroupOf L.ground.toSubgroup`; this quotient is definitionally the
Galois group `L.Gal = L.ground ⧸ L.relativeTop` of the layer, which is why `MulEquiv.refl` can
identify the two in the private `h2EquivExplicit`. The coefficient module `A^V` of the layer is read
as the fixed points `M^V` through `TauCeti.ClassFieldTheory.NormalLayer.coeffFixedPointsEquiv`.

The construction follows that of `TauCeti.ClassFieldTheory.layerBrLevelEquiv` and
`TauCeti.ClassFieldTheory.brInfl` in `TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation`,
which inflate from a layer `V ◁ G_K` of the formation of units, whose ground is the whole absolute
Galois group, into `Br K = H²(G_K, (Kˢ)ˣ)`. This file extends it to layers with an arbitrary open
ground subgroup and to an arbitrary coefficient dictionary `e`; the local invariant of a layer in
`TauCeti.NumberTheory.ClassFieldTheory.Brauer.LayerInvariant` uses it for the formation of units.

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

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The second cohomology of a layer as the explicit `H²` of its finite Galois group, with
coefficients the fixed points of its top subgroup in `M`. -/
private def h2EquivExplicit :
    L.H F 2 ≃+
      H2 (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M) :=
  (groupCohomology.mapIso (MulEquiv.refl L.Gal :
      L.Gal ≃* (L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup))
    (L.coeffFixedPointsEquiv e he).toIntLinearEquiv
    (fun g => LinearMap.ext fun x => L.coeffFixedPointsEquiv_ρ e he g x)
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
  ⟨fun q => L.coeffFixedPointsEquiv e he (c q), mem_Z2_iff.2 ⟨continuous_of_discreteTopology,
    fun g h j => by
      have hc := congrArg (L.coeffFixedPointsEquiv e he) ((mem_cocycles₂_iff c).1 c.2 g h j)
      rw [map_add, map_add] at hc
      exact hc.trans (congrArg (· + _) (L.coeffFixedPointsEquiv_ρ e he g (c (h, j))))⟩⟩

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
  exact L.coeffFixedPointsEquiv_apply_coe e he _

/-- **Inflation on cocycle classes**: `explicitInfl2 L e he` sends the class of a layer cocycle `c`
to the class of the inflated cocycle `inflCocycle2 L e he c`. -/
@[simp]
theorem explicitInfl2_H2π (c : cocycles₂ (L.rep F)) :
    L.explicitInfl2 e he (H2π _ c) = (inflCocycle2 L e he c : H2 _ _) := by
  rw [explicitInfl2, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2EquivExplicit_H2π,
    explicitInfl2_mk]
  rfl

/-- **Inflation from a layer is injective when `H¹(V, M)` vanishes**: the transgression into
`H²(U ⧸ V, M^V)` then vanishes. For the formation of units this is Hilbert 90 for `V`. -/
theorem explicitInfl2_injective_of_subsingleton
    [Subsingleton (H1 (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M)] :
    Function.Injective (L.explicitInfl2 e he) :=
  (ContCohomology.explicitInfl2_injective_of_subsingleton _ _ _
    (Subgroup.isClosed_of_isOpen _
      (L.ground.toSubgroup.subgroupOf_isOpen L.top.toSubgroup L.top.isOpen))).comp
    (h2EquivExplicit L e he).injective

/-- **Restriction to the top subgroup kills inflated classes**: restricting
`L.explicitInfl2 e he x` from the ground subgroup `U` to the top subgroup `V` gives `0`. -/
@[simp]
theorem explicitMap2_explicitInfl2_eq_zero (x : L.H F 2) :
    explicitMap2 L.ground.toSubgroup M L.top.toSubgroup M
      (ContinuousMonoidHom.subgroupInclusion (OpenSubgroup.toSubgroup_le.2 L.top_le_ground))
      (AddMonoidHom.id _) continuous_id (fun _ _ => rfl) (L.explicitInfl2 e he x) = 0 := by
  -- Restriction to `V` as a subgroup of `G` is restriction to `V` as a subgroup of `U`, which
  -- kills inflation (`explicitRes2_comp_explicitInfl2`), followed by pullback along
  -- `Subgroup.subgroupOfContinuousMulEquivOfLe`.
  have h0 : explicitRes2 L.ground.toSubgroup M
      (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (L.explicitInfl2 e he x) = 0 :=
    DFunLike.congr_fun (explicitRes2_comp_explicitInfl2 L.ground.toSubgroup M
      (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)) (h2EquivExplicit L e he x)
  have h1 := explicitMap2_comp L.ground.toSubgroup M
    (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) M
    (ContinuousMonoidHom.subgroupSubtype _) (AddMonoidHom.id _) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul _ _) L.top.toSubgroup M
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
theorem explicitInfl2_cohomologyRes {small big : NormalLayer G} (T : LayerRestriction small big)
    (x : big.H F 2) :
    small.explicitInfl2 e he (T.cohomologyRes F 2 x) =
      explicitMap2 big.ground.toSubgroup M small.ground.toSubgroup M
        (ContinuousMonoidHom.subgroupInclusion T.ground_toSubgroup_le) (AddMonoidHom.id _)
        continuous_id (fun _ _ => rfl) (big.explicitInfl2 e he x) := by
  induction x using H2_induction_on with
  | h c =>
    rw [LayerRestriction.cohomologyRes_def, H2π_comp_map_apply, explicitInfl2_H2π]
    refine Eq.trans ?_ (congrArg _ (explicitInfl2_H2π big e he c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    refine congrArg _ (Subtype.ext (funext fun p => Eq.trans ?_
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm))
    obtain ⟨u, v⟩ := p
    refine (inflCocycle2_apply small e he _ u v).trans
      (Eq.trans (congrArg _ ?_) (inflCocycle2_apply big e he c _ _).symm)
    exact (T.repIso_inv_apply_coe F _).trans
      (congrArg (fun q => ((c q : F.level big.top) : F.toRep.V))
        (Prod.ext (T.galHom_mk u) (T.galHom_mk v)))

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

/-- **Every class of `H²(U, M)` is inflated from a refinement of a given layer over `U`.**
For a layer `V ◁ U` and a class `c` in the continuous cohomology of its ground subgroup, there is a
layer `V' ◁ U` with `V' ≤ V` from whose `H²` the class `c` is inflated. The class `c` is read on the
ground subgroup of the refinement, which is `U` again. -/
theorem exists_explicitInfl2_eq (c : H2 L.ground.toSubgroup M) :
    ∃ (L' : NormalLayer G) (T : LayerRefinement L L') (y : L'.H F 2),
      L'.explicitInfl2 e he y =
        explicitMap2 L.ground.toSubgroup M L'.ground.toSubgroup M
          (ContinuousMonoidHom.subgroupInclusion T.same_ground_toSubgroup.ge) (AddMonoidHom.id _)
          continuous_id (fun _ _ => rfl) c := by
  -- The class is inflated from a finite quotient `U ⧸ N`; an open normal subgroup `W` of `G`
  -- inside both `N` and `V` gives a layer `W ◁ U` refining `V ◁ U` whose quotient refines `U ⧸ N`.
  obtain ⟨N, y, rfl⟩ := ContCohomology.exists_explicitInfl2_eq c
  let S : Set G := Subtype.val '' (N : Set L.ground.toSubgroup) ∩ (L.top : Set G)
  have hS : IsOpen S := (L.ground.isOpen.isOpenMap_subtype_val _ N.isOpen).inter L.top.isOpen
  have h1 : (1 : G) ∈ S := ⟨⟨1, N.one_mem, rfl⟩, L.top.one_mem⟩
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  have hWV : W.toOpenSubgroup ≤ L.top := fun w hw => (hW hw).2
  let L' : NormalLayer G :=
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
    (h2EquivExplicit L' e he).symm
      (explicitFiniteQuotientTransition2 L.ground.toSubgroup M N N' hN' y), ?_⟩
  -- `L'.explicitInfl2 e he` is inflation along `U → U ⧸ N'` after `h2EquivExplicit L' e he`, and
  -- the class read on the ground subgroup of `L'`, which is `U` itself, is unchanged.
  simp only [NormalLayer.explicitInfl2, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  refine (congrArg (ContCohomology.explicitInfl2 L.ground.toSubgroup M N'.toSubgroup)
      (AddEquiv.apply_symm_apply _ _)).trans <|
    (explicitInfl2_explicitFiniteQuotientTransition2 hN' y).trans ?_
  exact ((DFunLike.congr_fun (explicitMap2_congr_of_eq _ _ _ _ _ (ContinuousMonoidHom.id _) _
    (AddMonoidHom.id _) (hψ := fun _ _ => rfl) (ContinuousMonoidHom.ext fun _ => rfl) rfl) _).trans
    (DFunLike.congr_fun (explicitMap2_id _ _) _)).symm

/-- **Inflation is natural along maps that pull back inflated cocycles**: let `V ◁ U` be a layer
of `F` and `V' ◁ U'` a layer of a formation `F'` on `G'` read on `M'` through `e'`, and let
`(f, φ)` be a compatible pair from `(U, M)` to `(U', M')`. If a map `Ψ` of layer cohomologies
sends the class of each layer cocycle `c` to the class of a layer cocycle whose inflated cocycle is
the inflated cocycle of `c` pulled back along `(f, φ)`, then inflating `Ψ x` to `U'` is pulling back
the inflation of `x`. -/
theorem explicitInfl2_eq_explicitMap2_explicitInfl2 {G' : Type} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [CompactSpace G'] [TotallyDisconnectedSpace G'] {F' : Formation G'}
    {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
    [DiscreteTopology M'] [ContinuousSMul G' M'] (e' : M' ≃+ F'.toRep.V)
    (he' : ∀ (g : G') (x : M'), e' (g • x) = F'.toRep.ρ g (e' x)) {L' : NormalLayer G'}
    (f : L'.ground.toSubgroup →ₜ* L.ground.toSubgroup) (φ : M →+ M')
    (hφ : ∀ (u : L'.ground.toSubgroup) (m : M), φ (f u • m) = u • φ m)
    (Ψ : L.H F 2 → L'.H F' 2)
    (hΨ : ∀ c : cocycles₂ (L.rep F), ∃ c' : cocycles₂ (L'.rep F'), Ψ (H2π _ c) = H2π _ c' ∧
      inflCocycle2 L' e' he' c' = cocyclesMap2 L.ground.toSubgroup M L'.ground.toSubgroup M' f φ
        continuous_of_discreteTopology hφ (inflCocycle2 L e he c))
    (x : L.H F 2) :
    L'.explicitInfl2 e' he' (Ψ x) =
      explicitMap2 L.ground.toSubgroup M L'.ground.toSubgroup M' f φ
        continuous_of_discreteTopology hφ (L.explicitInfl2 e he x) := by
  induction x using H2_induction_on with
  | h c =>
    obtain ⟨c', hc, hc'⟩ := hΨ c
    rw [hc, explicitInfl2_H2π]
    refine Eq.trans ?_ (congrArg _ (explicitInfl2_H2π L e he c)).symm
    refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
    exact congrArg (fun z : Z2 L'.ground.toSubgroup M' => (z : H2 L'.ground.toSubgroup M')) hc'

end NormalLayer

end TauCeti.ClassFieldTheory
