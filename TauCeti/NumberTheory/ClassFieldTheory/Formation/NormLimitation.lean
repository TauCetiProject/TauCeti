/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.TrivialLayer
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Norms along a refinement and the norm limitation theorem

Let `F ⊆ K ⊆ L` be a tower inside a formation, so that the layer `L/F` refines the layer `K/F`:
both have ground subgroup `U = G_F`, and the top subgroup shrinks from `V = G_K` to `V' = G_L`.
The norm of the larger layer factors through the smaller one,

```text
N_{L/F} = N_{K/F} ∘ N_{L/K},
```

where `N_{L/K} : A^{V'} → A^V` is the norm between the two top levels
(`LayerRefinement.topNorm`). Consequently every norm from the larger layer is a norm from the
smaller one (`LayerRefinement.normSubgroup_le_map`).

The layers `V ◁ G` of the open normal subgroups `V` of `G` all have the ground level `A^G`, the
level of the ground field. Reading their norm subgroups there gives one family
`Formation.normSubgroup F V` of subgroups of `A^G`, indexed by `V`, which is monotone in `V`
(`Formation.normSubgroup_mono`) and equal to `A^G` for `V = G` (`Formation.normSubgroup_top`).

For a class formation the two norm subgroups have finite index equal to the orders of the
abelianized Galois groups (`ClassFormation.natCard_normQuotient_eq_natCard_abelianization`), so
the inclusion is an equality exactly when those orders agree
(`ClassFormation.map_normSubgroup_eq_iff`). Applied to an open normal subgroup `V` and its
maximal abelian sublayer `V · closure [G, G]`, whose Galois group `G ⧸ (V · closure [G, G])` has
the same order as `(G ⧸ V)^ab`
(`OpenNormalSubgroup.natCard_abelianization_gal_eq_degree_maximalAbelianLayer`), this
is the **norm limitation theorem** (`ClassFormation.normSubgroup_maximalAbelianLayer`): a layer and
its maximal abelian sublayer have the same norm subgroup in `A^G`. It is a consequence of
reciprocity, not of an existence theorem, and it is why a norm subgroup can only determine an
abelian layer.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRefinement.topNorm`: the norm `A^{V'} → A^V` between the top
  levels of a refinement.
* `TauCeti.ClassFieldTheory.Formation.normSubgroup`: the norm subgroup of the layer `V ◁ G`, read
  in the level `A^G`.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.norm_apply_coe_eq_explicitCor0Le`: the norm of a layer
  is relative degree-zero corestriction from its top subgroup to its ground subgroup.
* `TauCeti.ClassFieldTheory.LayerRefinement.topNorm_trans`: top-level norms compose along a
  tower of refinements.
* `TauCeti.ClassFieldTheory.LayerRefinement.groundEquiv_norm_topNorm`: transitivity of the norm
  along a refinement.
* `TauCeti.ClassFieldTheory.LayerRefinement.normSubgroup_le_map`: refining a layer shrinks its
  norm subgroup.
* `TauCeti.ClassFieldTheory.Formation.mem_normSubgroup_iff_mem_map`: the norm subgroup of `V ◁ G`
  read in the ground level of a refinement `V' ◁ G`.
* `TauCeti.ClassFieldTheory.Formation.normSubgroup_mono`: the norm subgroup of `V ◁ G` is monotone
  in `V`.
* `TauCeti.ClassFieldTheory.ClassFormation.map_normSubgroup_eq_iff`: in a class formation a
  refinement keeps the norm subgroup exactly when it keeps the order of the abelianized Galois
  group.
* `TauCeti.ClassFieldTheory.ClassFormation.normSubgroup_maximalAbelianLayer`: norm limitation.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J. Neukirch, *Class Field Theory*, Chapter III, Theorem 5.5 (Corollary).
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction Subgroup.fintypeQuotientOfFiniteIndex

/-! ### The norm of a layer as a level norm -/

namespace NormalLayer

variable (L : NormalLayer G) (F : Formation G)

-- `dsimp% only` on the left-hand side, as explained in the implementation notes of
-- `Formation/Basic.lean`.
/-- The norm `N_{U/V} : A^V → A^U` of a layer is Tau Ceti's relative degree-zero corestriction
`ContCohomology.explicitCor0Le` from the top subgroup `V` to the ground subgroup `U`, read on
levels. -/
theorem norm_apply_coe_eq_explicitCor0Le (x : F.level L.top) :
    (dsimp% only (L.norm F x : F.toRep.V)) =
      (ContCohomology.explicitCor0Le G F.toRep.V L.ground.toSubgroup L.top.toSubgroup
        (OpenSubgroup.toSubgroup_le.2 L.top_le_ground) (F.levelEquivH0 L.top x) : F.toRep.V) := by
  rw [← F.levelEquivH0_levelNorm L.top_le_ground, ← toAddMonoidHom_norm,
    Formation.levelEquivH0_apply_coe, LinearMap.toAddMonoidHom_coe]

end NormalLayer

/-! ### The norm between the top levels of a refinement -/

namespace LayerRefinement

variable {old new : NormalLayer G} (T : LayerRefinement old new) (F : Formation G)

/-- The **norm** `N_{V/V'} : A^{V'} → A^V` between the top levels of a refinement, whose top
subgroup shrinks from `V` to `V'`: the norm `Formation.levelNorm` between the two top levels,
evaluated by `topNorm_apply_coe`. In field notation it is the norm `N_{L/K}` for `F ⊆ K ⊆ L`. -/
def topNorm : F.level new.top →+ F.level old.top :=
  F.levelNorm T.top_le

-- `dsimp% only` on the left-hand side, as explained in the implementation notes of
-- `Formation/Basic.lean`.
/-- The norm between the top levels of a refinement is the sum of the translates by coset
representatives, read in the ambient module: `N_{V/V'} x = ∑ ρ(g) x` over the representatives
`g = q.out` of the cosets `q ∈ V/V'`. -/
@[simp]
theorem topNorm_apply_coe (x : F.level new.top) :
    (dsimp% only (T.topNorm F x : F.toRep.V)) =
      ∑ᶠ q : old.top.toSubgroup ⧸ new.top.toSubgroup.subgroupOf old.top.toSubgroup,
        F.toRep.ρ (q.out : G) x :=
  F.levelNorm_apply_coe T.top_le x

/-- The norm along the trivial refinement is the identity. -/
@[simp]
theorem topNorm_self {L : NormalLayer G} (T : LayerRefinement L L) :
    T.topNorm F = AddMonoidHom.id (F.level L.top) :=
  F.levelNorm_self T.top_le

/-- Top-level norms compose along a tower of refinements. -/
theorem topNorm_trans {a b c : NormalLayer G} (T : LayerRefinement a b)
    (T' : LayerRefinement b c) : (T.trans T').topNorm F = (T.topNorm F).comp (T'.topNorm F) :=
  F.levelNorm_trans T.top_le T'.top_le

/-- **Transitivity of the norm along a refinement**: `N_{L/F} = N_{K/F} ∘ N_{L/K}`, the two ground
levels being identified by `groundEquiv`. -/
theorem groundEquiv_norm_topNorm (x : F.level new.top) :
    T.groundEquiv F (old.norm F (T.topNorm F x)) = new.norm F x := by
  -- The two layers share their ground subgroup; destructuring them makes that equality a
  -- substitution, after which all three norms are level norms along `V' ≤ V ≤ U`.
  obtain ⟨og, ot, oh, on⟩ := old
  obtain ⟨ng, nt, nh, nn⟩ := new
  obtain ⟨hg, ht⟩ := T
  dsimp only at hg
  subst hg
  ext
  rw [groundEquiv_apply_coe, ← LinearMap.toAddMonoidHom_coe, ← LinearMap.toAddMonoidHom_coe,
    NormalLayer.toAddMonoidHom_norm, NormalLayer.toAddMonoidHom_norm, topNorm,
    ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans]

/-- **Refining a layer shrinks its norm subgroup**: a norm from the larger top level `A^{V'}` is a
norm from the smaller top level `A^V`, so `N_{L/F}(L) ⊆ N_{K/F}(K)` for `F ⊆ K ⊆ L`. -/
theorem normSubgroup_le_map :
    new.normSubgroup F ≤ (old.normSubgroup F).map (T.groundEquiv F).toLinearMap := by
  intro y hy
  obtain ⟨x, rfl⟩ := (NormalLayer.mem_normSubgroup _ _).1 hy
  exact ⟨old.norm F (T.topNorm F x), (NormalLayer.mem_normSubgroup _ _).2 ⟨_, rfl⟩,
    T.groundEquiv_norm_topNorm F x⟩

end LayerRefinement

/-! ### The norm subgroups of the layers of open normal subgroups -/

namespace Formation

variable (F : Formation G)

/-- The **norm subgroup** of the layer `V ◁ G` of an open normal subgroup `V`, read in the level
`A^G` of the whole group through `NormalLayer.groundEquivOfOpenNormal`. In field notation it is
`N_{L/K}(A_L) ⊆ A_K` for the finite Galois extension `L/K` cut out by `V`. Unlike
`NormalLayer.normSubgroup`, which lives in the ground level of its own layer, these subgroups share
one carrier, so the norm subgroups of different `V` can be compared. -/
def normSubgroup (V : OpenNormalSubgroup G) : Submodule ℤ (F.level ⊤) :=
  ((NormalLayer.ofOpenNormal V).normSubgroup F).comap
    (NormalLayer.groundEquivOfOpenNormal F V).toLinearMap

variable {F} in
/-- An element of `A^G` lies in the norm subgroup of `V` exactly when, read in the ground level of
the layer `V ◁ G`, it lies in the norm subgroup of that layer. -/
theorem mem_normSubgroup {V : OpenNormalSubgroup G} {a : F.level ⊤} :
    a ∈ F.normSubgroup V ↔
      NormalLayer.groundEquivOfOpenNormal F V a ∈ (NormalLayer.ofOpenNormal V).normSubgroup F :=
  Iff.rfl

variable {F} in
/-- For `V' ≤ V`, an element of `A^G` lies in the norm subgroup of `V` exactly when, read in the
ground level of the finer layer `V' ◁ G`, it lies in the norm subgroup of `V ◁ G` moved there by
the ground-level identification of the refinement. -/
theorem mem_normSubgroup_iff_mem_map {V V' : OpenNormalSubgroup G} (h : V' ≤ V)
    {a : F.level ⊤} :
    a ∈ F.normSubgroup V ↔ NormalLayer.groundEquivOfOpenNormal F V' a ∈
      ((NormalLayer.ofOpenNormal V).normSubgroup F).map
        ((LayerRefinement.ofOpenNormal h).groundEquiv F).toLinearMap := by
  rw [mem_normSubgroup, ← LayerRefinement.groundEquiv_groundEquivOfOpenNormal F h a]
  exact ⟨fun ha ↦ ⟨_, ha, rfl⟩,
    fun ⟨_, hy, hya⟩ ↦ (LayerRefinement.groundEquiv _ F).injective hya ▸ hy⟩

/-- **Norm subgroups are monotone in the open normal subgroup.** If `V' ≤ V`, then the extension
cut out by `V'` contains the one cut out by `V`, and every norm from the larger extension is a norm
from the smaller one. -/
theorem normSubgroup_mono : Monotone F.normSubgroup := fun _ _ h _ ha ↦
  (mem_normSubgroup_iff_mem_map h).2 ((LayerRefinement.ofOpenNormal h).normSubgroup_le_map F ha)

/-- **The layer of the whole group has the whole level `A^G` as its norm subgroup**: it cuts out the
ground field itself, whose norm to itself is the identity. -/
@[simp]
theorem normSubgroup_top : F.normSubgroup (openNormalSubgroupTop G) = ⊤ := by
  have hV : (NormalLayer.ofOpenNormal (openNormalSubgroupTop G)).top =
      (NormalLayer.ofOpenNormal (openNormalSubgroupTop G)).ground := by
    rw [NormalLayer.top_ofOpenNormal, NormalLayer.ground_ofOpenNormal]
    exact OpenSubgroup.toSubgroup_injective (openNormalSubgroupTop_toSubgroup G)
  rw [normSubgroup, NormalLayer.normSubgroup_eq_top_of_top_eq_ground _ F hV, Submodule.comap_top]

end Formation

/-! ### Norm limitation -/

namespace ClassFormation

variable {F : Formation G} (cf : ClassFormation F) {old new : NormalLayer G}

include cf in
/-- In a class formation, **a refinement keeps the norm subgroup exactly when it keeps the order
of the abelianized Galois group.** By reciprocity the two norm quotients have the orders of the
two abelianized Galois groups, and the norm subgroup of the refined layer lies in that of the
original one. -/
theorem map_normSubgroup_eq_iff (T : LayerRefinement old new) :
    (old.normSubgroup F).map (T.groundEquiv F).toLinearMap = new.normSubgroup F ↔
      Nat.card (Abelianization old.Gal) = Nat.card (Abelianization new.Gal) := by
  have hP : Nat.card (F.level new.ground ⧸
      (old.normSubgroup F).map (T.groundEquiv F).toLinearMap) =
        Nat.card (Abelianization old.Gal) := by
    rw [← cf.natCard_normQuotient_eq_natCard_abelianization old]
    exact Nat.card_congr (Submodule.Quotient.equiv _ _ (T.groundEquiv F) rfl).toEquiv.symm
  rw [← hP, ← cf.natCard_normQuotient_eq_natCard_abelianization new]
  refine ⟨fun h ↦ by rw [h], fun h ↦ le_antisymm ?_ (T.normSubgroup_le_map F)⟩
  -- The quotient map between the two norm quotients is a surjection between finite groups of the
  -- same order, hence injective; its kernel is the larger norm subgroup modulo the smaller one.
  have : Finite (new.NormQuotient F) := Finite.of_equiv _ (cf.artinEquiv new).symm.toEquiv
  have hinj := ((Submodule.factor_surjective (T.normSubgroup_le_map F)).bijective_of_nat_card_le
    h.ge).injective
  intro y hy
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hinj
  rw [map_zero, ← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact hy

include cf in
/-- **Norm limitation.** In a class formation, the layer `V ◁ G` of an open normal subgroup and
its maximal abelian sublayer `V · closure [G, G]` have the same norm subgroup in `A^G`: the norm
group of a finite Galois extension is the norm group of its maximal abelian subextension. -/
theorem normSubgroup_maximalAbelianLayer (V : OpenNormalSubgroup G) :
    F.normSubgroup V.maximalAbelianLayer = F.normSubgroup V := by
  let T := LayerRefinement.ofOpenNormal V.le_maximalAbelianLayer
  have hlim : ((NormalLayer.ofOpenNormal V.maximalAbelianLayer).normSubgroup F).map
      (T.groundEquiv F).toLinearMap = (NormalLayer.ofOpenNormal V).normSubgroup F := by
    refine (cf.map_normSubgroup_eq_iff T).2 ?_
    rw [V.natCard_abelianization_gal_eq_degree_maximalAbelianLayer,
      Nat.card_congr
        (abelianizationGalEquiv V.isAbelianClassFieldLayer_maximalAbelianLayer).toEquiv,
      NormalLayer.degree_eq_natCard_gal]
  ext a
  rw [Formation.mem_normSubgroup_iff_mem_map V.le_maximalAbelianLayer, hlim,
    Formation.mem_normSubgroup]

end ClassFormation

end TauCeti.ClassFieldTheory
