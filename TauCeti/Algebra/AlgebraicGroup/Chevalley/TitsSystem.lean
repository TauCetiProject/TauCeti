/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Intersection
public import TauCeti.GroupTheory.TitsSystem.Comap
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Multiplication
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.DoubleCoset.Map

/-!
# The Tits system of a Chevalley datum

Over any field `K`, a Chevalley datum `D` of valid Dynkin type `t` carries a canonical Tits system
on its extended elementary subgroup `D.extendedElementarySubgroup K` with Borel subgroup
`B(K) = D.borelSubgroup K` and Weyl subgroup `N(K) = D.weylSubgroup K`. Pulling back along the
decomposition `D.extendedElementarySubgroup K = D.elementarySubgroup K · T_D(K)` also equips the
elementary Chevalley group `D.elementarySubgroup K` with its canonical Tits system.

The key geometric input is the ambient rank-one double-coset reduction in
`Chevalley.Bruhat.Multiplication` (`ChevalleyDatum.doubleCoset_weylElement_mul_subset_union`),
together with `B(K) ∩ N(K) = T_D(K)` from `Chevalley.Weyl.Intersection`. Transporting the
canonical Weyl quotient `D.weylQuotientMulEquiv K` along `D.titsSubgroupNMulEquiv K` gives the
isomorphism `D.titsWeylGroupMulEquiv K : (D.titsSystem K).WeylGroup ≃* W`.

## Main definitions and results

* `ChevalleyDatum.titsSystem` and `ChevalleyDatum.mem_titsSystem_intersection_iff`: the Tits system
  on `D.extendedElementarySubgroup K`, whose `B ∩ N` intersection consists of the points of the
  actual torus `T_D(K)`.
* `ChevalleyDatum.titsWeylGroupMulEquiv`: the isomorphism `(D.titsSystem K).WeylGroup ≃* W`.
* `ChevalleyDatum.elementaryTitsSystem`,
  `ChevalleyDatum.mem_elementaryTitsSystem_intersection_iff`, and
  `ChevalleyDatum.elementaryTitsWeylGroupMulEquiv`: the induced Tits system on
  `D.elementarySubgroup K`, its intersection with the actual torus, and identification of its Weyl
  group with `W`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4 and Corollary 2.
* R. W. Carter, *Simple Groups of Lie Type*, §§8.2–8.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2.
-/

public section

open Multiplicative
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-! ### The Tits system on `D.extendedElementarySubgroup K` -/

private theorem mem_doubleCoset_borelSubgroupOf_iff
    (a x : D.extendedElementarySubgroup K) :
    x ∈ DoubleCoset.doubleCoset a
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K))
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ↔
      (x : D.points K) ∈
        DoubleCoset.doubleCoset (a : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  rw [← DoubleCoset.mem_doubleCoset_image_iff
    (D.extendedElementarySubgroup K).subtype_injective,
    ← Subgroup.coe_map,
    Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup K)]
  rfl

private theorem borelSubgroupOf_subgroupOf_weylSubgroupOf_eq :
    ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
        ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) =
      (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K)).comap
        (Subgroup.subgroupOfEquivOfLe
          (D.weylSubgroup_le_extendedElementarySubgroup K)).toMonoidHom := by
  ext n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf, Subgroup.subgroupOfEquivOfLe_apply_coe]
  exact D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K n.property

private instance normal_borelSubgroupOf_subgroupOf_weylSubgroupOf :
    (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))).Normal := by
  rw [D.borelSubgroupOf_subgroupOf_weylSubgroupOf_eq K]
  exact Subgroup.Normal.comap inferInstance _

private noncomputable def titsSimpleRepAux (i : Fin t.rank) :
    (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)).symm
    ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩

private theorem coe_titsSimpleRepAux (i : Fin t.rank) :
    (((D.titsSimpleRepAux K i : D.extendedElementarySubgroup K) : D.points K)) =
      D.weylElement (t.simpleIndex ht i) K 1 := by
  rw [titsSimpleRepAux, ← Subgroup.subgroupOfEquivOfLe_apply_coe
    (D.weylSubgroup_le_extendedElementarySubgroup K), MulEquiv.apply_symm_apply]

/-- Coercing a word in `titsSimpleRepAux` through the nested restricted Weyl subgroup to
`D.points K` recovers the corresponding product of pinned simple Weyl representatives. -/
private theorem coe_list_prod_map_titsSimpleRepAux (l : List (Fin t.rank)) :
    ((((l.map (D.titsSimpleRepAux K)).prod :
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) :
        D.extendedElementarySubgroup K) : D.points K) =
      (l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod := by
  let ι : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) →* D.points K :=
    (D.extendedElementarySubgroup K).subtype.comp
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subtype
  have hprod := map_list_prod ι (l.map (D.titsSimpleRepAux K))
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_subtype, List.map_map] at hprod
  rw [hprod]
  exact congrArg List.prod (List.map_congr_left fun i _ => D.coe_titsSimpleRepAux K i)

private theorem closure_titsSimpleAux_eq_top :
    Subgroup.closure
      (Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.titsSimpleRepAux K i) :
          (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) ⧸
            ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
              ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)))) = ⊤ := by
  have hword : ∀ m : List (Fin t.rank),
      (QuotientGroup.mk (m.map (D.titsSimpleRepAux K)).prod :
        (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) ⧸
          ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
            ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))) ∈
        Subgroup.closure (Set.range fun i : Fin t.rank =>
          QuotientGroup.mk (D.titsSimpleRepAux K i)) := by
    intro m
    rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_map]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure ⟨i, rfl⟩
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l, s, hls⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints K).mp n.property
  let eW := Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)
  let tE : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
    eW.symm ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩
  have hcoe_tE : ((tE : D.extendedElementarySubgroup K) : D.points K) = D.torusPoints K s := by
    rw [← Subgroup.subgroupOfEquivOfLe_apply_coe
      (D.weylSubgroup_le_extendedElementarySubgroup K), MulEquiv.apply_symm_apply]
  have hn_eq : (l.map (D.titsSimpleRepAux K)).prod * tE = n := by
    apply eW.injective
    apply Subtype.ext
    rw [Subgroup.subgroupOfEquivOfLe_apply_coe, Subgroup.subgroupOfEquivOfLe_apply_coe,
      Subgroup.coe_mul, Subgroup.coe_mul, D.coe_list_prod_map_titsSimpleRepAux K l, hcoe_tE, hls,
      Subgroup.subtype_apply]
  have htE : (QuotientGroup.mk tE :
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) ⧸
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
          ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe_tE]
    exact D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩
  rw [← hn_eq, QuotientGroup.mk_mul, htE, mul_one]
  exact hword l

/-- The canonical Tits system on the extended elementary subgroup of a Chevalley datum over a
field, with Borel subgroup `D.borelSubgroup K` and Weyl subgroup `D.weylSubgroup K`. -/
noncomputable def titsSystem : TitsSystem (D.extendedElementarySubgroup K) where
  subgroupB := (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  subgroupN := (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  closure_subgroupB_union_subgroupN := by
    rw [Subgroup.coe_subgroupOf, Subgroup.coe_subgroupOf, ← Set.preimage_union,
      MonoidHom.closure_preimage_eq_of_injective (D.extendedElementarySubgroup K).subtype
        (D.extendedElementarySubgroup K).subtype_injective,
      Subgroup.closure_union, (D.borelSubgroup K).closure_eq, (D.weylSubgroup K).closure_eq,
      D.borelSubgroup_sup_weylSubgroup K, Subgroup.comap_subtype,
      Subgroup.subgroupOf_self]
    rw [Subgroup.coe_subtype, Subtype.range_coe]
    exact Set.union_subset (D.borelSubgroup_le_extendedElementarySubgroup K)
      (D.weylSubgroup_le_extendedElementarySubgroup K)
  intersection_normal := inferInstance
  simple := Set.range fun i : Fin t.rank => QuotientGroup.mk (D.titsSimpleRepAux K i)
  closure_simple := D.closure_titsSimpleAux_eq_top K
  exists_simpleRep_mul_self_mem := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.titsSimpleRepAux K i, rfl, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      D.coe_titsSimpleRepAux K, D.weylElement_mul_self i K, D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  mul_doubleCoset_subset := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.titsSimpleRepAux K i, rfl, fun w x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rw [D.mem_doubleCoset_borelSubgroupOf_iff K] at hy hz
    have hprod : ((y * z : D.extendedElementarySubgroup K) : D.points K) ∈
        DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 *
            ((w : D.extendedElementarySubgroup K) : D.points K))
          (D.borelSubgroup K) (D.borelSubgroup K) ∪
          DoubleCoset.doubleCoset ((w : D.extendedElementarySubgroup K) : D.points K)
            (D.borelSubgroup K) (D.borelSubgroup K) := by
      rw [Subgroup.coe_mul]
      exact D.doubleCoset_weylElement_mul_subset_union K i ⟨(w : D.points K), w.property⟩
        ⟨(y : D.points K), hy, (z : D.points K), hz, rfl⟩
    rcases hprod with hleft | hright
    · left
      rw [D.mem_doubleCoset_borelSubgroupOf_iff K, Subgroup.coe_mul, Subgroup.coe_mul,
        D.coe_titsSimpleRepAux K]
      exact hleft
    · right
      exact (D.mem_doubleCoset_borelSubgroupOf_iff K w (y * z)).mpr hright
  exists_conj_not_mem := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup K i
    let bE := (Subgroup.subgroupOfEquivOfLe
      (D.borelSubgroup_le_extendedElementarySubgroup K)).symm b
    have hbE : ((bE : D.extendedElementarySubgroup K) : D.points K) = b := by
      rw [← Subgroup.subgroupOfEquivOfLe_apply_coe
        (D.borelSubgroup_le_extendedElementarySubgroup K), MulEquiv.apply_symm_apply]
    refine ⟨D.titsSimpleRepAux K i, rfl, bE, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      D.coe_titsSimpleRepAux K, hbE]
    exact hb

/-- The Borel subgroup of `D.titsSystem K` is `D.borelSubgroup K` restricted to
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem titsSystem_subgroupB :
    (D.titsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- The Weyl subgroup of `D.titsSystem K` is `D.weylSubgroup K` restricted to
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem titsSystem_subgroupN :
    (D.titsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- An element of `(D.titsSystem K).subgroupN` belongs to `(D.titsSystem K).intersection` if and
only if its underlying point in `D.points K` lies in the actual torus `(D.torusPoints K).range`. -/
theorem mem_titsSystem_intersection_iff (n : (D.titsSystem K).subgroupN) :
    n ∈ (D.titsSystem K).intersection ↔
      ((n : D.extendedElementarySubgroup K) : D.points K) ∈ (D.torusPoints K).range := by
  rw [TitsSystem.mem_intersection, titsSystem_subgroupB, Subgroup.mem_subgroupOf]
  exact D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K n.property

/-- The canonical isomorphism `(D.titsSystem K).subgroupN ≃* D.weylSubgroup K` induced by the
inclusion `D.weylSubgroup K ≤ D.extendedElementarySubgroup K`. -/
noncomputable def titsSubgroupNMulEquiv :
    (D.titsSystem K).subgroupN ≃* D.weylSubgroup K :=
  Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)

/-- `titsSubgroupNMulEquiv` preserves the underlying point in `D.points K`. -/
@[simp]
theorem coe_titsSubgroupNMulEquiv (n : (D.titsSystem K).subgroupN) :
    ((D.titsSubgroupNMulEquiv K n : D.weylSubgroup K) : D.points K) =
      ((n : D.extendedElementarySubgroup K) : D.points K) :=
  Subgroup.subgroupOfEquivOfLe_apply_coe (D.weylSubgroup_le_extendedElementarySubgroup K) n

/-- The inverse of `titsSubgroupNMulEquiv` preserves the underlying point in `D.points K`. -/
@[simp]
theorem coe_titsSubgroupNMulEquiv_symm (m : D.weylSubgroup K) :
    ((((D.titsSubgroupNMulEquiv K).symm m : (D.titsSystem K).subgroupN) :
      D.extendedElementarySubgroup K) : D.points K) = (m : D.points K) := by
  rw [← D.coe_titsSubgroupNMulEquiv K, MulEquiv.apply_symm_apply]

/-- The `i`-th pinned simple Weyl representative inside `(D.titsSystem K).subgroupN`. -/
noncomputable def titsSimpleRep (i : Fin t.rank) : (D.titsSystem K).subgroupN :=
  D.titsSimpleRepAux K i

/-- Coercing `titsSimpleRep` to `D.points K` recovers `D.weylElement (t.simpleIndex ht i) K 1`. -/
@[simp]
theorem coe_titsSimpleRep (i : Fin t.rank) :
    (((D.titsSimpleRep K i : D.extendedElementarySubgroup K) : D.points K)) =
      D.weylElement (t.simpleIndex ht i) K 1 :=
  D.coe_titsSimpleRepAux K i

/-- `titsSubgroupNMulEquiv` maps `titsSimpleRep` to `D.weylElement (t.simpleIndex ht i) K 1` in
`D.weylSubgroup K`. -/
@[simp]
theorem titsSubgroupNMulEquiv_titsSimpleRep (i : Fin t.rank) :
    D.titsSubgroupNMulEquiv K (D.titsSimpleRep K i) =
      ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ :=
  MulEquiv.apply_symm_apply (D.titsSubgroupNMulEquiv K) _

/-- The `i`-th simple reflection in `(D.titsSystem K).WeylGroup`. -/
noncomputable def titsSimpleReflection (i : Fin t.rank) : (D.titsSystem K).WeylGroup :=
  QuotientGroup.mk (D.titsSimpleRep K i)

/-- The simple reflections of `D.titsSystem K` are the classes `D.titsSimpleReflection K i`. -/
@[simp]
theorem titsSystem_simple :
    (D.titsSystem K).simple = Set.range (D.titsSimpleReflection K) :=
  (rfl)

/-- Every `D.titsSimpleReflection K i` belongs to `(D.titsSystem K).simple`. -/
theorem titsSimpleReflection_mem_simple (i : Fin t.rank) :
    D.titsSimpleReflection K i ∈ (D.titsSystem K).simple :=
  ⟨i, rfl⟩

/-! ### Identification of the Tits Weyl group -/

/-- The canonical isomorphism between the Weyl group of `D.titsSystem K` and the Weyl group of the
root datum. -/
noncomputable def titsWeylGroupMulEquiv :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.congr (D.titsSystem K).intersection
      (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K))
      (D.titsSubgroupNMulEquiv K) (by
        have h : (D.titsSystem K).intersection =
            (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K)).comap
              (D.titsSubgroupNMulEquiv K).toMonoidHom :=
          D.borelSubgroupOf_subgroupOf_weylSubgroupOf_eq K
        rw [h]
        exact Subgroup.map_comap_eq_self_of_surjective
          (D.titsSubgroupNMulEquiv K).surjective _)).trans
    (D.weylQuotientMulEquiv K)

/-- `titsWeylGroupMulEquiv` sends the class of `n` to `D.weylProjection K` of its image in
`D.weylSubgroup K`. -/
@[simp]
theorem titsWeylGroupMulEquiv_mk (n : (D.titsSystem K).subgroupN) :
    D.titsWeylGroupMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K (D.titsSubgroupNMulEquiv K n) := by
  rw [titsWeylGroupMulEquiv, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    D.weylQuotientMulEquiv_mk]

/-- `titsWeylGroupMulEquiv` sends the `i`-th Tits simple reflection to the `i`-th simple
reflection of the root datum's Weyl group. -/
@[simp]
theorem titsWeylGroupMulEquiv_titsSimpleReflection (i : Fin t.rank) :
    D.titsWeylGroupMulEquiv K (D.titsSimpleReflection K i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [titsSimpleReflection, titsWeylGroupMulEquiv_mk, titsSubgroupNMulEquiv_titsSimpleRep,
    D.weylProjection_weylElement K i]

/-- The inverse of `titsWeylGroupMulEquiv` sends `D.weylProjection K n` to the class of `n` inside
`(D.titsSystem K).subgroupN`. -/
@[simp]
theorem titsWeylGroupMulEquiv_symm_weylProjection (n : D.weylSubgroup K) :
    (D.titsWeylGroupMulEquiv K).symm (D.weylProjection K n) =
      QuotientGroup.mk ((D.titsSubgroupNMulEquiv K).symm n) := by
  rw [MulEquiv.symm_apply_eq, titsWeylGroupMulEquiv_mk, MulEquiv.apply_symm_apply]

/-- The inverse of `titsWeylGroupMulEquiv` sends the `i`-th simple reflection of the root datum's
Weyl group to `D.titsSimpleReflection K i`. -/
@[simp]
theorem titsWeylGroupMulEquiv_symm_ofIdx_simpleIndex (i : Fin t.rank) :
    (D.titsWeylGroupMulEquiv K).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      D.titsSimpleReflection K i := by
  rw [MulEquiv.symm_apply_eq, titsWeylGroupMulEquiv_titsSimpleReflection]

/-- Under `titsWeylGroupMulEquiv`, the simple reflections of `D.titsSystem K` are the preimage of
the root datum's simple reflections. -/
theorem titsSystem_simple_eq_preimage :
    (D.titsSystem K).simple =
      D.titsWeylGroupMulEquiv K ⁻¹'
        Set.range fun i : Fin t.rank =>
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  ext s
  simp only [titsSystem_simple, Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (D.titsWeylGroupMulEquiv_titsSimpleReflection K i).symm⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, (D.titsWeylGroupMulEquiv K).injective ?_⟩
    rw [D.titsWeylGroupMulEquiv_titsSimpleReflection K i, hi]

/-! ### The induced Tits system on the elementary Chevalley subgroup -/

private theorem exists_inclusion_elementarySubgroup_mul_mem_inf
    (g : D.extendedElementarySubgroup K) :
    ∃ x : D.elementarySubgroup K,
      ∃ z ∈ (D.titsSystem K).subgroupB ⊓ (D.titsSystem K).subgroupN,
        Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K) x * z = g := by
  obtain ⟨e, he, s, hes⟩ := (D.mem_extendedElementarySubgroup_iff K g.val).mp g.property
  let z : D.extendedElementarySubgroup K :=
    ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩
  have hz : z ∈ (D.titsSystem K).subgroupB ⊓ (D.titsSystem K).subgroupN := by
    rw [Subgroup.mem_inf, titsSystem_subgroupB, titsSystem_subgroupN,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup K s⟩
  refine ⟨⟨e, he⟩, z, hz, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inclusion]
  exact hes

/-- The canonical Tits system on the elementary Chevalley group `D.elementarySubgroup K`, obtained
by pulling `D.titsSystem K` back along `D.extendedElementarySubgroup K = D.elementarySubgroup K ·
T_D(K)`. -/
noncomputable def elementaryTitsSystem : TitsSystem (D.elementarySubgroup K) :=
  (D.titsSystem K).comap
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_inclusion_elementarySubgroup_mul_mem_inf K)

/-- The Borel subgroup of `D.elementaryTitsSystem K` is `D.borelSubgroup K` restricted to
`D.elementarySubgroup K`. -/
@[simp]
theorem elementaryTitsSystem_subgroupB :
    (D.elementaryTitsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupB, titsSystem_subgroupB,
    Subgroup.comap_inclusion_subgroupOf]

/-- The Weyl subgroup of `D.elementaryTitsSystem K` is `D.weylSubgroup K` restricted to
`D.elementarySubgroup K`. -/
@[simp]
theorem elementaryTitsSystem_subgroupN :
    (D.elementaryTitsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupN, titsSystem_subgroupN,
    Subgroup.comap_inclusion_subgroupOf]

/-- Coercing an element of `(D.elementaryTitsSystem K).subgroupN` to `D.points K` lands in
`D.weylSubgroup K`. -/
theorem coe_mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN
    (n : (D.elementaryTitsSystem K).subgroupN) :
    ((n : D.elementarySubgroup K) : D.points K) ∈ D.weylSubgroup K :=
  Subgroup.mem_subgroupOf.mp
    ((SetLike.ext_iff.mp (D.elementaryTitsSystem_subgroupN K) (n : D.elementarySubgroup K)).mp
      n.property)

/-- An element of `(D.elementaryTitsSystem K).subgroupN` belongs to
`(D.elementaryTitsSystem K).intersection` if and only if its underlying point in `D.points K`
lies in the actual torus `(D.torusPoints K).range`. -/
theorem mem_elementaryTitsSystem_intersection_iff
    (n : (D.elementaryTitsSystem K).subgroupN) :
    n ∈ (D.elementaryTitsSystem K).intersection ↔
      ((n : D.elementarySubgroup K) : D.points K) ∈ (D.torusPoints K).range := by
  rw [TitsSystem.mem_intersection, elementaryTitsSystem_subgroupB, Subgroup.mem_subgroupOf]
  exact D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K
    (D.coe_mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN K n)

/-- The Weyl group of `D.elementaryTitsSystem K` is canonically isomorphic to the Weyl group of
the root datum. -/
noncomputable def elementaryTitsWeylGroupMulEquiv :
    (D.elementaryTitsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  ((D.titsSystem K).comapWeylGroupMulEquiv
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_inclusion_elementarySubgroup_mul_mem_inf K)).trans
    (D.titsWeylGroupMulEquiv K)

/-- `elementaryTitsWeylGroupMulEquiv` sends the class of `n` to `D.weylProjection K` of its
underlying point. -/
@[simp]
theorem elementaryTitsWeylGroupMulEquiv_mk (n : (D.elementaryTitsSystem K).subgroupN) :
    D.elementaryTitsWeylGroupMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K ⟨((n : D.elementarySubgroup K) : D.points K),
        D.coe_mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN K n⟩ :=
  (congrArg (D.titsWeylGroupMulEquiv K)
    ((D.titsSystem K).comapWeylGroupMulEquiv_mk
      (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
      (D.exists_inclusion_elementarySubgroup_mul_mem_inf K) n)).trans
    ((D.titsWeylGroupMulEquiv_mk K _).trans (congrArg (D.weylProjection K)
      (Subtype.ext (by rw [coe_titsSubgroupNMulEquiv, Subgroup.coe_inclusion]))))

/-- Under `elementaryTitsWeylGroupMulEquiv`, the simple reflections of `D.elementaryTitsSystem K`
are the preimage of the root datum's simple reflections. -/
@[simp]
theorem elementaryTitsSystem_simple_eq_preimage :
    (D.elementaryTitsSystem K).simple =
      D.elementaryTitsWeylGroupMulEquiv K ⁻¹'
        Set.range fun i : Fin t.rank =>
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) :=
  ((D.titsSystem K).comap_simple
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_inclusion_elementarySubgroup_mul_mem_inf K)).trans
    (by
      rw [D.titsSystem_simple_eq_preimage K, ← Set.preimage_comp]
      rfl)

end TauCeti.DynkinType.ChevalleyDatum
