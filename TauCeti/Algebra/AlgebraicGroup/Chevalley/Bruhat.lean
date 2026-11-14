/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.TitsSystem
public import TauCeti.GroupTheory.TitsSystem.Bruhat.Length
import TauCeti.GroupTheory.DoubleCoset.Map
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Bruhat cells and the Bruhat decomposition of a Chevalley datum

Over any field `K`, transporting the Bruhat cells of `ChevalleyDatum.titsSystem` along
`ChevalleyDatum.titsWeylGroupMulEquiv` defines the `W`-indexed Bruhat cells `D.bruhatCell K w`
inside `D.points K`. For any lift `n : D.weylSubgroup K` projecting to `w ∈ W`, the cell
`D.bruhatCell K w` is the double coset `B(K) n B(K)` (and equally `U(K) n B(K)` or `B(K) n U(K)`,
since `N(K)` normalizes `T_D(K)` and `T_D(K)` normalizes `U(K)`).

Distinct elements of `W` index pairwise disjoint Bruhat cells whose union is the extended
elementary subgroup `D.extendedElementarySubgroup K`. Left multiplication by a simple cell
`B(K) sᵢ B(K)` either collapses to `B(K) (sᵢ w) B(K)` when `w⁻¹(αᵢ)` is positive or splits as
`B(K) (sᵢ w) B(K) ∪ B(K) w B(K)` when `w⁻¹(αᵢ)` is negative, characterizing Tits word-length
increase in terms of positive roots.

## Main definitions and results

* `ChevalleyDatum.bruhatCell`: the Bruhat cell in `D.points K` indexed by an element of the root
  datum's Weyl group.
* `ChevalleyDatum.bruhatCell_weylProjection`,
  `ChevalleyDatum.bruhatCell_weylProjection_eq_doubleCoset_positivePoints_left`, and
  `ChevalleyDatum.bruhatCell_weylProjection_eq_doubleCoset_positivePoints_right`: realization of
  `D.bruhatCell K (D.weylProjection K n)` as `B n B`, `U n B`, and `B n U`.
* `ChevalleyDatum.bruhatCell_injective`, `ChevalleyDatum.disjoint_bruhatCell_iff`,
  `ChevalleyDatum.iUnion_bruhatCell_eq_extendedElementarySubgroup`, and
  `ChevalleyDatum.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup`: the disjoint
  `W`-indexed Bruhat decomposition of `D.extendedElementarySubgroup K`.
* `ChevalleyDatum.bruhatCell_ofIdx_mul_eq_of_mem_posRoots`,
  `ChevalleyDatum.bruhatCell_ofIdx_mul_eq_union_of_mem_negRoots`, and
  `ChevalleyDatum.wordLength_titsSimpleReflection_mul_gt_iff_mem_posRoots`: root-positivity rules
  for simple Bruhat-cell multiplication and Tits word length.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4 and Corollary 1.
* R. W. Carter, *Simple Groups of Lie Type*, §§8.3–8.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2.
-/

public section

open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-- The Bruhat cell in `D.points K` indexed by an element `w` of the root datum's Weyl group. -/
noncomputable def bruhatCell (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    Set (D.points K) :=
  (D.extendedElementarySubgroup K).subtype ''
    (D.titsSystem K).bruhatCell ((D.titsWeylGroupMulEquiv K).symm w)

private theorem image_subtype_borelSubgroupOf_eq :
    (D.extendedElementarySubgroup K).subtype ''
        (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :
          Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K)) =
      (D.borelSubgroup K : Set (D.points K)) := by
  rw [← Subgroup.coe_map,
    Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup K)]

/-- For any lift `n : D.weylSubgroup K` with `D.weylProjection K n = w`, the Bruhat cell
`D.bruhatCell K w` is the double coset `B n B` in `D.points K`. -/
theorem bruhatCell_eq_doubleCoset_of_weylProjection_eq
    {n : D.weylSubgroup K} {w : (t.simplyConnectedRootDatum ht).weylGroup}
    (hn : D.weylProjection K n = w) :
    D.bruhatCell K w =
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  have hsymm :
      (D.titsWeylGroupMulEquiv K).symm w =
        QuotientGroup.mk ((D.titsSubgroupNMulEquiv K).symm n) := by
    apply (D.titsWeylGroupMulEquiv K).injective
    rw [MulEquiv.apply_symm_apply, titsWeylGroupMulEquiv_mk, MulEquiv.apply_symm_apply, hn]
  rw [bruhatCell, hsymm, (D.titsSystem K).bruhatCell_mk, titsSystem_subgroupB,
    DoubleCoset.image_doubleCoset, D.image_subtype_borelSubgroupOf_eq K, Subgroup.subtype_apply,
    coe_titsSubgroupNMulEquiv_symm]

/-- The Bruhat cell of `D.weylProjection K n` is the double coset `B n B` in `D.points K`. -/
@[simp]
theorem bruhatCell_weylProjection (n : D.weylSubgroup K) :
    D.bruhatCell K (D.weylProjection K n) =
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) :=
  D.bruhatCell_eq_doubleCoset_of_weylProjection_eq K rfl

/-- The identity Bruhat cell is the Borel subgroup `D.borelSubgroup K`. -/
@[simp]
theorem bruhatCell_one :
    D.bruhatCell K 1 = (D.borelSubgroup K : Set (D.points K)) := by
  rw [bruhatCell, map_one, (D.titsSystem K).bruhatCell_one, titsSystem_subgroupB]
  exact D.image_subtype_borelSubgroupOf_eq K

/-- The Bruhat cell of the `i`-th simple reflection is the double coset `B nᵢ(1) B`. -/
@[simp]
theorem bruhatCell_ofIdx_simpleIndex (i : Fin t.rank) :
    D.bruhatCell K
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
        (D.borelSubgroup K) (D.borelSubgroup K) :=
  D.bruhatCell_eq_doubleCoset_of_weylProjection_eq K (D.weylProjection_weylElement K i)

/-- Every element of the Bruhat cell `B n B` factors as `u * n * b` with `u ∈ D.positivePoints K`
and `b ∈ D.borelSubgroup K`. -/
theorem bruhatCell_weylProjection_eq_doubleCoset_positivePoints_left
    (n : D.weylSubgroup K) :
    D.bruhatCell K (D.weylProjection K n) =
      DoubleCoset.doubleCoset (n : D.points K) (D.positivePoints K) (D.borelSubgroup K) := by
  rw [D.bruhatCell_weylProjection K n]
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hb₁
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints K (inv_mem n.property)
    obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints K s)).mp ⟨s, rfl⟩
    have hb' : D.torusPoints K s' * b₂ ∈ D.borelSubgroup K :=
      mul_mem (D.range_torusPoints_le_borelSubgroup K ⟨s', rfl⟩) hb₂
    refine DoubleCoset.mem_doubleCoset.mpr ⟨u, hu, D.torusPoints K s' * b₂, hb', ?_⟩
    rw [hs']
    group
  · intro g hg
    obtain ⟨u, hu, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨u, D.positivePoints_le_borelSubgroup K hu, b, hb, rfl⟩

/-- Every element of the Bruhat cell `B n B` factors as `b * n * u` with `b ∈ D.borelSubgroup K`
and `u ∈ D.positivePoints K`. -/
theorem bruhatCell_weylProjection_eq_doubleCoset_positivePoints_right
    (n : D.weylSubgroup K) :
    D.bruhatCell K (D.weylProjection K n) =
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.positivePoints K) := by
  rw [D.bruhatCell_weylProjection K n]
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hb₂
    have hu' : D.torusPoints K s⁻¹ * u * (D.torusPoints K s⁻¹)⁻¹ ∈ D.positivePoints K :=
      (Subgroup.mem_normalizer_iff.mp
        (D.range_torusPoints_le_normalizer_positivePoints K ⟨s⁻¹, rfl⟩) u).mp hu
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints K n.property
    obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints K s)).mp ⟨s, rfl⟩
    have hb' : b₁ * D.torusPoints K s' ∈ D.borelSubgroup K :=
      mul_mem hb₁ (D.range_torusPoints_le_borelSubgroup K ⟨s', rfl⟩)
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁ * D.torusPoints K s', hb',
        D.torusPoints K s⁻¹ * u * (D.torusPoints K s⁻¹)⁻¹, hu', ?_⟩
    rw [(D.torusPoints K).map_inv, hs']
    group
  · intro g hg
    obtain ⟨b, hb, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨b, hb, u, D.positivePoints_le_borelSubgroup K hu, rfl⟩

/-- Every Bruhat cell lies inside `D.extendedElementarySubgroup K`. -/
theorem bruhatCell_subset_extendedElementarySubgroup
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    D.bruhatCell K w ⊆ (D.extendedElementarySubgroup K : Set (D.points K)) := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Distinct elements of the root datum's Weyl group index distinct Bruhat cells in `D.points K`. -/
theorem bruhatCell_injective : Function.Injective (D.bruhatCell K) := by
  intro w v h
  have hcell :
      (D.titsSystem K).bruhatCell ((D.titsWeylGroupMulEquiv K).symm w) =
        (D.titsSystem K).bruhatCell ((D.titsWeylGroupMulEquiv K).symm v) :=
    Set.image_injective.mpr (D.extendedElementarySubgroup K).subtype_injective h
  exact (D.titsWeylGroupMulEquiv K).symm.injective ((D.titsSystem K).bruhatCell_injective hcell)

/-- Two Bruhat cells in `D.points K` are equal if and only if their Weyl-group indices are equal. -/
@[simp]
theorem bruhatCell_inj {w v : (t.simplyConnectedRootDatum ht).weylGroup} :
    D.bruhatCell K w = D.bruhatCell K v ↔ w = v :=
  (D.bruhatCell_injective K).eq_iff

/-- Two Bruhat cells in `D.points K` are disjoint if and only if their Weyl-group indices differ. -/
@[simp]
theorem disjoint_bruhatCell_iff {w v : (t.simplyConnectedRootDatum ht).weylGroup} :
    Disjoint (D.bruhatCell K w) (D.bruhatCell K v) ↔ w ≠ v := by
  rw [bruhatCell, bruhatCell,
    Set.disjoint_image_iff (D.extendedElementarySubgroup K).subtype_injective,
    (D.titsSystem K).disjoint_bruhatCell_iff, ne_eq,
    (D.titsWeylGroupMulEquiv K).symm.injective.eq_iff]

/-- The Bruhat cells indexed by the root datum's Weyl group cover `D.extendedElementarySubgroup K`.
-/
@[simp]
theorem iUnion_bruhatCell_eq_extendedElementarySubgroup :
    (⋃ w : (t.simplyConnectedRootDatum ht).weylGroup, D.bruhatCell K w) =
      (D.extendedElementarySubgroup K : Set (D.points K)) := by
  have huniv : (⋃ q : (D.titsSystem K).WeylGroup, (D.titsSystem K).bruhatCell q) = Set.univ := by
    rw [← (D.titsSystem K).bruhatCells_eq_iUnion_bruhatCell, (D.titsSystem K).bruhatCells_eq_univ]
  calc
    (⋃ w, D.bruhatCell K w) =
        (D.extendedElementarySubgroup K).subtype ''
          ⋃ w, (D.titsSystem K).bruhatCell ((D.titsWeylGroupMulEquiv K).symm w) := by
      rw [Set.image_iUnion]
      rfl
    _ = (D.extendedElementarySubgroup K).subtype ''
          ⋃ q, (D.titsSystem K).bruhatCell q := by
      rw [(D.titsWeylGroupMulEquiv K).symm.surjective.iUnion_comp]
    _ = (D.extendedElementarySubgroup K : Set (D.points K)) := by
      rw [huniv, Set.image_univ]
      ext x
      simp only [Set.mem_range, Subgroup.coe_subtype, SetLike.mem_coe]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- **Bruhat decomposition of a Chevalley datum:** every point of `D.extendedElementarySubgroup K`
belongs to a unique Bruhat cell indexed by the root datum's Weyl group. -/
theorem existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup
    {g : D.points K} (hg : g ∈ D.extendedElementarySubgroup K) :
    ∃! w : (t.simplyConnectedRootDatum ht).weylGroup, g ∈ D.bruhatCell K w := by
  obtain ⟨q, hq, huniq⟩ := (D.titsSystem K).existsUnique_mem_bruhatCell ⟨g, hg⟩
  refine ⟨D.titsWeylGroupMulEquiv K q, ?_, ?_⟩
  · refine ⟨⟨g, hg⟩, ?_, rfl⟩
    simpa only [MulEquiv.symm_apply_apply] using hq
  · intro w ⟨x, hx, hxg⟩
    have hx_eq : x = ⟨g, hg⟩ := Subtype.ext hxg
    subst hx_eq
    have hq_eq := huniq ((D.titsWeylGroupMulEquiv K).symm w) hx
    simpa only [MulEquiv.apply_symm_apply] using congrArg (D.titsWeylGroupMulEquiv K) hq_eq

/-- A point of `D.points K` lies in `D.extendedElementarySubgroup K` if and only if it belongs to a
unique Bruhat cell. -/
theorem mem_extendedElementarySubgroup_iff_existsUnique_mem_bruhatCell {g : D.points K} :
    g ∈ D.extendedElementarySubgroup K ↔
      ∃! w : (t.simplyConnectedRootDatum ht).weylGroup, g ∈ D.bruhatCell K w := by
  refine ⟨D.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup K, ?_⟩
  rintro ⟨w, hw, _⟩
  exact D.bruhatCell_subset_extendedElementarySubgroup K w hw

/-- Positive root criterion for Bruhat-cell multiplication: if `w⁻¹(αᵢ)` is positive, left
multiplication by the simple cell `B sᵢ B` gives the single cell `B (sᵢ w) B`. -/
theorem bruhatCell_ofIdx_mul_eq_of_mem_posRoots
    (i : Fin t.rank) {w : (t.simplyConnectedRootDatum ht).weylGroup}
    (hw : (t.simplyConnectedRootDatum ht).weylGroupToPerm w⁻¹ (t.simpleIndex ht i) ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.bruhatCell K (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
        (t.simpleIndex ht i)) * D.bruhatCell K w =
      D.bruhatCell K (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
        (t.simpleIndex ht i) * w) := by
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
  have hr : D.weylProjection K
      (⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ * n) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) *
        D.weylProjection K n := by
    rw [map_mul, D.weylProjection_weylElement K i]
  rw [D.bruhatCell_ofIdx_simpleIndex K i, D.bruhatCell_weylProjection K n, ← hr,
    D.bruhatCell_weylProjection K]
  exact D.doubleCoset_weylElement_mul_eq_of_mem_posRoots K i n hw

/-- Negative root criterion for Bruhat-cell multiplication: if `w⁻¹(αᵢ)` is negative, left
multiplication by the simple cell `B sᵢ B` gives the union `B (sᵢ w) B ∪ B w B`. -/
theorem bruhatCell_ofIdx_mul_eq_union_of_mem_negRoots
    (i : Fin t.rank) {w : (t.simplyConnectedRootDatum ht).weylGroup}
    (hw : (t.simplyConnectedRootDatum ht).weylGroupToPerm w⁻¹ (t.simpleIndex ht i) ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.bruhatCell K (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
        (t.simpleIndex ht i)) * D.bruhatCell K w =
      D.bruhatCell K (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
        (t.simpleIndex ht i) * w) ∪ D.bruhatCell K w := by
  let α := t.simpleIndex ht i
  let s := RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) α
  have hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (s * w)⁻¹ α ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    let _ := (t.simplyConnectedRootDatum ht).indexNeg
    have hperm : (t.simplyConnectedRootDatum ht).weylGroupToPerm (s * w)⁻¹ α =
        (t.simplyConnectedRootDatum ht).reflectionPerm
          ((t.simplyConnectedRootDatum ht).weylGroupToPerm w⁻¹ α)
          ((t.simplyConnectedRootDatum ht).weylGroupToPerm w⁻¹ α) := by
      dsimp only [s]
      rw [mul_inv_rev, RootPairing.weylGroup.ofIdx_inv_eq, map_mul, Equiv.Perm.mul_apply,
        RootPairing.weylGroupToPerm_ofIdx_apply,
        ← (t.simplyConnectedRootDatum ht).indexNeg_neg,
        ← (t.simplyConnectedRootDatum ht).indexNeg_neg]
      exact (t.simplyConnectedRootDatum ht).weylGroupToPerm_neg w⁻¹ α
    rw [hperm, ← t.reflectionPerm_rationalRootSystem ht]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hw
  have hstep : D.bruhatCell K s * D.bruhatCell K (s * w) = D.bruhatCell K w := by
    have h := D.bruhatCell_ofIdx_mul_eq_of_mem_posRoots K i hpos
    dsimp only [s, α] at h ⊢
    rwa [← mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, one_mul] at h
  have hself : D.bruhatCell K s * D.bruhatCell K s = D.bruhatCell K 1 ∪ D.bruhatCell K s := by
    have hsymm : (D.titsWeylGroupMulEquiv K).symm s = D.titsSimpleReflection K i := by
      apply (D.titsWeylGroupMulEquiv K).injective
      rw [MulEquiv.apply_symm_apply, D.titsWeylGroupMulEquiv_titsSimpleReflection K i]
    calc
      D.bruhatCell K s * D.bruhatCell K s =
          (D.extendedElementarySubgroup K).subtype ''
            ((D.titsSystem K).bruhatCell (D.titsSimpleReflection K i) *
              (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i)) := by
        rw [bruhatCell, hsymm, Set.image_mul]
      _ = D.bruhatCell K 1 ∪ D.bruhatCell K s := by
        rw [(D.titsSystem K).bruhatCell_mul_self_eq_union_of_mem_simple
          (D.titsSimpleReflection_mem_simple K i), Set.image_union, bruhatCell, map_one,
          bruhatCell, hsymm]
  have habsorb : D.bruhatCell K 1 * D.bruhatCell K (s * w) = D.bruhatCell K (s * w) := by
    rw [bruhatCell, map_one, bruhatCell, ← Set.image_mul, (D.titsSystem K).bruhatCell_one,
      (D.titsSystem K).subgroupB_mul_bruhatCell]
  calc
    D.bruhatCell K s * D.bruhatCell K w =
        D.bruhatCell K s * (D.bruhatCell K s * D.bruhatCell K (s * w)) := by rw [hstep]
    _ = (D.bruhatCell K 1 ∪ D.bruhatCell K s) * D.bruhatCell K (s * w) := by
        rw [← mul_assoc, hself]
    _ = D.bruhatCell K (s * w) ∪ D.bruhatCell K w := by
        rw [Set.union_mul, habsorb, hstep]

/-- Left multiplication by the `i`-th simple reflection increases the Tits word length of `q`
precisely when `(titsWeylGroupMulEquiv q)⁻¹(αᵢ)` is a positive root. -/
theorem wordLength_titsSimpleReflection_mul_gt_iff_mem_posRoots
    (i : Fin t.rank) (q : (D.titsSystem K).WeylGroup) :
    (D.titsSystem K).simpleGenerators.wordLength q <
        (D.titsSystem K).simpleGenerators.wordLength (D.titsSimpleReflection K i * q) ↔
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.titsWeylGroupMulEquiv K q)⁻¹
        (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  rw [← (D.titsSystem K).bruhatCell_mul_eq_iff_wordLength_lt
    (D.titsSimpleReflection_mem_simple K i) q]
  let w := D.titsWeylGroupMulEquiv K q
  let s := RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)
  have hsymm_s : (D.titsWeylGroupMulEquiv K).symm s = D.titsSimpleReflection K i := by
    apply (D.titsWeylGroupMulEquiv K).injective
    rw [MulEquiv.apply_symm_apply, D.titsWeylGroupMulEquiv_titsSimpleReflection K i]
  have hsymm_w : (D.titsWeylGroupMulEquiv K).symm w = q :=
    (D.titsWeylGroupMulEquiv K).symm_apply_apply q
  have hsymm_sw : (D.titsWeylGroupMulEquiv K).symm (s * w) =
      D.titsSimpleReflection K i * q := by
    rw [map_mul, hsymm_s, hsymm_w]
  have hcell :
      (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i) * (D.titsSystem K).bruhatCell q =
          (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i * q) ↔
        D.bruhatCell K s * D.bruhatCell K w = D.bruhatCell K (s * w) := by
    rw [bruhatCell, bruhatCell, bruhatCell, hsymm_s, hsymm_w, hsymm_sw, ← Set.image_mul]
    exact (Set.image_injective.mpr (D.extendedElementarySubgroup K).subtype_injective).eq_iff.symm
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht)
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm w⁻¹ (t.simpleIndex ht i)) with hpos | hneg
  · exact iff_of_true (hcell.mpr (D.bruhatCell_ofIdx_mul_eq_of_mem_posRoots K i hpos)) hpos
  · refine iff_of_false ?_ (not_mem_posRoots_iff_mem_negRoots _ _ _ |>.mpr hneg)
    intro heqT
    have hunion : D.bruhatCell K s * D.bruhatCell K w =
        D.bruhatCell K (s * w) ∪ D.bruhatCell K w :=
      D.bruhatCell_ofIdx_mul_eq_union_of_mem_negRoots K i hneg
    rw [hcell.mp heqT] at hunion
    have hunionT :
        (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i * q) =
          (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i * q) ∪
            (D.titsSystem K).bruhatCell q := by
      apply Set.image_injective.mpr (D.extendedElementarySubgroup K).subtype_injective
      rw [Set.image_union, ← hsymm_sw, ← hsymm_w, ← bruhatCell, ← bruhatCell]
      exact hunion
    have hsub : (D.titsSystem K).bruhatCell q ⊆
        (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i * q) :=
      hunionT ▸ Set.subset_union_right
    exact (D.titsSystem K).simple_ne_one (D.titsSimpleReflection_mem_simple K i)
      (by simpa using (D.titsSystem K).bruhatCell_subset_iff.mp hsub)

end TauCeti.DynkinType.ChevalleyDatum
