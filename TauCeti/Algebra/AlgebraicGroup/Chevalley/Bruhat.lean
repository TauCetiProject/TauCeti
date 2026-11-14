/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
public import TauCeti.GroupTheory.TitsSystem.Bruhat.Uniqueness
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.DoubleCoset.Map
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# The Tits system and Bruhat decomposition of a Chevalley group over a field

For every valid Dynkin type `t` and Chevalley datum `D` of type `t`, the Borel-type subgroup
`D.borelSubgroup` and the Weyl subgroup `D.weylSubgroup` sit inside `D.extendedElementarySubgroup`,
generate it (`borelSubgroup_sup_weylSubgroup`), and intersect in the actual character-lattice torus
`(D.torusPoints A).range` (`borelSubgroup_inf_weylSubgroup`) over every commutative ring `A`.

Over an arbitrary field `k`, combining the simple-root factorization `U = U⁽ⁱ⁾ Xᵢ` and
`nᵢ`-normalization of `U⁽ⁱ⁾` from `TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection`,
the rank-one exchange relation from `TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne`, the Weyl
quotient theorem from `TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient`, and the generic
Bruhat decomposition of `TauCeti.TitsSystem` (`TauCeti.TitsSystem.existsUnique_mem_bruhatCell` in
`TauCeti.GroupTheory.TitsSystem.Bruhat.Uniqueness`) yields:

1. **The Tits multiplication axiom** (`doubleCoset_weylElement_mul_subset`):
   `(B nᵢ B) (B w B) ⊆ B (nᵢ w) B ∪ B w B` inside `D.points k`.
2. **The canonical Tits system** (`titsSystem`) on `D.extendedElementarySubgroup k`, together with
   its Weyl-group isomorphism `titsSystemWeylGroupMulEquiv` onto
   `(t.simplyConnectedRootDatum ht).weylGroup`, following the API pattern of `TauCeti.glTitsSystem`
   in `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.TitsSystem`.
3. **Bruhat decomposition** of `D.extendedElementarySubgroup k` into disjoint `B`-double cosets
   indexed by `(t.simplyConnectedRootDatum ht).weylGroup`
   (`existsUnique_mem_bruhatCell_titsSystemWeylGroupMulEquiv_symm`,
   `mem_extendedElementarySubgroup_iff_exists_mem_doubleCoset`,
   `weylProjection_eq_of_mem_doubleCoset_borelSubgroup`, `doubleCoset_borelSubgroup_eq_iff`).
4. **Steinberg's sharpened Bruhat normal form**: disjointness of `U ∩ n U⁻ n⁻¹` from `n B n⁻¹` and
   uniqueness of `(u, b)` in `u * n * b` over every commutative ring
   (`disjoint_positivePoints_inf_map_negativePoints_map_borelSubgroup`,
   `eq_and_eq_of_mem_positivePoints_inf_map_negativePoints_of_mem_borelSubgroup_of_mul_mul_eq`),
   the inversion-root characterization `positivePoints_inf_map_negativePoints_eq_iSup` of
   `U(k) ∩ n U⁻(k) n⁻¹`, and existence and uniqueness of `(u, b)` on each Bruhat cell over a field
   (`mem_doubleCoset_borelSubgroup_iff_exists_mul`,
   `existsUnique_mul_weylSubgroup_mul_eq_of_mem_doubleCoset_borelSubgroup`).

We package the Tits system on `D.extendedElementarySubgroup k` rather than on all scheme points
`D.points k`, because equality of `D.extendedElementarySubgroup k` with `D.points k` over a field
is not asserted in this file (while `D.elementarySubgroup k` alone can be a proper subgroup of
`D.extendedElementarySubgroup k` when `D` is not simply connected, e.g. its image in `PGL₂(k)` has
determinant in `(kˣ)²`).

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.titsSystem`: the Tits system on
  `D.extendedElementarySubgroup k` over any field `k`.
* `TauCeti.DynkinType.ChevalleyDatum.titsSystemSimpleRep`: the `i`-th pinned simple reflection
  representative in `(D.titsSystem k).subgroupN`.
* `TauCeti.DynkinType.ChevalleyDatum.titsSystemWeylGroupMulEquiv`: the canonical isomorphism
  `(D.titsSystem k).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_sup_weylSubgroup` and
  `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup`:
  `D.borelSubgroup A ⊔ D.weylSubgroup A = D.extendedElementarySubgroup A` and
  `D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.doubleCoset_weylElement_mul_subset`: the Tits double-coset
  multiplication inclusion over any field `k`.
* `TauCeti.DynkinType.ChevalleyDatum.mem_extendedElementarySubgroup_iff_exists_mem_doubleCoset`
  and `TauCeti.DynkinType.ChevalleyDatum.doubleCoset_borelSubgroup_eq_iff`: covering and
  Weyl-indexed separation of `B`-double cosets in `D.points k`.
* `positivePoints_inf_map_negativePoints_eq_iSup`,
  `eq_and_eq_of_mem_positivePoints_inf_map_negativePoints_of_mem_borelSubgroup_of_mul_mul_eq`,
  `mem_doubleCoset_borelSubgroup_iff_exists_mul`, and
  `existsUnique_mul_weylSubgroup_mul_eq_of_mem_doubleCoset_borelSubgroup`:
  root-subgroup characterization of `U(k) ∩ n U⁻(k) n⁻¹` and Steinberg's unique factorization on
  each Bruhat cell.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorems 4 and 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§8.2–8.4.
-/

public section

open scoped Pointwise
open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Join and intersection of `borelSubgroup` and `weylSubgroup` -/

/-- All positive points lie in the elementary subgroup over every commutative ring. -/
theorem positivePoints_le_elementarySubgroup (A : Type v) [CommRing A] :
    D.positivePoints A ≤ D.elementarySubgroup A :=
  D.positivePoints_le_iff.mpr fun γ _ u => D.rootSubgroupPoints_mem_elementarySubgroup A γ u

/-- All negative points lie in the elementary subgroup over every commutative ring. -/
theorem negativePoints_le_elementarySubgroup (A : Type v) [CommRing A] :
    D.negativePoints A ≤ D.elementarySubgroup A :=
  D.negativePoints_le_iff.mpr fun γ _ u => D.rootSubgroupPoints_mem_elementarySubgroup A γ u

/-- The Borel-type subgroup is contained in the extended elementary subgroup over every commutative
ring. -/
theorem borelSubgroup_le_extendedElementarySubgroup (A : Type v) [CommRing A] :
    D.borelSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.borelSubgroup_def, D.extendedElementarySubgroup_def]
  exact sup_le ((D.positivePoints_le_elementarySubgroup A).trans le_sup_left) le_sup_right

/-- The Weyl subgroup is contained in the extended elementary subgroup over every commutative
ring. -/
theorem weylSubgroup_le_extendedElementarySubgroup (A : Type v) [CommRing A] :
    D.weylSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.weylSubgroup_def, Subgroup.closure_le]
  rintro g (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · exact D.torusPoints_mem_extendedElementarySubgroup A s
  · dsimp only
    rw [D.weylElement_def]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact D.elementarySubgroup_le_extendedElementarySubgroup A
        (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)

/-- **Over every commutative ring, the Borel-type subgroup and the Weyl subgroup generate the
extended elementary subgroup.** -/
@[simp]
theorem borelSubgroup_sup_weylSubgroup (A : Type v) [CommRing A] :
    D.borelSubgroup A ⊔ D.weylSubgroup A = D.extendedElementarySubgroup A := by
  apply le_antisymm
  · exact sup_le (D.borelSubgroup_le_extendedElementarySubgroup A)
      (D.weylSubgroup_le_extendedElementarySubgroup A)
  · rw [D.extendedElementarySubgroup_def, sup_le_iff]
    refine ⟨?_, (D.range_torusPoints_le_borelSubgroup A).trans le_sup_left⟩
    rw [D.elementarySubgroup_eq_closure_simpleRootPair A, Subgroup.closure_iUnion, iSup_le_iff]
    intro i
    rw [D.closure_simpleRootPair_eq i A, Subgroup.closure_le]
    rintro g ((⟨u, rfl⟩ | ⟨s, rfl⟩) | rfl)
    · exact Subgroup.mem_sup_left (D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A (simpleIndex_mem_posRoots i) u))
    · rw [D.simpleCorootPoints_eq_torusPoints]
      exact Subgroup.mem_sup_left (D.range_torusPoints_le_borelSubgroup A ⟨_, rfl⟩)
    · exact Subgroup.mem_sup_right (D.weylElement_simpleIndex_one_mem_weylSubgroup A i)

private theorem borelSubgroup_inf_weylSubgroup_field (k : Type v) [Field k] :
    D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  apply le_antisymm
  · rintro g ⟨hgB, hgN⟩
    let n : D.weylSubgroup k := ⟨g, hgN⟩
    suffices hw : D.weylProjection k n = 1 by
      have hker : n ∈ (D.weylProjection k).ker := hw
      rwa [D.ker_weylProjection, Subgroup.mem_subgroupOf] at hker
    refine eq_one_of_forall_mem_support_mem_posRoots P b fun γ hγ => ?_
    by_contra hneg
    have hγ_pos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [posRoots_rationalRootSystem]
      exact support_subset_posRoots P b hγ
    have hneg_rat :
        P.weylGroupToPerm (D.weylProjection k n) γ ∈
          negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [← not_mem_posRoots_iff_mem_negRoots, posRoots_rationalRootSystem]
      exact hneg
    obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints k n γ
    have hconj := hc ((c⁻¹ : kˣ) : k)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hconj
    have hmemB :
        D.rootSubgroupPoints (P.weylGroupToPerm (D.weylProjection k n) γ) k (ofAdd 1) ∈
          D.borelSubgroup k := by
      rw [← hconj, MulAut.conj_apply]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ hgB
          (D.positivePoints_le_borelSubgroup k
            (D.rootSubgroupPoints_mem_positivePoints k hγ_pos _)))
        (Subgroup.inv_mem _ hgB)
    rw [D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots k hneg_rat] at hmemB
    exact D.rootSubgroupPoints_ofAdd_one_ne_one k _ hmemB
  · refine le_inf (D.range_torusPoints_le_borelSubgroup k) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup k s

/-- **Intersection of the Borel and Weyl subgroups.** Over every commutative ring `A`,
`D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range`. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup (A : Type v) [CommRing A] :
    D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range := by
  apply le_antisymm
  · rintro g ⟨hgB, hgN⟩
    rcases subsingleton_or_nontrivial A with hsub | _
    · exact ⟨1, Subtype.ext (Units.ext (Matrix.ext fun _ _ => Subsingleton.elim _ _))⟩
    · obtain ⟨s, l, rfl⟩ := (D.mem_weylSubgroup_iff A).mp hgN
      have hwB : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈
          D.borelSubgroup A := by
        simpa using (D.borelSubgroup A).mul_mem
          ((D.borelSubgroup A).inv_mem (D.range_torusPoints_le_borelSubgroup A ⟨s, rfl⟩)) hgB
      -- Reduce modulo a maximal ideal to detect that `l` spells `1` in the Weyl group.
      obtain ⟨M, hM⟩ := Ideal.exists_maximal A
      let _ : M.IsMaximal := hM
      let _ := Ideal.Quotient.field M
      let π := (D.pointsPresentation A).map (D.pointsPresentation (A ⧸ M)) (Ideal.Quotient.mk M)
      have hπ_weyl (i : Fin t.rank) :
          π (D.weylElement (t.simpleIndex ht i) A 1) =
            D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1 := by
        apply Subtype.ext
        rw [GeneralLinear.IntegralPointsPresentation.coe_map, D.map_weylElement, map_one]
      have hπ_word :
          π ((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod) =
            (l.map fun i => D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1).prod := by
        rw [map_list_prod, List.map_map]
        exact congrArg List.prod (List.map_congr_left fun i _ => hπ_weyl i)
      have hwB_quot :
          (l.map fun i => D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1).prod ∈
            D.borelSubgroup (A ⧸ M) :=
        D.map_borelSubgroup_le A (Ideal.Quotient.mk M) ⟨_, hwB, hπ_word⟩
      have hmemT_quot :
          (l.map fun i => D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1).prod ∈
            (D.torusPoints (A ⧸ M)).range := by
        rw [← D.borelSubgroup_inf_weylSubgroup_field (A ⧸ M)]
        exact ⟨hwB_quot, D.weylWord_mem_weylSubgroup (A ⧸ M) l⟩
      have hl : t.geckWeylWordProd ht l = 1 := by
        have hker :
            (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1).prod,
                D.weylWord_mem_weylSubgroup (A ⧸ M) l⟩ : D.weylSubgroup (A ⧸ M)) ∈
              (D.weylProjection (A ⧸ M)).ker := by
          rw [D.ker_weylProjection]
          exact hmemT_quot
        rwa [MonoidHom.mem_ker, D.weylProjection_weylWord] at hker
      exact Subgroup.mul_mem _ ⟨s, rfl⟩
        (D.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one A l hl)
  · refine le_inf (D.range_torusPoints_le_borelSubgroup A) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup A s

/-- Double cosets modulo `(D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A)` coincide
with ambient `D.borelSubgroup A`-double cosets inside `D.points A`. -/
@[simp]
theorem mem_doubleCoset_borelSubgroup_subgroupOf_iff (A : Type v) [CommRing A]
    (g h : D.extendedElementarySubgroup A) :
    g ∈ DoubleCoset.doubleCoset h
        ((D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A))
        ((D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A)) ↔
      (g : D.points A) ∈
        DoubleCoset.doubleCoset (h : D.points A) (D.borelSubgroup A) (D.borelSubgroup A) := by
  have hmap :
      ((D.extendedElementarySubgroup A).subtype : _ → D.points A) ''
          (((D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A) :
            Subgroup _) : Set _) =
        (D.borelSubgroup A : Set (D.points A)) := by
    rw [← Subgroup.coe_map,
      Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup A)]
  rw [← DoubleCoset.mem_doubleCoset_image_iff (D.extendedElementarySubgroup A).subtype_injective,
    hmap]
  rfl

/-! ## The Tits double-coset multiplication law over a field -/

private theorem conj_inv_rootSubgroupPoints_mem_borelSubgroup (k : Type v) [Field k]
    (w : D.weylSubgroup k) {γ : Fin t.numRoots}
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k w⁻¹) γ ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : Multiplicative k) :
    (w : D.points k)⁻¹ * D.rootSubgroupPoints γ k u * (w : D.points k) ∈ D.borelSubgroup k := by
  have hmem :
      MulAut.conj ((w⁻¹ : D.weylSubgroup k) : D.points k) (D.rootSubgroupPoints γ k u) ∈
        (D.rootSubgroupPoints γ k).range.map
          (MulAut.conj ((w⁻¹ : D.weylSubgroup k) : D.points k)).toMonoidHom :=
    ⟨D.rootSubgroupPoints γ k u, ⟨u, rfl⟩, rfl⟩
  rw [D.map_range_rootSubgroupPoints_conj] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hconj :
      MulAut.conj ((w⁻¹ : D.weylSubgroup k) : D.points k) (D.rootSubgroupPoints γ k u) =
        (w : D.points k)⁻¹ * D.rootSubgroupPoints γ k u * (w : D.points k) := by
    simp
  rw [← hconj, ← hv]
  exact D.positivePoints_le_borelSubgroup k (D.rootSubgroupPoints_mem_positivePoints k hpos v)

private theorem weylGroupToPerm_inv_weylElement_mul_mem_posRoots (k : Type v) [Field k]
    (i : Fin t.rank) (w : D.weylSubgroup k)
    (hnot : (t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection k w⁻¹) (t.simpleIndex ht i) ∉
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    let nᵢ : D.weylSubgroup k :=
      ⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_simpleIndex_one_mem_weylSubgroup k i⟩
    (t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection k (nᵢ * w)⁻¹) (t.simpleIndex ht i) ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  intro nᵢ
  let P := t.simplyConnectedRootDatum ht
  let β := P.weylGroupToPerm (D.weylProjection k w⁻¹) (t.simpleIndex ht i)
  have hneg_perm :
      P.weylGroupToPerm (D.weylProjection k w⁻¹)
          (P.reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) =
        (t.rationalRootSystem ht).reflectionPerm β β := by
    let _ := P.indexNeg
    rw [t.reflectionPerm_rationalRootSystem ht, ← RootPairing.indexNeg_neg,
      ← RootPairing.indexNeg_neg, P.weylGroupToPerm_neg]
  have hproj :
      P.weylGroupToPerm (D.weylProjection k (nᵢ * w)⁻¹) (t.simpleIndex ht i) =
        (t.rationalRootSystem ht).reflectionPerm β β := by
    rw [mul_inv_rev, map_mul, map_mul, Equiv.Perm.mul_apply, map_inv (D.weylProjection k) nᵢ]
    dsimp only [nᵢ]
    rw [D.weylProjection_weylElement_simpleIndex_one, RootPairing.weylGroup.ofIdx_inv_eq,
      RootPairing.weylGroupToPerm_ofIdx_apply]
    exact hneg_perm
  rw [hproj, reflectionPerm_self_mem_posRoots_iff_mem_negRoots]
  exact (not_mem_posRoots_iff_mem_negRoots _ _ β).mp hnot

/-- Rank-one Bruhat exchange step when `w⁻¹ αᵢ` is negative and the root parameter `a` is a unit:
rewriting `nᵢ xᵢ(a) nᵢ` places the left factors in `B` and pushes the right factor past `nᵢ w`. -/
private theorem weylElement_mul_rootSubgroupPoints_unit_mul_mem_doubleCoset (k : Type v) [Field k]
    (i : Fin t.rank) (a : kˣ) (w : D.weylSubgroup k)
    (hnot : (t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection k w⁻¹) (t.simpleIndex ht i) ∉
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) k 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (a : k)) * (w : D.points k) ∈
      DoubleCoset.doubleCoset (w : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) := by
  let nᵢ : D.weylSubgroup k :=
    ⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_simpleIndex_one_mem_weylSubgroup k i⟩
  let w' : D.weylSubgroup k := nᵢ * w
  let h₀ := D.simpleCorootPoints i k (-1)
  -- Commute the rank-one inverse-exchange factors across `h₀⁻¹ = nᵢ⁻²` and `w' = nᵢ w`.
  have hpos' := D.weylGroupToPerm_inv_weylElement_mul_mem_posRoots k i w hnot
  obtain ⟨u', hu'⟩ :
      ∃ u', h₀ * D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((a⁻¹ : kˣ) : k))) *
          h₀⁻¹ = D.rootSubgroupPoints (t.simpleIndex ht i) k u' :=
    ⟨_, D.simpleCorootPoints_conj_rootSubgroup i k (-1) (-((a⁻¹ : kˣ) : k))⟩
  have hxcomm :
      D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((a⁻¹ : kˣ) : k))) * h₀⁻¹ =
        h₀⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k u' := by
    rw [← hu']
    group
  have hb₀ :
      D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((a⁻¹ : kˣ) : k))) *
        D.simpleCorootPoints i k (-a⁻¹) ∈ D.borelSubgroup k :=
    Subgroup.mul_mem _
      (D.positivePoints_le_borelSubgroup k
        (D.rootSubgroupPoints_mem_positivePoints k (simpleIndex_mem_posRoots i) _))
      (by
        rw [D.simpleCorootPoints_eq_torusPoints]
        exact D.range_torusPoints_le_borelSubgroup k ⟨_, rfl⟩)
  have hw_eq : (w : D.points k) = (nᵢ : D.points k) * h₀⁻¹ * (w' : D.points k) := by
    have hn_sq : (nᵢ : D.points k) * (nᵢ : D.points k) = h₀ := D.weylElement_mul_self i k
    simp only [w', Subgroup.coe_mul, ← hn_sq]
    group
  -- Reassemble `nᵢ xᵢ(a) w` as a `B`-double coset around `w` using `nᵢ xᵢ(a) nᵢ`.
  refine DoubleCoset.mem_doubleCoset.mpr
    ⟨_, hb₀,
      (w' : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k u' * (w' : D.points k),
      D.conj_inv_rootSubgroupPoints_mem_borelSubgroup k w' hpos' u', ?_⟩
  calc
    D.weylElement (t.simpleIndex ht i) k 1 *
          D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (a : k)) * (w : D.points k)
        = ((nᵢ : D.points k) * D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (a : k)) *
            (nᵢ : D.points k)) * h₀⁻¹ * (w' : D.points k) := by
          rw [hw_eq]
          dsimp only [nᵢ]
          group
    _ = (D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((a⁻¹ : kˣ) : k))) *
          D.simpleCorootPoints i k (-a⁻¹) * (nᵢ : D.points k)) *
          (h₀⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k u') * (w' : D.points k) := by
          dsimp only [nᵢ]
          rw [D.weylElement_mul_rootSubgroup_mul_weylElement i k a, mul_assoc _ _ h₀⁻¹, hxcomm]
    _ = D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((a⁻¹ : kˣ) : k))) *
          D.simpleCorootPoints i k (-a⁻¹) * (w : D.points k) *
          ((w' : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k u' *
            (w' : D.points k)) := by
          rw [hw_eq]
          group

private theorem weylElement_mul_rootSubgroupPoints_mul_mem_union (k : Type v) [Field k]
    (i : Fin t.rank) (u : Multiplicative k) (w : D.weylSubgroup k) :
    D.weylElement (t.simpleIndex ht i) k 1 * D.rootSubgroupPoints (t.simpleIndex ht i) k u *
        (w : D.points k) ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1 * (w : D.points k))
          (D.borelSubgroup k) (D.borelSubgroup k) ∪
        DoubleCoset.doubleCoset (w : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) := by
  -- If `w⁻¹ αᵢ > 0`, conjugate `xᵢ(u)` directly across `w` into `B`.
  by_cases hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm
      (D.weylProjection k w⁻¹) (t.simpleIndex ht i) ∈
    posRoots (t.rationalRootSystem ht) (t.rationalBase ht)
  · exact Or.inl <| DoubleCoset.mem_doubleCoset.mpr
      ⟨1, (D.borelSubgroup k).one_mem,
        (w : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k u * (w : D.points k),
        D.conj_inv_rootSubgroupPoints_mem_borelSubgroup k w hpos u, by group⟩
  -- When `w⁻¹ αᵢ < 0`, split on whether the additive parameter vanishes or is a unit.
  · by_cases hu : toAdd u = 0
    · have hu1 : D.rootSubgroupPoints (t.simpleIndex ht i) k u = 1 := by
        rw [← ofAdd_toAdd u, hu, ofAdd_zero, map_one]
      rw [hu1, mul_one]
      exact Or.inl (DoubleCoset.mem_doubleCoset_self _ _ _)
    · rw [← ofAdd_toAdd u]
      exact Or.inr <|
        D.weylElement_mul_rootSubgroupPoints_unit_mul_mem_doubleCoset k i
          (Units.mk0 (toAdd u) hu) w hpos

/-- **The Tits double-coset multiplication law for a Chevalley datum over any field `k`.** -/
theorem doubleCoset_weylElement_mul_subset (k : Type v) [Field k] (i : Fin t.rank)
    (w : D.weylSubgroup k) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) *
      DoubleCoset.doubleCoset (w : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) ⊆
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1 * (w : D.points k))
        (D.borelSubgroup k) (D.borelSubgroup k) ∪
      DoubleCoset.doubleCoset (w : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) := by
  rintro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz
  -- Factor `b₂ * b₃ ∈ U⁽ⁱ⁾ Xᵢ T` and sweep `U⁽ⁱ⁾` left past `nᵢ` and `T` right past `w`.
  obtain ⟨u, hu, s, hs⟩ := (D.mem_borelSubgroup_iff k).mp ((D.borelSubgroup k).mul_mem hb₂ hb₃)
  obtain ⟨v, hv, a, rfl⟩ := (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints i k u).mp hu
  let nᵢ := D.weylElement (t.simpleIndex ht i) k 1
  have hv' : nᵢ * v * nᵢ⁻¹ ∈ D.borelSubgroup k := by
    have hnorm := (Subgroup.mem_normalizer_iff.mp
      (D.weylElement_mem_normalizer_positivePoints_diff_singleton i k 1) v).mp hv
    have hle :
        (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
          (D.rootSubgroupPoints γ k).range : Subgroup (D.points k)) ≤ D.positivePoints k :=
      iSup₂_le fun γ hγ => by
        rintro _ ⟨c, rfl⟩
        exact D.rootSubgroupPoints_mem_positivePoints k hγ.1 c
    exact D.positivePoints_le_borelSubgroup k (hle hnorm)
  have htw : (w : D.points k)⁻¹ * D.torusPoints k s * (w : D.points k) ∈ D.borelSubgroup k :=
    D.range_torusPoints_le_borelSubgroup k <|
      (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints k w.property) _).mpr ⟨s, by group⟩
  have hbL : b₁ * (nᵢ * v * nᵢ⁻¹) ∈ D.borelSubgroup k := (D.borelSubgroup k).mul_mem hb₁ hv'
  have hbR : (w : D.points k)⁻¹ * D.torusPoints k s * (w : D.points k) * b₄ ∈ D.borelSubgroup k :=
    (D.borelSubgroup k).mul_mem htw hb₄
  -- Reduce the remaining middle factor `nᵢ xᵢ(a) w` via the rank-one exchange lemma.
  have hmid := D.weylElement_mul_rootSubgroupPoints_mul_mem_union k i a w
  have hmul_eq :
      (b₁ * nᵢ * b₂) * (b₃ * (w : D.points k) * b₄) =
        (b₁ * (nᵢ * v * nᵢ⁻¹)) * (nᵢ * D.rootSubgroupPoints (t.simpleIndex ht i) k a *
          (w : D.points k)) *
          ((w : D.points k)⁻¹ * D.torusPoints k s * (w : D.points k) * b₄) := by
    have hb₂₃ : b₂ * b₃ = v * D.rootSubgroupPoints (t.simpleIndex ht i) k a * D.torusPoints k s :=
      hs.symm
    calc
      (b₁ * nᵢ * b₂) * (b₃ * (w : D.points k) * b₄)
          = b₁ * nᵢ * (b₂ * b₃) * (w : D.points k) * b₄ := by group
      _ = _ := by
        rw [hb₂₃]
        group
  rw [hmul_eq]
  rcases hmid with hm | hm
  · obtain ⟨c₁, hc₁, c₂, hc₂, hcm⟩ := DoubleCoset.mem_doubleCoset.mp hm
    exact Or.inl <| DoubleCoset.mem_doubleCoset.mpr
      ⟨_, (D.borelSubgroup k).mul_mem hbL hc₁, _, (D.borelSubgroup k).mul_mem hc₂ hbR,
        by dsimp only [nᵢ]; rw [hcm]; group⟩
  · obtain ⟨c₁, hc₁, c₂, hc₂, hcm⟩ := DoubleCoset.mem_doubleCoset.mp hm
    exact Or.inr <| DoubleCoset.mem_doubleCoset.mpr
      ⟨_, (D.borelSubgroup k).mul_mem hbL hc₁, _, (D.borelSubgroup k).mul_mem hc₂ hbR,
        by dsimp only [nᵢ]; rw [hcm]; group⟩

/-! ## The Tits system on `extendedElementarySubgroup` over a field -/

private noncomputable def weylSubgroupOfProjection (k : Type v) [Field k] :
    (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) →*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (D.weylProjection k).comp
    (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup k)).toMonoidHom

@[simp]
private theorem weylSubgroupOfProjection_apply (k : Type v) [Field k]
    (n : (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) :
    D.weylSubgroupOfProjection k n =
      D.weylProjection k ⟨((n : D.extendedElementarySubgroup k) : D.points k), n.property⟩ := by
  simp only [weylSubgroupOfProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1

private theorem weylSubgroupOfProjection_surjective (k : Type v) [Field k] :
    Function.Surjective (D.weylSubgroupOfProjection k) :=
  (D.weylProjection_surjective k).comp
    (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup k)).surjective

private theorem ker_weylSubgroupOfProjection (k : Type v) [Field k] :
    ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
        ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) =
      (D.weylSubgroupOfProjection k).ker := by
  ext n
  simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, D.weylSubgroupOfProjection_apply]
  have hn_mem :
      ((n : D.extendedElementarySubgroup k) : D.points k) ∈ D.borelSubgroup k ↔
        ((n : D.extendedElementarySubgroup k) : D.points k) ∈
          D.borelSubgroup k ⊓ D.weylSubgroup k :=
    ⟨fun h => ⟨h, n.property⟩, fun h => h.1⟩
  rw [hn_mem, D.borelSubgroup_inf_weylSubgroup, ← MonoidHom.mem_ker, D.ker_weylProjection,
    Subgroup.mem_subgroupOf]

private noncomputable def simpleSubgroupRep (A : Type v) [CommRing A] (i : Fin t.rank) :
    (D.weylSubgroup A).subgroupOf (D.extendedElementarySubgroup A) :=
  ⟨⟨D.weylElement (t.simpleIndex ht i) A 1,
      D.weylSubgroup_le_extendedElementarySubgroup A
        (D.weylElement_simpleIndex_one_mem_weylSubgroup A i)⟩,
    D.weylElement_simpleIndex_one_mem_weylSubgroup A i⟩

@[simp]
private theorem coe_simpleSubgroupRep (A : Type v) [CommRing A] (i : Fin t.rank) :
    (((D.simpleSubgroupRep A i :
        (D.weylSubgroup A).subgroupOf (D.extendedElementarySubgroup A)) :
        D.extendedElementarySubgroup A) : D.points A) =
      D.weylElement (t.simpleIndex ht i) A 1 :=
  (rfl)

private noncomputable def weylSubgroupOfQuotientEquiv (k : Type v) [Field k] :
    letI : (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
        ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
      rw [D.ker_weylSubgroupOfProjection k]; infer_instance
    ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) ⧸
        ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
          ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup := by
  letI : (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
      ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
    rw [D.ker_weylSubgroupOfProjection k]; infer_instance
  exact (QuotientGroup.quotientMulEquivOfEq (D.ker_weylSubgroupOfProjection k)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylSubgroupOfProjection k)
      (D.weylSubgroupOfProjection_surjective k))

@[simp]
private theorem weylSubgroupOfQuotientEquiv_mk (k : Type v) [Field k]
    (n : (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) :
    letI : (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
        ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
      rw [D.ker_weylSubgroupOfProjection k]; infer_instance
    D.weylSubgroupOfQuotientEquiv k (QuotientGroup.mk n) = D.weylSubgroupOfProjection k n := by
  simp [weylSubgroupOfQuotientEquiv, QuotientGroup.quotientKerEquivOfSurjective]

private theorem closure_range_mk_simpleSubgroupRep (k : Type v) [Field k] :
    letI : (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
        ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
      rw [D.ker_weylSubgroupOfProjection k]; infer_instance
    Subgroup.closure
      (Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.simpleSubgroupRep k i) :
          (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) ⧸
            ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
              ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)))) = ⊤ := by
  let _ : (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
      ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
    rw [D.ker_weylSubgroupOfProjection k]; infer_instance
  let φ := D.weylSubgroupOfQuotientEquiv k
  have hword (l : List (Fin t.rank)) :
      φ ((l.map fun i => QuotientGroup.mk (D.simpleSubgroupRep k i)).prod) =
        t.geckWeylWordProd ht l := by
    induction l with
    | nil => simp [geckWeylWordProd_nil]
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih, geckWeylWordProd_cons]
      have hmk : φ (QuotientGroup.mk (D.simpleSubgroupRep k i)) =
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
        rw [D.weylSubgroupOfQuotientEquiv_mk, D.weylSubgroupOfProjection_apply]
        simp only [D.coe_simpleSubgroupRep, D.weylProjection_weylElement_simpleIndex_one]
      rw [hmk]
  rw [eq_top_iff]
  intro x _
  obtain ⟨l, hl⟩ := t.geckWeylWordProd_surjective ht (φ x)
  have hx : (l.map fun i => QuotientGroup.mk (D.simpleSubgroupRep k i)).prod = x :=
    φ.injective ((hword l).trans hl)
  rw [← hx]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  rw [List.mem_map] at hy
  obtain ⟨i, _, rfl⟩ := hy
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- **The canonical Tits system on `D.extendedElementarySubgroup k` over any field `k`.** -/
noncomputable def titsSystem (k : Type v) [Field k] :
    TitsSystem (D.extendedElementarySubgroup k) where
  subgroupB := (D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)
  subgroupN := (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)
  closure_subgroupB_union_subgroupN := by
    rw [← Subgroup.sup_eq_closure,
      ← Subgroup.subgroupOf_sup (D.borelSubgroup_le_extendedElementarySubgroup k)
        (D.weylSubgroup_le_extendedElementarySubgroup k),
      D.borelSubgroup_sup_weylSubgroup, Subgroup.subgroupOf_self]
  intersection_normal := by
    rw [D.ker_weylSubgroupOfProjection k]
    infer_instance
  simple := Set.range fun i : Fin t.rank => QuotientGroup.mk (D.simpleSubgroupRep k i)
  closure_simple := D.closure_range_mk_simpleSubgroupRep k
  exists_simpleRep_mul_self_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleSubgroupRep k i, rfl, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      D.coe_simpleSubgroupRep, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup k ⟨_, rfl⟩
  mul_doubleCoset_subset s hs := by
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleSubgroupRep k i, rfl, fun w x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
    rw [D.mem_doubleCoset_borelSubgroup_subgroupOf_iff] at hy hz
    rcases D.doubleCoset_weylElement_mul_subset k i ⟨(w : D.points k), w.property⟩
        (Set.mul_mem_mul hy hz) with h1 | h2
    · exact Or.inl ((D.mem_doubleCoset_borelSubgroup_subgroupOf_iff k _ _).mpr h1)
    · exact Or.inr ((D.mem_doubleCoset_borelSubgroup_subgroupOf_iff k _ _).mpr h2)
  exists_conj_not_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup k i
    refine ⟨D.simpleSubgroupRep k i, rfl,
      ⟨⟨b.val, D.borelSubgroup_le_extendedElementarySubgroup k b.property⟩, b.property⟩, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      D.coe_simpleSubgroupRep]
    exact hb

/-- The `B` subgroup of `D.titsSystem k` is `D.borelSubgroup k` restricted to
`D.extendedElementarySubgroup k`. -/
@[simp]
theorem titsSystem_subgroupB (k : Type v) [Field k] :
    (D.titsSystem k).subgroupB =
      (D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :=
  (rfl)

/-- The `N` subgroup of `D.titsSystem k` is `D.weylSubgroup k` restricted to
`D.extendedElementarySubgroup k`. -/
@[simp]
theorem titsSystem_subgroupN (k : Type v) [Field k] :
    (D.titsSystem k).subgroupN =
      (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :=
  (rfl)

/-- In `D.titsSystem k`, the intersection `B ∩ N` consists of the points of the actual torus
`T_D(k)`. -/
theorem titsSystem_mem_intersection (k : Type v) [Field k] (n : (D.titsSystem k).subgroupN) :
    n ∈ (D.titsSystem k).intersection ↔
      ((n : D.extendedElementarySubgroup k) : D.points k) ∈ (D.torusPoints k).range := by
  rw [TitsSystem.mem_intersection, D.titsSystem_subgroupB, Subgroup.mem_subgroupOf]
  have hn :
      ((n : D.extendedElementarySubgroup k) : D.points k) ∈ D.borelSubgroup k ↔
        ((n : D.extendedElementarySubgroup k) : D.points k) ∈
          D.borelSubgroup k ⊓ D.weylSubgroup k :=
    ⟨fun h => ⟨h, n.property⟩, fun h => h.1⟩
  rw [hn, D.borelSubgroup_inf_weylSubgroup]

/-- The `i`-th pinned simple Weyl representative in `(D.titsSystem k).subgroupN`. -/
noncomputable def titsSystemSimpleRep (k : Type v) [Field k] (i : Fin t.rank) :
    (D.titsSystem k).subgroupN :=
  D.simpleSubgroupRep k i

/-- Forgetting to `D.points k` sends `titsSystemSimpleRep` to
`D.weylElement (t.simpleIndex ht i) k 1`. -/
@[simp]
theorem coe_titsSystemSimpleRep (k : Type v) [Field k] (i : Fin t.rank) :
    (((D.titsSystemSimpleRep k i : (D.titsSystem k).subgroupN) :
        D.extendedElementarySubgroup k) : D.points k) =
      D.weylElement (t.simpleIndex ht i) k 1 :=
  D.coe_simpleSubgroupRep k i

/-- The simple reflections of `D.titsSystem k` are the classes of `D.titsSystemSimpleRep k i`. -/
@[simp]
theorem titsSystem_simple (k : Type v) [Field k] :
    (D.titsSystem k).simple =
      Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.titsSystemSimpleRep k i) : (D.titsSystem k).WeylGroup) :=
  (rfl)

/-- **The Weyl group of `D.titsSystem k` is canonically isomorphic to
`(t.simplyConnectedRootDatum ht).weylGroup`.** -/
noncomputable def titsSystemWeylGroupMulEquiv (k : Type v) [Field k] :
    (D.titsSystem k).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  D.weylSubgroupOfQuotientEquiv k

/-- `titsSystemWeylGroupMulEquiv` evaluates on a coset representative via `D.weylProjection k`. -/
@[simp]
theorem titsSystemWeylGroupMulEquiv_mk (k : Type v) [Field k] (n : (D.titsSystem k).subgroupN) :
    D.titsSystemWeylGroupMulEquiv k (QuotientGroup.mk n) =
      D.weylProjection k
        ⟨((n : D.extendedElementarySubgroup k) : D.points k),
          by simpa only [titsSystem_subgroupN, Subgroup.mem_subgroupOf] using n.property⟩ :=
  (D.weylSubgroupOfQuotientEquiv_mk k n).trans (D.weylSubgroupOfProjection_apply k n)

/-- `titsSystemWeylGroupMulEquiv` sends the `i`-th simple representative to the `i`-th simple
reflection of `(t.simplyConnectedRootDatum ht).weylGroup`. -/
theorem titsSystemWeylGroupMulEquiv_simpleRep (k : Type v) [Field k] (i : Fin t.rank) :
    D.titsSystemWeylGroupMulEquiv k (QuotientGroup.mk (D.titsSystemSimpleRep k i)) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.titsSystemWeylGroupMulEquiv_mk, ← D.weylProjection_weylElement_simpleIndex_one k i]
  exact congrArg (D.weylProjection k) (Subtype.ext (D.coe_titsSystemSimpleRep k i))

/-- The simple reflections of `D.titsSystem k` correspond under `titsSystemWeylGroupMulEquiv` to
the simple reflections of `(t.simplyConnectedRootDatum ht).weylGroup`. -/
theorem titsSystem_simple_eq_preimage (k : Type v) [Field k] :
    (D.titsSystem k).simple =
      D.titsSystemWeylGroupMulEquiv k ⁻¹'
        Set.range fun i : Fin t.rank =>
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  ext w
  simp only [titsSystem_simple, Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (D.titsSystemWeylGroupMulEquiv_simpleRep k i).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (D.titsSystemWeylGroupMulEquiv k).injective
      (by rw [D.titsSystemWeylGroupMulEquiv_simpleRep, hi])⟩

/-! ## Bruhat decomposition and Steinberg's unique normal form -/

/-- **Bruhat decomposition indexed by `(t.simplyConnectedRootDatum ht).weylGroup`**: every element
of `D.extendedElementarySubgroup k` belongs to the Bruhat cell of a unique element of the root
datum's Weyl group. -/
theorem existsUnique_mem_bruhatCell_titsSystemWeylGroupMulEquiv_symm (k : Type v) [Field k]
    (g : D.extendedElementarySubgroup k) :
    ∃! w : (t.simplyConnectedRootDatum ht).weylGroup,
      g ∈ (D.titsSystem k).bruhatCell ((D.titsSystemWeylGroupMulEquiv k).symm w) := by
  obtain ⟨w₀, hw₀, huniq⟩ := (D.titsSystem k).existsUnique_mem_bruhatCell g
  refine ⟨D.titsSystemWeylGroupMulEquiv k w₀, by simpa using hw₀, fun w hw => ?_⟩
  simpa using congrArg (D.titsSystemWeylGroupMulEquiv k) (huniq _ hw)

/-- **Bruhat covering inside `D.points k`**: over any field `k`, a datum point belongs to
`D.extendedElementarySubgroup k` if and only if it belongs to a `B`-double coset represented by
`D.weylSubgroup k`. -/
theorem mem_extendedElementarySubgroup_iff_exists_mem_doubleCoset (k : Type v) [Field k]
    {g : D.points k} :
    g ∈ D.extendedElementarySubgroup k ↔
      ∃ n : D.weylSubgroup k,
        g ∈ DoubleCoset.doubleCoset (n : D.points k)
          (D.borelSubgroup k) (D.borelSubgroup k) := by
  constructor
  · intro hg
    obtain ⟨n₀, hn₀⟩ := (D.titsSystem k).exists_mem_doubleCoset ⟨g, hg⟩
    rw [D.titsSystem_subgroupB, D.mem_doubleCoset_borelSubgroup_subgroupOf_iff] at hn₀
    exact ⟨⟨((n₀ : D.extendedElementarySubgroup k) : D.points k),
      by simpa only [titsSystem_subgroupN, Subgroup.mem_subgroupOf] using n₀.property⟩, hn₀⟩
  · rintro ⟨n, hn⟩
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hn
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (D.borelSubgroup_le_extendedElementarySubgroup k hb₁)
        (D.weylSubgroup_le_extendedElementarySubgroup k n.property))
      (D.borelSubgroup_le_extendedElementarySubgroup k hb₂)

/-- **Bruhat separation inside `D.points k`**: if a datum point lies in the `B`-double cosets of
two Weyl lifts `n₁, n₂ : D.weylSubgroup k`, then `n₁` and `n₂` have the same Weyl projection. -/
theorem weylProjection_eq_of_mem_doubleCoset_borelSubgroup (k : Type v) [Field k]
    {g : D.points k} {n₁ n₂ : D.weylSubgroup k}
    (h₁ : g ∈ DoubleCoset.doubleCoset (n₁ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k))
    (h₂ : g ∈ DoubleCoset.doubleCoset (n₂ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k)) :
    D.weylProjection k n₁ = D.weylProjection k n₂ := by
  have hg : g ∈ D.extendedElementarySubgroup k :=
    (D.mem_extendedElementarySubgroup_iff_exists_mem_doubleCoset k).mpr ⟨n₁, h₁⟩
  let m₁ : (D.titsSystem k).subgroupN :=
    ⟨⟨(n₁ : D.points k), D.weylSubgroup_le_extendedElementarySubgroup k n₁.property⟩, n₁.property⟩
  let m₂ : (D.titsSystem k).subgroupN :=
    ⟨⟨(n₂ : D.points k), D.weylSubgroup_le_extendedElementarySubgroup k n₂.property⟩, n₂.property⟩
  have hm₁ : (⟨g, hg⟩ : D.extendedElementarySubgroup k) ∈
      (D.titsSystem k).bruhatCell (QuotientGroup.mk m₁) := by
    rw [TitsSystem.bruhatCell_mk, D.titsSystem_subgroupB,
      D.mem_doubleCoset_borelSubgroup_subgroupOf_iff]
    exact h₁
  have hm₂ : (⟨g, hg⟩ : D.extendedElementarySubgroup k) ∈
      (D.titsSystem k).bruhatCell (QuotientGroup.mk m₂) := by
    rw [TitsSystem.bruhatCell_mk, D.titsSystem_subgroupB,
      D.mem_doubleCoset_borelSubgroup_subgroupOf_iff]
    exact h₂
  have heq := congrArg (D.titsSystemWeylGroupMulEquiv k)
    ((D.titsSystem k).eq_of_mem_bruhatCell_of_mem hm₁ hm₂)
  simpa only [D.titsSystemWeylGroupMulEquiv_mk, Subtype.coe_eta] using heq

/-- Two Weyl lifts determine the same `B`-double coset in `D.points k` if and only if they have the
same Weyl projection. -/
@[simp]
theorem doubleCoset_borelSubgroup_eq_iff (k : Type v) [Field k] (n₁ n₂ : D.weylSubgroup k) :
    DoubleCoset.doubleCoset (n₁ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) =
        DoubleCoset.doubleCoset (n₂ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) ↔
      D.weylProjection k n₁ = D.weylProjection k n₂ := by
  constructor
  · intro h
    have hn₁ : (n₁ : D.points k) ∈
        DoubleCoset.doubleCoset (n₁ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) :=
      DoubleCoset.mem_doubleCoset_self _ _ _
    exact D.weylProjection_eq_of_mem_doubleCoset_borelSubgroup k hn₁ (h ▸ hn₁)
  · intro h
    have hker : n₁⁻¹ * n₂ ∈ (D.weylProjection k).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [D.ker_weylProjection, Subgroup.mem_subgroupOf] at hker
    have hb : ((n₁⁻¹ * n₂ : D.weylSubgroup k) : D.points k) ∈ D.borelSubgroup k :=
      D.range_torusPoints_le_borelSubgroup k hker
    symm
    apply DoubleCoset.doubleCoset_eq_of_mem
    refine DoubleCoset.mem_doubleCoset.mpr ⟨1, (D.borelSubgroup k).one_mem, _, hb, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

/-- Two `B`-double cosets of Weyl lifts in `D.points k` are disjoint if and only if their Weyl
projections differ. -/
@[simp]
theorem disjoint_doubleCoset_borelSubgroup_iff (k : Type v) [Field k] (n₁ n₂ : D.weylSubgroup k) :
    Disjoint
        (DoubleCoset.doubleCoset (n₁ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k))
        (DoubleCoset.doubleCoset (n₂ : D.points k) (D.borelSubgroup k) (D.borelSubgroup k)) ↔
      D.weylProjection k n₁ ≠ D.weylProjection k n₂ := by
  constructor
  · rintro h heq
    rw [← D.doubleCoset_borelSubgroup_eq_iff] at heq
    exact Set.disjoint_left.mp h (DoubleCoset.mem_doubleCoset_self _ _ _)
      (heq ▸ DoubleCoset.mem_doubleCoset_self _ _ _)
  · intro hne
    rw [Set.disjoint_left]
    intro g h₁ h₂
    exact hne (D.weylProjection_eq_of_mem_doubleCoset_borelSubgroup k h₁ h₂)

/-- For every datum point `n`, the unipotent subgroup `U(A) ∩ n U⁻(A) n⁻¹` meets the conjugate
Borel subgroup `n B(A) n⁻¹` trivially, over every commutative ring `A`. -/
theorem disjoint_positivePoints_inf_map_negativePoints_map_borelSubgroup
    (A : Type v) [CommRing A] (n : D.points A) :
    Disjoint
      (D.positivePoints A ⊓ (D.negativePoints A).map (MulAut.conj n).toMonoidHom)
      ((D.borelSubgroup A).map (MulAut.conj n).toMonoidHom) := by
  rw [disjoint_iff, inf_assoc]
  refine le_bot_iff.mp (inf_le_right.trans_eq ?_)
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, D.borelSubgroup_def,
    D.negativePoints_inf_positivePoints_sup_range_torusPoints_eq_bot, Subgroup.map_bot]

/-- **Uniqueness in Steinberg's Bruhat normal form over an arbitrary commutative ring.** For any
datum point `n : D.points A`, if `u₁, u₂ ∈ U(A) ∩ n U⁻(A) n⁻¹` and `b₁, b₂ ∈ B(A)` satisfy
`u₁ * n * b₁ = u₂ * n * b₂`, then `u₁ = u₂` and `b₁ = b₂`. -/
theorem eq_and_eq_of_mem_positivePoints_inf_map_negativePoints_of_mem_borelSubgroup_of_mul_mul_eq
    (A : Type v) [CommRing A] (n : D.points A) {u₁ u₂ b₁ b₂ : D.points A}
    (hu₁ : u₁ ∈ D.positivePoints A ⊓ (D.negativePoints A).map (MulAut.conj n).toMonoidHom)
    (hu₂ : u₂ ∈ D.positivePoints A ⊓ (D.negativePoints A).map (MulAut.conj n).toMonoidHom)
    (hb₁ : b₁ ∈ D.borelSubgroup A) (hb₂ : b₂ ∈ D.borelSubgroup A)
    (heq : u₁ * n * b₁ = u₂ * n * b₂) :
    u₁ = u₂ ∧ b₁ = b₂ := by
  have hinj := Subgroup.mul_mul_injective_of_disjoint
    (D.positivePoints A ⊓ (D.negativePoints A).map (MulAut.conj n).toMonoidHom)
    (D.borelSubgroup A)
    (D.disjoint_positivePoints_inf_map_negativePoints_map_borelSubgroup A n)
  have hpair := hinj (a₁ := (⟨u₁, hu₁⟩, ⟨b₁, hb₁⟩)) (a₂ := (⟨u₂, hu₂⟩, ⟨b₂, hb₂⟩)) heq
  exact ⟨congrArg (Subtype.val ∘ Prod.fst) hpair, congrArg (Subtype.val ∘ Prod.snd) hpair⟩

private theorem iSup_inversions_le_positivePoints_inf_map_negativePoints (k : Type v) [Field k]
    (n : D.weylSubgroup k) :
    (⨆ γ ∈ {γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) |
        (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
          negRoots (t.rationalRootSystem ht) (t.rationalBase ht)},
      (D.rootSubgroupPoints γ k).range : Subgroup (D.points k)) ≤
      D.positivePoints k ⊓ (D.negativePoints k).map (MulAut.conj (n : D.points k)).toMonoidHom := by
  let P := t.simplyConnectedRootDatum ht
  let R := t.rationalRootSystem ht
  let rb := t.rationalBase ht
  let S : Set (Fin t.numRoots) :=
    {γ ∈ posRoots R rb | P.weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈ negRoots R rb}
  refine le_inf (iSup₂_le fun γ hγ => ?_) ?_
  · rintro _ ⟨c, rfl⟩
    exact D.rootSubgroupPoints_mem_positivePoints k hγ.1 c
  · have hconj :
        (⨆ γ ∈ S, (D.rootSubgroupPoints γ k).range).map
            (MulAut.conj ((n⁻¹ : D.weylSubgroup k) : D.points k)).toMonoidHom ≤
          D.negativePoints k := by
      rw [D.map_iSup_rootSubgroupPoints_conj]
      refine iSup₂_le fun δ hδ => ?_
      obtain ⟨γ, hγ, rfl⟩ := hδ
      rintro _ ⟨c, rfl⟩
      exact D.rootSubgroupPoints_mem_negativePoints k hγ.2 c
    intro u hu
    refine ⟨MulAut.conj ((n⁻¹ : D.weylSubgroup k) : D.points k) u, hconj ⟨u, hu, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv]
    group

private theorem map_iSup_posRoots_diff_inversions_conj_inv_le_borelSubgroup (k : Type v) [Field k]
    (n : D.weylSubgroup k) :
    (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \
        {γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) |
          (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
            negRoots (t.rationalRootSystem ht) (t.rationalBase ht)},
      (D.rootSubgroupPoints γ k).range).map
        (MulAut.conj ((n⁻¹ : D.weylSubgroup k) : D.points k)).toMonoidHom ≤
      D.borelSubgroup k := by
  rw [D.map_iSup_rootSubgroupPoints_conj]
  refine (iSup₂_le fun δ hδ => ?_).trans (D.positivePoints_le_borelSubgroup k)
  obtain ⟨γ, hγ, rfl⟩ := hδ
  have hpos :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    by_contra hnot
    exact hγ.2 ⟨hγ.1, (not_mem_posRoots_iff_mem_negRoots _ _ _).mp hnot⟩
  rintro _ ⟨c, rfl⟩
  exact D.rootSubgroupPoints_mem_positivePoints k hpos c

/-- **Root-subgroup characterization of the unipotent Bruhat cell factor `U(k) ∩ n U⁻(k) n⁻¹`**:
over any field `k`, it is generated by the positive root subgroups sent to negative roots by
`n⁻¹`. -/
theorem positivePoints_inf_map_negativePoints_eq_iSup (k : Type v) [Field k]
    (n : D.weylSubgroup k) :
    D.positivePoints k ⊓
        (D.negativePoints k).map (MulAut.conj (n : D.points k)).toMonoidHom =
      ⨆ γ ∈ {γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) |
          (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
            negRoots (t.rationalRootSystem ht) (t.rationalBase ht)},
        (D.rootSubgroupPoints γ k).range := by
  apply le_antisymm _ (D.iSup_inversions_le_positivePoints_inf_map_negativePoints k n)
  intro u hu
  let S : Set (Fin t.numRoots) :=
    {γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) |
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
        negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ :=
    (D.mem_positivePoints_iff_exists_mul_of_subset (S := S) (fun _ h => h.1) k u).mp hu.1
  have hu₁_mem := D.iSup_inversions_le_positivePoints_inf_map_negativePoints k n hu₁
  have hb : (n : D.points k)⁻¹ * u₂ * (n : D.points k) ∈ D.borelSubgroup k :=
    D.map_iSup_posRoots_diff_inversions_conj_inv_le_borelSubgroup k n ⟨u₂, hu₂, by simp⟩
  have heq :
      u * (n : D.points k) * 1 =
        u₁ * (n : D.points k) * ((n : D.points k)⁻¹ * u₂ * (n : D.points k)) := by
    rw [← hmul]
    group
  exact (D.eq_and_eq_of_mem_positivePoints_inf_map_negativePoints_of_mem_borelSubgroup_of_mul_mul_eq
    k (n : D.points k) hu hu₁_mem (D.borelSubgroup k).one_mem hb heq).1 ▸ hu₁

/-- **Steinberg's Bruhat cell factorization over a field**: every element of the `B`-double coset
of `n : D.weylSubgroup k` factors as `u * n * b` with `u ∈ U(k) ∩ n U⁻(k) n⁻¹` and `b ∈ B(k)`. -/
theorem mem_doubleCoset_borelSubgroup_iff_exists_mul (k : Type v) [Field k]
    (n : D.weylSubgroup k) {g : D.points k} :
    g ∈ DoubleCoset.doubleCoset (n : D.points k) (D.borelSubgroup k) (D.borelSubgroup k) ↔
      ∃ u ∈ D.positivePoints k ⊓
          (D.negativePoints k).map (MulAut.conj (n : D.points k)).toMonoidHom,
        ∃ b ∈ D.borelSubgroup k, u * (n : D.points k) * b = g := by
  constructor
  · intro hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    obtain ⟨u₀, hu₀, s, hs⟩ := (D.mem_borelSubgroup_iff k).mp hb₁
    let S : Set (Fin t.numRoots) :=
      {γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) |
        (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n⁻¹) γ ∈
          negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ :=
      (D.mem_positivePoints_iff_exists_mul_of_subset (S := S) (fun _ h => h.1) k u₀).mp hu₀
    have hu₁_mem := D.iSup_inversions_le_positivePoints_inf_map_negativePoints k n hu₁
    have hu₂_conj : (n : D.points k)⁻¹ * u₂ * (n : D.points k) ∈ D.borelSubgroup k :=
      D.map_iSup_posRoots_diff_inversions_conj_inv_le_borelSubgroup k n ⟨u₂, hu₂, by simp⟩
    have htn : (n : D.points k)⁻¹ * D.torusPoints k s * (n : D.points k) ∈ D.borelSubgroup k :=
      D.range_torusPoints_le_borelSubgroup k <|
        (Subgroup.mem_normalizer_iff.mp
          (D.weylSubgroup_le_normalizer_range_torusPoints k n.property) _).mpr ⟨s, by group⟩
    refine ⟨u₁, hu₁_mem,
      ((n : D.points k)⁻¹ * u₂ * (n : D.points k)) *
        ((n : D.points k)⁻¹ * D.torusPoints k s * (n : D.points k)) * b₂,
      (D.borelSubgroup k).mul_mem ((D.borelSubgroup k).mul_mem hu₂_conj htn) hb₂, ?_⟩
    rw [← hs]
    group
  · rintro ⟨u, hu, b, hb, rfl⟩
    exact DoubleCoset.mem_doubleCoset.mpr ⟨u, D.positivePoints_le_borelSubgroup k hu.1, b, hb, rfl⟩

/-- **Steinberg's unique normal form on each Bruhat cell over a field**: every element of the
`B`-double coset of `n : D.weylSubgroup k` factors uniquely as `u * n * b` with
`u ∈ U(k) ∩ n U⁻(k) n⁻¹` and `b ∈ B(k)`. -/
theorem existsUnique_mul_weylSubgroup_mul_eq_of_mem_doubleCoset_borelSubgroup
    (k : Type v) [Field k] (n : D.weylSubgroup k) {g : D.points k}
    (hg : g ∈ DoubleCoset.doubleCoset (n : D.points k) (D.borelSubgroup k) (D.borelSubgroup k)) :
    ∃! p : ↥(D.positivePoints k ⊓
        (D.negativePoints k).map (MulAut.conj (n : D.points k)).toMonoidHom) ×
      D.borelSubgroup k,
      (p.1 : D.points k) * (n : D.points k) * (p.2 : D.points k) = g := by
  obtain ⟨u, hu, b, hb, rfl⟩ := (D.mem_doubleCoset_borelSubgroup_iff_exists_mul k n).mp hg
  exact ⟨(⟨u, hu⟩, ⟨b, hb⟩), rfl, fun p hp =>
    Subgroup.mul_mul_injective_of_disjoint _ _
      (D.disjoint_positivePoints_inf_map_negativePoints_map_borelSubgroup k (n : D.points k)) hp⟩

end TauCeti.DynkinType.ChevalleyDatum
