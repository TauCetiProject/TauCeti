/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.FieldTheory.IsAlgClosed.Units
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The intersection of the Chevalley Weyl and Borel subgroups

For any Chevalley datum `D` and any field `K` (including finite fields and fields of small
characteristic), the Weyl subgroup `N(K)` meets the positive Borel-type subgroup `B(K)` in
precisely the actual character-lattice torus `T(K)`.

First, any element `g ∈ N(K) ∩ B(K)` has trivial Weyl projection: if its projected Weyl element
sent some positive root `γ` to a negative root `δ`, conjugating `x_γ(1) ∈ B(K)` by `g ∈ B(K)`
would produce a nontrivial negative root element inside `B(K)`, contradicting
`ChevalleyDatum.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots`. Writing `g = u * t`
with `u ∈ U(K)` and `t ∈ T(K)` reduces to a positive element `u ∈ N(K)` with trivial Weyl
projection. Extending scalars to `L = AlgebraicClosure K` — where the field is infinite and units
are divisible, so full-weight torus parameters cover the actual torus — places the image of `u`
inside `U(L) ∩ Z_{G(L)}(T(L)) = 1`
(`ChevalleyDatum.positivePoints_inf_centralizer_range_torusPoints`), whence `u = 1`.

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_of_mem_borelSubgroup`: every element of
  `N(K) ∩ B(K)` projects to `1` in the Weyl group.
* `TauCeti.DynkinType.ChevalleyDatum.weylSubgroup_inf_borelSubgroup` and
  `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup`: `N(K) ∩ B(K) = T(K)` over
  every field `K`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 27 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §8.2.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

-- Match the coefficient structure used by `D.points`, including on an algebraic closure.
attribute [local instance high] Ring.toIntAlgebra
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-- Every element of the Weyl subgroup that also lies in the positive Borel-type subgroup acts
trivially in the Weyl group. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup {g : D.weylSubgroup K}
    (hg : (g : D.points K) ∈ D.borelSubgroup K) :
    D.weylProjection K g = 1 := by
  let : (t.simplyConnectedRootDatum ht).IsReduced := t.isReduced_simplyConnectedRootDatum ht
  apply eq_one_of_mapsTo_posRoots (P := t.simplyConnectedRootDatum ht)
    (b := t.simplyConnectedBase ht)
  intro γ hγ
  by_contra hnot
  have hγ_rat : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rwa [t.posRoots_rationalRootSystem ht]
  have hδ_neg :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ ∈
        negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rwa [← not_mem_posRoots_iff_mem_negRoots, t.posRoots_rationalRootSystem ht]
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints K g γ
  have hxB : D.rootSubgroupPoints γ K (Multiplicative.ofAdd 1) ∈ D.borelSubgroup K :=
    D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hγ_rat _)
  have hconjB :
      MulAut.conj (g : D.points K) (D.rootSubgroupPoints γ K (Multiplicative.ofAdd 1)) ∈
        D.borelSubgroup K := by
    rw [MulAut.conj_apply]
    exact (D.borelSubgroup K).mul_mem ((D.borelSubgroup K).mul_mem hg hxB)
      ((D.borelSubgroup K).inv_mem hg)
  rw [hc 1, D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hδ_neg, ← hc 1,
    map_eq_one_iff _ (MulAut.conj (g : D.points K)).injective] at hconjB
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K γ hconjB

/-- Over every field, the Weyl subgroup meets the positive Borel-type subgroup in the actual
character-lattice torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup :
    D.weylSubgroup K ⊓ D.borelSubgroup K = (D.torusPoints K).range := by
  apply le_antisymm
  · rintro g ⟨hgN, hgB⟩
    obtain ⟨u, huP, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    have huN : u ∈ D.weylSubgroup K := by
      simpa only [mul_inv_cancel_right] using
        (D.weylSubgroup K).mul_mem hgN
          ((D.weylSubgroup K).inv_mem (D.torusPoints_mem_weylSubgroup K s))
    have hu_proj : D.weylProjection K ⟨u, huN⟩ = 1 :=
      D.weylProjection_eq_one_of_mem_borelSubgroup K (D.positivePoints_le_borelSubgroup K huP)
    let φ := (D.pointsPresentation K).map (D.pointsPresentation (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K))
    have hφu_pos : φ u ∈ D.positivePoints (AlgebraicClosure K) :=
      D.map_positivePoints_le (algebraMap K (AlgebraicClosure K)) ⟨u, huP, rfl⟩
    have hφu_cent :
        φ u ∈ Subgroup.centralizer (Set.range (D.torusPoints (AlgebraicClosure K))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      obtain ⟨s', rfl⟩ := D.fullWeightTorusRestriction_surjective (AlgebraicClosure K) r
      have hcomm := (D.weylProjection_eq_iff K ⟨u, huN⟩ 1).mp hu_proj s'
      simp only [map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hcomm
      apply Subtype.ext
      simp only [φ, Subgroup.coe_mul]
      rw [GeneralLinear.IntegralPointsPresentation.coe_map, D.coe_torusPoints,
        ← D.kostantTorusMatrix_weight, kostantTorusMatrix_apply]
      exact hcomm.symm
    have hφu_one : φ u = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← D.positivePoints_inf_centralizer_range_torusPoints (AlgebraicClosure K)]
      exact ⟨hφu_pos, hφu_cent⟩
    have hu_one : u = 1 := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.map_injective (algebraMap K (AlgebraicClosure K)).injective
      have hval := congrArg Subtype.val hφu_one
      simp only [φ, Subgroup.coe_one] at hval
      rw [GeneralLinear.IntegralPointsPresentation.coe_map] at hval
      exact hval.trans (map_one _).symm
    rw [hu_one, one_mul]
    exact ⟨s, rfl⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨D.torusPoints_mem_weylSubgroup K s, D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩⟩

/-- Symmetric form of `ChevalleyDatum.weylSubgroup_inf_borelSubgroup`: `B(K) ∩ N(K) = T(K)`. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup :
    D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range := by
  rw [inf_comm, D.weylSubgroup_inf_borelSubgroup]

/-- Viewed inside `N(K)`, the intersection `B(K) ∩ N(K)` is the actual torus subgroup. -/
@[simp]
theorem borelSubgroup_subgroupOf_weylSubgroup :
    (D.borelSubgroup K).subgroupOf (D.weylSubgroup K) =
      ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext g
  simp only [Subgroup.mem_subgroupOf, ← D.weylSubgroup_inf_borelSubgroup K,
    Subgroup.mem_inf, g.2, true_and]

/-- The intersection `B(K) ∩ N(K)` is normal in `N(K)` over every field. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup K).subgroupOf (D.weylSubgroup K)).Normal := by
  rw [D.borelSubgroup_subgroupOf_weylSubgroup K]
  exact D.normal_torusPoints_subgroupOf_weylSubgroup K

end TauCeti.DynkinType.ChevalleyDatum
