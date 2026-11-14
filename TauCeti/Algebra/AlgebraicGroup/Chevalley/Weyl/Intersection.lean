/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Intersections of the Borel and positive subgroups with the Weyl subgroup

For a Chevalley datum `D` over an arbitrary field `k` (including finite fields and `𝔽₂`), the
positive subgroup `D.positivePoints k` meets `D.weylSubgroup k` trivially, and the intersection of
`D.borelSubgroup k` with `D.weylSubgroup k` is the actual weight-lattice torus
`(D.torusPoints k).range`.

First, any element `g ∈ D.weylSubgroup k` lying in `D.borelSubgroup k` has trivial Weyl projection:
if `w = D.weylProjection k g ≠ 1`, then `w` sends some simple root `γ` to a negative root `w γ`, so
conjugating a suitable root element `x_γ(u) ∈ D.borelSubgroup k` by `g` produces the nonidentity
negative root element `x_{w γ}(1)` inside `D.borelSubgroup k`, contradicting
`D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots`.

Second, if `u ∈ D.positivePoints k ⊓ D.weylSubgroup k`, base change to `AlgebraicClosure k` makes
`u` commute with the represented weight torus over an infinite field, forcing all off-block entries
between distinct Cartan weights to vanish, while weight-block unitriangularity
(`D.coe_apply_eq_one_of_mem_positivePoints_of_weight_eq`) forces `u` to act as the identity on each
weight space regardless of weight multiplicity. The semidirect decomposition
`D.borelSubgroup k = D.positivePoints k ⊔ (D.torusPoints k).range` then yields
`D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.range_torusPoints_le_weylSubgroup`: the actual weight-lattice
  torus lies in `D.weylSubgroup A` over every commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_of_mem_borelSubgroup`: every element of
  `D.weylSubgroup k` lying in `D.borelSubgroup k` has trivial Weyl projection.
* `TauCeti.DynkinType.ChevalleyDatum.positivePoints_inf_weylSubgroup_eq_bot`:
  `D.positivePoints k ⊓ D.weylSubgroup k = ⊥` over any field `k`.
* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints` and
  `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_subgroupOf_weylSubgroup`:
  `D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range` over any field `k`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

-- Match the coefficient structure used by `D.points`, including on an algebraic closure.
attribute [local instance high] Ring.toIntAlgebra
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The actual weight-lattice torus image is contained in the Weyl subgroup over every commutative
ring. -/
theorem range_torusPoints_le_weylSubgroup (A : Type v) [CommRing A] :
    (D.torusPoints A).range ≤ D.weylSubgroup A := by
  rintro _ ⟨s, rfl⟩
  exact D.torusPoints_mem_weylSubgroup A s

variable (k : Type v) [Field k]

/-- An element of `D.weylSubgroup k` that also belongs to `D.borelSubgroup k` projects to `1` in
the Weyl group. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup {g : D.weylSubgroup k}
    (hg : (g : D.points k) ∈ D.borelSubgroup k) :
    D.weylProjection k g = 1 := by
  by_contra hne
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨γ, -, hγinv⟩ := exists_mem_support_mem_inversions_of_ne_one
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) hne
  have hγpos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [posRoots_rationalRootSystem]
    exact inversions_subset_posRoots _ _ _ hγinv
  have hγneg :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k g) γ ∈
        negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    have hneg := mapsTo_inversions_negRoots
      (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) (D.weylProjection k g) hγinv
    rwa [mem_negRoots, ← mem_posRoots, ← posRoots_rationalRootSystem, mem_posRoots,
      ← mem_negRoots] at hneg
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints k g γ
  have hconj := hc ((c⁻¹ : kˣ) : k)
  rw [Units.mul_inv, MulAut.conj_apply] at hconj
  have hmem : D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k g) γ) k
      (Multiplicative.ofAdd 1) ∈ D.borelSubgroup k := by
    rw [← hconj]
    exact mul_mem (mul_mem hg (D.positivePoints_le_borelSubgroup k
      (D.rootSubgroupPoints_mem_positivePoints k hγpos _))) (inv_mem hg)
  exact D.rootSubgroupPoints_ofAdd_one_ne_one k _
    ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots k hγneg _).mp hmem)

/-- An element of `D.weylSubgroup k` lying in `D.positivePoints k` projects to `1` in the Weyl
group. -/
theorem weylProjection_eq_one_of_mem_positivePoints {g : D.weylSubgroup k}
    (hg : (g : D.points k) ∈ D.positivePoints k) :
    D.weylProjection k g = 1 :=
  D.weylProjection_eq_one_of_mem_borelSubgroup k (D.positivePoints_le_borelSubgroup k hg)

/-- Over any field, the positive subgroup meets the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints k ⊓ D.weylSubgroup k = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huP, huW⟩
  rw [Subgroup.mem_bot]
  have hw : D.weylProjection k ⟨u, huW⟩ = 1 :=
    D.weylProjection_eq_one_of_mem_positivePoints k huP
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  let uK : D.points K := (D.pointsPresentation k).map (D.pointsPresentation K) φ u
  have huKP : uK ∈ D.positivePoints K := D.map_positivePoints_le φ ⟨u, huP, rfl⟩
  have huK_coe : (uK : Matrix.GeneralLinearGroup (Fin D.dim) K) =
      Matrix.GeneralLinearGroup.map φ (u : Matrix.GeneralLinearGroup (Fin D.dim) k) :=
    GeneralLinear.IntegralPointsPresentation.coe_map
      (D.pointsPresentation k) (D.pointsPresentation K) φ u
  have hcomm (s : Fin t.rank → Kˣ) :
      (uK : Matrix.GeneralLinearGroup (Fin D.dim) K) *
          diagGL (fun j => torusCharacter s (D.weight j)) =
        diagGL (fun j => torusCharacter s (D.weight j)) *
          (uK : Matrix.GeneralLinearGroup (Fin D.dim) K) := by
    have hs := (D.weylProjection_eq_iff k ⟨u, huW⟩ 1).mp hw s
    simpa only [K, φ, ← huK_coe, map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul] using hs
  have huK_one : (uK : Matrix.GeneralLinearGroup (Fin D.dim) K) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun r c => ?_
    by_cases hrc : D.weight r = D.weight c
    · exact D.coe_apply_eq_one_of_mem_positivePoints_of_weight_eq K huKP hrc
    · have hne_char : weightChar K (D.weight r) ≠ weightChar K (D.weight c) :=
        fun h => hrc (weightChar_injective (K := K) h)
      obtain ⟨s, hs⟩ : ∃ s : Fin t.rank → Kˣ,
          torusCharacter s (D.weight r) ≠ torusCharacter s (D.weight c) := by
        by_contra! hall
        exact hne_char (MonoidHom.ext fun s => by simpa only [weightChar_apply] using hall s)
      have hentry := congrArg
        (fun M : Matrix.GeneralLinearGroup (Fin D.dim) K =>
          (M : Matrix (Fin D.dim) (Fin D.dim) K) r c) (hcomm s)
      simp only [Units.val_mul, diagGL_coe, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
      have hzero : (((uK : Matrix.GeneralLinearGroup (Fin D.dim) K) :
          Matrix (Fin D.dim) (Fin D.dim) K) r c) = 0 := by
        have hsub : ((torusCharacter s (D.weight c) : K) -
            (torusCharacter s (D.weight r) : K)) *
            (((uK : Matrix.GeneralLinearGroup (Fin D.dim) K) :
              Matrix (Fin D.dim) (Fin D.dim) K) r c) = 0 := by
          linear_combination hentry
        exact (mul_eq_zero.mp hsub).resolve_left
          (sub_ne_zero.mpr fun hval => hs (Units.ext hval.symm))
      have hrne : r ≠ c := fun h => hrc (congrArg D.weight h)
      rw [hzero, Units.val_one, Matrix.one_apply_ne hrne]
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.map_injective φ.injective
  rw [← huK_coe, huK_one, Subgroup.coe_one, map_one]

/-- Over any field, the intersection of the Borel subgroup with the Weyl subgroup is the actual
weight-lattice torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range := by
  apply le_antisymm
  · rintro g ⟨hgB, hgW⟩
    obtain ⟨u, huP, s, rfl⟩ := (D.mem_borelSubgroup_iff k).mp hgB
    have huW : u ∈ D.weylSubgroup k := by
      simpa only [mul_inv_cancel_right] using
        (D.weylSubgroup k).mul_mem hgW
          ((D.weylSubgroup k).inv_mem (D.torusPoints_mem_weylSubgroup k s))
    have hu1 : u = 1 := Subgroup.mem_bot.mp
      ((D.positivePoints_inf_weylSubgroup_eq_bot k) ▸ Subgroup.mem_inf.mpr ⟨huP, huW⟩)
    rw [hu1, one_mul]
    exact ⟨s, rfl⟩
  · exact le_inf (D.range_torusPoints_le_borelSubgroup k) (D.range_torusPoints_le_weylSubgroup k)

/-- Read inside `D.weylSubgroup k`, the Borel subgroup cuts out the actual weight-lattice torus. -/
@[simp]
theorem borelSubgroup_subgroupOf_weylSubgroup :
    (D.borelSubgroup k).subgroupOf (D.weylSubgroup k) =
      ((D.torusPoints k).range).subgroupOf (D.weylSubgroup k) := by
  rw [Subgroup.subgroupOf_inj, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints,
    inf_eq_left.mpr (D.range_torusPoints_le_weylSubgroup k)]

end TauCeti.DynkinType.ChevalleyDatum
