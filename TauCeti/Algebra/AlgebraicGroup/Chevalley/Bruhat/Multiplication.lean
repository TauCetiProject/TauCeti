/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
public import TauCeti.GroupTheory.DoubleCoset.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Rank-one double-coset multiplication for a Chevalley datum

Over any field `K`, for a simple root `αᵢ` with pinned Weyl representative `nᵢ(1)` and any
`n : D.weylSubgroup K` projecting to `w = D.weylProjection K n ∈ W`, left multiplication of the
double coset `B(K) n B(K)` by the simple double coset `B(K) nᵢ(1) B(K)` inside `D.points K`
satisfies:
* if `w⁻¹(αᵢ)` is positive, `(B nᵢ(1) B)(B n B) = B (nᵢ(1) n) B`;
* if `w⁻¹(αᵢ)` is negative, `(B nᵢ(1) B)(B n B) ⊆ B (nᵢ(1) n) B ∪ B n B`.

These ambient rank-one double-coset reduction formulas do not depend on a Tits system; they are
used both to construct `ChevalleyDatum.titsSystem` and to identify simple Bruhat-cell products
in `Chevalley.Bruhat.Basic`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.doubleCoset_weylElement_mul_eq_of_mem_posRoots`:
  when `w⁻¹(αᵢ)` is positive, `(B nᵢ(1) B)(B n B) = B (nᵢ(1) n) B`.
* `TauCeti.DynkinType.ChevalleyDatum.doubleCoset_weylElement_mul_subset_union`:
  for every `n : D.weylSubgroup K`, `(B nᵢ(1) B)(B n B) ⊆ B (nᵢ(1) n) B ∪ B n B`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§8.2–8.3.
-/

public section

open Multiplicative
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-- Inverse conjugation by a Weyl lift `n` maps elements of a root subgroup into the root subgroup
indexed by `(D.weylProjection K n)⁻¹` applied to that root. -/
private theorem inv_conj_mem_range_rootSubgroupPoints
    (n : D.weylSubgroup K) {γ : Fin t.numRoots} {x : D.points K}
    (hx : x ∈ (D.rootSubgroupPoints γ K).range) :
    (n : D.points K)⁻¹ * x * (n : D.points K) ∈
      (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection K n)⁻¹ γ) K).range := by
  rw [← map_inv (D.weylProjection K), ← D.map_range_rootSubgroupPoints_conj K n⁻¹]
  exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩

/-- When `w⁻¹(αᵢ)` is positive, `nᵢ(1) * x_{αᵢ}(a) * n` lies in `B (nᵢ(1) n) B`. -/
private theorem weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_mem_posRoots
    (i : Fin t.rank) (n : D.weylSubgroup K) (a : K)
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (n : D.points K) ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (n : D.points K))
        (D.borelSubgroup K) (D.borelSubgroup K) := by
  let x : D.points K := D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a)
  obtain ⟨u', hu'⟩ :=
    D.inv_conj_mem_range_rootSubgroupPoints K n (x := x) ⟨ofAdd a, rfl⟩
  have hb₂ : (n : D.points K)⁻¹ * x * (n : D.points K) ∈ D.borelSubgroup K := by
    rw [← hu']
    exact D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hpos u')
  refine DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, _, hb₂, ?_⟩
  dsimp only [x]
  group

/-- When `w⁻¹(αᵢ)` is negative and `a ≠ 0`, `nᵢ(1) * x_{αᵢ}(a) * n` lies in `B n B`. -/
private theorem weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_mem_negRoots
    (i : Fin t.rank) (n : D.weylSubgroup K) {a : K} (ha : a ≠ 0)
    (hneg : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n)⁻¹
      (t.simpleIndex ht i) ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (n : D.points K) ∈
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  let α := t.simpleIndex ht i
  let r := D.weylElement α K 1
  let u₀ : Kˣ := Units.mk0 a ha
  let b₁ : D.points K :=
    D.rootSubgroupPoints α K (ofAdd (-((u₀⁻¹ : Kˣ) : K))) * D.simpleCorootPoints i K (-u₀⁻¹)
  let y : D.points K := r * D.rootSubgroupPoints α K (ofAdd (-((u₀⁻¹ : Kˣ) : K))) * r⁻¹
  have hrx : r * D.rootSubgroupPoints α K (ofAdd a) = b₁ * y := by
    have hexch := congrArg (· * r⁻¹) (D.weylElement_mul_rootSubgroup_mul_weylElement i K u₀)
    simpa only [r, α, u₀, Units.val_mk0, b₁, y, mul_assoc, mul_inv_cancel, mul_one] using hexch
  have hb₁ : b₁ ∈ D.borelSubgroup K := by
    refine mul_mem (D.positivePoints_le_borelSubgroup K
      (D.rootSubgroupPoints_mem_positivePoints K (simpleIndex_mem_posRoots i) _)) ?_
    rw [D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  let P := t.simplyConnectedRootDatum ht
  have hy_range : y ∈ (D.rootSubgroupPoints (P.reflectionPerm α α) K).range :=
    ⟨_, (D.weylElement_conj_rootSubgroupPoints i α K (-((u₀⁻¹ : Kˣ) : K))).symm⟩
  have hconj_mem := D.inv_conj_mem_range_rootSubgroupPoints K n hy_range
  have hβ_pos :
      P.weylGroupToPerm (D.weylProjection K n)⁻¹ (P.reflectionPerm α α) ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [P.weylGroupToPerm_reflectionPerm_self, ← t.reflectionPerm_rationalRootSystem ht]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hneg
  obtain ⟨v', hv'⟩ := hconj_mem
  have hb₂ : (n : D.points K)⁻¹ * y * (n : D.points K) ∈ D.borelSubgroup K := by
    rw [← hv']
    exact D.positivePoints_le_borelSubgroup K
      (D.rootSubgroupPoints_mem_positivePoints K hβ_pos v')
  refine DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, _, hb₂, ?_⟩
  dsimp only [r, α] at hrx
  rw [hrx]
  group

/-- When `w⁻¹(αᵢ)` is negative, `nᵢ(1) * x_{αᵢ}(a) * n` lies in `B (nᵢ(1) n) B ∪ B n B`. -/
private theorem weylElement_mul_rootSubgroup_mul_mem_union_of_mem_negRoots
    (i : Fin t.rank) (n : D.weylSubgroup K) (a : K)
    (hneg : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n)⁻¹
      (t.simpleIndex ht i) ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (n : D.points K) ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (n : D.points K))
        (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  by_cases ha : a = 0
  · subst ha
    rw [ofAdd_zero, map_one, mul_one]
    exact Or.inl (DoubleCoset.mem_doubleCoset_self _ _ _)
  · exact Or.inr (D.weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_mem_negRoots K i n ha hneg)

/-- Factoring `b ∈ B(K)` across `U⁽ⁱ⁾`, `X_{αᵢ}`, and `T_D(K)` reduces `nᵢ(1) b n` to
`b₁ * (nᵢ(1) x_{αᵢ}(a) n) * b₂` with `b₁, b₂ ∈ B(K)`. -/
private theorem exists_weylElement_mul_borelSubgroup_mul_eq
    (i : Fin t.rank) (n : D.weylSubgroup K) {b : D.points K} (hb : b ∈ D.borelSubgroup K) :
    ∃ b₁ ∈ D.borelSubgroup K, ∃ b₂ ∈ D.borelSubgroup K, ∃ a : K,
      D.weylElement (t.simpleIndex ht i) K 1 * b * (n : D.points K) =
        b₁ * (D.weylElement (t.simpleIndex ht i) K 1 *
          D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (n : D.points K)) * b₂ := by
  let r := D.weylElement (t.simpleIndex ht i) K 1
  obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hb
  obtain ⟨v, hv, u₀, rfl⟩ := (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints K i u).mp hu
  have hv' : r * v * r⁻¹ ∈ D.borelSubgroup K :=
    D.positivePoints_le_borelSubgroup K
      (D.iSup_rootSubgroupPoints_diff_singleton_le_positivePoints K i
        ((Subgroup.mem_normalizer_iff.mp
          (D.weylElement_mem_normalizer_positivePoints_diff_singleton K i 1) v).mp hv))
  have hts' : (n : D.points K)⁻¹ * D.torusPoints K s * (n : D.points K) ∈ D.borelSubgroup K :=
    D.weylSubgroup_inv_conj_torusPoints_mem_borelSubgroup K n s
  refine ⟨r * v * r⁻¹, hv', (n : D.points K)⁻¹ * D.torusPoints K s * (n : D.points K), hts',
    toAdd u₀, ?_⟩
  rw [ofAdd_toAdd]
  dsimp only [r]
  group

/-- Every element of `(B nᵢ(1) B)(B n B)` reduces to `b₁ * (nᵢ(1) x_{αᵢ}(a) n) * b₂` with
`b₁, b₂ ∈ B(K)`. -/
private theorem exists_eq_borel_mul_weylElement_mul_rootSubgroup_mul_of_mem_mul
    (i : Fin t.rank) (n : D.weylSubgroup K) {z : D.points K}
    (hz : z ∈ DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
        (D.borelSubgroup K) (D.borelSubgroup K) *
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K)) :
    ∃ b₁ ∈ D.borelSubgroup K, ∃ b₂ ∈ D.borelSubgroup K, ∃ a : K,
      z = b₁ * (D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (n : D.points K)) * b₂ := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
  obtain ⟨c₁, hc₁, c₂, hc₂, a, hmid⟩ :=
    D.exists_weylElement_mul_borelSubgroup_mul_eq K i n (mul_mem hb₂ hb₃)
  refine ⟨b₁ * c₁, mul_mem hb₁ hc₁, c₂ * b₄, mul_mem hc₂ hb₄, a, ?_⟩
  calc
    b₁ * D.weylElement (t.simpleIndex ht i) K 1 * b₂ * (b₃ * (n : D.points K) * b₄) =
        b₁ * (D.weylElement (t.simpleIndex ht i) K 1 * (b₂ * b₃) * (n : D.points K)) *
          b₄ := by group
    _ = _ := by rw [hmid]; group

/-- If `w⁻¹(αᵢ)` is positive for `w = D.weylProjection K n`, multiplying `B n B` on the left by
`B nᵢ(1) B` gives the single double coset `B (nᵢ(1) n) B`. -/
theorem doubleCoset_weylElement_mul_eq_of_mem_posRoots
    (i : Fin t.rank) (n : D.weylSubgroup K)
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
        (D.borelSubgroup K) (D.borelSubgroup K) *
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) =
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (n : D.points K))
        (D.borelSubgroup K) (D.borelSubgroup K) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨b₁, hb₁, b₂, hb₂, a, rfl⟩ :=
      D.exists_eq_borel_mul_weylElement_mul_rootSubgroup_mul_of_mem_mul K i n hz
    exact DoubleCoset.mul_mul_mem_doubleCoset hb₁
      (D.weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_mem_posRoots K i n a hpos) hb₂
  · exact DoubleCoset.doubleCoset_mul_subset_mul_doubleCoset (M := D.points K)
      (D.borelSubgroup K) (D.borelSubgroup K) (D.borelSubgroup K)
      (D.borelSubgroup K).one_mem _ _

/-- For every simple root `αᵢ` and every `n : D.weylSubgroup K`, the product `(B nᵢ(1) B)(B n B)`
is contained in `B (nᵢ(1) n) B ∪ B n B`. -/
theorem doubleCoset_weylElement_mul_subset_union (i : Fin t.rank) (n : D.weylSubgroup K) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
        (D.borelSubgroup K) (D.borelSubgroup K) *
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) ⊆
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (n : D.points K))
        (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht)
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n)⁻¹
        (t.simpleIndex ht i)) with hpos | hneg
  · rw [D.doubleCoset_weylElement_mul_eq_of_mem_posRoots K i n hpos]
    exact Set.subset_union_left
  · intro z hz
    obtain ⟨b₁, hb₁, b₂, hb₂, a, rfl⟩ :=
      D.exists_eq_borel_mul_weylElement_mul_rootSubgroup_mul_of_mem_mul K i n hz
    exact (D.weylElement_mul_rootSubgroup_mul_mem_union_of_mem_negRoots K i n a hneg).imp
      (fun hcore => DoubleCoset.mul_mul_mem_doubleCoset hb₁ hcore hb₂)
      (fun hcore => DoubleCoset.mul_mul_mem_doubleCoset hb₁ hcore hb₂)

end TauCeti.DynkinType.ChevalleyDatum
