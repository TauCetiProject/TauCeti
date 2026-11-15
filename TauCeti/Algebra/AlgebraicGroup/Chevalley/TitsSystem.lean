/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
public import TauCeti.GroupTheory.TitsSystem.Comap
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.DoubleCoset.Basic
import TauCeti.GroupTheory.DoubleCoset.Map
import TauCeti.GroupTheory.TitsSystem.Bruhat.Length
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The Tits system and Weyl quotient of a Chevalley datum

Over any field `K`, a Chevalley datum `D` of valid Dynkin type `t` carries a canonical Tits system
on its extended elementary subgroup `D.extendedElementarySubgroup K` with Borel subgroup
`B(K) = D.borelSubgroup K` and Weyl subgroup `N(K) = D.weylSubgroup K`. Pulling back along the
decomposition `D.extendedElementarySubgroup K = D.elementarySubgroup K · T_D(K)` also equips the
elementary Chevalley group `D.elementarySubgroup K` with its canonical Tits system.

The key geometric input is the rank-one double-coset reduction for `B(K)` in `D.points K`: for a
simple root `αᵢ` with pinned Weyl representative `nᵢ(1)` and any `n : D.weylSubgroup K` projecting
to `w ∈ W`,
* if `w⁻¹(αᵢ)` is positive, `(B nᵢ(1) B)(B n B) = B (nᵢ(1) n) B`;
* if `w⁻¹(αᵢ)` is negative, `(B nᵢ(1) B)(B n B) ⊆ B (nᵢ(1) n) B ∪ B n B`.

Comparing the positive double-coset equality with the length-decreasing union formula in the Tits
Weyl group proves without Coxeter braid presentations that `D.weylProjection K` descends to an
isomorphism `D.titsWeylGroupMulEquiv K : (D.titsSystem K).WeylGroup ≃* W`. Consequently the kernel
of `D.weylProjection K` is precisely the actual torus `T_D(K)`, yielding the canonical Weyl
quotient isomorphism `D.weylSubgroupQuotientMulEquiv K : N(K) / T_D(K) ≃* W` over every field.

## Main definitions and results

* `ChevalleyDatum.doubleCoset_weylElement_mul_eq_of_mem_posRoots` and
  `ChevalleyDatum.doubleCoset_weylElement_mul_subset_union`: rank-one double-coset multiplication
  for `D.borelSubgroup K` in `D.points K`.
* `ChevalleyDatum.titsSystem`: the Tits system on `D.extendedElementarySubgroup K`.
* `ChevalleyDatum.titsWeylGroupMulEquiv`: the isomorphism `(D.titsSystem K).WeylGroup ≃* W`.
* `ChevalleyDatum.ker_weylProjection` and `ChevalleyDatum.weylSubgroupQuotientMulEquiv`: the kernel
  of `D.weylProjection K` is the actual torus, giving `N(K) / T_D(K) ≃* W`.
* `ChevalleyDatum.elementaryTitsSystem` and `ChevalleyDatum.elementaryTitsWeylGroupMulEquiv`: the
  induced Tits system on `D.elementarySubgroup K` and identification of its Weyl group with `W`.

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

/-! ### Rank-one double-coset reduction in `D.points K` -/

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
  have hconj_mem :
      (n : D.points K)⁻¹ * x * (n : D.points K) ∈
        (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).weylGroupToPerm
          (D.weylProjection K n)⁻¹ (t.simpleIndex ht i)) K).range := by
    rw [← map_inv (D.weylProjection K), ← D.map_range_rootSubgroupPoints_conj K n⁻¹]
    exact Subgroup.mem_map.mpr ⟨x, ⟨ofAdd a, rfl⟩, by simp⟩
  obtain ⟨u', hu'⟩ := hconj_mem
  have hb₂ : (n : D.points K)⁻¹ * x * (n : D.points K) ∈ D.borelSubgroup K := by
    rw [← hu']
    exact D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hpos u')
  refine DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, _, hb₂, ?_⟩
  dsimp only [x]
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
  let α := t.simpleIndex ht i
  let r := D.weylElement α K 1
  by_cases ha : a = 0
  · subst ha
    rw [ofAdd_zero, map_one, mul_one]
    exact Or.inl (DoubleCoset.mem_doubleCoset_self _ _ _)
  · right
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
    have hconj_mem :
        (n : D.points K)⁻¹ * y * (n : D.points K) ∈
          (D.rootSubgroupPoints (P.weylGroupToPerm (D.weylProjection K n)⁻¹
            (P.reflectionPerm α α)) K).range := by
      rw [← map_inv (D.weylProjection K), ← D.map_range_rootSubgroupPoints_conj K n⁻¹]
      exact Subgroup.mem_map.mpr ⟨y, hy_range, by simp⟩
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
  have hv' : r * v * r⁻¹ ∈ D.borelSubgroup K := by
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (D.weylElement_mem_normalizer_positivePoints_diff_singleton K i 1) v).mp hv
    have hle :
        (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
          (D.rootSubgroupPoints γ K).range) ≤ D.positivePoints K := by
      refine iSup₂_le fun γ hγ => ?_
      rintro _ ⟨w, rfl⟩
      exact D.rootSubgroupPoints_mem_positivePoints K hγ.1 w
    exact D.positivePoints_le_borelSubgroup K (hle hmem)
  have htnorm := D.weylSubgroup_le_normalizer_range_torusPoints K (inv_mem n.property)
  obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.mp htnorm (D.torusPoints K s)).mp ⟨s, rfl⟩
  have hts' : D.torusPoints K s' ∈ D.borelSubgroup K :=
    D.range_torusPoints_le_borelSubgroup K ⟨s', rfl⟩
  refine ⟨r * v * r⁻¹, hv', D.torusPoints K s', hts', toAdd u₀, ?_⟩
  rw [ofAdd_toAdd, hs']
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
    Subgroup.image_subtype_subgroupOf_of_le (D.borelSubgroup_le_extendedElementarySubgroup K)]
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
  ⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
    D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
    D.weylElement_mem_weylSubgroup K i⟩

private theorem coe_titsSimpleRepAux (i : Fin t.rank) :
    (((D.titsSimpleRepAux K i : D.extendedElementarySubgroup K) : D.points K)) =
      D.weylElement (t.simpleIndex ht i) K 1 :=
  rfl

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
  let tE : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
    ⟨⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩,
      D.torusPoints_mem_weylSubgroup K s⟩
  have hn_eq : (l.map (D.titsSimpleRepAux K)).prod * tE = n := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.val_list_prod, Subgroup.val_list_prod,
      List.map_map, List.map_map]
    simpa only [Function.comp_def, D.coe_titsSimpleRepAux K, Subgroup.coe_subtype, tE] using hls
  have htE : (QuotientGroup.mk tE :
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) ⧸
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
          ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))) = 1 :=
    (QuotientGroup.eq_one_iff tE).mpr (D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩)
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
            (D.borelSubgroup K) (D.borelSubgroup K) :=
      D.doubleCoset_weylElement_mul_subset_union K i ⟨(w : D.points K), w.property⟩
        ⟨(y : D.points K), hy, (z : D.points K), hz, rfl⟩
    rcases hprod with hleft | hright
    · left
      exact (D.mem_doubleCoset_borelSubgroupOf_iff K
        (D.titsSimpleRepAux K i * w) (y * z)).mpr hleft
    · right
      exact (D.mem_doubleCoset_borelSubgroupOf_iff K w (y * z)).mpr hright
  exists_conj_not_mem := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup K i
    refine ⟨D.titsSimpleRepAux K i, rfl,
      ⟨⟨b.1, D.borelSubgroup_le_extendedElementarySubgroup K b.2⟩, b.2⟩, ?_⟩
    intro hmem
    exact hb hmem

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
  (rfl)

/-- The inverse of `titsSubgroupNMulEquiv` preserves the underlying point in `D.points K`. -/
@[simp]
theorem coe_titsSubgroupNMulEquiv_symm (m : D.weylSubgroup K) :
    ((((D.titsSubgroupNMulEquiv K).symm m : (D.titsSystem K).subgroupN) :
      D.extendedElementarySubgroup K) : D.points K) = (m : D.points K) :=
  (rfl)

/-- The `i`-th pinned simple Weyl representative inside `(D.titsSystem K).subgroupN`. -/
noncomputable def titsSimpleRep (i : Fin t.rank) : (D.titsSystem K).subgroupN :=
  D.titsSimpleRepAux K i

/-- Coercing `titsSimpleRep` to `D.points K` recovers `D.weylElement (t.simpleIndex ht i) K 1`. -/
@[simp]
theorem coe_titsSimpleRep (i : Fin t.rank) :
    (((D.titsSimpleRep K i : D.extendedElementarySubgroup K) : D.points K)) =
      D.weylElement (t.simpleIndex ht i) K 1 :=
  (rfl)

/-- `titsSubgroupNMulEquiv` maps `titsSimpleRep` to `D.weylElement (t.simpleIndex ht i) K 1` in
`D.weylSubgroup K`. -/
@[simp]
theorem titsSubgroupNMulEquiv_titsSimpleRep (i : Fin t.rank) :
    D.titsSubgroupNMulEquiv K (D.titsSimpleRep K i) =
      ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ :=
  (rfl)

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

/-! ### Identification of the Tits Weyl group and the kernel of `weylProjection` -/

private noncomputable def titsWeylProjectionHom :
    (D.titsSystem K).WeylGroup →* (t.simplyConnectedRootDatum ht).weylGroup :=
  QuotientGroup.lift (D.titsSystem K).intersection
    ((D.weylProjection K).comp (D.titsSubgroupNMulEquiv K).toMonoidHom)
    (by
      intro n hn
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      obtain ⟨s, hs⟩ :=
        (D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K n.property).mp hn
      have heq : D.titsSubgroupNMulEquiv K n =
          ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ :=
        Subtype.ext hs.symm
      rw [heq, D.weylProjection_torusPoints])

private theorem titsWeylProjectionHom_mk (n : (D.titsSystem K).subgroupN) :
    D.titsWeylProjectionHom K (QuotientGroup.mk n) =
      D.weylProjection K (D.titsSubgroupNMulEquiv K n) :=
  rfl

private theorem titsWeylProjectionHom_surjective :
    Function.Surjective (D.titsWeylProjectionHom K) := by
  intro w
  obtain ⟨m, rfl⟩ := D.weylProjection_surjective K w
  refine ⟨QuotientGroup.mk ((D.titsSubgroupNMulEquiv K).symm m), ?_⟩
  rw [titsWeylProjectionHom_mk, MulEquiv.apply_symm_apply]

private theorem bruhatCell_titsSimpleReflection_mul_eq_of_mem_posRoots
    (i : Fin t.rank) (n : (D.titsSystem K).subgroupN)
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm
      (D.weylProjection K (D.titsSubgroupNMulEquiv K n))⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i) *
        (D.titsSystem K).bruhatCell (QuotientGroup.mk n) =
      (D.titsSystem K).bruhatCell (D.titsSimpleReflection K i * QuotientGroup.mk n) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, z, hz, rfl⟩
    rw [titsSimpleReflection, (D.titsSystem K).bruhatCell_mk, titsSystem_subgroupB,
      D.mem_doubleCoset_borelSubgroupOf_iff K] at hy
    rw [(D.titsSystem K).bruhatCell_mk, titsSystem_subgroupB,
      D.mem_doubleCoset_borelSubgroupOf_iff K] at hz
    rw [titsSimpleReflection, ← QuotientGroup.mk_mul, (D.titsSystem K).bruhatCell_mk,
      titsSystem_subgroupB, D.mem_doubleCoset_borelSubgroupOf_iff K]
    have hmul := D.doubleCoset_weylElement_mul_eq_of_mem_posRoots K i
      (D.titsSubgroupNMulEquiv K n) hpos
    exact hmul ▸ ⟨(y : D.points K), hy, (z : D.points K), hz, rfl⟩
  · exact (D.titsSystem K).subset_bruhatCell_mul_of_mem_simple
      (D.titsSimpleReflection_mem_simple K i) (QuotientGroup.mk n)

private theorem titsWeylProjectionHom_injective :
    Function.Injective (D.titsWeylProjectionHom K) := by
  rw [injective_iff_map_eq_one]
  intro q hq1
  by_contra hq_ne
  obtain ⟨l, hl, hlen, hprod⟩ := (D.titsSystem K).exists_prod_eq_of_wordLength q
  rcases l with _ | ⟨s, l'⟩
  · exact hq_ne (by simpa using hprod.symm)
  rw [List.forall_mem_cons] at hl
  obtain ⟨hs, hl'⟩ := hl
  have hsq : s * q = l'.prod := by
    rw [← hprod, List.prod_cons, (D.titsSystem K).simple_mul_simple_cancel_left hs]
  have hlt : (D.titsSystem K).simpleGenerators.wordLength (s * q) <
      (D.titsSystem K).simpleGenerators.wordLength q := by
    have hle := (D.titsSystem K).wordLength_prod_le hl'
    rw [hsq, ← hlen, List.length_cons]
    omega
  have hunion := (D.titsSystem K).bruhatCell_mul_eq_union_of_wordLength_lt hs hlt
  rw [titsSystem_simple] at hs
  obtain ⟨i, rfl⟩ := hs
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  have hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm
      (D.weylProjection K (D.titsSubgroupNMulEquiv K n))⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    have hproj : D.weylProjection K (D.titsSubgroupNMulEquiv K n) = 1 := hq1
    rw [hproj, inv_one, map_one, Equiv.Perm.one_apply]
    exact simpleIndex_mem_posRoots i
  have hsingle := D.bruhatCell_titsSimpleReflection_mul_eq_of_mem_posRoots K i n hpos
  exact (D.titsSystem K).bruhatCell_mul_ne_union_of_ne_one
    ((D.titsSystem K).simple_ne_one (D.titsSimpleReflection_mem_simple K i)) _
    (hsingle ▸ hunion)

/-- The canonical isomorphism between the Weyl group of `D.titsSystem K` and the Weyl group of the
root datum. -/
noncomputable def titsWeylGroupMulEquiv :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  MulEquiv.ofBijective (D.titsWeylProjectionHom K)
    ⟨D.titsWeylProjectionHom_injective K, D.titsWeylProjectionHom_surjective K⟩

/-- `titsWeylGroupMulEquiv` sends the class of `n` to `D.weylProjection K` of its image in
`D.weylSubgroup K`. -/
@[simp]
theorem titsWeylGroupMulEquiv_mk (n : (D.titsSystem K).subgroupN) :
    D.titsWeylGroupMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K (D.titsSubgroupNMulEquiv K n) :=
  (rfl)

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

/-- Over every field, the kernel of `D.weylProjection K` is precisely the actual torus inside
`D.weylSubgroup K`. -/
@[simp]
theorem ker_weylProjection :
    (D.weylProjection K).ker = ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← (D.titsWeylGroupMulEquiv K).symm.map_eq_one_iff,
    D.titsWeylGroupMulEquiv_symm_weylProjection K m, QuotientGroup.eq_one_iff,
    TitsSystem.mem_intersection, titsSystem_subgroupB, Subgroup.mem_subgroupOf,
    coe_titsSubgroupNMulEquiv_symm]
  exact D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K m.property

/-- Over any field, the quotient of `D.weylSubgroup K` by the actual torus `T_D(K)` is canonically
isomorphic to the Weyl group of the root datum. -/
noncomputable def weylSubgroupQuotientMulEquiv :
    D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection K)
      (D.weylProjection_surjective K))

/-- `weylSubgroupQuotientMulEquiv` evaluates on the class of `n` as `D.weylProjection K n`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk (n : D.weylSubgroup K) :
    D.weylSubgroupQuotientMulEquiv K (QuotientGroup.mk n) = D.weylProjection K n :=
  (rfl)

/-! ### The induced Tits system on the elementary Chevalley subgroup -/

private theorem exists_inclusion_elementarySubgroup_mul_mem_inf
    (g : D.extendedElementarySubgroup K) :
    ∃ x : D.elementarySubgroup K,
      ∃ z ∈ (D.titsSystem K).subgroupB ⊓ (D.titsSystem K).subgroupN,
        Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K) x * z = g := by
  obtain ⟨e, he, s, hes⟩ := (D.mem_extendedElementarySubgroup_iff K g.1).mp g.2
  refine ⟨⟨e, he⟩, ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩,
    ⟨D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup K s⟩, ?_⟩
  exact Subtype.ext hes

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
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupB, titsSystem_subgroupB]
  ext x
  rfl

/-- The Weyl subgroup of `D.elementaryTitsSystem K` is `D.weylSubgroup K` restricted to
`D.elementarySubgroup K`. -/
@[simp]
theorem elementaryTitsSystem_subgroupN :
    (D.elementaryTitsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupN, titsSystem_subgroupN]
  ext x
  rfl

/-- Coercing an element of `(D.elementaryTitsSystem K).subgroupN` to `D.points K` lands in
`D.weylSubgroup K`. -/
theorem coe_mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN
    (n : (D.elementaryTitsSystem K).subgroupN) :
    ((n : D.elementarySubgroup K) : D.points K) ∈ D.weylSubgroup K :=
  Subgroup.mem_subgroupOf.mp
    ((SetLike.ext_iff.mp (D.elementaryTitsSystem_subgroupN K) (n : D.elementarySubgroup K)).mp
      n.property)

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
    ((D.titsWeylGroupMulEquiv_mk K _).trans (congrArg (D.weylProjection K) (Subtype.ext rfl)))

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
