/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
public import TauCeti.GroupTheory.TitsSystem.Comap
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange

/-!
# The Tits system of a Chevalley datum

Over any field `K`, the Borel-type subgroup `B(K) = U(K) ⊔ T(K)` and the Weyl subgroup `N(K)` of a
Chevalley datum restrict to a Tits system (BN-pair) on the extended elementary subgroup
`D.extendedElementarySubgroup K = E(K) ⊔ T(K)`, and pull back along `E(K) ≤ E(K) ⊔ T(K)` to a Tits
system on the elementary subgroup `D.elementarySubgroup K`.

Generation is supplied by `ChevalleyDatum.borelSubgroup_sup_weylSubgroup`. The key remaining input
is the rank-one double-coset multiplication inclusion
`B nᵢ B * B w B ⊆ B (nᵢ w) B ∪ B w B` inside `D.points K`. Writing an element of `B(K)` as
`v * xᵢ(a) * t` with `v` in the punctured positive subgroup normalized by `nᵢ`, the torus factor
moves across `w` and `v` moves across `nᵢ`, reducing to `nᵢ * xᵢ(a) * w`. If `w⁻¹(αᵢ) > 0` then
`w⁻¹ xᵢ(a) w ∈ U(K) ≤ B(K)`. If `w⁻¹(αᵢ) < 0` and `a ≠ 0`, the rank-one identity
`nᵢ xᵢ(a) = xᵢ(-a⁻¹) hᵢ(-a⁻¹) (nᵢ xᵢ(-a⁻¹) nᵢ⁻¹)` expresses `nᵢ xᵢ(a)` as an element of `B(K)`
times a `-αᵢ`-root element, which `w⁻¹` conjugates to the positive root `-w⁻¹(αᵢ)`.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.titsSystem`: the Tits system on
  `D.extendedElementarySubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.elementaryTitsSystem`: the pulled-back Tits system on
  `D.elementarySubgroup K`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylElement_mem_elementarySubgroup`: every Weyl element
  `n_γ(u)` lies in `D.elementarySubgroup A` over any commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.doubleCoset_weylElement_mul_subset`: the Tits multiplication
  inclusion `B nᵢ B * B w B ⊆ B (nᵢ w) B ∪ B w B` in `D.points K`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 25 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §8.2.
-/

public section

open Multiplicative
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section Ring

variable (A : Type v) [CommRing A]

/-- Every Weyl element `n_γ(u)` lies in the elementary subgroup over any commutative ring. -/
theorem weylElement_mem_elementarySubgroup (γ : Fin t.numRoots) (u : Aˣ) :
    D.weylElement γ A u ∈ D.elementarySubgroup A := by
  rw [D.weylElement_def]
  exact mul_mem (mul_mem (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)
    (D.rootSubgroupPoints_mem_elementarySubgroup A _ _))
    (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)

end Ring

section Field

variable (K : Type v) [Field K]

private theorem inv_conj_rootSubgroupPoints_mem_borelSubgroup (w : D.weylSubgroup K)
    {γ : Fin t.numRoots}
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w)⁻¹ γ ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : K) :
    (w : D.points K)⁻¹ * D.rootSubgroupPoints γ K (ofAdd u) * (w : D.points K) ∈
      D.borelSubgroup K := by
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints K w⁻¹ γ
  have hc' := hc u
  rw [Subgroup.coe_inv, MulAut.conj_apply, inv_inv, map_inv] at hc'
  rw [hc']
  exact D.positivePoints_le_borelSubgroup K
    (D.rootSubgroupPoints_mem_positivePoints K hpos _)

private theorem weylElement_mul_rootSubgroupPoints_mul_mem_of_mem_inversions (i : Fin t.rank)
    (w : D.weylSubgroup K)
    (hinv : t.simpleIndex ht i ∈
      inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (D.weylProjection K w)⁻¹)
    (a : K) :
    let n := D.weylElement (t.simpleIndex ht i) K 1
    n * D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (w : D.points K) ∈
      DoubleCoset.doubleCoset (n * (w : D.points K)) (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (w : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  intro n
  by_cases ha : a = 0
  · subst ha
    refine Or.inl (DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, 1, one_mem _, ?_⟩)
    simp
  · let P := t.simplyConnectedRootDatum ht
    let b := t.simplyConnectedBase ht
    let α := t.simpleIndex ht i
    let u : Kˣ := Units.mk0 a ha
    have hαpos : b.IsPos α := b.isPos_of_mem_support
      (by rw [← support_rationalBase]; exact t.simpleIndex_mem_support i)
    have hnot : α ∉ inversions P b
        ((D.weylProjection K w)⁻¹ * RootPairing.weylGroup.ofIdx P α) := fun hmem =>
      ((mem_inversions_mul_ofIdx_iff_not_mem P (D.weylProjection K w)⁻¹ b hαpos).mp hmem) hinv
    have himgPos : P.weylGroupToPerm (D.weylProjection K w)⁻¹ (P.reflectionPerm α α) ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [t.posRoots_rationalRootSystem ht, mem_posRoots]
      have hpos' : b.IsPos (P.weylGroupToPerm
          ((D.weylProjection K w)⁻¹ * RootPairing.weylGroup.ofIdx P α) α) := by
        by_contra hneg
        exact hnot ((mem_inversions P b _ _).mpr ⟨hαpos, hneg⟩)
      rwa [RootPairing.weylGroupToPerm_mul_ofIdx_apply] at hpos'
    have hleft : D.rootSubgroupPoints α K (ofAdd (-((u⁻¹ : Kˣ) : K))) *
        D.simpleCorootPoints i K (-u⁻¹) ∈ D.borelSubgroup K := by
      refine mul_mem (D.positivePoints_le_borelSubgroup K
        (D.rootSubgroupPoints_mem_positivePoints K ?_ _)) ?_
      · rw [t.posRoots_rationalRootSystem ht, mem_posRoots]
        exact hαpos
      · rw [D.simpleCorootPoints_eq_torusPoints]
        exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
    have hright : (w : D.points K)⁻¹ *
        (n * D.rootSubgroupPoints α K (ofAdd (-((u⁻¹ : Kˣ) : K))) * n⁻¹) *
        (w : D.points K) ∈ D.borelSubgroup K := by
      rw [D.weylElement_conj_rootSubgroupPoints]
      exact D.inv_conj_rootSubgroupPoints_mem_borelSubgroup K w himgPos _
    refine Or.inr (DoubleCoset.mem_doubleCoset.mpr ⟨_, hleft, _, hright, ?_⟩)
    calc
      n * D.rootSubgroupPoints α K (ofAdd a) * (w : D.points K)
        = (n * D.rootSubgroupPoints α K (ofAdd (u : K)) * n) * n⁻¹ *
            (w : D.points K) := by simp only [u, Units.val_mk0, mul_inv_cancel_right]
      _ = (D.rootSubgroupPoints α K (ofAdd (-((u⁻¹ : Kˣ) : K))) *
            D.simpleCorootPoints i K (-u⁻¹)) * (w : D.points K) *
            ((w : D.points K)⁻¹ *
              (n * D.rootSubgroupPoints α K (ofAdd (-((u⁻¹ : Kˣ) : K))) * n⁻¹) *
              (w : D.points K)) := by
            dsimp only [n, α]
            rw [D.weylElement_mul_rootSubgroup_mul_weylElement i K u]
            group

private theorem weylElement_mul_rootSubgroupPoints_mul_mem (i : Fin t.rank)
    (w : D.weylSubgroup K) (a : K) :
    let n := D.weylElement (t.simpleIndex ht i) K 1
    n * D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * (w : D.points K) ∈
      DoubleCoset.doubleCoset (n * (w : D.points K)) (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (w : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  intro n
  by_cases hinv : t.simpleIndex ht i ∈
      inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (D.weylProjection K w)⁻¹
  · exact D.weylElement_mul_rootSubgroupPoints_mul_mem_of_mem_inversions K i w hinv a
  · have hαpos : (t.simplyConnectedBase ht).IsPos (t.simpleIndex ht i) :=
      (t.simplyConnectedBase ht).isPos_of_mem_support
        (by rw [← support_rationalBase]; exact t.simpleIndex_mem_support i)
    have himgPos :
        (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w)⁻¹
          (t.simpleIndex ht i) ∈
          posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [t.posRoots_rationalRootSystem ht, mem_posRoots]
      by_contra hneg
      exact hinv ((mem_inversions _ _ _ _).mpr ⟨hαpos, hneg⟩)
    refine Or.inl (DoubleCoset.mem_doubleCoset.mpr
      ⟨1, one_mem _, _, D.inv_conj_rootSubgroupPoints_mem_borelSubgroup K w himgPos a, ?_⟩)
    group

/-- **The Tits double-coset multiplication inclusion** inside `D.points K`: for every simple index
`i` and every Weyl lift `w`, `B nᵢ B * B w B ⊆ B (nᵢ w) B ∪ B w B`. -/
theorem doubleCoset_weylElement_mul_subset (i : Fin t.rank) (w : D.weylSubgroup K) :
    let n := D.weylElement (t.simpleIndex ht i) K 1
    DoubleCoset.doubleCoset n (D.borelSubgroup K) (D.borelSubgroup K) *
        DoubleCoset.doubleCoset (w : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) ⊆
      DoubleCoset.doubleCoset (n * (w : D.points K)) (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (w : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  intro n z hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₁
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₂
  obtain ⟨u, hu, s, hs⟩ := (D.mem_borelSubgroup_iff K).mp (mul_mem hb₂ hb₃)
  obtain ⟨v, hv, a, rfl⟩ := (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints K i u).mp hu
  have hv' : n * v * n⁻¹ ∈ D.borelSubgroup K :=
    D.positivePoints_le_borelSubgroup K (D.positivePoints_diff_singleton_le_positivePoints K i
      ((Subgroup.mem_normalizer_iff.mp
        (D.weylElement_mem_normalizer_positivePoints_diff_singleton K i 1) v).mp hv))
  have ht' : (w : D.points K)⁻¹ * D.torusPoints K s * (w : D.points K) ∈ D.borelSubgroup K :=
    D.range_torusPoints_le_borelSubgroup K
      ((Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K w⁻¹.property) (D.torusPoints K s)).mp
        ⟨s, rfl⟩)
  have wrap {x : D.points K}
      (hx : n * D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd (toAdd a)) * (w : D.points K) ∈
        DoubleCoset.doubleCoset x (D.borelSubgroup K) (D.borelSubgroup K)) :
      b₁ * n * b₂ * (b₃ * (w : D.points K) * b₄) ∈
        DoubleCoset.doubleCoset x (D.borelSubgroup K) (D.borelSubgroup K) := by
    obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁ * (n * v * n⁻¹) * c₁, mul_mem (mul_mem hb₁ hv') hc₁,
        c₂ * (((w : D.points K)⁻¹ * D.torusPoints K s * (w : D.points K)) * b₄),
        mul_mem hc₂ (mul_mem ht' hb₄), ?_⟩
    rw [ofAdd_toAdd] at hc
    calc
      b₁ * n * b₂ * (b₃ * (w : D.points K) * b₄)
        = b₁ * n * (b₂ * b₃) * (w : D.points K) * b₄ := by group
      _ = b₁ * n * (v * D.rootSubgroupPoints (t.simpleIndex ht i) K a * D.torusPoints K s) *
            (w : D.points K) * b₄ := by rw [← hs]
      _ = b₁ * (n * v * n⁻¹) *
            (n * D.rootSubgroupPoints (t.simpleIndex ht i) K a * (w : D.points K)) *
            ((w : D.points K)⁻¹ * D.torusPoints K s * (w : D.points K)) * b₄ := by group
      _ = (b₁ * (n * v * n⁻¹) * c₁) * x *
            (c₂ * (((w : D.points K)⁻¹ * D.torusPoints K s * (w : D.points K)) * b₄)) := by
            rw [hc]; group
  exact (D.weylElement_mul_rootSubgroupPoints_mul_mem K i w (toAdd a)).imp wrap wrap

/-- Double cosets of `(D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)` agree with
those of `D.borelSubgroup K` inside `D.points K`. -/
theorem mem_doubleCoset_subgroupOf_borelSubgroup_iff
    {g x : D.extendedElementarySubgroup K} :
    g ∈ DoubleCoset.doubleCoset x
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K))
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ↔
      (g : D.points K) ∈
        DoubleCoset.doubleCoset (x : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁.val, hb₁, b₂.val, hb₂, rfl⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, h⟩
    exact ⟨⟨b₁, D.borelSubgroup_le_extendedElementarySubgroup K hb₁⟩, hb₁,
      ⟨b₂, D.borelSubgroup_le_extendedElementarySubgroup K hb₂⟩, hb₂, Subtype.ext h⟩

/-- The pinned `i`-th simple Weyl representative in the Weyl subgroup of
`D.extendedElementarySubgroup K`. -/
noncomputable def extendedWeylElement (i : Fin t.rank) :
    (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  ⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
      D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
    D.weylElement_mem_weylSubgroup K i⟩

/-- Coercing `D.extendedWeylElement K i` to `D.points K` recovers the pinned simple Weyl element. -/
@[simp]
theorem coe_extendedWeylElement (i : Fin t.rank) :
    (((D.extendedWeylElement K i : D.extendedElementarySubgroup K) : D.points K)) =
      D.weylElement (t.simpleIndex ht i) K 1 := by
  rfl

private instance normal_subgroupOf_borelSubgroup_subgroupOf_weylSubgroup :
    (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))).Normal := by
  refine ⟨fun x hx y => ?_⟩
  have hxy : ((x : D.extendedElementarySubgroup K) : D.points K) ∈
      D.borelSubgroup K ⊓ D.weylSubgroup K :=
    ⟨Subgroup.mem_subgroupOf.mp hx, Subgroup.mem_subgroupOf.mp x.2⟩
  rw [D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K] at hxy
  have hconj : (((y * x * y⁻¹ : (D.weylSubgroup K).subgroupOf _) :
        D.extendedElementarySubgroup K) : D.points K) ∈ (D.torusPoints K).range :=
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints K (Subgroup.mem_subgroupOf.mp y.2)) _).mp hxy
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
    (D.range_torusPoints_le_borelSubgroup K hconj))

private theorem closure_extendedBorel_union_extendedWeyl :
    Subgroup.closure
      (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :
          Set (D.extendedElementarySubgroup K)) ∪
        ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :
          Set (D.extendedElementarySubgroup K))) =
      ⊤ := by
  rw [← Subgroup.sup_eq_closure,
    ← Subgroup.subgroupOf_sup (D.borelSubgroup_le_extendedElementarySubgroup K)
      (D.weylSubgroup_le_extendedElementarySubgroup K),
    D.borelSubgroup_sup_weylSubgroup K, Subgroup.subgroupOf_self]

private theorem closure_range_extendedWeylElement :
    Subgroup.closure
      (Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.extendedWeylElement K i) :
          ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ⧸
            (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
              ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))))) = ⊤ := by
  let e := Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)
  let H := (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
    ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)))
  let f := (QuotientGroup.mk' H).comp e.symm.toMonoidHom
  let S := Subgroup.closure
    (Set.range fun i : Fin t.rank =>
      (QuotientGroup.mk (D.extendedWeylElement K i) :
        ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ⧸ H))
  have hle : D.weylSubgroup K ≤ (S.comap f).map (D.weylSubgroup K).subtype := by
    apply (D.weylSubgroup_def K).le.trans
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have h1 : f ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
          (D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩)))
      rw [h1]
      exact one_mem _
    · refine ⟨⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩,
        Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, heq⟩ := hle (e n).2
  have hme : m = e n := Subtype.ext heq
  subst hme
  simpa only [SetLike.mem_coe, Subgroup.mem_comap, f, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, S] using hm

/-- **The Tits system on the extended elementary subgroup** `D.extendedElementarySubgroup K` of a
Chevalley datum over a field `K`, with `B` and `N` the restrictions of `D.borelSubgroup K` and
`D.weylSubgroup K` and simple reflections indexed by the pinned simple Weyl representatives. -/
noncomputable def titsSystem : TauCeti.TitsSystem (D.extendedElementarySubgroup K) where
  subgroupB := (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  subgroupN := (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  closure_subgroupB_union_subgroupN := D.closure_extendedBorel_union_extendedWeyl K
  intersection_normal := D.normal_subgroupOf_borelSubgroup_subgroupOf_weylSubgroup K
  simple := Set.range fun i : Fin t.rank => QuotientGroup.mk (D.extendedWeylElement K i)
  closure_simple := D.closure_range_extendedWeylElement K
  exists_simpleRep_mul_self_mem := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.extendedWeylElement K i, rfl, ?_⟩
    apply Subgroup.mem_subgroupOf.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simp only [Subgroup.coe_mul, D.coe_extendedWeylElement, D.weylElement_mul_self,
      D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  mul_doubleCoset_subset := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.extendedWeylElement K i, rfl, fun w z hz => ?_⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hz
    rw [D.mem_doubleCoset_subgroupOf_borelSubgroup_iff K] at hz₁ hz₂
    have hprod := D.doubleCoset_weylElement_mul_subset K i
      ⟨(w : D.extendedElementarySubgroup K), Subgroup.mem_subgroupOf.mp w.2⟩
      (Set.mul_mem_mul hz₁ hz₂)
    simpa only [Set.mem_union, D.mem_doubleCoset_subgroupOf_borelSubgroup_iff K,
      Subgroup.coe_mul, D.coe_extendedWeylElement] using hprod
  exists_conj_not_mem := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup K i
    exact ⟨D.extendedWeylElement K i, rfl,
      ⟨⟨b.val, D.borelSubgroup_le_extendedElementarySubgroup K b.2⟩, b.2⟩, hb⟩

/-- The distinguished subgroup `B` of `D.titsSystem K` is the restriction of `D.borelSubgroup K`. -/
@[simp]
theorem titsSystem_subgroupB :
    (D.titsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) := by
  rfl

/-- The Weyl-lift subgroup `N` of `D.titsSystem K` is the restriction of `D.weylSubgroup K`. -/
@[simp]
theorem titsSystem_subgroupN :
    (D.titsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) := by
  rfl

/-- Restricting `D.weylSubgroup K` to `D.extendedElementarySubgroup K` identifies
`(D.titsSystem K).subgroupN` with `D.weylSubgroup K`. -/
noncomputable def titsSystemSubgroupNEquiv :
    (D.titsSystem K).subgroupN ≃* D.weylSubgroup K :=
  Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)

/-- `D.titsSystemSubgroupNEquiv K` preserves the underlying point in `D.points K`. -/
@[simp]
theorem coe_titsSystemSubgroupNEquiv (n : (D.titsSystem K).subgroupN) :
    (D.titsSystemSubgroupNEquiv K n : D.points K) =
      ((n : D.extendedElementarySubgroup K) : D.points K) := by
  rfl

/-- The `i`-th simple reflection in `(D.titsSystem K).WeylGroup`. -/
noncomputable def titsSystemSimple (i : Fin t.rank) : (D.titsSystem K).WeylGroup :=
  QuotientGroup.mk (D.extendedWeylElement K i)

/-- The generating set of simple reflections of `D.titsSystem K` is the range of
`D.titsSystemSimple K`. -/
theorem titsSystem_simple :
    (D.titsSystem K).simple = Set.range (D.titsSystemSimple K) := by
  rfl

/-- Transporting the `i`-th pinned simple Weyl element into `(D.titsSystem K).WeylGroup` gives
`D.titsSystemSimple K i`. -/
theorem titsSystemSubgroupNEquiv_symm_weylElement (i : Fin t.rank) :
    QuotientGroup.mk
        ((D.titsSystemSubgroupNEquiv K).symm
          ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩) =
      D.titsSystemSimple K i := by
  rfl

private theorem exists_elementary_mul_mem_titsSystem_inf
    (g : D.extendedElementarySubgroup K) :
    ∃ x : D.elementarySubgroup K,
      ∃ t ∈ (D.titsSystem K).subgroupB ⊓ (D.titsSystem K).subgroupN,
        Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K) x * t = g := by
  obtain ⟨e, he, s, hs⟩ := (D.mem_extendedElementarySubgroup_iff K g.val).mp g.2
  refine ⟨⟨e, he⟩, ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩,
    ⟨D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup K s⟩,
    Subtype.ext hs⟩

/-- **The Tits system on the elementary subgroup** `D.elementarySubgroup K` of a Chevalley datum
over a field `K`, obtained by pulling back `D.titsSystem K` along the normal inclusion
`D.elementarySubgroup K ≤ D.extendedElementarySubgroup K`. -/
noncomputable def elementaryTitsSystem : TauCeti.TitsSystem (D.elementarySubgroup K) :=
  (D.titsSystem K).comap
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_elementary_mul_mem_titsSystem_inf K)

/-- The distinguished subgroup `B` of `D.elementaryTitsSystem K` is the restriction of
`D.borelSubgroup K` to `D.elementarySubgroup K`. -/
@[simp]
theorem elementaryTitsSystem_subgroupB :
    (D.elementaryTitsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  ext x
  simp [elementaryTitsSystem, Subgroup.mem_subgroupOf]

/-- The Weyl-lift subgroup `N` of `D.elementaryTitsSystem K` is the restriction of
`D.weylSubgroup K` to `D.elementarySubgroup K`. -/
@[simp]
theorem elementaryTitsSystem_subgroupN :
    (D.elementaryTitsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  ext x
  simp [elementaryTitsSystem, Subgroup.mem_subgroupOf]

/-- The inclusion of `(D.elementaryTitsSystem K).subgroupN` into `D.weylSubgroup K`. -/
noncomputable def elementaryTitsSystemSubgroupNToWeylSubgroup :
    (D.elementaryTitsSystem K).subgroupN →* D.weylSubgroup K where
  toFun n := ⟨n.1.1,
    Subgroup.mem_subgroupOf.mp
      ((SetLike.ext_iff.mp (D.elementaryTitsSystem_subgroupN K) n.1).mp n.2)⟩
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- `D.elementaryTitsSystemSubgroupNToWeylSubgroup K` preserves the underlying point in
`D.points K`. -/
@[simp]
theorem coe_elementaryTitsSystemSubgroupNToWeylSubgroup
    (n : (D.elementaryTitsSystem K).subgroupN) :
    (D.elementaryTitsSystemSubgroupNToWeylSubgroup K n : D.points K) =
      ((n : D.elementarySubgroup K) : D.points K) := by
  rfl

/-- The natural isomorphism between the Weyl groups of `D.elementaryTitsSystem K` and
`D.titsSystem K`. -/
noncomputable def elementaryToExtendedWeylGroupEquiv :
    (D.elementaryTitsSystem K).WeylGroup ≃* (D.titsSystem K).WeylGroup :=
  (D.titsSystem K).comapWeylGroupMulEquiv
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_elementary_mul_mem_titsSystem_inf K)

/-- `D.elementaryToExtendedWeylGroupEquiv K` sends the class of `n` to the class of its image in
`D.weylSubgroup K`. -/
@[simp]
theorem elementaryToExtendedWeylGroupEquiv_mk (n : (D.elementaryTitsSystem K).subgroupN) :
    D.elementaryToExtendedWeylGroupEquiv K (QuotientGroup.mk n) =
      QuotientGroup.mk
        ((D.titsSystemSubgroupNEquiv K).symm
          (D.elementaryTitsSystemSubgroupNToWeylSubgroup K n)) := by
  unfold elementaryTitsSystem elementaryToExtendedWeylGroupEquiv at *
  rw [TitsSystem.comapWeylGroupMulEquiv_mk]
  congr 1

/-- The simple reflections of `D.elementaryTitsSystem K` are the preimage of those of
`D.titsSystem K` under `D.elementaryToExtendedWeylGroupEquiv K`. -/
theorem elementaryTitsSystem_simple :
    (D.elementaryTitsSystem K).simple =
      D.elementaryToExtendedWeylGroupEquiv K ⁻¹' (D.titsSystem K).simple :=
  (D.titsSystem K).comap_simple
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_elementary_mul_mem_titsSystem_inf K)

/-- Each Bruhat cell of `D.elementaryTitsSystem K` is the intersection with `D.elementarySubgroup K`
of the corresponding Bruhat cell of `D.titsSystem K`. -/
theorem elementaryTitsSystem_bruhatCell (w : (D.elementaryTitsSystem K).WeylGroup) :
    (D.elementaryTitsSystem K).bruhatCell w =
      Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K) ⁻¹'
        (D.titsSystem K).bruhatCell (D.elementaryToExtendedWeylGroupEquiv K w) :=
  (D.titsSystem K).comap_bruhatCell
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_elementary_mul_mem_titsSystem_inf K) w

end Field

end TauCeti.DynkinType.ChevalleyDatum
