/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Intersection
public import TauCeti.GroupTheory.TitsSystem.Comap
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.TitsSystem.Parabolic.Normalizer
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The Tits system and Weyl quotient of a Chevalley datum over a field

Let `D` be a Chevalley datum of valid Dynkin type `t` and `K` any field. Over every commutative
ring `A`, the Borel-type subgroup `D.borelSubgroup A` and the Weyl subgroup `D.weylSubgroup A`
generate `D.extendedElementarySubgroup A = D.elementarySubgroup A ⊔ (D.torusPoints A).range`.

Over a field `K`, this file establishes the Tits-system axioms for the pair
`((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K),
  (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))`
inside `D.extendedElementarySubgroup K` (`D.titsSystem K`), with simple reflections represented by
`n_{αᵢ}(1)`:

* Generation follows from `D.borelSubgroup_sup_weylSubgroup_eq_extendedElementarySubgroup K`.
* Normality of `B ∩ N` inside `N` follows from `B(K) ∩ N(K) = T(K)`
  (`borelSubgroup_inf_weylSubgroup_eq_range_torusPoints`) and normalization of `T(K)` by `N(K)`.
* The rank-one multiplication axiom `B sᵢ B w B ⊆ B (sᵢ w) B ∪ B w B` factors an arbitrary element
  of `B` in `U^{(i)} X_{αᵢ} T` (`mem_borelSubgroup_iff_exists_puncturedPositivePoints_mul`), moves
  `U^{(i)}` past `n_{αᵢ}(1)` and `T` past `w`, and splits on the sign of `w⁻¹(αᵢ)` using the
  rank-one exchange relation `weylElement_mul_rootSubgroup_mul_weylElement`.
* Nondegeneracy follows from `exists_weylElement_conj_notMem_borelSubgroup`.

Pulling `D.titsSystem K` back along the inclusion of `D.elementarySubgroup K` into
`D.extendedElementarySubgroup K` via `TauCeti.TitsSystem.comap` yields the companion Tits system
`D.elementaryTitsSystem K` on the elementary Chevalley group `E_D(K)` for every Chevalley datum.

Finally, self-normalization of the Borel subgroup of a Tits system
(`TauCeti.TitsSystem.normalizer_subgroupB`) identifies the kernel of `D.weylProjection K` with the
actual torus `T_D(K)` over every field (including finite fields), yielding the canonical Weyl-group
isomorphisms `N_D(K) ⧸ T_D(K) ≃* W` (`weylQuotientEquiv`) and
`(D.titsSystem K).WeylGroup ≃* W` (`titsSystemWeylGroupEquiv`).

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_sup_weylSubgroup_eq_extendedElementarySubgroup`:
  `B(A) ⊔ N(A) = E(A) ⊔ T(A)` over every commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.titsSystem`: the Tits system on
  `D.extendedElementarySubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.elementaryTitsSystem`: the pulled-back Tits system on
  `D.elementarySubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.ker_weylProjection`: `ker (D.weylProjection K)` is the actual
  torus inside `D.weylSubgroup K`.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientEquiv`: `N_D(K) ⧸ T_D(K) ≃* W`.
* `TauCeti.DynkinType.ChevalleyDatum.titsSystemWeylGroupEquiv`:
  `(D.titsSystem K).WeylGroup ≃* W`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4 and Corollary 2.
* R. W. Carter, *Simple Groups of Lie Type*, §§8.2–8.3.
-/

public section

open Multiplicative
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Subgroup containments and generation over commutative rings -/

/-- Every positive point lies in the elementary Chevalley subgroup. -/
theorem positivePoints_le_elementarySubgroup (A : Type v) [CommRing A] :
    D.positivePoints A ≤ D.elementarySubgroup A :=
  D.positivePoints_le_iff.mpr fun γ _ u => D.rootSubgroupPoints_mem_elementarySubgroup A γ u

/-- Every negative point lies in the elementary Chevalley subgroup. -/
theorem negativePoints_le_elementarySubgroup (A : Type v) [CommRing A] :
    D.negativePoints A ≤ D.elementarySubgroup A :=
  D.negativePoints_le_iff.mpr fun γ _ u => D.rootSubgroupPoints_mem_elementarySubgroup A γ u

/-- Every Weyl element `n_γ(s)` lies in the elementary Chevalley subgroup. -/
theorem weylElement_mem_elementarySubgroup (γ : Fin t.numRoots) (A : Type v) [CommRing A]
    (s : Aˣ) : D.weylElement γ A s ∈ D.elementarySubgroup A := by
  rw [D.weylElement_def]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)
      (D.rootSubgroupPoints_mem_elementarySubgroup A _ _))
    (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)

/-- The Borel-type subgroup lies in the extended elementary subgroup over every commutative ring. -/
theorem borelSubgroup_le_extendedElementarySubgroup (A : Type v) [CommRing A] :
    D.borelSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.borelSubgroup_def, D.extendedElementarySubgroup_def]
  exact sup_le_sup_right (D.positivePoints_le_elementarySubgroup A) _

/-- The Weyl subgroup lies in the extended elementary subgroup over every commutative ring. -/
theorem weylSubgroup_le_extendedElementarySubgroup (A : Type v) [CommRing A] :
    D.weylSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.weylSubgroup_def, Subgroup.closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · exact D.torusPoints_mem_extendedElementarySubgroup A s
  · exact D.elementarySubgroup_le_extendedElementarySubgroup A
      (D.weylElement_mem_elementarySubgroup (t.simpleIndex ht i) A 1)

/-- Over every commutative ring, the Borel-type subgroup and the Weyl subgroup generate the
extended elementary subgroup `E_D(A) ⊔ T_D(A)`. -/
theorem borelSubgroup_sup_weylSubgroup_eq_extendedElementarySubgroup (A : Type v) [CommRing A] :
    D.borelSubgroup A ⊔ D.weylSubgroup A = D.extendedElementarySubgroup A := by
  apply le_antisymm
    (sup_le (D.borelSubgroup_le_extendedElementarySubgroup A)
      (D.weylSubgroup_le_extendedElementarySubgroup A))
  rw [D.extendedElementarySubgroup_def, sup_le_iff]
  refine ⟨?_, (D.range_torusPoints_le_borelSubgroup A).trans le_sup_left⟩
  rw [D.elementarySubgroup_eq_closure_simpleRootPair, Subgroup.closure_le, Set.iUnion_subset_iff]
  intro i
  rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
  · have hpos : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
      support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
    exact Subgroup.mem_sup_left
      (D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos u))
  · let ε := t.chevalleyWeylSign ht (t.simpleIndex ht i) (t.simpleIndex ht i)
    have hε : ((ε : ℤ) : A) * (((ε : ℤ) : A) * toAdd u) = toAdd u := by
      rcases Int.units_eq_one_or ε with h | h <;> simp [h]
    have hconj := D.weylElement_conj_rootSubgroupPoints i (t.simpleIndex ht i) A
      (((ε : ℤ) : A) * toAdd u)
    rw [hε, ofAdd_toAdd] at hconj
    rw [← hconj]
    have hpos : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
      support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
    have hn : D.weylElement (t.simpleIndex ht i) A 1 ∈ D.borelSubgroup A ⊔ D.weylSubgroup A :=
      Subgroup.mem_sup_right (D.weylElement_mem_weylSubgroup A i)
    have hx : D.rootSubgroupPoints (t.simpleIndex ht i) A
        (ofAdd (((ε : ℤ) : A) * toAdd u)) ∈ D.borelSubgroup A ⊔ D.weylSubgroup A :=
      Subgroup.mem_sup_left
        (D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos _))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx) (Subgroup.inv_mem _ hn)

/-! ## The rank-one Bruhat multiplication step -/

private theorem simpleWeylElement_mul_rootSubgroup_unit_mul_mem_doubleCoset
    (K : Type v) [Field K] (i : Fin t.rank) (c : Kˣ)
    {w : D.points K} (hw : w ∈ D.weylSubgroup K)
    (hneg : ((t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection K ⟨w, hw⟩))⁻¹ (t.simpleIndex ht i) ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd (c : K)) * w ∈
      DoubleCoset.doubleCoset w (D.borelSubgroup K) (D.borelSubgroup K) := by
  let α := t.simpleIndex ht i
  let n := D.weylElement α K 1
  let wN : D.weylSubgroup K := ⟨w, hw⟩
  let wPerm := (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K wN)
  have hexch := congrArg (fun x => x * n⁻¹)
    (D.weylElement_mul_rootSubgroup_mul_weylElement i K c)
  simp only [α, n, mul_inv_cancel_right] at hexch
  have hposα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
    support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
  have hb₁ : D.rootSubgroupPoints α K (ofAdd (-((c⁻¹ : Kˣ) : K))) *
      D.simpleCorootPoints i K (-c⁻¹) ∈ D.borelSubgroup K := by
    refine Subgroup.mul_mem _
      (D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hposα _)) ?_
    rw [D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  let y := n * D.rootSubgroupPoints α K (ofAdd (-((c⁻¹ : Kˣ) : K))) * n⁻¹
  have hy_range : y ∈ (D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).reflectionPerm α α) K).range :=
    ⟨_, (D.weylElement_conj_rootSubgroupPoints i α K (-((c⁻¹ : Kˣ) : K))).symm⟩
  have hneg_pos : wPerm⁻¹ ((t.simplyConnectedRootDatum ht).reflectionPerm α α) ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    have hperm : wPerm⁻¹ ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (wPerm⁻¹ α) (wPerm⁻¹ α) := by
      have h := (t.simplyConnectedRootDatum ht).weylGroupToPerm_neg (D.weylProjection K wN)⁻¹ α
      simpa only [RootPairing.indexNeg_neg, map_inv] using h
    rw [hperm, ← t.reflectionPerm_rationalRootSystem ht]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hneg
  have hb₂ : w⁻¹ * y * w ∈ D.borelSubgroup K := by
    have hrng : MulAut.conj (wN⁻¹ : D.weylSubgroup K).val y ∈
        (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) K).range.map
          (MulAut.conj (wN⁻¹ : D.weylSubgroup K).val).toMonoidHom :=
      ⟨y, hy_range, rfl⟩
    rw [D.map_range_rootSubgroupPoints_conj K wN⁻¹, map_inv, map_inv] at hrng
    obtain ⟨v, hv⟩ := hrng
    have hv' : w⁻¹ * y * w = D.rootSubgroupPoints
        (wPerm⁻¹ ((t.simplyConnectedRootDatum ht).reflectionPerm α α)) K v := by
      simpa only [Subgroup.coe_inv, MulAut.conj_apply, inv_inv, wN, wPerm] using hv.symm
    rw [hv']
    exact D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hneg_pos v)
  refine DoubleCoset.mem_doubleCoset.mpr ⟨_, hb₁, _, hb₂, ?_⟩
  calc
    n * D.rootSubgroupPoints α K (ofAdd (c : K)) * w =
        (D.rootSubgroupPoints α K (ofAdd (-((c⁻¹ : Kˣ) : K))) *
          D.simpleCorootPoints i K (-c⁻¹) * n *
          D.rootSubgroupPoints α K (ofAdd (-((c⁻¹ : Kˣ) : K))) * n⁻¹) * w := by
      rw [hexch]
    _ = _ := by simp only [y]; group

private theorem simpleWeylElement_mul_rootSubgroup_mul_mem_union_doubleCoset
    (K : Type v) [Field K] (i : Fin t.rank) (u : Multiplicative K)
    {w : D.points K} (hw : w ∈ D.weylSubgroup K) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K u * w ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * w)
          (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset w (D.borelSubgroup K) (D.borelSubgroup K) := by
  let α := t.simpleIndex ht i
  let wN : D.weylSubgroup K := ⟨w, hw⟩
  let wPerm := (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K wN)
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht)
      (wPerm⁻¹ α) with hpos | hneg
  · left
    have hmem : w⁻¹ * D.rootSubgroupPoints α K u * w ∈ D.borelSubgroup K := by
      have hrng : MulAut.conj (wN⁻¹ : D.weylSubgroup K).val (D.rootSubgroupPoints α K u) ∈
          (D.rootSubgroupPoints α K).range.map
            (MulAut.conj (wN⁻¹ : D.weylSubgroup K).val).toMonoidHom :=
        ⟨D.rootSubgroupPoints α K u, ⟨u, rfl⟩, rfl⟩
      rw [D.map_range_rootSubgroupPoints_conj K wN⁻¹ α, map_inv, map_inv] at hrng
      obtain ⟨v, hv⟩ := hrng
      have hv' : w⁻¹ * D.rootSubgroupPoints α K u * w = D.rootSubgroupPoints (wPerm⁻¹ α) K v := by
        simpa only [Subgroup.coe_inv, MulAut.conj_apply, inv_inv, wN, wPerm] using hv.symm
      rw [hv']
      exact D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hpos v)
    exact DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, _, hmem, by simp [α]; group⟩
  · by_cases hu : toAdd u = 0
    · left
      have hu1 : u = 1 := toAdd.injective (hu.trans toAdd_one.symm)
      rw [hu1, map_one, mul_one]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    · right
      let c : Kˣ := Units.mk0 (toAdd u) hu
      have huc : u = ofAdd (c : K) := by simp [c]
      rw [huc]
      exact D.simpleWeylElement_mul_rootSubgroup_unit_mul_mem_doubleCoset K i c hw hneg

private theorem mul_doubleCoset_borelSubgroup_subset (K : Type v) [Field K] (i : Fin t.rank)
    {w : D.points K} (hw : w ∈ D.weylSubgroup K) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
        (D.borelSubgroup K) (D.borelSubgroup K) *
      DoubleCoset.doubleCoset w (D.borelSubgroup K) (D.borelSubgroup K) ⊆
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * w)
        (D.borelSubgroup K) (D.borelSubgroup K) ∪
      DoubleCoset.doubleCoset w (D.borelSubgroup K) (D.borelSubgroup K) := by
  intro z hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₁
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₂
  obtain ⟨v, hv, u, s, hb₂₃⟩ :=
    (D.mem_borelSubgroup_iff_exists_puncturedPositivePoints_mul i K).mp
      (Subgroup.mul_mem _ hb₂ hb₃)
  let n := D.weylElement (t.simpleIndex ht i) K 1
  have hnv : n * v * n⁻¹ ∈ D.borelSubgroup K :=
    D.puncturedPositivePoints_le_borelSubgroup i K
      ((Subgroup.mem_normalizer_iff.mp
        (D.weylElement_mem_normalizer_puncturedPositivePoints i K 1) v).mp hv)
  have htw : w⁻¹ * D.torusPoints K s * w ∈ D.borelSubgroup K := by
    apply D.range_torusPoints_le_borelSubgroup K
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints K
      (Subgroup.inv_mem _ hw)
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints K s)).mp ⟨s, rfl⟩
  have hmid := D.simpleWeylElement_mul_rootSubgroup_mul_mem_union_doubleCoset K i u hw
  have hrewrite : b₁ * n * b₂ * (b₃ * w * b₄) =
      (b₁ * (n * v * n⁻¹)) * (n * D.rootSubgroupPoints (t.simpleIndex ht i) K u * w) *
        ((w⁻¹ * D.torusPoints K s * w) * b₄) := by
    calc
      b₁ * n * b₂ * (b₃ * w * b₄) = b₁ * n * (b₂ * b₃) * w * b₄ := by group
      _ = b₁ * n * (v * D.rootSubgroupPoints (t.simpleIndex ht i) K u * D.torusPoints K s) *
            w * b₄ := by rw [hb₂₃]
      _ = _ := by group
  have hwrap {m : D.points K}
      (hcell : n * D.rootSubgroupPoints (t.simpleIndex ht i) K u * w ∈
        DoubleCoset.doubleCoset m (D.borelSubgroup K) (D.borelSubgroup K)) :
      (b₁ * (n * v * n⁻¹)) * (n * D.rootSubgroupPoints (t.simpleIndex ht i) K u * w) *
          ((w⁻¹ * D.torusPoints K s * w) * b₄) ∈
        DoubleCoset.doubleCoset m (D.borelSubgroup K) (D.borelSubgroup K) := by
    obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := DoubleCoset.mem_doubleCoset.mp hcell
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁ * (n * v * n⁻¹) * c₁, Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁ hnv) hc₁,
        c₂ * ((w⁻¹ * D.torusPoints K s * w) * b₄),
        Subgroup.mul_mem _ hc₂ (Subgroup.mul_mem _ htw hb₄), ?_⟩
    rw [hc]
    group
  rw [hrewrite]
  exact hmid.imp hwrap hwrap

/-! ## The Tits systems on `extendedElementarySubgroup` and `elementarySubgroup` -/

/-- The pinned `i`-th simple Weyl element viewed inside
`(D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)`. -/
noncomputable def simpleWeylRep (K : Type v) [Field K] (i : Fin t.rank) :
    (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  ⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
      D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
    D.weylElement_mem_weylSubgroup K i⟩

@[simp]
private theorem coe_simpleWeylRep (K : Type v) [Field K] (i : Fin t.rank) :
    ((D.simpleWeylRep K i : D.extendedElementarySubgroup K) : D.points K) =
      D.weylElement (t.simpleIndex ht i) K 1 :=
  rfl

private theorem mem_doubleCoset_subgroupOf_borelSubgroup_iff (K : Type v) [Field K]
    (x y : D.extendedElementarySubgroup K) :
    x ∈ DoubleCoset.doubleCoset y
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K))
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ↔
      (x : D.points K) ∈ DoubleCoset.doubleCoset (y : D.points K)
        (D.borelSubgroup K) (D.borelSubgroup K) := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, hx⟩
    exact ⟨⟨b₁, D.borelSubgroup_le_extendedElementarySubgroup K hb₁⟩, hb₁,
      ⟨b₂, D.borelSubgroup_le_extendedElementarySubgroup K hb₂⟩, hb₂, Subtype.ext hx⟩

private instance normal_borelSubgroup_subgroupOf_weylSubgroup_extended (K : Type v) [Field K] :
    (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))).Normal := by
  constructor
  intro x hx y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx ⊢
  have hxT : ((x : D.extendedElementarySubgroup K) : D.points K) ∈ (D.torusPoints K).range := by
    rw [← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K]
    exact ⟨hx, x.2⟩
  have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints K y.2
  exact D.range_torusPoints_le_borelSubgroup K
    ((Subgroup.mem_normalizer_iff.mp hnorm _).mp hxT)

private def liftExtendedWeyl (K : Type v) [Field K] (x : D.points K)
    (hx : x ∈ D.weylSubgroup K) :
    (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  ⟨⟨x, D.weylSubgroup_le_extendedElementarySubgroup K hx⟩, hx⟩

private theorem closure_simple_titsSystem (K : Type v) [Field K] :
    let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup_extended K
    Subgroup.closure (Set.range fun i : Fin t.rank =>
      (QuotientGroup.mk (D.simpleWeylRep K i) :
        ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ⧸
          ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
            ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)))) = ⊤ := by
  let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup_extended K
  let Q := ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ⧸
    ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))
  refine eq_top_iff.mpr fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H n =>
    suffices ∀ x (hx : x ∈ D.weylSubgroup K),
        (QuotientGroup.mk (D.liftExtendedWeyl K x hx) : Q) ∈
          Subgroup.closure (Set.range fun i : Fin t.rank =>
            QuotientGroup.mk (D.simpleWeylRep K i)) from this _ n.2
    intro x hx
    have hx' := hx
    rw [D.weylSubgroup_def] at hx'
    induction hx' using Subgroup.closure_induction with
    | mem x hxgen =>
      rcases hxgen with ⟨s, rfl⟩ | ⟨i, rfl⟩
      · have hone : (QuotientGroup.mk (D.liftExtendedWeyl K (D.torusPoints K s) hx) : Q) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩)
        exact hone.symm ▸ one_mem _
      · exact Subgroup.subset_closure ⟨i, rfl⟩
    | one => exact one_mem _
    | mul x y hxm hym ihx ihy =>
      have hxW : x ∈ D.weylSubgroup K := by rwa [D.weylSubgroup_def]
      have hyW : y ∈ D.weylSubgroup K := by rwa [D.weylSubgroup_def]
      change (QuotientGroup.mk
        (D.liftExtendedWeyl K x hxW * D.liftExtendedWeyl K y hyW) : Q) ∈ _
      rw [QuotientGroup.mk_mul]
      exact mul_mem (ihx hxW) (ihy hyW)
    | inv x hxm ihx =>
      have hxW : x ∈ D.weylSubgroup K := by rwa [D.weylSubgroup_def]
      change (QuotientGroup.mk (D.liftExtendedWeyl K x hxW)⁻¹ : Q) ∈ _
      rw [QuotientGroup.mk_inv]
      exact inv_mem (ihx hxW)

/-- **The Tits system (BN-pair) on the extended elementary Chevalley group**
`D.extendedElementarySubgroup K = E_D(K) ⊔ T_D(K)` over any field `K`. -/
noncomputable def titsSystem (K : Type v) [Field K] :
    TauCeti.TitsSystem (D.extendedElementarySubgroup K) where
  subgroupB := (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  subgroupN := (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  closure_subgroupB_union_subgroupN := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    apply Subgroup.map_injective (D.extendedElementarySubgroup K).subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup K),
      Subgroup.map_subgroupOf_eq_of_le (D.weylSubgroup_le_extendedElementarySubgroup K),
      D.borelSubgroup_sup_weylSubgroup_eq_extendedElementarySubgroup K]
    ext y
    simp
  intersection_normal := D.normal_borelSubgroup_subgroupOf_weylSubgroup_extended K
  simple := Set.range fun i : Fin t.rank => QuotientGroup.mk (D.simpleWeylRep K i)
  closure_simple := D.closure_simple_titsSystem K
  exists_simpleRep_mul_self_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleWeylRep K i, rfl, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change D.weylElement (t.simpleIndex ht i) K 1 * D.weylElement (t.simpleIndex ht i) K 1 ∈
      D.borelSubgroup K
    rw [D.weylElement_mul_self i K, D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  mul_doubleCoset_subset s hs := by
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleWeylRep K i, rfl, fun w z hz => ?_⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hz
    rw [D.mem_doubleCoset_subgroupOf_borelSubgroup_iff K] at hz₁ hz₂
    have hmem := D.mul_doubleCoset_borelSubgroup_subset K i w.2 (Set.mul_mem_mul hz₁ hz₂)
    simpa only [Set.mem_union, D.mem_doubleCoset_subgroupOf_borelSubgroup_iff K,
      Subgroup.coe_mul, Subgroup.coe_subtype, coe_simpleWeylRep] using hmem
  exists_conj_not_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup K i
    refine ⟨D.simpleWeylRep K i, rfl,
      ⟨⟨b.1, D.borelSubgroup_le_extendedElementarySubgroup K b.2⟩, b.2⟩, ?_⟩
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_simpleWeylRep] using hb

/-- The `B` subgroup of `D.titsSystem K` is the Borel-type subgroup restricted to
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem titsSystem_subgroupB (K : Type v) [Field K] :
    (D.titsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- The `N` subgroup of `D.titsSystem K` is the Weyl subgroup restricted to
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem titsSystem_subgroupN (K : Type v) [Field K] :
    (D.titsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- Every element of `(D.titsSystem K).subgroupN` belongs to `D.weylSubgroup K` as a point. -/
theorem mem_weylSubgroup_of_mem_titsSystem_subgroupN (K : Type v) [Field K]
    (n : (D.titsSystem K).subgroupN) : (n.1 : D.points K) ∈ D.weylSubgroup K := by
  simpa only [titsSystem_subgroupN, Subgroup.mem_subgroupOf] using n.2

private theorem exists_mul_torus_mem_intersection_titsSystem (K : Type v) [Field K]
    (g : D.extendedElementarySubgroup K) :
    ∃ x : D.elementarySubgroup K,
      ∃ t ∈ (D.titsSystem K).subgroupB ⊓ (D.titsSystem K).subgroupN,
        Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K) x * t = g := by
  obtain ⟨e, he, s, hes⟩ := (D.mem_extendedElementarySubgroup_iff K g.1).mp g.2
  refine ⟨⟨e, he⟩, ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩,
    ⟨D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup K s⟩,
    Subtype.ext hes⟩

/-- **The Tits system (BN-pair) on the elementary Chevalley group `E_D(K)`**, pulled back from
`D.titsSystem K` along `E_D(K) ↪ E_D(K) ⊔ T_D(K)` via `TauCeti.TitsSystem.comap`. -/
noncomputable def elementaryTitsSystem (K : Type v) [Field K] :
    TauCeti.TitsSystem (D.elementarySubgroup K) :=
  (D.titsSystem K).comap
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_mul_torus_mem_intersection_titsSystem K)

/-- The `B` subgroup of `D.elementaryTitsSystem K` is `B(K) ∩ E_D(K)`. -/
@[simp]
theorem elementaryTitsSystem_subgroupB (K : Type v) [Field K] :
    (D.elementaryTitsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  ext x
  simp [elementaryTitsSystem]

/-- The `N` subgroup of `D.elementaryTitsSystem K` is `N(K) ∩ E_D(K)`. -/
@[simp]
theorem elementaryTitsSystem_subgroupN (K : Type v) [Field K] :
    (D.elementaryTitsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.elementarySubgroup K) := by
  ext x
  simp [elementaryTitsSystem]

/-- Every element of `(D.elementaryTitsSystem K).subgroupN` belongs to `D.weylSubgroup K` as a
point. -/
theorem mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN (K : Type v) [Field K]
    (n : (D.elementaryTitsSystem K).subgroupN) : (n.1 : D.points K) ∈ D.weylSubgroup K := by
  simpa only [elementaryTitsSystem_subgroupN, Subgroup.mem_subgroupOf] using n.2

/-! ## The kernel of `weylProjection` and the Weyl quotient isomorphisms -/

private theorem map_conj_borelSubgroup_of_weylProjection_eq_one (K : Type v) [Field K]
    {g : D.weylSubgroup K} (hg : D.weylProjection K g = 1) :
    (D.borelSubgroup K).map (MulAut.conj (g : D.points K)).toMonoidHom = D.borelSubgroup K := by
  have hU : (D.positivePoints K).map (MulAut.conj (g : D.points K)).toMonoidHom =
      D.positivePoints K := by
    rw [D.positivePoints_eq_iSup, D.map_iSup_rootSubgroupPoints_conj K g, hg, map_one]
    simp
  have hT : ((D.torusPoints K).range).map (MulAut.conj (g : D.points K)).toMonoidHom =
      (D.torusPoints K).range := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K g.2) x).mp hx
    · intro x hx
      refine ⟨(g : D.points K)⁻¹ * x * (g : D.points K), ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp
          (D.weylSubgroup_le_normalizer_range_torusPoints K g.2)
          ((g : D.points K)⁻¹ * x * (g : D.points K))).mpr
          (by simpa [← mul_assoc] using hx)
      · simp [MulAut.conj_apply, ← mul_assoc]
  rw [D.borelSubgroup_def, Subgroup.map_sup, hU, hT]

/-- Over every field (finite or infinite), the kernel of `D.weylProjection K` is precisely the
actual torus `T_D(K)` inside `D.weylSubgroup K`. -/
@[simp]
theorem ker_weylProjection (K : Type v) [Field K] :
    (D.weylProjection K).ker = ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  apply le_antisymm
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_subgroupOf, ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K]
    refine ⟨?_, g.2⟩
    let gE : D.extendedElementarySubgroup K :=
      ⟨g.1, D.weylSubgroup_le_extendedElementarySubgroup K g.2⟩
    have hgNorm : gE ∈ Subgroup.normalizer
        ((D.titsSystem K).subgroupB : Set (D.extendedElementarySubgroup K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [titsSystem_subgroupB, Subgroup.mem_subgroupOf]
      have hB := D.map_conj_borelSubgroup_of_weylProjection_eq_one K hg
      constructor
      · intro hx
        have hmem : MulAut.conj (g : D.points K) x.1 ∈
            (D.borelSubgroup K).map (MulAut.conj (g : D.points K)).toMonoidHom :=
          ⟨x.1, hx, rfl⟩
        rw [hB] at hmem
        exact hmem
      · intro hx
        rw [← hB] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [(MulAut.conj (g : D.points K)).injective hyx] at hy
    rw [(D.titsSystem K).normalizer_subgroupB] at hgNorm
    exact hgNorm
  · rintro g ⟨s, hs⟩
    rw [MonoidHom.mem_ker]
    have hg : g = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := Subtype.ext hs.symm
    rw [hg, D.weylProjection_torusPoints]

/-- An element of `D.weylSubgroup K` projects to `1` in the Weyl group if and only if it belongs
to the actual torus `T_D(K)`. -/
@[simp]
theorem weylProjection_eq_one_iff_mem_range_torusPoints (K : Type v) [Field K]
    (g : D.weylSubgroup K) :
    D.weylProjection K g = 1 ↔ (g : D.points K) ∈ (D.torusPoints K).range := by
  rw [← MonoidHom.mem_ker, D.ker_weylProjection K, Subgroup.mem_subgroupOf]

/-- **The Weyl quotient isomorphism `N_D(K) ⧸ T_D(K) ≃* W`** over any field `K`. -/
noncomputable def weylQuotientEquiv (K : Type v) [Field K] :
    D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  MulEquiv.ofBijective
    (QuotientGroup.lift (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K))
      (D.weylProjection K) fun _ hg => (D.ker_weylProjection K).ge hg)
    ⟨by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [QuotientGroup.lift_mk] at hq
        exact (QuotientGroup.eq_one_iff g).mpr ((D.ker_weylProjection K).le hq),
      fun w => by
        obtain ⟨g, rfl⟩ := D.weylProjection_surjective K w
        exact ⟨QuotientGroup.mk g, rfl⟩⟩

/-- `weylQuotientEquiv` evaluates on the class of `g ∈ N_D(K)` as `D.weylProjection K g`. -/
@[simp]
theorem weylQuotientEquiv_mk (K : Type v) [Field K] (g : D.weylSubgroup K) :
    D.weylQuotientEquiv K (QuotientGroup.mk g) = D.weylProjection K g :=
  (rfl)

/-- `weylQuotientEquiv` sends the coset of every all-root Weyl element `n_γ(s)` (`s : Kˣ`) to the
reflection `s_γ`. -/
theorem weylQuotientEquiv_mk_weylElement (K : Type v) [Field K] (γ : Fin t.numRoots) (s : Kˣ) :
    D.weylQuotientEquiv K
        (QuotientGroup.mk ⟨D.weylElement γ K s, D.weylElement_unit_mem_weylSubgroup K γ s⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ :=
  D.weylProjection_weylElement_unit K γ s

private def titsSystemSubgroupNToWeylSubgroup (K : Type v) [Field K] :
    (D.titsSystem K).subgroupN →* D.weylSubgroup K where
  toFun n := ⟨n.1.1, D.mem_weylSubgroup_of_mem_titsSystem_subgroupN K n⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The Weyl group of `D.titsSystem K` is canonically isomorphic to the root datum's Weyl
group.** -/
noncomputable def titsSystemWeylGroupEquiv (K : Type v) [Field K] :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  MulEquiv.ofBijective
    (QuotientGroup.lift (D.titsSystem K).intersection
      ((D.weylProjection K).comp (D.titsSystemSubgroupNToWeylSubgroup K)) fun n hn => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
          D.weylProjection_eq_one_iff_mem_range_torusPoints K,
          ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K]
        exact ⟨hn, n.2⟩)
    ⟨by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H n =>
        rw [QuotientGroup.lift_mk, MonoidHom.comp_apply,
          D.weylProjection_eq_one_iff_mem_range_torusPoints K] at hq
        exact (QuotientGroup.eq_one_iff n).mpr (D.range_torusPoints_le_borelSubgroup K hq),
      fun w => by
        obtain ⟨g, rfl⟩ := D.weylProjection_surjective K w
        exact ⟨QuotientGroup.mk
          ⟨⟨g.1, D.weylSubgroup_le_extendedElementarySubgroup K g.2⟩, g.2⟩, rfl⟩⟩

/-- `titsSystemWeylGroupEquiv` evaluates on `QuotientGroup.mk n` via `D.weylProjection K`. -/
@[simp]
theorem titsSystemWeylGroupEquiv_mk (K : Type v) [Field K] (n : (D.titsSystem K).subgroupN) :
    D.titsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K ⟨n.1.1, D.mem_weylSubgroup_of_mem_titsSystem_subgroupN K n⟩ :=
  (rfl)

/-- Under `titsSystemWeylGroupEquiv`, the simple reflections of `D.titsSystem K` match the simple
reflections of `t.simplyConnectedRootDatum ht`. -/
theorem image_titsSystemWeylGroupEquiv_simple (K : Type v) [Field K] :
    D.titsSystemWeylGroupEquiv K '' (D.titsSystem K).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, rfl⟩ : s ∈ Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.simpleWeylRep K i) : (D.titsSystem K).WeylGroup) := hs
    exact ⟨i, (D.weylProjection_weylElement K i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨QuotientGroup.mk (D.simpleWeylRep K i), ⟨i, rfl⟩, D.weylProjection_weylElement K i⟩

/-- **The Weyl group of `D.elementaryTitsSystem K` is canonically isomorphic to the root datum's
Weyl group.** -/
noncomputable def elementaryTitsSystemWeylGroupEquiv (K : Type v) [Field K] :
    (D.elementaryTitsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  ((D.titsSystem K).comapWeylGroupMulEquiv
    (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
    (D.exists_mul_torus_mem_intersection_titsSystem K)).trans (D.titsSystemWeylGroupEquiv K)

/-- `elementaryTitsSystemWeylGroupEquiv` evaluates on `QuotientGroup.mk n` via
`D.weylProjection K`. -/
@[simp]
theorem elementaryTitsSystemWeylGroupEquiv_mk (K : Type v) [Field K]
    (n : (D.elementaryTitsSystem K).subgroupN) :
    D.elementaryTitsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K ⟨n.1.1, D.mem_weylSubgroup_of_mem_elementaryTitsSystem_subgroupN K n⟩ := by
  let n' : ((D.titsSystem K).comap
      (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
      (D.exists_mul_torus_mem_intersection_titsSystem K)).subgroupN := n
  change (((D.titsSystem K).comapWeylGroupMulEquiv
      (Subgroup.inclusion (D.elementarySubgroup_le_extendedElementarySubgroup K))
      (D.exists_mul_torus_mem_intersection_titsSystem K)).trans (D.titsSystemWeylGroupEquiv K))
      (QuotientGroup.mk n') = _
  rw [MulEquiv.trans_apply, TauCeti.TitsSystem.comapWeylGroupMulEquiv_mk,
    titsSystemWeylGroupEquiv_mk]
  rfl

end TauCeti.DynkinType.ChevalleyDatum
