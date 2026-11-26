/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Normalizer and centralizer of the torus and the centre of a Chevalley group

Over an infinite field `K`, the normalizer of the actual torus `T_D(K)` inside the extended
elementary group `E_D(K) = D.extendedElementarySubgroup K` is the Weyl subgroup `D.weylSubgroup K`,
and its centralizer inside `E_D(K)` is `T_D(K)` itself. Inside `E_D(K)`, the quotient of the
torus normalizer by the torus centralizer is therefore canonically isomorphic to the root datum's
Weyl group `W`.

Over an arbitrary field `k` (with no infinity or divisibility assumption on `kˣ`), any element of
`E_D(k)` that commutes with the simple root elements `x_{αᵢ}(1)` and the pinned simple Weyl
representatives `n_{αᵢ}(1)` — in particular any element of `E_D(k)` centralizing the elementary
subgroup `D.elementarySubgroup k` — belongs to `T_D(k)`. Sharp Bruhat normal form forces the Weyl
index to be `1` via commutation with the `x_{αᵢ}(1)`, and commutation with a Weyl lift of the
longest element `w₀` pushes the positive unipotent factor into the opposite subgroup, where
`U(k) ∩ (U⁻(k) ⊔ T_D(k)) = 1` forces it to be trivial. Consequently, for any intermediate subgroup
`E(k) ≤ H ≤ E_D(k)`, the centre of `H` is the restriction of the toral centralizer of
`D.rootTorusSubgroup k`, and since every root parametrization is injective over a field
(`ChevalleyDatum.rootSubgroupPoints_injective`), this identifies `Subgroup.center (E_D(k))` with
`AddChar ((Fin t.rank → ℤ) ⧸ Q_D) kˣ` (and `AddChar (P / Q) kˣ` in the simply connected case),
and gives trivial centre when the coordinate roots span `Fin t.rank → ℤ`.

## Main definitions and results

* `ChevalleyDatum.positivePoints_inf_normalizer_range_torusPoints_le_centralizer`: over any
  commutative ring, any positive point normalizing `T_D(A)` centralizes it.
* `ChevalleyDatum.borelSubgroup_inf_normalizer_range_torusPoints`: over an infinite field, `T_D(K)`
  is self-normalizing in `D.borelSubgroup K`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_normalizer_range_torusPoints` and
  `ChevalleyDatum.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup`: over an
  infinite field, the normalizer of `T_D(K)` in `E_D(K)` is `D.weylSubgroup K`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_range_torusPoints` and
  `ChevalleyDatum.centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup`: over an
  infinite field, `T_D(K)` is self-centralizing in `E_D(K)`.
* `ChevalleyDatum.normalizerTorusQuotientMulEquiv`: `N_{E_D(K)}(T_D(K)) / C_{E_D(K)}(T_D(K)) ≃* W`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_elementarySubgroup`:
  over any field, the centralizer of `D.elementarySubgroup k` inside
  `D.extendedElementarySubgroup k` equals the toral centralizer of `D.rootTorusSubgroup k`.
* `ChevalleyDatum.center_eq_subgroupOf_of_le` and `ChevalleyDatum.centerEquivOfLe`:
  identification of the full centre of any intermediate subgroup `E(k) ≤ H ≤ E_D(k)` over any
  field, specialized to `E_D(k)` (`ChevalleyDatum.centerExtendedElementarySubgroupEquiv`) and
  `E(k)` (`ChevalleyDatum.centerElementarySubgroupEquivOfLe`).
* `scChevalleyDatumCenterEquiv`: over any field,
  `AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ ≃*
    Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(d) and Theorem 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1--7.2 and 8.4.
-/

public section

namespace TauCeti.DynkinType

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

universe v

namespace ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ### Normalizer and centralizer of the torus over an infinite field -/

/-- Over any commutative ring, any positive point normalizing the actual torus `T_D(A)`
centralizes it. -/
theorem positivePoints_inf_normalizer_range_torusPoints_le_centralizer
    (A : Type v) [CommRing A] :
    D.positivePoints A ⊓ Subgroup.normalizer (D.torusPoints A).range ≤
      Subgroup.centralizer (Set.range (D.torusPoints A)) := by
  rintro u ⟨hu, hu_norm⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  let t₀ := D.torusPoints A s
  have hT : u * t₀ * u⁻¹ * t₀⁻¹ ∈ (D.torusPoints A).range :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hu_norm t₀).mp ⟨s, rfl⟩) (inv_mem ⟨s, rfl⟩)
  have hU : u * t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints A := by
    have ht_pos : t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints A :=
      (Subgroup.mem_normalizer_iff.mp
        (D.range_torusPoints_le_normalizer_positivePoints A ⟨s, rfl⟩) u⁻¹).mp (inv_mem hu)
    rw [mul_assoc u, mul_assoc u]
    exact mul_mem hu ht_pos
  have hbot : u * t₀ * u⁻¹ * t₀⁻¹ = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_range_torusPoints_eq_bot A]
    exact ⟨hU, hT⟩
  exact (mul_inv_eq_one.mp (by simpa only [mul_inv_rev, mul_assoc] using hbot)).symm

section InfiniteField

variable (K : Type v) [Field K] [Infinite K]

local notation "T_E" =>
  Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) (D.extendedElementarySubgroup K)
local notation "N_E" =>
  Subgroup.normalizer
    ((T_E : Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K))
local notation "C_E" =>
  Subgroup.centralizer
    ((T_E : Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K))

/-- Over an infinite field, the actual torus is self-normalizing inside `D.borelSubgroup K`. -/
theorem borelSubgroup_inf_normalizer_range_torusPoints :
    D.borelSubgroup K ⊓ Subgroup.normalizer (D.torusPoints K).range =
      (D.torusPoints K).range := by
  apply le_antisymm
  · intro b hb_mem
    obtain ⟨hb, hnorm⟩ := Subgroup.mem_inf.mp hb_mem
    obtain ⟨u, hu, s₀, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hb
    have hu_norm : u ∈ Subgroup.normalizer (D.torusPoints K).range := by
      have hs₀ : D.torusPoints K s₀ ∈ Subgroup.normalizer (D.torusPoints K).range :=
        (D.torusPoints K).range.le_normalizer ⟨s₀, rfl⟩
      simpa only [mul_inv_cancel_right] using mul_mem hnorm (inv_mem hs₀)
    have hu1 : u = 1 := by
      rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
      exact ⟨hu, D.positivePoints_inf_normalizer_range_torusPoints_le_centralizer K ⟨hu, hu_norm⟩⟩
    rw [hu1, one_mul]
    exact ⟨s₀, rfl⟩
  · exact le_inf (D.range_torusPoints_le_borelSubgroup K) (D.torusPoints K).range.le_normalizer

omit [Infinite K] in
private theorem mem_centralizer_torusPoints_of_bruhatNormalForm_of_mem_normalizer
    {g u b : D.points K} {n : D.weylSubgroup K}
    (hgnorm : g ∈ Subgroup.normalizer (D.torusPoints K).range)
    (hu : u ∈ D.inversionPoints K (D.weylProjection K n)) (hb : b ∈ D.borelSubgroup K)
    (hprod : u * (n : D.points K) * b = g) :
    u ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  obtain ⟨s', hs'⟩ :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hgnorm) (D.torusPoints K s)).mp ⟨s, rfl⟩
  rw [inv_inv] at hs'
  have hle := D.inversionPoints_le_map_negativePoints_conj K n
  have hu_conj : D.torusPoints K s * u * (D.torusPoints K s)⁻¹ ∈
      D.inversionPoints K (D.weylProjection K n) :=
    (Subgroup.mem_normalizer_iff.mp
      (D.range_torusPoints_le_normalizer_inversionPoints K (D.weylProjection K n) ⟨s, rfl⟩)
      u).mp hu
  have hb' : (n : D.points K)⁻¹ * D.torusPoints K s * (n : D.points K) * b ∈
      D.borelSubgroup K :=
    mul_mem (by
      simpa only [Subgroup.coe_inv, inv_inv] using
        D.weylSubgroup_conj_torusPoints_mem_borelSubgroup K n⁻¹ s)
      hb
  have heq :
      (D.torusPoints K s * u * (D.torusPoints K s)⁻¹) * (n : D.points K) *
          ((n : D.points K)⁻¹ * D.torusPoints K s * (n : D.points K) * b) =
        u * (n : D.points K) * (b * D.torusPoints K s') := by
    calc
      _ = D.torusPoints K s * g := by rw [← hprod]; group
      _ = g * D.torusPoints K s' := by rw [hs']; group
      _ = _ := by rw [← hprod]; group
  exact eq_mul_of_mul_inv_eq (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq K
    (hle hu_conj) (hle hu) hb'
    (mul_mem hb (D.range_torusPoints_le_borelSubgroup K ⟨s', rfl⟩)) heq).1

/-- Over an infinite field, the normalizer of the actual torus `T_D(K)` inside the extended
elementary subgroup `E_D(K)` is precisely the Weyl subgroup `D.weylSubgroup K`. -/
theorem extendedElementarySubgroup_inf_normalizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.normalizer (D.torusPoints K).range =
      D.weylSubgroup K := by
  apply le_antisymm
  · rintro g ⟨hgE, hgnorm⟩
    obtain ⟨n, u, b, hu, hb, hprod⟩ := D.exists_bruhatNormalForm K hgE
    have hu_cent : u ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) :=
      D.mem_centralizer_torusPoints_of_bruhatNormalForm_of_mem_normalizer K
        hgnorm hu hb hprod
    have hu1 : u = 1 := by
      rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
      exact ⟨D.inversionPoints_le_positivePoints K (D.weylProjection K n) hu, hu_cent⟩
    have hb_norm : b ∈ Subgroup.normalizer (D.torusPoints K).range := by
      have hgb : b = (n : D.points K)⁻¹ * g := by
        rw [← hprod, hu1, one_mul, inv_mul_cancel_left]
      rw [hgb]
      exact mul_mem (inv_mem (D.weylSubgroup_le_normalizer_range_torusPoints K n.property))
        hgnorm
    obtain ⟨s₀, hs₀⟩ :=
      ((D.borelSubgroup_inf_normalizer_range_torusPoints K).le ⟨hb, hb_norm⟩ :
        b ∈ (D.torusPoints K).range)
    rw [← hprod, hu1, one_mul, ← hs₀]
    exact mul_mem n.property (D.torusPoints_mem_weylSubgroup K s₀)
  · exact le_inf (D.weylSubgroup_le_extendedElementarySubgroup K)
      (D.weylSubgroup_le_normalizer_range_torusPoints K)

/-- Over an infinite field, the normalizer of the actual torus inside the extended elementary
group `D.extendedElementarySubgroup K` is `D.weylSubgroup K`. -/
@[simp]
theorem normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup :
    N_E = (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) := by
  rw [← Subgroup.subgroupOf_normalizer_eq (D.range_torusPoints_le_extendedElementarySubgroup K),
    ← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
  ext ⟨x, hx⟩
  simp [Subgroup.mem_subgroupOf]

/-- Over an infinite field, the actual torus `T_D(K)` is its own centralizer inside the
extended elementary subgroup `E_D(K)`. -/
theorem extendedElementarySubgroup_inf_centralizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  apply le_antisymm
  · intro g hg_mem
    obtain ⟨hgE, hgc⟩ := Subgroup.mem_inf.mp hg_mem
    have hgW : g ∈ D.weylSubgroup K := by
      rw [← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
      exact Subgroup.mem_inf.mpr ⟨hgE, Subgroup.centralizer_le_normalizer _ (by
        simpa only [MonoidHom.coe_range] using hgc)⟩
    have hproj : D.weylProjection K ⟨g, hgW⟩ = 1 :=
      (D.weylProjection_eq_one_iff K ⟨g, hgW⟩).mpr fun s =>
        (Units.ext (by
          simp only [Units.val_mul, diagGL_coe]
          exact (commute_diagonal_of_apply_eq_zero
            (t := fun j => (torusCharacter s (D.weight j) : K))
            fun i j hij => (D.mem_centralizer_range_torusPoints_iff K g).mp hgc i j
              fun hw => hij (by rw [hw])).eq)).symm
    exact (D.weylProjection_eq_one_iff_mem_range_torusPoints K ⟨g, hgW⟩).mp hproj
  · refine le_inf (D.range_torusPoints_le_extendedElementarySubgroup K) ?_
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    exact ((Commute.all r s).map (D.torusPoints K)).eq

/-- Over an infinite field, the actual torus is self-centralizing inside
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup :
    C_E = T_E := by
  ext ⟨g, hgE⟩
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf,
    MonoidHom.mem_range]
  constructor
  · intro hc
    have hgc : g ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact congrArg Subtype.val
        (hc ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ ⟨s, rfl⟩)
    have hmem : g ∈ D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (Set.range (D.torusPoints K)) :=
      Subgroup.mem_inf.mpr ⟨hgE, hgc⟩
    rwa [D.extendedElementarySubgroup_inf_centralizer_range_torusPoints K] at hmem
  · rintro ⟨s, hs⟩ ⟨x, hxE⟩ ⟨r, hr⟩
    dsimp only at hr
    exact Subtype.ext (by
      simpa [← hr, ← hs] using ((Commute.all r s).map (D.torusPoints K)).eq)

private noncomputable def normalizerEquivWeylSubgroup :
    N_E ≃* D.weylSubgroup K :=
  (MulEquiv.subgroupCongr
    (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K)).trans
    (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K))

@[local simp]
private theorem normalizerEquivWeylSubgroup_apply (n : N_E) :
    D.normalizerEquivWeylSubgroup K n =
      ⟨(n : D.extendedElementarySubgroup K),
        (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K).le n.property⟩ :=
  rfl

private theorem map_range_torusPoints_subgroupOf_normalizerEquiv :
    (Subgroup.subgroupOf T_E N_E).map ((D.normalizerEquivWeylSubgroup K : _ ≃* _) : _ →* _) =
      ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext n
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv]
  simp [Subgroup.mem_subgroupOf, normalizerEquivWeylSubgroup, MulEquiv.subgroupCongr_symm_apply]

/-- Over an infinite field, the normalizer of `T_D(K)` inside `E_D(K)` modulo its centralizer is
canonically isomorphic to the root datum's Weyl group. -/
noncomputable def normalizerTorusQuotientMulEquiv :
    (N_E : Subgroup (D.extendedElementarySubgroup K)) ⧸ (Subgroup.subgroupOf C_E N_E) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [D.centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K])).trans
    ((QuotientGroup.congr (Subgroup.subgroupOf T_E N_E)
        (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K))
        (D.normalizerEquivWeylSubgroup K)
        (D.map_range_torusPoints_subgroupOf_normalizerEquiv K)).trans
      (D.weylSubgroupQuotientMulEquiv K))

/-- Evaluating `normalizerTorusQuotientMulEquiv` on the class of a normalizer element returns its
Weyl projection. -/
@[simp]
theorem normalizerTorusQuotientMulEquiv_mk (n : N_E) :
    D.normalizerTorusQuotientMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K
        ⟨(n : D.extendedElementarySubgroup K),
          (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K).le
            n.property⟩ := by
  simp [normalizerTorusQuotientMulEquiv]

end InfiniteField

/-! ### The centre over an arbitrary field -/

section Field

attribute [local instance] isReduced_simplyConnectedRootDatum

variable (k : Type v) [Field k]

/-- Over any field, an element of `D.extendedElementarySubgroup k` that commutes with each simple
root element `x_{αᵢ}(1)` belongs to `D.borelSubgroup k`. -/
theorem mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot
    {g : D.points k} (hg : g ∈ D.extendedElementarySubgroup k)
    (hcomm : ∀ i : Fin t.rank,
      Commute g (D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd 1))) :
    g ∈ D.borelSubgroup k := by
  obtain ⟨n, u, b, hu, hb, hprod⟩ := D.exists_bruhatNormalForm k hg
  have hw : D.weylProjection k n = 1 := by
    by_contra hwne
    obtain ⟨α, hαsupp, hαinv⟩ := exists_mem_support_mem_inversions_of_ne_one
      (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) (inv_ne_one.mpr hwne)
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support (by rwa [support_rationalBase])
    let x := D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd 1)
    have hx_inv : x ∈ D.inversionPoints k (D.weylProjection k n) :=
      D.rootSubgroupPoints_mem_inversionPoints k hαinv (ofAdd 1)
    have hx_B : x ∈ D.borelSubgroup k :=
      D.positivePoints_le_borelSubgroup k
        (D.rootSubgroupPoints_mem_positivePoints k (simpleIndex_mem_posRoots i) (ofAdd 1))
    have hmul : (x * u) * (n : D.points k) * b = u * (n : D.points k) * (b * x) := by
      calc
        (x * u) * (n : D.points k) * b = x * (u * (n : D.points k) * b) := by group
        _ = x * g := by rw [hprod]
        _ = g * x := (hcomm i).symm.eq
        _ = u * (n : D.points k) * (b * x) := by rw [← hprod]; group
    have hle := D.inversionPoints_le_map_negativePoints_conj k n
    have hxu_eq := (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq k
      (hle (mul_mem hx_inv hu)) (hle hu) hb (mul_mem hb hx_B) hmul).1
    exact D.rootSubgroupPoints_ofAdd_one_ne_one k (t.simpleIndex ht i)
      (mul_right_cancel (by simpa only [one_mul] using hxu_eq))
  rw [hw, D.inversionPoints_one k, Subgroup.mem_bot] at hu
  have hnT : (n : D.points k) ∈ (D.torusPoints k).range :=
    (D.weylProjection_eq_one_iff_mem_range_torusPoints k n).mp hw
  rw [← hprod, hu, one_mul]
  exact mul_mem (D.range_torusPoints_le_borelSubgroup k hnT) hb

/-- Over any field, an element of `D.borelSubgroup k` that commutes with each pinned simple Weyl
representative `n_{αᵢ}(1)` lies in the actual torus `(D.torusPoints k).range`. -/
theorem mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement
    {g : D.points k} (hg : g ∈ D.borelSubgroup k)
    (hcomm : ∀ i : Fin t.rank, Commute g (D.weylElement (t.simpleIndex ht i) k 1)) :
    g ∈ (D.torusPoints k).range := by
  obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff k).mp hg
  let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
  obtain ⟨l, hl⟩ := t.simplyConnectedWeylWordProd_surjective ht w₀
  let n₀ : D.weylSubgroup k :=
    ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) k 1).prod,
      D.list_prod_map_weylElement_mem_weylSubgroup k l⟩
  have hn₀_proj : D.weylProjection k n₀ = w₀ := by
    rw [D.weylProjection_list_prod k l, hl]
  have hcomm_n₀ : Commute (u * D.torusPoints k s) (n₀ : D.points k) :=
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact hcomm i
  have hu_neg : (n₀ : D.points k) * u * (n₀ : D.points k)⁻¹ ∈ D.negativePoints k := by
    rw [← D.map_positivePoints_conj_eq_negativePoints k n₀
      (by rw [hn₀_proj, inversions_longestElement])]
    exact ⟨u, hu, rfl⟩
  obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.mp
    (D.weylSubgroup_le_normalizer_range_torusPoints k n₀.property) (D.torusPoints k s)).mp
    ⟨s, rfl⟩
  have hu_eq : u =
      ((n₀ : D.points k) * u * (n₀ : D.points k)⁻¹) *
        (D.torusPoints k s' * (D.torusPoints k s)⁻¹) := by
    rw [hs']
    calc
      u = (u * D.torusPoints k s) * (D.torusPoints k s)⁻¹ := by group
      _ = ((n₀ : D.points k) * (u * D.torusPoints k s) * (n₀ : D.points k)⁻¹) *
            (D.torusPoints k s)⁻¹ := by rw [hcomm_n₀.symm.eq]; group
      _ = _ := by group
  have hu_in_opp : u ∈ D.negativePoints k ⊔ (D.torusPoints k).range := by
    rw [hu_eq]
    exact mul_mem (Subgroup.mem_sup_left hu_neg)
      (Subgroup.mem_sup_right (mul_mem ⟨s', rfl⟩ (inv_mem ⟨s, rfl⟩)))
  have hu1 : u = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_negativePoints_sup_range_torusPoints_eq_bot k]
    exact ⟨hu, hu_in_opp⟩
  rw [hu1, one_mul]
  exact ⟨s, rfl⟩

/-- Over any field, an element of `D.extendedElementarySubgroup k` commuting with the simple root
elements `x_{αᵢ}(1)` and simple Weyl elements `n_{αᵢ}(1)` belongs to the actual torus
`T_D(k)`. -/
theorem mem_range_torusPoints_of_mem_extendedElementarySubgroup_of_commute
    {g : D.points k} (hg : g ∈ D.extendedElementarySubgroup k)
    (hroot : ∀ i : Fin t.rank,
      Commute g (D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd 1)))
    (hweyl : ∀ i : Fin t.rank, Commute g (D.weylElement (t.simpleIndex ht i) k 1)) :
    g ∈ (D.torusPoints k).range :=
  D.mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement k
    (D.mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot k hg hroot) hweyl

/-- Over any field, every element of `D.extendedElementarySubgroup k` centralizing the elementary
subgroup `D.elementarySubgroup k` lies in the actual torus `(D.torusPoints k).range`. -/
theorem extendedElementarySubgroup_inf_centralizer_elementarySubgroup_le_range_torusPoints :
    D.extendedElementarySubgroup k ⊓
        Subgroup.centralizer (D.elementarySubgroup k : Set (D.points k)) ≤
      (D.torusPoints k).range := by
  intro g hg
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg
  obtain ⟨hgE, hgc⟩ := hg
  refine D.mem_range_torusPoints_of_mem_extendedElementarySubgroup_of_commute k hgE ?_ ?_
  · intro i
    exact (hgc _ (D.rootSubgroupPoints_mem_elementarySubgroup k _ _)).symm
  · intro i
    exact (hgc _ (D.weylElement_mem_elementarySubgroup k _ _)).symm

private theorem mem_centralizer_rootTorusSubgroup_of_mem_range_torusPoints_of_mem_centralizer
    {g : D.points k} (hgT : g ∈ (D.torusPoints k).range)
    (hgc : g ∈ Subgroup.centralizer (D.elementarySubgroup k : Set (D.points k))) :
    g ∈ Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) := by
  rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup k, D.extendedElementarySubgroup_def,
    ← Subgroup.centralizer_closure]
  rw [Subgroup.mem_centralizer_iff]
  rintro x hx
  have hclosure : x ∈ D.elementarySubgroup k ⊔ (D.torusPoints k).range := by
    simpa only [Subgroup.closure_eq, SetLike.mem_coe] using hx
  rw [Subgroup.mem_sup_of_right_le_normalizer_left
    (D.range_torusPoints_le_normalizer_elementarySubgroup k)] at hclosure
  obtain ⟨e, he, _, ⟨s, rfl⟩, rfl⟩ := hclosure
  obtain ⟨r, rfl⟩ := hgT
  exact (Commute.mul_left (Subgroup.mem_centralizer_iff.mp hgc e he)
    ((Commute.all s r).map (D.torusPoints k))).eq

/-- Over any field, the centralizer of `D.elementarySubgroup k` inside
`D.extendedElementarySubgroup k` equals the toral centralizer of `D.rootTorusSubgroup k`. -/
theorem extendedElementarySubgroup_inf_centralizer_elementarySubgroup :
    D.extendedElementarySubgroup k ⊓
        Subgroup.centralizer (D.elementarySubgroup k : Set (D.points k)) =
      (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) := by
  apply le_antisymm
  · rintro g ⟨hgE, hgc⟩
    have hgT : g ∈ (D.torusPoints k).range :=
      D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup_le_range_torusPoints k
        ⟨hgE, hgc⟩
    exact ⟨hgT,
      D.mem_centralizer_rootTorusSubgroup_of_mem_range_torusPoints_of_mem_centralizer k hgT hgc⟩
  · refine le_inf
      (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup k))
      (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup k]
    exact SetLike.coe_subset_coe.mpr (D.elementarySubgroup_le_extendedElementarySubgroup k)

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)`, the
centralizer of `H` in itself equals its intersection with the toral centralizer of
`D.rootTorusSubgroup k`. -/
theorem inf_centralizer_of_le {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k) :
    H ⊓ Subgroup.centralizer (H : Set (D.points k)) =
      H ⊓ ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))) := by
  apply le_antisymm
  · rw [← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup k]
    exact le_inf inf_le_left (inf_le_inf hHE (Subgroup.centralizer_le hEH))
  · refine inf_le_inf_left H (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup k]
    exact SetLike.coe_subset_coe.mpr hHE

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)`, the
centre of `H` (viewed inside `D.points k`) is the part of the toral centralizer of
`D.rootTorusSubgroup k` lying in `H`. -/
theorem map_center_subtype_of_le {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k) :
    (Subgroup.center H).map H.subtype =
      H ⊓ ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))) := by
  rw [← D.inf_centralizer_of_le k hEH hHE]
  ext g
  constructor
  · rintro ⟨⟨g, hgH⟩, hcomm, rfl⟩
    refine ⟨hgH, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcomm ⟨x, hx⟩)
  · rintro ⟨hgH, hcomm⟩
    refine ⟨⟨g, hgH⟩, Subgroup.mem_center_iff.mpr fun ⟨x, hx⟩ => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hcomm x hx

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)`,
`Subgroup.center H` is the restriction of the toral centralizer of `D.rootTorusSubgroup k` to
`H`. -/
theorem center_eq_subgroupOf_of_le {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k) :
    Subgroup.center H =
      ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [D.map_center_subtype_of_le k hEH hHE, Subgroup.subgroupOf_map_subtype, inf_comm]

/-- Over any field, `Subgroup.center (D.extendedElementarySubgroup k)` is the restriction of the
toral centralizer of `D.rootTorusSubgroup k`. -/
theorem center_extendedElementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.extendedElementarySubgroup k) =
      ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))).subgroupOf
        (D.extendedElementarySubgroup k) :=
  D.center_eq_subgroupOf_of_le k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl

/-- Over any field, `Subgroup.center (D.elementarySubgroup k)` is the restriction of the toral
centralizer of `D.rootTorusSubgroup k` to `D.elementarySubgroup k`. -/
theorem center_elementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.elementarySubgroup k) =
      ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))).subgroupOf
        (D.elementarySubgroup k) :=
  D.center_eq_subgroupOf_of_le k le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup k)

/-- Over any field, an element of an intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)`
belongs to `Subgroup.center H` if and only if it is a torus point on which every root character is
trivial. -/
theorem mem_center_iff_of_le {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k) (g : H) :
    g ∈ Subgroup.center H ↔
      ∃ s : Fin t.rank → kˣ, (g : D.points k) = D.torusPoints k s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_eq_subgroupOf_of_le k hEH hHE, Subgroup.mem_subgroupOf,
    ← D.map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup
      (D.rootSubgroupPoints_injective k),
    Subgroup.mem_map]
  simp only [mem_torusAnnihilator_span_iff, eq_comm, and_comm]

/-- Over any field, a torus point belongs to the centre of `D.extendedElementarySubgroup k` if
and only if every root character evaluates to `1` on it. -/
@[simp]
theorem torusPoints_mem_center_extendedElementarySubgroup_iff (s : Fin t.rank → kˣ) :
    (⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩ :
        D.extendedElementarySubgroup k) ∈
        Subgroup.center (D.extendedElementarySubgroup k) ↔
      ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_extendedElementarySubgroup_eq_subgroupOf k, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, and_iff_right ⟨s, rfl⟩,
    D.torusPoints_mem_centralizer_rootTorusSubgroup_iff (D.rootSubgroupPoints_injective k) s]

/-- Over any field, an element belongs to the centre of `D.extendedElementarySubgroup k` if and
only if it is a torus point on which every root character is trivial. -/
theorem mem_center_extendedElementarySubgroup_iff (g : D.extendedElementarySubgroup k) :
    g ∈ Subgroup.center (D.extendedElementarySubgroup k) ↔
      ∃ s : Fin t.rank → kˣ, (g : D.points k) = D.torusPoints k s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 :=
  D.mem_center_iff_of_le k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl g

/-- Over any field, an element belongs to the centre of `D.elementarySubgroup k` if and only if it
is an elementary torus point on which every root character is trivial. -/
theorem mem_center_elementarySubgroup_iff (g : D.elementarySubgroup k) :
    g ∈ Subgroup.center (D.elementarySubgroup k) ↔
      ∃ s : Fin t.rank → kˣ, (g : D.points k) = D.torusPoints k s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 :=
  D.mem_center_iff_of_le k le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup k) g

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)`
containing the toral centralizer of `D.rootTorusSubgroup k`, `AddChar (Λ(D) / Q) kˣ` identifies
with `Subgroup.center H`. -/
noncomputable def centerEquivOfLe {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k)
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤ H) :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ ≃*
      Subgroup.center H :=
  (D.torusInfCentralizerRootTorusSubgroupEquiv k (D.rootSubgroupPoints_injective k)).trans
    ((Subgroup.subgroupOfEquivOfLe hZ).symm.trans
      (MulEquiv.subgroupCongr (D.center_eq_subgroupOf_of_le k hEH hHE).symm))

/-- Evaluating `centerEquivOfLe` recovers the corresponding torus point inside `H`. -/
@[simp]
theorem coe_centerEquivOfLe {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k)
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤ H)
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ) :
    ((D.centerEquivOfLe k hEH hHE hZ χ : H) : D.points k) =
      D.torusPoints k (quotientCharTorusPoint _ χ) := by
  simp [centerEquivOfLe]

private theorem centerSubgroupEquivOfLe_symm_apply {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k)
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤ H)
    (s : Fin t.rank → kˣ) (hsH : D.torusPoints k s ∈ H)
    (hg : (⟨D.torusPoints k s, hsH⟩ : H) ∈ Subgroup.center H) :
    ((Subgroup.subgroupOfEquivOfLe hZ).symm.trans
        (MulEquiv.subgroupCongr (D.center_eq_subgroupOf_of_le k hEH hHE).symm)).symm
        ⟨⟨D.torusPoints k s, hsH⟩, hg⟩ =
      ⟨D.torusPoints k s,
        Subgroup.mem_subgroupOf.mp ((D.center_eq_subgroupOf_of_le k hEH hHE).le hg)⟩ := by
  ext
  simp [MulEquiv.subgroupCongr_symm_apply]

/-- The inverse equivalence `centerEquivOfLe` evaluates a quotient class on the torus parameter of
the given central element. -/
@[simp]
theorem centerEquivOfLe_symm_apply_mk {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k)
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤ H)
    (s : Fin t.rank → kˣ) (hsH : D.torusPoints k s ∈ H)
    (hg : (⟨D.torusPoints k s, hsH⟩ : H) ∈ Subgroup.center H) (μ : Fin t.rank → ℤ) :
    (D.centerEquivOfLe k hEH hHE hZ).symm ⟨⟨D.torusPoints k s, hsH⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ := by
  rw [centerEquivOfLe, MulEquiv.symm_trans_apply,
    D.centerSubgroupEquivOfLe_symm_apply k hEH hHE hZ s hsH hg]
  exact D.torusInfCentralizerRootTorusSubgroupEquiv_symm_apply_mk k
    (D.rootSubgroupPoints_injective k) s _ μ

/-- Over any field, the centre of `D.extendedElementarySubgroup k` is canonically isomorphic to
`AddChar (Λ(D) / Q) kˣ`, with the lattices written in the chosen basis of `Λ(D)`. -/
noncomputable def centerExtendedElementarySubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup k) :=
  D.centerEquivOfLe k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup k))

/-- The centre equivalence sends a quotient character to the corresponding torus point inside
`D.extendedElementarySubgroup k`. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv k χ : D.extendedElementarySubgroup k) :
        D.points k) =
      D.torusPoints k (quotientCharTorusPoint _ χ) :=
  D.coe_centerEquivOfLe k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup k)) χ

/-- The inverse centre equivalence evaluates a quotient class on the torus parameter of the given
central element. -/
@[simp]
theorem centerExtendedElementarySubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → kˣ)
    (hg : (⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩ :
        D.extendedElementarySubgroup k) ∈
        Subgroup.center (D.extendedElementarySubgroup k))
    (μ : Fin t.rank → ℤ) :
    (D.centerExtendedElementarySubgroupEquiv k).symm
        ⟨⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ :=
  D.centerEquivOfLe_symm_apply_mk k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup k)) s
    (D.torusPoints_mem_extendedElementarySubgroup k s) hg μ

/-- Over any field, when the toral centralizer of `D.rootTorusSubgroup k` lies inside
`D.elementarySubgroup k`, `AddChar (Λ(D) / Q) kˣ` identifies with
`Subgroup.center (D.elementarySubgroup k)`. -/
noncomputable def centerElementarySubgroupEquivOfLe
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k) :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ ≃*
      Subgroup.center (D.elementarySubgroup k) :=
  D.centerEquivOfLe k le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup k) hZ

/-- Evaluating `centerElementarySubgroupEquivOfLe` recovers the same torus coordinates. -/
@[simp]
theorem coe_centerElementarySubgroupEquivOfLe
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k)
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ) :
    ((D.centerElementarySubgroupEquivOfLe k hZ χ : D.elementarySubgroup k) : D.points k) =
      D.torusPoints k (quotientCharTorusPoint _ χ) :=
  D.coe_centerEquivOfLe k le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup k) hZ χ

/-- The inverse equivalence `centerElementarySubgroupEquivOfLe` evaluates a quotient class on the
torus parameter of the given central element. -/
@[simp]
theorem centerElementarySubgroupEquivOfLe_symm_apply_mk
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k)
    (s : Fin t.rank → kˣ)
    (hsE : D.torusPoints k s ∈ D.elementarySubgroup k)
    (hg : (⟨D.torusPoints k s, hsE⟩ : D.elementarySubgroup k) ∈
        Subgroup.center (D.elementarySubgroup k))
    (μ : Fin t.rank → ℤ) :
    (D.centerElementarySubgroupEquivOfLe k hZ).symm
        ⟨⟨D.torusPoints k s, hsE⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ :=
  D.centerEquivOfLe_symm_apply_mk k le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup k)
    hZ s hsE hg μ

/-- Over any field, if the coordinate roots span `Fin t.rank → ℤ` (for instance, for an adjoint
Chevalley datum), any intermediate subgroup `D.elementarySubgroup k ≤ H ≤ E_D(k)` has trivial
centre. -/
theorem center_eq_bot_of_le {H : Subgroup (D.points k)}
    (hEH : D.elementarySubgroup k ≤ H) (hHE : H ≤ D.extendedElementarySubgroup k)
    (hspan : Submodule.span ℤ (Set.range D.coordinateRoot) = ⊤) :
    Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [D.mem_center_iff_of_le k hEH hHE] at hg
  obtain ⟨s, hgs, hroot⟩ := hg
  have hs_ann : s ∈ torusAnnihilator (R := k) (Submodule.span ℤ (Set.range D.coordinateRoot)) :=
    (mem_torusAnnihilator_span_iff D.coordinateRoot s).mpr hroot
  rw [hspan] at hs_ann
  have hs1 : s = 1 := by
    funext i
    simpa only [torusCharacter_single, zpow_one, Pi.one_apply] using
      (mem_torusAnnihilator ⊤ s).mp hs_ann (Pi.single i 1) trivial
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  rw [hgs, hs1, map_one, Subgroup.coe_one]

/-- Over any field, if the coordinate roots span `Fin t.rank → ℤ` (for instance, for an adjoint
Chevalley datum), `D.extendedElementarySubgroup k` has trivial centre. -/
theorem center_extendedElementarySubgroup_eq_bot
    (hspan : Submodule.span ℤ (Set.range D.coordinateRoot) = ⊤) :
    Subgroup.center (D.extendedElementarySubgroup k) = ⊥ :=
  D.center_eq_bot_of_le k (D.elementarySubgroup_le_extendedElementarySubgroup k) le_rfl hspan

end Field

end ChevalleyDatum

/-! ### Simply connected Chevalley groups -/

section SimplyConnected

variable (t : DynkinType) (ht : t.Valid)

section InfiniteField

variable (K : Type v) [Field K] [Infinite K]

/-- Over an infinite field, the normalizer of the torus inside the simply connected elementary
Chevalley group is its Weyl subgroup. -/
theorem scChevalleyDatum_elementarySubgroup_inf_normalizer_range_torusPoints :
    (t.scChevalleyDatum ht).elementarySubgroup K ⊓
        Subgroup.normalizer ((t.scChevalleyDatum ht).torusPoints K).range =
      (t.scChevalleyDatum ht).weylSubgroup K := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_normalizer_range_torusPoints K

/-- Over an infinite field, the torus of the simply connected Chevalley group is self-centralizing
inside its elementary group. -/
theorem scChevalleyDatum_elementarySubgroup_inf_centralizer_range_torusPoints :
    (t.scChevalleyDatum ht).elementarySubgroup K ⊓
        Subgroup.centralizer (Set.range ((t.scChevalleyDatum ht).torusPoints K)) =
      ((t.scChevalleyDatum ht).torusPoints K).range := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_centralizer_range_torusPoints K

end InfiniteField

section Field

variable (k : Type v) [Field k]

/-- Over any field, the centralizer of the simply connected elementary Chevalley group inside
itself, viewed as a subgroup of `(t.scChevalleyDatum ht).points k`, is the toral centralizer of
`(t.scChevalleyDatum ht).rootTorusSubgroup k`. -/
theorem scChevalleyDatum_elementarySubgroup_inf_centralizer_elementarySubgroup :
    (t.scChevalleyDatum ht).elementarySubgroup k ⊓
        Subgroup.centralizer
          ((t.scChevalleyDatum ht).elementarySubgroup k :
            Set ((t.scChevalleyDatum ht).points k)) =
      ((t.scChevalleyDatum ht).torusPoints k).range ⊓
        Subgroup.centralizer
          ((t.scChevalleyDatum ht).rootTorusSubgroup k :
            Set ((t.scChevalleyDatum ht).points k)) := by
  nth_rw 1 [← t.scChevalleyDatum_extendedElementarySubgroup ht k]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_centralizer_elementarySubgroup k

/-- Over any field, a simply connected torus point belongs to the centre of the simply connected
elementary Chevalley group if and only if every root character evaluates to `1` on it. -/
@[simp]
theorem scChevalleyDatum_torusPoints_mem_center_elementarySubgroup_iff (s : Fin t.rank → kˣ) :
    (⟨(t.scChevalleyDatum ht).torusPoints k s,
        (t.scChevalleyDatum ht).range_torusPoints_le_elementarySubgroup_of_weightLattice_eq_top k
          (t.scChevalleyDatum_weightLattice ht) ⟨s, rfl⟩⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup k) ∈
        Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k) ↔
      ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  rw [((t.scChevalleyDatum ht).center_elementarySubgroup_eq_subgroupOf k), Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, and_iff_right ⟨s, rfl⟩,
    scChevalleyDatum_torusPoints_mem_centralizer_rootTorusSubgroup_iff]

/-- Over any field, an element of `(t.scChevalleyDatum ht).elementarySubgroup k` belongs to the
centre if and only if it is a torus point on which every root character is trivial. -/
theorem mem_center_scChevalleyDatum_elementarySubgroup_iff
    (g : (t.scChevalleyDatum ht).elementarySubgroup k) :
    g ∈ Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k) ↔
      ∃ s : Fin t.rank → kˣ, (g : (t.scChevalleyDatum ht).points k) =
          (t.scChevalleyDatum ht).torusPoints k s ∧
        ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  simpa only [scChevalleyDatum_coordinateRoot] using
    (t.scChevalleyDatum ht).mem_center_elementarySubgroup_iff k g

private noncomputable def scRootQuotientCharEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ ≃*
      AddChar ((Fin t.rank → ℤ) ⧸
        Submodule.span ℤ (Set.range (t.scChevalleyDatum ht).coordinateRoot)) kˣ :=
  let hspan :
      (t.simplyConnectedRootDatum ht).rootSpan ℤ =
        Submodule.span ℤ (Set.range (t.scChevalleyDatum ht).coordinateRoot) := by
    rw [RootPairing.rootSpan, funext (t.scChevalleyDatum_coordinateRoot ht)]
  let e := Submodule.quotEquivOfEq _ _ hspan
  let eInv := Submodule.quotEquivOfEq _ _ hspan.symm
  { toFun := fun χ => χ.compAddMonoidHom eInv.toAddMonoidHom
    invFun := fun ψ => ψ.compAddMonoidHom e.toAddMonoidHom
    left_inv := fun χ => by
      ext x
      induction x using Submodule.Quotient.induction_on
      simp [e, eInv, Submodule.quotEquivOfEq_mk]
    right_inv := fun ψ => by
      ext x
      induction x using Submodule.Quotient.induction_on
      simp [e, eInv, Submodule.quotEquivOfEq_mk]
    map_mul' := fun _ _ => by ext x; simp }

@[simp]
private theorem scRootQuotientCharEquiv_apply_mk
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ)
    (μ : Fin t.rank → ℤ) :
    scRootQuotientCharEquiv t ht k χ (Submodule.Quotient.mk μ) =
      χ (Submodule.Quotient.mk μ) := by
  simp [scRootQuotientCharEquiv, Submodule.quotEquivOfEq_mk]

@[simp]
private theorem scRootQuotientCharEquiv_symm_apply_mk
    (ψ : AddChar ((Fin t.rank → ℤ) ⧸
      Submodule.span ℤ (Set.range (t.scChevalleyDatum ht).coordinateRoot)) kˣ)
    (μ : Fin t.rank → ℤ) :
    (scRootQuotientCharEquiv t ht k).symm ψ (Submodule.Quotient.mk μ) =
      ψ (Submodule.Quotient.mk μ) := by
  simp [scRootQuotientCharEquiv, Submodule.quotEquivOfEq_mk]

/-- Over any field, unit-valued characters of `P / Q` identify with the full centre of the simply
connected elementary Chevalley group. -/
noncomputable def scChevalleyDatumCenterEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k) :=
  (scRootQuotientCharEquiv t ht k).trans
    ((t.scChevalleyDatum ht).centerElementarySubgroupEquivOfLe k
      (inf_le_left.trans
        ((t.scChevalleyDatum ht).range_torusPoints_le_elementarySubgroup_of_weightLattice_eq_top k
          (t.scChevalleyDatum_weightLattice ht))))

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point in `(t.scChevalleyDatum ht).elementarySubgroup k`. -/
@[simp]
theorem coe_scChevalleyDatumCenterEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ) :
    ((t.scChevalleyDatumCenterEquiv ht k χ : (t.scChevalleyDatum ht).elementarySubgroup k) :
        (t.scChevalleyDatum ht).points k) =
      (t.scChevalleyDatum ht).torusPoints k (quotientCharTorusPoint _ χ) := by
  rw [scChevalleyDatumCenterEquiv, MulEquiv.trans_apply,
    ChevalleyDatum.coe_centerElementarySubgroupEquivOfLe]
  congr 1
  ext i
  simp only [quotientCharTorusPoint_apply, Submodule.mkQ_apply, scRootQuotientCharEquiv_apply_mk]

/-- The inverse simply connected centre equivalence evaluates a weight class on the torus
parameter of the given central element. -/
@[simp]
theorem scChevalleyDatumCenterEquiv_symm_apply_mk (s : Fin t.rank → kˣ)
    (hg : (⟨(t.scChevalleyDatum ht).torusPoints k s,
        (t.scChevalleyDatum ht).range_torusPoints_le_elementarySubgroup_of_weightLattice_eq_top k
          (t.scChevalleyDatum_weightLattice ht) ⟨s, rfl⟩⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup k) ∈
        Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k))
    (μ : Fin t.rank → ℤ) :
    (t.scChevalleyDatumCenterEquiv ht k).symm
        ⟨⟨(t.scChevalleyDatum ht).torusPoints k s,
          (t.scChevalleyDatum ht).range_torusPoints_le_elementarySubgroup_of_weightLattice_eq_top k
            (t.scChevalleyDatum_weightLattice ht) ⟨s, rfl⟩⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ := by
  simp only [scChevalleyDatumCenterEquiv, MulEquiv.symm_trans_apply,
    scRootQuotientCharEquiv_symm_apply_mk]
  exact ChevalleyDatum.centerElementarySubgroupEquivOfLe_symm_apply_mk _ k _ s _ hg μ

end Field

end SimplyConnected

end TauCeti.DynkinType

