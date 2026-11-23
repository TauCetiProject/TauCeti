/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
public import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Triangular
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Blocks
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
`U(k) ∩ (U⁻(k) ⊔ T_D(k)) = 1` forces it to be trivial. Consequently, the centre of `E_D(k)`
equals the toral centralizer of `D.rootTorusSubgroup k`, and when the root parametrizations are
injective — in particular for `t.scChevalleyDatum ht` — this identifies `Subgroup.center (E_D(k))`
with `AddChar ((Fin t.rank → ℤ) ⧸ Q_D) kˣ` (and `AddChar (P / Q) kˣ` in the simply connected
case), and gives trivial centre when the coordinate roots span `Fin t.rank → ℤ`.

## Main definitions and results

* `ChevalleyDatum.extendedElementarySubgroup_inf_normalizer_range_torusPoints` and
  `ChevalleyDatum.normalizer_torusPoints_subgroupOf_extendedElementarySubgroup`: over an infinite
  field, the normalizer of `T_D(K)` in `E_D(K)` is `D.weylSubgroup K`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_range_torusPoints` and
  `ChevalleyDatum.centralizer_torusPoints_subgroupOf_extendedElementarySubgroup`: over an infinite
  field, `T_D(K)` is self-centralizing in `E_D(K)`.
* `ChevalleyDatum.normalizerTorusQuotientMulEquiv`: `N_{E_D(K)}(T_D(K)) / C_{E_D(K)}(T_D(K)) ≃* W`.
* `ChevalleyDatum.map_positivePoints_conj_of_weylProjection_eq_longestElement`: conjugating
  `D.positivePoints k` by any Weyl lift of the longest element yields `D.negativePoints k`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_elementarySubgroup`:
  over any field, the centralizer of `D.elementarySubgroup k` inside
  `D.extendedElementarySubgroup k` equals the toral centralizer of `D.rootTorusSubgroup k`.
* `ChevalleyDatum.map_center_extendedElementarySubgroup_subtype` and
  `ChevalleyDatum.centerExtendedElementarySubgroupEquiv`: identification of the full centre of
  `D.extendedElementarySubgroup k` over any field.
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

section InfiniteField

variable (K : Type v) [Field K] [Infinite K]

omit [Infinite K] in
private theorem torusPoints_conj_mem_inversionPoints
    (w : (t.simplyConnectedRootDatum ht).weylGroup) (s : Fin t.rank → Kˣ)
    {u : D.points K} (hu : u ∈ D.inversionPoints K w) :
    D.torusPoints K s * u * (D.torusPoints K s)⁻¹ ∈ D.inversionPoints K w := by
  have hle : D.inversionPoints K w ≤
      (D.inversionPoints K w).comap (MulAut.conj (D.torusPoints K s)).toMonoidHom :=
    D.inversionPoints_le_iff.mpr fun γ hγ a => by
      have hconj := D.torusPoints_conj_rootSubgroupPoints γ K s (toAdd a)
      rw [ofAdd_toAdd] at hconj
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj]
      exact D.rootSubgroupPoints_mem_inversionPoints K hγ _
  exact hle hu

private theorem mem_range_torusPoints_of_mem_borelSubgroup_of_mem_normalizer
    {b : D.points K} (hb : b ∈ D.borelSubgroup K)
    (hnorm : b ∈ Subgroup.normalizer (D.torusPoints K).range) :
    b ∈ (D.torusPoints K).range := by
  obtain ⟨u, hu, s₀, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hb
  have hu_norm : u ∈ Subgroup.normalizer (D.torusPoints K).range := by
    have hs₀ : D.torusPoints K s₀ ∈ Subgroup.normalizer (D.torusPoints K).range :=
      (D.torusPoints K).range.le_normalizer ⟨s₀, rfl⟩
    simpa only [mul_inv_cancel_right] using mul_mem hnorm (inv_mem hs₀)
  have hu_cent : u ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    let t₀ := D.torusPoints K s
    have hT : u * t₀ * u⁻¹ * t₀⁻¹ ∈ (D.torusPoints K).range :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hu_norm t₀).mp ⟨s, rfl⟩)
        (inv_mem ⟨s, rfl⟩)
    have hU : u * t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints K := by
      have ht_pos : t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints K :=
        (Subgroup.mem_normalizer_iff.mp
          (D.range_torusPoints_le_normalizer_positivePoints K ⟨s, rfl⟩) u⁻¹).mp (inv_mem hu)
      simpa only [mul_assoc] using mul_mem hu ht_pos
    have hbot : u * t₀ * u⁻¹ * t₀⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← D.positivePoints_inf_range_torusPoints_eq_bot K]
      exact ⟨hU, hT⟩
    exact (mul_inv_eq_one.mp (by simpa only [mul_inv_rev, mul_assoc] using hbot)).symm
  have hu1 : u = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
    exact ⟨hu, hu_cent⟩
  rw [hu1, one_mul]
  exact ⟨s₀, rfl⟩

omit [Infinite K] in
private theorem mem_centralizer_torusPoints_of_bruhatNormalForm_of_mem_normalizer
    {g u b : D.points K} {w : (t.simplyConnectedRootDatum ht).weylGroup}
    (rep : (t.simplyConnectedRootDatum ht).weylGroup → D.weylSubgroup K)
    (hrep : ∀ v, D.weylProjection K (rep v) = v)
    (hgnorm : g ∈ Subgroup.normalizer (D.torusPoints K).range)
    (hu : u ∈ D.inversionPoints K w) (hb : b ∈ D.borelSubgroup K)
    (hprod : u * (rep w : D.points K) * b = g) :
    u ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  obtain ⟨s', hs'⟩ :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hgnorm) (D.torusPoints K s)).mp ⟨s, rfl⟩
  rw [inv_inv] at hs'
  have hle : D.inversionPoints K w ≤
      (D.negativePoints K).map (MulAut.conj (rep w : D.points K)).toMonoidHom := by
    have hle' := D.inversionPoints_le_map_negativePoints_conj K (rep w)
    rwa [hrep w] at hle'
  have hb' : (rep w : D.points K)⁻¹ * D.torusPoints K s * (rep w : D.points K) * b ∈
      D.borelSubgroup K :=
    mul_mem (by
      simpa only [Subgroup.coe_inv, inv_inv] using
        D.weylSubgroup_conj_torusPoints_mem_borelSubgroup K (rep w)⁻¹ s)
      hb
  have heq :
      (D.torusPoints K s * u * (D.torusPoints K s)⁻¹) * (rep w : D.points K) *
          ((rep w : D.points K)⁻¹ * D.torusPoints K s * (rep w : D.points K) * b) =
        u * (rep w : D.points K) * (b * D.torusPoints K s') := by
    calc
      _ = D.torusPoints K s * g := by rw [← hprod]; group
      _ = g * D.torusPoints K s' := by rw [hs']; group
      _ = _ := by rw [← hprod]; group
  exact eq_mul_of_mul_inv_eq (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq K
    (hle (D.torusPoints_conj_mem_inversionPoints K w s hu)) (hle hu) hb'
    (mul_mem hb (D.range_torusPoints_le_borelSubgroup K ⟨s', rfl⟩)) heq).1

/-- Over an infinite field, the normalizer of the actual torus `T_D(K)` inside the extended
elementary subgroup `E_D(K)` is precisely the Weyl subgroup `D.weylSubgroup K`. -/
theorem extendedElementarySubgroup_inf_normalizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.normalizer (D.torusPoints K).range =
      D.weylSubgroup K := by
  apply le_antisymm
  · rintro g ⟨hgE, hgnorm⟩
    let rep : (t.simplyConnectedRootDatum ht).weylGroup → D.weylSubgroup K :=
      fun w => (D.weylProjection_surjective K w).choose
    have hrep : ∀ w, D.weylProjection K (rep w) = w :=
      fun w => (D.weylProjection_surjective K w).choose_spec
    obtain ⟨⟨w, u, b⟩, ⟨hu, hb, hprod⟩, -⟩ :=
      D.existsUnique_bruhatNormalForm K rep hrep hgE
    have hu_cent : u ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) :=
      D.mem_centralizer_torusPoints_of_bruhatNormalForm_of_mem_normalizer K
        rep hrep hgnorm hu hb hprod
    have hu1 : u = 1 := by
      rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
      exact ⟨D.inversionPoints_le_positivePoints K w hu, hu_cent⟩
    have hb_norm : b ∈ Subgroup.normalizer (D.torusPoints K).range := by
      have hgb : b = (rep w : D.points K)⁻¹ * g := by
        rw [← hprod, hu1, one_mul, inv_mul_cancel_left]
      rw [hgb]
      exact mul_mem (inv_mem (D.weylSubgroup_le_normalizer_range_torusPoints K (rep w).property))
        hgnorm
    obtain ⟨s₀, hs₀⟩ := D.mem_range_torusPoints_of_mem_borelSubgroup_of_mem_normalizer K hb hb_norm
    rw [← hprod, hu1, one_mul, ← hs₀]
    exact mul_mem (rep w).property (D.torusPoints_mem_weylSubgroup K s₀)
  · exact le_inf (D.weylSubgroup_le_extendedElementarySubgroup K)
      (D.weylSubgroup_le_normalizer_range_torusPoints K)

/-- Over an infinite field, the normalizer of the actual torus inside the extended elementary
group `D.extendedElementarySubgroup K` is `D.weylSubgroup K`. -/
@[simp]
theorem normalizer_torusPoints_subgroupOf_extendedElementarySubgroup :
    Subgroup.normalizer
        ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
          Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K)) =
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) := by
  have hTE : (D.torusPoints K).range ≤ D.extendedElementarySubgroup K := by
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_extendedElementarySubgroup K s
  rw [← Subgroup.subgroupOf_normalizer_eq hTE,
    ← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
  ext ⟨x, hx⟩
  simp [Subgroup.mem_subgroupOf]

/-- Over an infinite field, the elements of `D.elementarySubgroup K` normalizing the actual torus
are precisely its intersection with `D.weylSubgroup K`. -/
theorem elementarySubgroup_inf_normalizer_range_torusPoints :
    D.elementarySubgroup K ⊓ Subgroup.normalizer (D.torusPoints K).range =
      D.elementarySubgroup K ⊓ D.weylSubgroup K := by
  nth_rw 1 [← inf_eq_left.mpr (D.elementarySubgroup_le_extendedElementarySubgroup K)]
  rw [inf_assoc, D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]

private theorem weylProjection_eq_one_of_mem_centralizer_range_torusPoints
    {n : D.weylSubgroup K}
    (hc : (n : D.points K) ∈ Subgroup.centralizer (Set.range (D.torusPoints K))) :
    D.weylProjection K n = 1 := by
  obtain ⟨l, s, hls⟩ :=
    (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints K).mp n.property
  let word : D.points K := (l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod
  have hts_cent : D.torusPoints K s ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    exact ((Commute.all r s).map (D.torusPoints K)).eq
  have hword_cent : word ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
    have heq : word = (n : D.points K) * (D.torusPoints K s)⁻¹ := eq_mul_inv_of_mul_eq hls
    rw [heq]
    exact mul_mem hc (inv_mem hts_cent)
  have hblock : ∀ i j, D.weight i ≠ D.weight j →
      ((word : Matrix.GeneralLinearGroup (Fin D.dim) K) :
        Matrix (Fin D.dim) (Fin D.dim) K) i j = 0 :=
    (D.mem_centralizer_range_torusPoints_iff K word).mp hword_cent
  let r := weightBlockEquiv (t.weightDegree ht) D.weight
  have hword_tri : t.geckWeylWordProd ht l = 1 := by
    rw [← D.exists_blockLDU_weylWord_iff l K r]
    refine ⟨1,
      ((word : Matrix.GeneralLinearGroup (Fin D.dim) K) : Matrix (Fin D.dim) (Fin D.dim) K),
      1, Matrix.blockUnitriangular_one, ?_, ?_, Matrix.blockUnitriangular_one, ?_, ?_⟩
    · intro i j hij
      apply hblock i j
      intro heq
      have hr : r ⟨D.weight j, Set.mem_range_self j⟩ = r ⟨D.weight i, Set.mem_range_self i⟩ :=
        congrArg r (Subtype.ext heq.symm)
      exact hij.ne hr
    · intro i j hij
      apply hblock i j
      intro heq
      exact hij.ne (congrArg (OrderDual.toDual ∘ r) (Subtype.ext heq.symm))
    · exact (Matrix.isUnit_iff_isUnit_det _).mp
        (word : Matrix.GeneralLinearGroup (Fin D.dim) K).isUnit
    · simp only [one_mul, mul_one, word]
  have hn_eq : n =
      ⟨word * D.torusPoints K s,
        mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
          (D.torusPoints_mem_weylSubgroup K s)⟩ :=
    Subtype.ext hls.symm
  rw [hn_eq, D.weylProjection_list_prod_mul_torusPoints K l s, hword_tri]

/-- Over an infinite field, the actual torus `T_D(K)` is its own centralizer inside the
extended elementary subgroup `E_D(K)`. -/
theorem extendedElementarySubgroup_inf_centralizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE, hgc⟩ := hg
    have hgW : g ∈ D.weylSubgroup K := by
      rw [← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
      refine Subgroup.mem_inf.mpr ⟨hgE, Subgroup.centralizer_le_normalizer _ ?_⟩
      simpa only [MonoidHom.coe_range] using hgc
    have hproj : D.weylProjection K ⟨g, hgW⟩ = 1 :=
      D.weylProjection_eq_one_of_mem_centralizer_range_torusPoints K hgc
    have hker : (⟨g, hgW⟩ : D.weylSubgroup K) ∈ (D.weylProjection K).ker := hproj
    rw [D.ker_weylProjection K, Subgroup.mem_subgroupOf] at hker
    exact hker
  · refine le_inf ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact D.torusPoints_mem_extendedElementarySubgroup K s
    · rintro _ ⟨s, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      exact ((Commute.all r s).map (D.torusPoints K)).eq

/-- Over an infinite field, the actual torus is self-centralizing inside
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem centralizer_torusPoints_subgroupOf_extendedElementarySubgroup :
    Subgroup.centralizer
        ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
          Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K)) =
      ((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) := by
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

/-- Over an infinite field, the elements of `D.elementarySubgroup K` centralizing the actual torus
are precisely its intersection with `(D.torusPoints K).range`. -/
theorem elementarySubgroup_inf_centralizer_range_torusPoints :
    D.elementarySubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      D.elementarySubgroup K ⊓ (D.torusPoints K).range := by
  nth_rw 1 [← inf_eq_left.mpr (D.elementarySubgroup_le_extendedElementarySubgroup K)]
  rw [inf_assoc, D.extendedElementarySubgroup_inf_centralizer_range_torusPoints K]

/-- Over an infinite field, the normalizer of `T_D(K)` inside `E_D(K)` modulo its centralizer is
canonically isomorphic to the root datum's Weyl group. -/
noncomputable def normalizerTorusQuotientMulEquiv :
    (Subgroup.normalizer
        ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
          Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K)) :
        Subgroup (D.extendedElementarySubgroup K)) ⧸
      ((Subgroup.centralizer
          ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
            Subgroup (D.extendedElementarySubgroup K)) :
              Set (D.extendedElementarySubgroup K))).subgroupOf
        (Subgroup.normalizer
          ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
            Subgroup (D.extendedElementarySubgroup K)) :
              Set (D.extendedElementarySubgroup K)))) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [D.centralizer_torusPoints_subgroupOf_extendedElementarySubgroup K])).trans
    ((QuotientGroup.congr
        ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf _)
        (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K))
        ((MulEquiv.subgroupCongr
          (D.normalizer_torusPoints_subgroupOf_extendedElementarySubgroup K)).trans
          (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)))
        (by
          ext n
          rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
          constructor
          · rintro ⟨m, hm, hmn⟩
            rw [Subgroup.mem_subgroupOf] at hm
            rw [← hmn]
            exact hm
          · rintro hn
            have hnE : (n : D.points K) ∈ D.extendedElementarySubgroup K :=
              D.weylSubgroup_le_extendedElementarySubgroup K n.property
            have hnN : (⟨(n : D.points K), hnE⟩ : D.extendedElementarySubgroup K) ∈
                Subgroup.normalizer
                  ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
                    Subgroup (D.extendedElementarySubgroup K)) :
                      Set (D.extendedElementarySubgroup K)) := by
              rw [D.normalizer_torusPoints_subgroupOf_extendedElementarySubgroup K,
                Subgroup.mem_subgroupOf]
              exact n.property
            refine ⟨⟨⟨(n : D.points K), hnE⟩, hnN⟩, ?_, Subtype.ext rfl⟩
            rw [Subgroup.mem_subgroupOf]
            exact hn)).trans
      (D.weylSubgroupQuotientMulEquiv K))

/-- Evaluating `normalizerTorusQuotientMulEquiv` on the class of a normalizer element returns its
Weyl projection. -/
@[simp]
theorem normalizerTorusQuotientMulEquiv_mk
    (n : Subgroup.normalizer
      ((((D.torusPoints K).range).subgroupOf (D.extendedElementarySubgroup K) :
        Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K))) :
    D.normalizerTorusQuotientMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K
        ⟨(n : D.extendedElementarySubgroup K),
          ((D.normalizer_torusPoints_subgroupOf_extendedElementarySubgroup K ▸ n.property) :
            (n : D.extendedElementarySubgroup K) ∈
              (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))⟩ := by
  simp [normalizerTorusQuotientMulEquiv, QuotientGroup.congr, MulEquiv.subgroupCongr,
    Subgroup.subgroupOfEquivOfLe]
  rfl

end InfiniteField

/-! ### The centre over an arbitrary field -/

section Field

attribute [local instance] isReduced_simplyConnectedRootDatum

variable (k : Type v) [Field k]

/-- Conjugating the positive unipotent subgroup by any Weyl lift of the longest element gives the
negative unipotent subgroup. -/
theorem map_positivePoints_conj_of_weylProjection_eq_longestElement (n₀ : D.weylSubgroup k)
    (hn₀ : D.weylProjection k n₀ =
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) :
    (D.positivePoints k).map (MulAut.conj (n₀ : D.points k)).toMonoidHom =
      D.negativePoints k := by
  have hneg : negRoots (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) =
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    ext γ
    simp only [mem_negRoots, RootPairing.Base.isPos_iff, height_rationalBase]
  rw [D.positivePoints_eq_iSup k, D.negativePoints_eq_iSup k, D.map_iSup_rootSubgroupPoints_conj,
    hn₀, t.posRoots_rationalRootSystem ht,
    image_weylGroupToPerm_longestElement_posRoots, hneg]

/-- Over any field, an element of `D.extendedElementarySubgroup k` that commutes with each simple
root element `x_{αᵢ}(1)` belongs to `D.borelSubgroup k`. -/
theorem mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot
    {g : D.points k} (hg : g ∈ D.extendedElementarySubgroup k)
    (hcomm : ∀ i : Fin t.rank,
      Commute g (D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd 1))) :
    g ∈ D.borelSubgroup k := by
  let rep : (t.simplyConnectedRootDatum ht).weylGroup → D.weylSubgroup k :=
    fun w => (D.weylProjection_surjective k w).choose
  have hrep : ∀ w, D.weylProjection k (rep w) = w :=
    fun w => (D.weylProjection_surjective k w).choose_spec
  obtain ⟨⟨w, u, b⟩, ⟨hu, hb, hprod⟩, huniq⟩ :=
    D.existsUnique_bruhatNormalForm k rep hrep hg
  have hw : w = 1 := by
    by_contra hwne
    obtain ⟨α, hαsupp, hαinv⟩ := exists_mem_support_mem_inversions_of_ne_one
      (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) (inv_ne_one.mpr hwne)
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support (by rwa [support_rationalBase])
    let x := D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd 1)
    have hx_inv : x ∈ D.inversionPoints k w :=
      D.rootSubgroupPoints_mem_inversionPoints k hαinv (ofAdd 1)
    have hx_B : x ∈ D.borelSubgroup k :=
      D.positivePoints_le_borelSubgroup k
        (D.rootSubgroupPoints_mem_positivePoints k (simpleIndex_mem_posRoots i) (ofAdd 1))
    have hmul : (x * u) * (rep w : D.points k) * b = u * (rep w : D.points k) * (b * x) := by
      calc
        (x * u) * (rep w : D.points k) * b = x * (u * (rep w : D.points k) * b) := by group
        _ = x * g := by rw [hprod]
        _ = g * x := (hcomm i).symm.eq
        _ = u * (rep w : D.points k) * (b * x) := by rw [← hprod]; group
    have hle : D.inversionPoints k w ≤
        (D.negativePoints k).map (MulAut.conj (rep w : D.points k)).toMonoidHom := by
      have hle' := D.inversionPoints_le_map_negativePoints_conj k (rep w)
      rwa [hrep w] at hle'
    have hxu_eq := (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq k
      (hle (mul_mem hx_inv hu)) (hle hu) hb (mul_mem hb hx_B) hmul).1
    exact D.rootSubgroupPoints_ofAdd_one_ne_one k (t.simpleIndex ht i)
      (mul_right_cancel (by simpa only [one_mul] using hxu_eq))
  subst hw
  rw [D.inversionPoints_one k, Subgroup.mem_bot] at hu
  have hrep1 : (rep 1 : D.points k) ∈ (D.torusPoints k).range := by
    have hker : rep 1 ∈ (D.weylProjection k).ker := hrep 1
    rwa [D.ker_weylProjection k, Subgroup.mem_subgroupOf] at hker
  rw [← hprod, hu, one_mul]
  exact mul_mem (D.range_torusPoints_le_borelSubgroup k hrep1) hb

/-- Over any field, an element of `D.borelSubgroup k` that commutes with each pinned simple Weyl
representative `n_{αᵢ}(1)` lies in the actual torus `(D.torusPoints k).range`. -/
theorem mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement
    {g : D.points k} (hg : g ∈ D.borelSubgroup k)
    (hcomm : ∀ i : Fin t.rank, Commute g (D.weylElement (t.simpleIndex ht i) k 1)) :
    g ∈ (D.torusPoints k).range := by
  obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff k).mp hg
  let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
  obtain ⟨l, hl⟩ := t.geckWeylWordProd_surjective ht w₀
  let n₀ : D.weylSubgroup k :=
    ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) k 1).prod,
      D.list_prod_map_weylElement_mem_weylSubgroup k l⟩
  have hn₀_proj : D.weylProjection k n₀ = w₀ := by
    have hsub : n₀ =
        ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) k 1).prod * D.torusPoints k 1,
          mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup k l)
            (D.torusPoints_mem_weylSubgroup k 1)⟩ :=
      Subtype.ext (by simp [n₀])
    rw [hsub, D.weylProjection_list_prod_mul_torusPoints k l 1, hl]
  have hcomm_n₀ : Commute (u * D.torusPoints k s) (n₀ : D.points k) :=
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact hcomm i
  have hu_neg : (n₀ : D.points k) * u * (n₀ : D.points k)⁻¹ ∈ D.negativePoints k := by
    rw [← D.map_positivePoints_conj_of_weylProjection_eq_longestElement k n₀ hn₀_proj]
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
  have hcomm_e : e * D.torusPoints k r = D.torusPoints k r * e :=
    Subgroup.mem_centralizer_iff.mp hgc e he
  have hcomm_s : D.torusPoints k s * D.torusPoints k r = D.torusPoints k r * D.torusPoints k s :=
    ((Commute.all s r).map (D.torusPoints k)).eq
  calc
    (e * D.torusPoints k s) * D.torusPoints k r =
        e * (D.torusPoints k s * D.torusPoints k r) := by rw [mul_assoc]
    _ = e * (D.torusPoints k r * D.torusPoints k s) := by rw [hcomm_s]
    _ = (e * D.torusPoints k r) * D.torusPoints k s := by rw [← mul_assoc]
    _ = (D.torusPoints k r * e) * D.torusPoints k s := by rw [hcomm_e]
    _ = D.torusPoints k r * (e * D.torusPoints k s) := by rw [mul_assoc]

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
      (inf_le_left.trans (fun _ ⟨s, hs⟩ => hs ▸ D.torusPoints_mem_extendedElementarySubgroup k s))
      (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup k]
    exact SetLike.coe_subset_coe.mpr (D.elementarySubgroup_le_extendedElementarySubgroup k)

/-- Over any field, the centralizer of `D.extendedElementarySubgroup k` in itself is the toral
centralizer of `D.rootTorusSubgroup k`. -/
theorem extendedElementarySubgroup_inf_centralizer_extendedElementarySubgroup :
    D.extendedElementarySubgroup k ⊓
        Subgroup.centralizer (D.extendedElementarySubgroup k : Set (D.points k)) =
      (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) := by
  apply le_antisymm
  · refine (inf_le_inf_left _ (Subgroup.centralizer_le ?_)).trans
      (D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup k).le
    exact SetLike.coe_subset_coe.mpr (D.elementarySubgroup_le_extendedElementarySubgroup k)
  · refine le_inf
      (inf_le_left.trans (fun _ ⟨s, hs⟩ => hs ▸ D.torusPoints_mem_extendedElementarySubgroup k s))
      (inf_le_right.trans ?_)
    rw [D.extendedElementarySubgroup_eq_rootTorusSubgroup k]

/-- Over any field, the centre of `D.extendedElementarySubgroup k` (viewed inside `D.points k`)
is the toral centralizer of `D.rootTorusSubgroup k`. -/
theorem map_center_extendedElementarySubgroup_subtype :
    (Subgroup.center (D.extendedElementarySubgroup k)).map
        (D.extendedElementarySubgroup k).subtype =
      (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) := by
  rw [← D.extendedElementarySubgroup_inf_centralizer_extendedElementarySubgroup k]
  ext g
  constructor
  · rintro ⟨⟨g, hgE⟩, hcomm, rfl⟩
    refine ⟨hgE, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcomm ⟨x, hx⟩)
  · rintro ⟨hgE, hcomm⟩
    refine ⟨⟨g, hgE⟩, Subgroup.mem_center_iff.mpr fun ⟨x, hx⟩ => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hcomm x hx

/-- Over any field, `Subgroup.center (D.extendedElementarySubgroup k)` is the restriction of the
toral centralizer of `D.rootTorusSubgroup k`. -/
theorem center_extendedElementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.extendedElementarySubgroup k) =
      ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))).subgroupOf
        (D.extendedElementarySubgroup k) := by
  apply Subgroup.map_injective (D.extendedElementarySubgroup k).subtype_injective
  have hle : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.extendedElementarySubgroup k :=
    inf_le_left.trans (fun _ ⟨s, hs⟩ => hs ▸ D.torusPoints_mem_extendedElementarySubgroup k s)
  rw [D.map_center_extendedElementarySubgroup_subtype k,
    Subgroup.map_subgroupOf_eq_of_le hle]

/-- Over any field, the centre of `D.elementarySubgroup k` (viewed inside `D.points k`) is the
part of the toral centralizer of `D.rootTorusSubgroup k` lying in `D.elementarySubgroup k`. -/
theorem map_center_elementarySubgroup_subtype :
    (Subgroup.center (D.elementarySubgroup k)).map (D.elementarySubgroup k).subtype =
      D.elementarySubgroup k ⊓
        ((D.torusPoints k).range ⊓
          Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))) := by
  rw [← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup k]
  ext g
  constructor
  · rintro ⟨⟨g, hgE⟩, hcomm, rfl⟩
    refine ⟨hgE, D.elementarySubgroup_le_extendedElementarySubgroup k hgE,
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcomm ⟨x, hx⟩)
  · rintro ⟨hgE, -, hcomm⟩
    refine ⟨⟨g, hgE⟩, Subgroup.mem_center_iff.mpr fun ⟨x, hx⟩ => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hcomm x hx

/-- Over any field, `Subgroup.center (D.elementarySubgroup k)` is the restriction of the toral
centralizer of `D.rootTorusSubgroup k` to `D.elementarySubgroup k`. -/
theorem center_elementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.elementarySubgroup k) =
      ((D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k))).subgroupOf
        (D.elementarySubgroup k) := by
  apply Subgroup.map_injective (D.elementarySubgroup k).subtype_injective
  rw [D.map_center_elementarySubgroup_subtype k, Subgroup.subgroupOf_map_subtype, inf_comm]

section InjectiveRoots

/-- With injective root parametrizations over any field, a torus point belongs to the centre of
`D.extendedElementarySubgroup k` if and only if every root character evaluates to `1` on it. -/
theorem torusPoints_mem_center_extendedElementarySubgroup_iff
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k)) (s : Fin t.rank → kˣ) :
    (⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩ :
        D.extendedElementarySubgroup k) ∈
        Subgroup.center (D.extendedElementarySubgroup k) ↔
      ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_extendedElementarySubgroup_eq_subgroupOf k, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, and_iff_right ⟨s, rfl⟩,
    D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s]

/-- With injective root parametrizations over any field, an element belongs to the centre of
`D.extendedElementarySubgroup k` if and only if it is a torus point on which every root
character is trivial. -/
theorem mem_center_extendedElementarySubgroup_iff
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (g : D.extendedElementarySubgroup k) :
    g ∈ Subgroup.center (D.extendedElementarySubgroup k) ↔
      ∃ s : Fin t.rank → kˣ, (g : D.points k) = D.torusPoints k s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_extendedElementarySubgroup_eq_subgroupOf k, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨s, hs⟩, hgc⟩
    refine ⟨s, hs.symm, ?_⟩
    rw [← hs] at hgc
    exact (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).mp hgc
  · rintro ⟨s, hs, hroot⟩
    refine ⟨⟨s, hs.symm⟩, ?_⟩
    rw [hs]
    exact (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).mpr hroot

/-- With injective root parametrizations over any field, an element belongs to the centre of
`D.elementarySubgroup k` if and only if it is an elementary torus point on which every root
character is trivial. -/
theorem mem_center_elementarySubgroup_iff
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (g : D.elementarySubgroup k) :
    g ∈ Subgroup.center (D.elementarySubgroup k) ↔
      ∃ s : Fin t.rank → kˣ, (g : D.points k) = D.torusPoints k s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_elementarySubgroup_eq_subgroupOf k, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨s, hs⟩, hgc⟩
    refine ⟨s, hs.symm, ?_⟩
    rw [← hs] at hgc
    exact (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).mp hgc
  · rintro ⟨s, hs, hroot⟩
    refine ⟨⟨s, hs.symm⟩, ?_⟩
    rw [hs]
    exact (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).mpr hroot

/-- With injective root parametrizations over any field, the centre of
`D.extendedElementarySubgroup k` is canonically isomorphic to `AddChar (Λ(D) / Q) kˣ`, with the
lattices written in the chosen basis of `Λ(D)`. -/
noncomputable def centerExtendedElementarySubgroupEquiv
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k)) :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup k) :=
  let hle : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.extendedElementarySubgroup k :=
    inf_le_left.trans (fun _ ⟨s, hs⟩ => hs ▸ D.torusPoints_mem_extendedElementarySubgroup k s)
  (D.torusInfCentralizerRootTorusSubgroupEquiv k hinj).trans
    ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (MulEquiv.subgroupCongr (D.center_extendedElementarySubgroup_eq_subgroupOf k).symm))

/-- The centre equivalence sends a quotient character to the corresponding torus point inside
`D.extendedElementarySubgroup k`. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv k hinj χ : D.extendedElementarySubgroup k) :
        D.points k) =
      D.torusPoints k (quotientCharTorusPoint _ χ) := by
  simp [centerExtendedElementarySubgroupEquiv]

/-- The inverse centre equivalence evaluates a quotient class on the torus parameter of the given
central element. -/
@[simp]
theorem centerExtendedElementarySubgroupEquiv_symm_apply_mk
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (s : Fin t.rank → kˣ)
    (hg : (⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩ :
        D.extendedElementarySubgroup k) ∈
        Subgroup.center (D.extendedElementarySubgroup k))
    (μ : Fin t.rank → ℤ) :
    (D.centerExtendedElementarySubgroupEquiv k hinj).symm
        ⟨⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint _
      ((D.centerExtendedElementarySubgroupEquiv k hinj).symm
        ⟨⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩, hg⟩) = s := by
    apply D.torusPoints_injective k
    rw [← D.coe_centerExtendedElementarySubgroupEquiv k hinj, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

/-- When the toral centralizer of `D.rootTorusSubgroup k` lies inside `D.elementarySubgroup k`
and the root parametrizations are injective, `AddChar (Λ(D) / Q) kˣ` identifies with
`Subgroup.center (D.elementarySubgroup k)`. -/
noncomputable def centerElementarySubgroupEquivOfLe
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k) :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ ≃*
      Subgroup.center (D.elementarySubgroup k) :=
  (D.torusInfCentralizerRootTorusSubgroupEquiv k hinj).trans
    ((Subgroup.subgroupOfEquivOfLe hZ).symm.trans
      (MulEquiv.subgroupCongr (D.center_elementarySubgroup_eq_subgroupOf k).symm))

/-- Evaluating `centerElementarySubgroupEquivOfLe` recovers the same torus coordinates. -/
@[simp]
theorem coe_centerElementarySubgroupEquivOfLe
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k)
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) kˣ) :
    ((D.centerElementarySubgroupEquivOfLe k hinj hZ χ : D.elementarySubgroup k) : D.points k) =
      D.torusPoints k (quotientCharTorusPoint _ χ) := by
  simp [centerElementarySubgroupEquivOfLe]

/-- The inverse equivalence `centerElementarySubgroupEquivOfLe` evaluates a quotient class on the
torus parameter of the given central element. -/
@[simp]
theorem centerElementarySubgroupEquivOfLe_symm_apply_mk
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (hZ : (D.torusPoints k).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup k : Set (D.points k)) ≤
      D.elementarySubgroup k)
    (s : Fin t.rank → kˣ)
    (hsE : D.torusPoints k s ∈ D.elementarySubgroup k)
    (hg : (⟨D.torusPoints k s, hsE⟩ : D.elementarySubgroup k) ∈
        Subgroup.center (D.elementarySubgroup k))
    (μ : Fin t.rank → ℤ) :
    (D.centerElementarySubgroupEquivOfLe k hinj hZ).symm
        ⟨⟨D.torusPoints k s, hsE⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint _
      ((D.centerElementarySubgroupEquivOfLe k hinj hZ).symm
        ⟨⟨D.torusPoints k s, hsE⟩, hg⟩) = s := by
    apply D.torusPoints_injective k
    rw [← D.coe_centerElementarySubgroupEquivOfLe k hinj hZ, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

/-- If the coordinate roots span `Fin t.rank → ℤ` (for instance, for an adjoint Chevalley datum)
and the root parametrizations are injective, `D.extendedElementarySubgroup k` has trivial centre.
-/
theorem center_extendedElementarySubgroup_eq_bot
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ k))
    (hspan : Submodule.span ℤ (Set.range D.coordinateRoot) = ⊤) :
    Subgroup.center (D.extendedElementarySubgroup k) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [D.mem_center_extendedElementarySubgroup_iff k hinj] at hg
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

end InjectiveRoots

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

/-- Over any field, the centralizer of the simply connected elementary Chevalley group in
`(t.scChevalleyDatum ht).points k` is the toral centralizer of the generated group. -/
theorem scChevalleyDatum_elementarySubgroup_inf_centralizer :
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
theorem scChevalleyDatum_torusPoints_mem_center_iff (s : Fin t.rank → kˣ) :
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
    (t.scChevalleyDatum ht).mem_center_elementarySubgroup_iff k
      (fun γ => t.scChevalleyDatum_rootSubgroupPoints_injective ht γ k) g

/-- Over any field, unit-valued characters of `P / Q` identify with the full centre of the simply
connected elementary Chevalley group. -/
noncomputable def scChevalleyDatumCenterEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup k) :=
  (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht k).trans
    (((Subgroup.subgroupOfEquivOfLe (inf_le_left.trans (by
        rw [← t.scChevalleyDatum_extendedElementarySubgroup ht k]
        exact fun _ ⟨s, hs⟩ =>
          hs ▸ (t.scChevalleyDatum ht).torusPoints_mem_extendedElementarySubgroup k s))).symm).trans
      (MulEquiv.subgroupCongr
        ((t.scChevalleyDatum ht).center_elementarySubgroup_eq_subgroupOf k).symm))

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point in `(t.scChevalleyDatum ht).elementarySubgroup k`. -/
@[simp]
theorem coe_scChevalleyDatumCenterEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) kˣ) :
    ((t.scChevalleyDatumCenterEquiv ht k χ : (t.scChevalleyDatum ht).elementarySubgroup k) :
        (t.scChevalleyDatum ht).points k) =
      (t.scChevalleyDatum ht).torusPoints k (quotientCharTorusPoint _ χ) := by
  simp [scChevalleyDatumCenterEquiv]

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
  have hcoord : quotientCharTorusPoint _
      ((t.scChevalleyDatumCenterEquiv ht k).symm
        ⟨⟨(t.scChevalleyDatum ht).torusPoints k s,
          (t.scChevalleyDatum ht).range_torusPoints_le_elementarySubgroup_of_weightLattice_eq_top k
            (t.scChevalleyDatum_weightLattice ht) ⟨s, rfl⟩⟩, hg⟩) = s := by
    apply (t.scChevalleyDatum ht).torusPoints_injective k
    rw [← coe_scChevalleyDatumCenterEquiv, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end Field

end SimplyConnected

end TauCeti.DynkinType
