/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
public import TauCeti.RingTheory.LocalRing.Herbrand
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.NumberTheory.RamificationInertia.Galois
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
import TauCeti.RingTheory.LocalRing.ResidueField.Instances
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Herbrand's lemma in the lower numbering for discrete valuation rings

Let a finite group `G` act on a discrete valuation ring `B` by `A`-algebra automorphisms over a
local ring `A`, and let `H ⊴ G` be a normal subgroup. Assuming the residue field extension
`𝓀(B) / 𝓀(A)` is separable — with neither completeness of `B`, finiteness of the residue field,
faithfulness of the `G`-action, nor `A = B^G` required — this file proves **Herbrand's theorem in
the lower numbering**:

`(G ⧸ H)_{φ_H(u)} = G_u H / H`  for every `u : ℝ`.

The deduction from Serre's counting formula `#H_0 · i(σ') = ∑_{k < j} #H_k`
(`TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`) uses only the DVR lower-index
filtration and is first isolated in abstract form so that both the DVR API and the nonarchimedean
local-field API (`TauCeti.NumberTheory.LocalField.Herbrand.Quotient`) share the same proof.

## Main results

* `TauCeti.IsLocalRing.lowerIndex_ne_top_of_mul_eq_sum_card`,
  `TauCeti.IsLocalRing.herbrandFun_sub_one_eq_of_mul_eq_sum_card`,
  `TauCeti.IsLocalRing.map_ramificationGroupReal_eq_herbrandFun_of_sum_card`: abstract deduction of
  Serre's lemma `φ_H(j - 1) = i(σ') - 1` and Herbrand's lower-numbering theorem from the counting
  identity `#H_0 · i(σ') = ∑_{k < j} #H_k`.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_eq_ramificationIdx`: `#G_0 = e(B/A)` for a
  faithful finite group action on a DVR `B` with invariant DVR `A` and separable residue extension.
* `TauCeti.IsLocalRing.ramificationGroupReal_quotient_herbrandFun_eq_map`:
  `(G ⧸ H)_{φ_H(u)} = G_u H / H` on `FixedPoints.subalgebra A B H` for all `u : ℝ`.
* `TauCeti.IsLocalRing.ramificationGroupReal_quotient_subring_herbrandFun_eq_map`: base-free form
  on `FixedPoints.subring B H`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1, 3, Lemmas 4–5 and Proposition 14.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 3.
-/

public section
noncomputable section

namespace TauCeti.IsLocalRing

/-! ### Abstract deduction of Herbrand's theorem from Serre's counting formula -/

section AbstractLowerIndex

variable {C B : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  {G G' H : Type*} [Group G] [MulSemiringAction G B]
  [Group G'] [MulSemiringAction G' C]
  [Group H] [Finite H] [MulSemiringAction H B]

/-- If `#H_0 · i_C(σ') = ∑_{k < j} #H_k` with `H` finite, then `i_C(σ') ≠ ⊤`. -/
theorem lowerIndex_ne_top_of_mul_eq_sum_card {σ' : G'} {j : ℕ}
    (hsum : (Nat.card (ramificationGroup H B 0) : ℕ∞) * lowerIndex C σ' =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞)) :
    lowerIndex C σ' ≠ ⊤ := fun htop ↦ by
  rw [htop, ENat.mul_top (by exact_mod_cast Nat.card_pos.ne'), ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

/-- **Abstract Serre's lemma.** If `#H_0 · i_C(σ') = ∑_{k < j} #H_k` with `H` finite, then
`φ_H(j - 1) = i_C(σ') - 1`. -/
theorem herbrandFun_sub_one_eq_of_mul_eq_sum_card {σ' : G'} {j : ℕ}
    (hsum : (Nat.card (ramificationGroup H B 0) : ℕ∞) * lowerIndex C σ' =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞)) :
    herbrandFun H B ((j : ℝ) - 1) = ((lowerIndex C σ').toNat : ℝ) - 1 := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lowerIndex_ne_top_of_mul_eq_sum_card hsum)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [← hn, ENat.toNat_natCast]
  rcases j with _ | m
  · rw [Nat.cast_zero, zero_sub, herbrandFun_neg_one]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast,
      div_eq_iff (by exact_mod_cast Nat.card_pos.ne')]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
        Nat.card (ramificationGroup H B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

/-- Under Serre's counting formula at finite lower indices of `σ`, `σ'` lies in `G'_{φ_H(u)}` if
and only if `σ` lies in `G_u`. -/
theorem mem_ramificationGroupReal_herbrandFun_iff_of_forall_mul_eq_sum_card
    [FaithfulSMul G B] {σ : G} {σ' : G'} (h1 : σ = 1 → σ' = 1)
    (hsum : ∀ {j : ℕ}, lowerIndex B σ = j →
      (Nat.card (ramificationGroup H B 0) : ℕ∞) * lowerIndex C σ' =
        ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞))
    (u : ℝ) :
    σ' ∈ ramificationGroupReal G' C (herbrandFun H B u) ↔ σ ∈ ramificationGroupReal G B u := by
  rcases eq_or_ne (lowerIndex B σ) ⊤ with htop | htop
  · rw [lowerIndex_eq_top_iff] at htop
    rw [h1 htop, htop]
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  have hsumj := hsum hj.symm
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_ne_top_of_mul_eq_sum_card hsumj)).symm,
    ← herbrandFun_sub_one_eq_of_mul_eq_sum_card hsumj,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm]
  exact (herbrandFun_strictMono H B).le_iff_le

/-- **Abstract Herbrand's theorem in the lower numbering.** Let `G` act faithfully on `B`, `H` be
finite acting on `B`, `π : G →* G'` be surjective, and `ι : H →* G` satisfy `π (σ * ι τ) = π σ`.
If Serre's counting formula `#H_0 · i_C(π σ) = ∑_{k < j} #H_k` holds whenever `σ` has finite
maximal lower index `j` in its `ι(H)`-coset, then `(G_u).map π = G'_{φ_H(u)}` for all `u : ℝ`. -/
theorem map_ramificationGroupReal_eq_herbrandFun_of_sum_card
    [FaithfulSMul G B] (π : G →* G') (hπ : Function.Surjective π) (ι : H →* G)
    (hπ_mul : ∀ (σ : G) (τ : H), π (σ * ι τ) = π σ)
    (hsum : ∀ (σ : G) {j : ℕ}, lowerIndex B σ = j →
      (∀ τ : H, lowerIndex B (σ * ι τ) ≤ lowerIndex B σ) →
      (Nat.card (ramificationGroup H B 0) : ℕ∞) * lowerIndex C (π σ) =
        ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞))
    (u : ℝ) :
    (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u) := by
  have hmax (σ : G) : ∃ τ₀ : H, ∀ τ : H,
      lowerIndex B (σ * ι τ₀ * ι τ) ≤ lowerIndex B (σ * ι τ₀) := by
    have : Finite ι.range := Set.finite_range ι
    obtain ⟨_, ⟨τ₀, rfl⟩, hτ₀⟩ := Subgroup.exists_mem_forall_lowerIndex_mul_le (S := B) ι.range σ
    exact ⟨τ₀, fun τ ↦ hτ₀ _ ⟨τ, rfl⟩⟩
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ₀, hτ₀⟩ := hmax σ
    rw [← hπ_mul σ τ₀, mem_ramificationGroupReal_herbrandFun_iff_of_forall_mul_eq_sum_card
      (fun h ↦ by rw [h, map_one]) (fun hj ↦ hsum _ hj hτ₀)]
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans (by simpa only [map_inv, mul_inv_cancel_right] using hτ₀ τ₀⁻¹)
  · intro hq
    obtain ⟨σ, rfl⟩ := hπ q
    obtain ⟨τ₀, hτ₀⟩ := hmax σ
    refine ⟨σ * ι τ₀, ?_, hπ_mul σ τ₀⟩
    rw [← mem_ramificationGroupReal_herbrandFun_iff_of_forall_mul_eq_sum_card
      (fun h ↦ by rw [h, map_one]) (fun hj ↦ hsum _ hj hτ₀), hπ_mul]
    exact hq

end AbstractLowerIndex

/-! ### Inertia cardinality and the faithful DVR case -/

section Faithful

/-- For a faithful finite group action on a DVR `B` with invariant DVR `A` and separable residue
extension, `#G_0` equals the ramification index of `B / A`. -/
theorem natCard_ramificationGroup_zero_eq_ramificationIdx (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [FaithfulSMul G B] :
    Nat.card (ramificationGroup G B 0) = (_root_.IsLocalRing.maximalIdeal B).ramificationIdx A := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := IsDiscreteValuationRing.faithfulSMul_of_isIntegral (R := A) (S := B)
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have := hasSeparableResidueFieldsAt_under_maximalIdeal A B
  rw [ramificationGroup_zero_eq_inertia,
    Ideal.card_inertia_eq_ramificationIdx A G (_root_.IsLocalRing.maximalIdeal B)]

/-- Herbrand's lemma in the lower numbering when `G` acts faithfully with invariant DVR `A`. -/
private theorem ramificationGroupReal_quotient_herbrandFun_eq_map_of_faithful
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [FaithfulSMul G B] (H : Subgroup G) [H.Normal] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have := Algebra.isSeparable_tower_top_of_isSeparable
    (_root_.IsLocalRing.ResidueField A)
    (_root_.IsLocalRing.ResidueField (FixedPoints.subalgebra A B H))
    (_root_.IsLocalRing.ResidueField B)
  symm
  refine map_ramificationGroupReal_eq_herbrandFun_of_sum_card (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) H.subtype (fun σ τ ↦ ?_) (fun σ _ hj hσ ↦ ?_) u
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mul_inv_rev,
      inv_mul_cancel_right]
    exact H.inv_mem τ.property
  · rw [natCard_ramificationGroup_zero_eq_ramificationIdx (FixedPoints.subalgebra A B H) B H]
    exact ramificationIdx_mul_lowerIndex_mk_eq_sum_card A H hj fun τ hτ ↦ hσ ⟨τ, hτ⟩

end Faithful

/-! ### General DVR case (arbitrary local base ring and non-faithful action) -/

section General

/-- **Herbrand's theorem in the lower numbering** for `FixedPoints.subalgebra A B H`:
`(G ⧸ H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`. Neither completeness of `B`, finiteness of the
residue field, faithfulness of the `G`-action, nor `A = B^G` is required. -/
theorem ramificationGroupReal_quotient_herbrandFun_eq_map
    (A B : Type*) [CommRing A] [_root_.IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    (H : Subgroup G) [H.Normal] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  set K := (MulSemiringAction.toRingAut G B).ker
  set A₀ := FixedPoints.subalgebra A B G
  have := Algebra.isSeparable_tower_top_of_isSeparable
    (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField A₀)
    (_root_.IsLocalRing.ResidueField B)
  set q := QuotientGroup.mk' K
  set H' := H.map q
  have : H'.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective K)
  let f : G ⧸ H →* (G ⧸ K) ⧸ H' := QuotientGroup.map H H' q (Subgroup.le_comap_map q H)
  have hq_smul : ∀ (g : G) (b : B), q g • b = g • b :=
    fun g b ↦ TauCeti.MulSemiringAction.quotientKerToRingAut_mk_smul g b
  have hH_surj : Function.Surjective (q.subgroupMap H) := by
    rintro ⟨_, g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  have hφH : herbrandFun H B u = herbrandFun H' B u :=
    herbrandFun_eq_of_surjective_ringEquiv (q.subgroupMap H) hH_surj (RingEquiv.refl B)
      (fun _ _ ↦ rfl) u
  have hQ : ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal ((G ⧸ K) ⧸ H') (FixedPoints.subalgebra A₀ B H')
        (herbrandFun H' B u)).comap f := by
    rw [hφH]
    exact ramificationGroupReal_eq_comap_of_ringEquiv f
      (TauCeti.FixedPoints.subalgebraEquivMap A A₀ hq_smul H)
      (TauCeti.FixedPoints.subalgebraEquivMap_smul hq_smul H) _
  have hG : ramificationGroupReal G B u = (ramificationGroupReal (G ⧸ K) B u).comap q :=
    ramificationGroupReal_eq_comap_of_ringEquiv q (RingEquiv.refl B)
      (fun g b ↦ (hq_smul g b).symm) u
  rw [hQ, hG, ramificationGroupReal_quotient_herbrandFun_eq_map_of_faithful A₀ B (G ⧸ K) H' u,
    Subgroup.comap_quotientGroupMap_map_mk' _ q (Subgroup.le_comap_map q H) le_rfl]

/-- Base-free form of **Herbrand's theorem in the lower numbering** on `FixedPoints.subring B H`:
`(G ⧸ H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`. -/
theorem ramificationGroupReal_quotient_subring_herbrandFun_eq_map
    (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Group G] [Finite G] [MulSemiringAction G B]
    (H : Subgroup G) [H.Normal]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)]
    (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  rw [← ramificationGroupReal_quotient_herbrandFun_eq_map (FixedPoints.subring B G) B G H u]
  simpa using (ramificationGroupReal_map_of_ringEquiv (MulEquiv.refl (G ⧸ H))
    (TauCeti.FixedPoints.subalgebraEquivSubring (FixedPoints.subring B G) B H)
    (TauCeti.FixedPoints.subalgebraEquivSubring_smul H)
    (herbrandFun H B u)).symm

end General

end TauCeti.IsLocalRing
