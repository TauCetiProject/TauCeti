/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# Multi-step quotients of the unit filtration via scaled maximal-ideal classes

Given an irreducible element `c ∈ 𝒪[K]` of a nonarchimedean local field `K` and a scaling factor
`β ∈ 𝒪[K]` with `valuation K β = valuation K c ^ n`, sending `s ∈ 𝓂[K]` to `1 + β s` produces a
unit in `U(K, n + 1)` (`TauCeti.mkScaledUnit`, `TauCeti.coe_mkScaledUnit`) and induces a bijection
between the maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)` and the multi-step quotient
`U(K, n + 1) ⧸ U(K, n + m + 1)` (`TauCeti.maximalIdealQuotientEquivUnitFiltrationQuotient`,
`TauCeti.maximalIdealQuotientEquivUnitFiltrationQuotient_mk`).

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `v(β) = v(c)^n`, `n₁ = n + 1`, and `s ∈ 𝓂[K]`, the unit `1 + β s` lies in `U(K, n₁)`. -/
def mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) : unitFiltration K n₁ :=
  have hle : valuation K ((β : K) * (s : K)) ≤ valuation K (c : K) ^ (n + 1) := by
    rw [map_mul, hvβ, pow_succ]
    exact mul_le_mul' le_rfl
      ((Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) s).mp hs)
  ⟨Units.mk0 (1 + (β : K) * (s : K)) fun h0 ↦ by
      have hlt := hle.trans_lt
        (pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hc) (by omega))
      simpa [h0] using (valuation K).map_one_add_of_lt hlt,
    (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mpr
      (by simpa only [Units.val_mk0, add_sub_cancel_left, hn₁] using hle)⟩

/-- Coercing `mkScaledUnit hc hvβ hn₁ hs` to `K` gives `1 + β s`. -/
@[simp]
theorem coe_mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) :
    (((mkScaledUnit hc hvβ hn₁ hs : unitFiltration K n₁) : Kˣ) : K) = 1 + (β : K) * (s : K) := by
  simp only [mkScaledUnit, Units.val_mk0]

private def scaledElemOfUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (u : unitFiltration K n₁) : 𝒪[K] :=
  ⟨(((u : Kˣ) : K) - 1) / (β : K), by
    have hu := (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mp u.2
    rw [Valuation.mem_integer_iff, map_div₀, hvβ]
    refine ((div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n)).mpr ?_).trans
      (Valuation.integer.v_irreducible_lt_one hc).le
    rwa [mul_comm, ← pow_succ, ← hn₁]⟩

private theorem coe_scaledElemOfUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (u : unitFiltration K n₁) :
    (scaledElemOfUnit hc hvβ hn₁ u : K) = (((u : Kˣ) : K) - 1) / (β : K) := by
  simp only [scaledElemOfUnit]

private theorem scaledElemOfUnit_mem_maximalIdeal {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (u : unitFiltration K n₁) : scaledElemOfUnit hc hvβ hn₁ u ∈ 𝓂[K] := by
  rw [← SetLike.mem_coe, hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K), Set.mem_ofPred_eq,
    coe_scaledElemOfUnit, map_div₀, hvβ,
    div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n), mul_comm, ← pow_succ, ← hn₁]
  exact (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mp u.2

private theorem scaledElemOfUnit_mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) :
    scaledElemOfUnit hc hvβ hn₁ (mkScaledUnit hc hvβ hn₁ hs) = s := by
  have hβ0 : (β : K) ≠ 0 := (Valuation.pos_iff _).mp
    (hvβ ▸ pow_pos (Valuation.integer.v_irreducible_pos hc) n)
  ext
  rw [coe_scaledElemOfUnit, coe_mkScaledUnit, add_sub_cancel_left, mul_div_cancel_left₀ _ hβ0]

private theorem scaledElemOfUnit_sub_mem_iff {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ n₂ m : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (hn₂ : n₂ = n + m + 1) (u₁ u₂ : unitFiltration K n₁) :
    scaledElemOfUnit hc hvβ hn₁ u₁ - scaledElemOfUnit hc hvβ hn₁ u₂ ∈ 𝓂[K] ^ (m + 1) ↔
      u₁⁻¹ * u₂ ∈ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) := by
  have hu₁ : valuation K ((u₁ : Kˣ) : K) = 1 :=
    (mem_unitFiltration_zero _).mp (unitFiltration_antitone (Nat.zero_le _) u₁.2)
  rw [← SetLike.mem_coe,
    Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) (m + 1)) _,
    Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc]
  have hid : ((scaledElemOfUnit hc hvβ hn₁ u₁ - scaledElemOfUnit hc hvβ hn₁ u₂ : 𝒪[K]) : K) =
      -((u₁ : Kˣ) : K) * ((((u₁ : Kˣ)⁻¹ * (u₂ : Kˣ) : Kˣ) : K) - 1) / (β : K) := by
    have : ((u₁ : Kˣ) : K) ≠ 0 := (u₁ : Kˣ).ne_zero
    push_cast; rw [coe_scaledElemOfUnit, coe_scaledElemOfUnit]; field_simp; ring
  rw [hid, map_div₀, map_mul, Valuation.map_neg, hu₁, one_mul, hvβ,
    div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n), ← pow_add,
    show m + 1 + n = n₂ by omega]

/-- When `v(β) = v(c)^n`, `n₁ = n + 1`, and `n₂ = n + m + 1`, the map `[s] ↦ [1 + β s]` is a
bijection between the maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)` and
`U(K, n₁) ⧸ U(K, n₂)`. -/
def maximalIdealQuotientEquivUnitFiltrationQuotient {c β : 𝒪[K]} (hc : Irreducible c)
    {n n₁ n₂ : ℕ} (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (m : ℕ)
    (hn₁ : n₁ = n + 1) (hn₂ : n₂ = n + m + 1) :
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} ≃
    unitFiltration K n₁ ⧸ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) := by
  let invMap : unitFiltration K n₁ ⧸ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) →
      {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} :=
    Quotient.lift
      (fun u ↦ ⟨Ideal.Quotient.mk _ (scaledElemOfUnit hc hvβ hn₁ u), by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact scaledElemOfUnit_mem_maximalIdeal hc hvβ hn₁ u⟩)
      fun u₁ u₂ h ↦ Subtype.ext <| Ideal.Quotient.eq.mpr <|
        (scaledElemOfUnit_sub_mem_iff hc hvβ hn₁ hn₂ u₁ u₂).mpr (QuotientGroup.leftRel_apply.mp h)
  refine (Equiv.ofBijective invMap ⟨fun q₁ q₂ h ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩).symm
  · obtain ⟨u₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨u₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.mpr ((scaledElemOfUnit_sub_mem_iff hc hvβ hn₁ hn₂ u₁ u₂).mp
      (Ideal.Quotient.eq.mp (congrArg Subtype.val h)))
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs : s ∈ 𝓂[K] := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy)
    exact ⟨QuotientGroup.mk (mkScaledUnit hc hvβ hn₁ hs),
      Subtype.ext (congrArg (Ideal.Quotient.mk _) (scaledElemOfUnit_mkScaledUnit hc hvβ hn₁ hs))⟩

/-- `maximalIdealQuotientEquivUnitFiltrationQuotient` sends the class of `s ∈ 𝓂[K]` to the coset
of `mkScaledUnit hc hvβ hn₁ hs`. -/
theorem maximalIdealQuotientEquivUnitFiltrationQuotient_mk {c β : 𝒪[K]} (hc : Irreducible c)
    {n n₁ n₂ : ℕ} (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (m : ℕ)
    (hn₁ : n₁ = n + 1) (hn₂ : n₂ = n + m + 1) {s : 𝒪[K]} (hs : s ∈ 𝓂[K])
    (hs0 : Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m))
      (Ideal.Quotient.mk (𝓂[K] ^ (m + 1)) s) = 0) :
    maximalIdealQuotientEquivUnitFiltrationQuotient hc hvβ m hn₁ hn₂
        ⟨Ideal.Quotient.mk (𝓂[K] ^ (m + 1)) s, hs0⟩ =
      QuotientGroup.mk (mkScaledUnit hc hvβ hn₁ hs) := by
  unfold maximalIdealQuotientEquivUnitFiltrationQuotient
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext
    (congrArg (Ideal.Quotient.mk _) (scaledElemOfUnit_mkScaledUnit hc hvβ hn₁ hs).symm)

end TauCeti
