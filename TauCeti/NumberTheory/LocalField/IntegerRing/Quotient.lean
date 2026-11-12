/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Maximal-ideal power quotients of a discretely valued field

For a discretely valued field `K` and irreducible `c ∈ 𝒪[K]`, membership in `𝓂[K] ^ n` is
`valuation K x ≤ valuation K c ^ n` (`TauCeti.mem_maximalIdeal_pow_iff_valuation_le`). Left
multiplication by `r₀ ∈ 𝒪[K]` of valuation `valuation K c ^ d` shifts congruence modulo `𝓂[K] ^ M`
to `𝓂[K] ^ (d + M)` (`TauCeti.mul_sub_mem_maximalIdeal_pow_iff`) and induces an injective linear map
`TauCeti.mulLeftMaximalIdealPowQuotient`. The Artin–Schreier map `y ↦ y ^ 2 - y` is a bijection on
maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)` (`TauCeti.artinSchreierMaximalIdealQuotientEquiv`).

## References

* J.-P. Serre, *Local Fields*, Chapter I, §4 and Chapter IV, §2.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

/-- For an irreducible `c ∈ 𝒪[K]`, `x ∈ 𝓂[K] ^ n` iff `valuation K x ≤ valuation K c ^ n`. -/
theorem mem_maximalIdeal_pow_iff_valuation_le {c x : 𝒪[K]} (hc : Irreducible c) (n : ℕ) :
    x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (c : K) ^ n := by
  rw [← SetLike.mem_coe, hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) n,
    Set.mem_ofPred_eq]

/-- Multiplying by `r₀ ∈ 𝒪[K]` (`valuation K r₀ = valuation K c ^ d`) shifts congruence modulo
`𝓂[K] ^ M` to `𝓂[K] ^ N` (`N = d + M`). -/
theorem mul_sub_mem_maximalIdeal_pow_iff {c r₀ : 𝒪[K]} (hc : Irreducible c) {d M N : ℕ}
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ d) (hN : N = d + M) (s₁ s₂ : 𝒪[K]) :
    r₀ * s₁ - r₀ * s₂ ∈ 𝓂[K] ^ N ↔ s₁ - s₂ ∈ 𝓂[K] ^ M := by
  rw [mem_maximalIdeal_pow_iff_valuation_le hc N, mem_maximalIdeal_pow_iff_valuation_le hc M,
    show r₀ * s₁ - r₀ * s₂ = r₀ * (s₁ - s₂) by ring, Subring.coe_mul, map_mul, hvr₀, hN, pow_add]
  exact ⟨fun h ↦ le_of_mul_le_mul_left h (pow_pos (Valuation.integer.v_irreducible_pos hc) d),
    fun h ↦ mul_le_mul' le_rfl h⟩

/-- Left multiplication by `r₀ ∈ 𝒪[K]` (`valuation K r₀ = valuation K c ^ d`) as an `𝒪[K]`-linear
map `𝒪[K] ⧸ 𝓂[K] ^ M →ₗ[𝒪[K]] 𝒪[K] ⧸ 𝓂[K] ^ N` (`N = d + M`). -/
def mulLeftMaximalIdealPowQuotient {c r₀ : 𝒪[K]} (hc : Irreducible c) {d M N : ℕ}
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ d) (hN : N = d + M) :
    (𝒪[K] ⧸ 𝓂[K] ^ M) →ₗ[𝒪[K]] (𝒪[K] ⧸ 𝓂[K] ^ N) :=
  (𝓂[K] ^ M).mapQ (𝓂[K] ^ N) (LinearMap.mulLeft 𝒪[K] r₀) fun s hs ↦ by
    simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, sub_zero, mul_zero] using
      (mul_sub_mem_maximalIdeal_pow_iff hc hvr₀ hN s 0).mpr (by simpa only [sub_zero] using hs)

/-- Evaluating `mulLeftMaximalIdealPowQuotient` on `[s]` gives `[r₀ * s]`. -/
@[simp]
theorem mulLeftMaximalIdealPowQuotient_mk {c r₀ : 𝒪[K]} (hc : Irreducible c) {d M N : ℕ}
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ d) (hN : N = d + M) (s : 𝒪[K]) :
    mulLeftMaximalIdealPowQuotient hc hvr₀ hN (Ideal.Quotient.mk (𝓂[K] ^ M) s) =
      Ideal.Quotient.mk (𝓂[K] ^ N) (r₀ * s) := by
  rw [mulLeftMaximalIdealPowQuotient, ← Ideal.Quotient.mk_eq_mk, Submodule.mapQ_apply,
    Ideal.Quotient.mk_eq_mk, LinearMap.mulLeft_apply]

/-- `mulLeftMaximalIdealPowQuotient` is injective when `valuation K r₀ = valuation K c ^ d`. -/
theorem mulLeftMaximalIdealPowQuotient_injective {c r₀ : 𝒪[K]} (hc : Irreducible c) {d M N : ℕ}
    (hvr₀ : valuation K (r₀ : K) = valuation K (c : K) ^ d) (hN : N = d + M) :
    Function.Injective (mulLeftMaximalIdealPowQuotient hc hvr₀ hN) := fun y₁ y₂ h ↦ by
  obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
  obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
  rw [mulLeftMaximalIdealPowQuotient_mk, mulLeftMaximalIdealPowQuotient_mk, Ideal.Quotient.eq] at h
  exact Ideal.Quotient.eq.mpr ((mul_sub_mem_maximalIdeal_pow_iff hc hvr₀ hN s₁ s₂).mp h)

private theorem exists_mem_maximalIdeal_sq_sub_sub_mem_pow {b : 𝒪[K]} (hb : b ∈ 𝓂[K]) :
    ∀ m : ℕ, ∃ s ∈ 𝓂[K], s ^ 2 - s - b ∈ 𝓂[K] ^ (m + 1)
  | 0 => ⟨0, zero_mem _, by
      simpa only [zero_add, pow_one, zero_pow two_ne_zero, sub_zero, zero_sub] using neg_mem hb⟩
  | m + 1 => by
    obtain ⟨s, hs, hδ⟩ := exists_mem_maximalIdeal_sq_sub_sub_mem_pow hb m
    obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (2 * s)
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ 2 hs))
    let h : 𝒪[K] := (s ^ 2 - s - b) * ↑u⁻¹
    have hh : h ∈ 𝓂[K] ^ (m + 1) := Ideal.mul_mem_right _ _ hδ
    have hhm : h ∈ 𝓂[K] := Ideal.pow_le_self (Nat.succ_ne_zero m) hh
    refine ⟨s + h, add_mem hs hhm, ?_⟩
    have hu' : (1 - 2 * s) * h = s ^ 2 - s - b := by
      dsimp only [h]; rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
    rw [show (s + h) ^ 2 - (s + h) - b = (s ^ 2 - s - b) - (1 - 2 * s) * h + h * h by ring,
      hu', sub_self, zero_add, pow_succ]
    exact Ideal.mul_mem_mul hh hhm

/-- On the maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)`, the Artin–Schreier polynomial
`y ↦ y ^ 2 - y` is a bijection. -/
def artinSchreierMaximalIdealQuotientEquiv (K : Type*) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing 𝒪[K]] (m : ℕ) :
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} ≃
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} :=
  Equiv.ofBijective
    (fun x ↦ ⟨x.1 ^ 2 - x.1, by rw [map_sub, map_pow, x.2, zero_pow two_ne_zero, sub_self]⟩)
    (show Function.Bijective _ from ⟨fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ h ↦ by
      obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      have hmem : (s₁ - s₂) * (s₁ + s₂ - 1) ∈ 𝓂[K] ^ (m + 1) := by
        simpa only [show (s₁ - s₂) * (s₁ + s₂ - 1) = (s₁ ^ 2 - s₁) - (s₂ ^ 2 - s₂) by ring] using
          Ideal.Quotient.eq.mp (by simpa [← map_pow, ← map_sub] using congrArg Subtype.val h)
      have hw : IsUnit (s₁ + s₂ - 1) := by
        simpa only [neg_sub] using (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (s₁ + s₂)
          ((IsLocalRing.mem_maximalIdeal _).mp (add_mem
            (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy₁))
            (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy₂))))).neg
      exact Subtype.ext
        (Ideal.Quotient.eq.mpr (((𝓂[K] ^ (m + 1)).mul_unit_mem_iff_mem hw).mp hmem)),
    fun ⟨y, hy⟩ ↦ by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hb : b ∈ 𝓂[K] := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy)
      obtain ⟨s, hs, hmem⟩ := exists_mem_maximalIdeal_sq_sub_sub_mem_pow hb m
      refine ⟨⟨Ideal.Quotient.mk _ s, ?_⟩, Subtype.ext ?_⟩
      · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hs
      · simpa only [← map_pow, ← map_sub] using Ideal.Quotient.eq.mpr hmem⟩)

/-- Evaluating `artinSchreierMaximalIdealQuotientEquiv` applies `y ↦ y ^ 2 - y`. -/
@[simp]
theorem coe_artinSchreierMaximalIdealQuotientEquiv_apply (m : ℕ)
    (x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0}) :
    (artinSchreierMaximalIdealQuotientEquiv K m x : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1)) = x.1 ^ 2 - x.1 := by
  rw [artinSchreierMaximalIdealQuotientEquiv, Equiv.coe_ofBijective]

end TauCeti
