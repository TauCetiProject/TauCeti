/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic

import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Valuation

/-!
# Eisenstein norm families for odd-defect unit radicands

For a unit `a` of a nonarchimedean local field `K` whose quadratic defect exponent `d = 2k + 1` is
odd, an optimal square approximation `ξ²` of `a` with `v_K(a - ξ²) = 2k + 1` transforms
`p² - a q² = b` on `QuadraticAlgebra K a 0` into `X² - t X Y + c Y² = b`, where
`t = 2ξ / π^k ∈ 𝓂[K]` and `c = (ξ² - a) / π^(2k)` is irreducible in `𝒪[K]`
(`TauCeti.exists_eisenstein_coefficients_of_defectExponent_eq_odd`).

Consequently, valuation-one norms in `quadraticNormSubgroup (a : K)` have the normal form
`u² (1 - t v + c v²)`, all nonzero norms are `c ^ n * u² * (1 - t v + c v²)`, and
`TauCeti.unitQuadraticNormSquareClasses (a : K)` equals
`TauCeti.eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal`
(`TauCeti.exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem mem_quadraticNormSubgroup_unit_iff_of_eisenstein_eq {π t c : 𝒪[K]}
    (hπ : Irreducible π) {a ξ : K} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) {k : ℕ}
    (ht_eq : (t : K) = 2 * ξ / (π : K) ^ k) (hc_eq : (c : K) = (ξ ^ 2 - a) / (π : K) ^ (2 * k))
    {b : Kˣ} (hb : valuation K (b : K) = 1) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ (u : 𝒪[K]ˣ) (v : 𝒪[K]),
        (b : K) = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have ht_mul : (t : K) * (π : K) ^ k = 2 * ξ := ht_eq ▸ div_mul_cancel₀ _ (pow_ne_zero k hπ0)
  have hc_mul : (c : K) * (π : K) ^ (2 * k) = ξ ^ 2 - a :=
    hc_eq ▸ div_mul_cancel₀ _ (pow_ne_zero (2 * k) hπ0)
  have hpow2k : ((π : K) ^ k) ^ 2 = (π : K) ^ (2 * k) := by rw [← pow_mul, mul_comm]
  have hnorm : ∀ p q : K, (⟨p, q⟩ : QuadraticAlgebra K a 0).norm = p ^ 2 - a * q ^ 2 := fun p q ↦ by
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero]; ring
  rw [mem_quadraticNormSubgroup_iff_exists_norm_eq]
  constructor
  · rintro ⟨z, hz⟩
    let X : K := z.re + ξ * z.im
    let Y : K := (π : K) ^ k * z.im
    have hXY : X ^ 2 - (t : K) * X * Y + (c : K) * Y ^ 2 = (b : K) := by
      dsimp only [X, Y]
      rw [← hz, hnorm, mul_pow, hpow2k]
      linear_combination -z.im * (z.re + ξ * z.im) * ht_mul + z.im ^ 2 * hc_mul
    obtain ⟨hXv, hYv⟩ := (valuation_sq_sub_mul_add_mul_sq_eq_one_iff ht hc X Y).mp (hXY ▸ hb)
    have hX0 : X ≠ 0 := fun h0 ↦ by simp [h0] at hXv
    have hxu : IsUnit (⟨X, hXv.le⟩ : 𝒪[K]) :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hXv
    refine ⟨hxu.unit, ⟨Y / X, (Valuation.mem_integer_iff _ _).mpr
      (by simpa only [map_div₀, hXv, div_one] using hYv)⟩, ?_⟩
    rw [show ((hxu.unit : 𝒪[K]) : K) = X from congrArg ((↑) : 𝒪[K] → K) hxu.unit_spec, ← hXY]
    field_simp
  · rintro ⟨u, v, hbuv⟩
    let β : K := (u : K) * (v : K) / (π : K) ^ k
    refine ⟨⟨(u : K) - ξ * β, β⟩, ?_⟩
    rw [hnorm, hbuv]; dsimp only [β]
    calc ((u : K) - ξ * ((u : K) * (v : K) / (π : K) ^ k)) ^ 2 -
          a * ((u : K) * (v : K) / (π : K) ^ k) ^ 2
        = (u : K) ^ 2 - (2 * ξ) * (u : K) ^ 2 * (v : K) / (π : K) ^ k +
            (ξ ^ 2 - a) * (u : K) ^ 2 * (v : K) ^ 2 / ((π : K) ^ k) ^ 2 := by field_simp; ring
      _ = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
          rw [← ht_mul, ← hc_mul, hpow2k]; field_simp

private theorem mem_quadraticNormSubgroup_iff_of_eisenstein_eq {π t c : 𝒪[K]}
    (hπ : Irreducible π) {a ξ : K} (ht : t ∈ 𝓂[K]) (hc : Irreducible c) {k : ℕ}
    (ht_eq : (t : K) = 2 * ξ / (π : K) ^ k) (hc_eq : (c : K) = (ξ ^ 2 - a) / (π : K) ^ (2 * k))
    (b : Kˣ) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ (n : ℤ) (u : 𝒪[K]ˣ) (v : 𝒪[K]),
        (b : K) = (c : K) ^ n * (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hc0 : (c : K) ≠ 0 := fun h0 ↦ hc.ne_zero (Subtype.ext h0)
  let cUnit : Kˣ := Units.mk0 (c : K) hc0
  have hc_mem : cUnit ∈ quadraticNormSubgroup a := by
    rw [mem_quadraticNormSubgroup_iff_exists_norm_eq]
    refine ⟨⟨ξ / (π : K) ^ k, 1 / (π : K) ^ k⟩, ?_⟩
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero, cUnit, Units.val_mk0, hc_eq,
      show (π : K) ^ (2 * k) = ((π : K) ^ k) ^ 2 by rw [← pow_mul, mul_comm]]
    field_simp
  have hc_val : (normalizedValuation K cUnit).toAdd = 1 := by
    dsimp only [cUnit]; rw [normalizedValuation_irreducible hc, toAdd_ofAdd]
  rw [mem_quadraticNormSubgroup_iff_exists_zpow_mul_unit hc_mem hc_val]
  constructor
  · rintro ⟨n, b₀, hb₀, hb₀v, rfl⟩
    obtain ⟨u, v, hbuv⟩ :=
      (mem_quadraticNormSubgroup_unit_iff_of_eisenstein_eq hπ ht hc ht_eq hc_eq hb₀v).mp hb₀
    exact ⟨n, u, v, by rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hbuv]; ring⟩
  · rintro ⟨n, u, v, hbuv⟩
    let b₀ : Kˣ := b * cUnit ^ (-n)
    have hb₀_eq : (b₀ : K) = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
      dsimp only [b₀]
      rw [zpow_neg, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, hbuv, mul_assoc ((c : K) ^ n), mul_comm ((c : K) ^ n),
        mul_inv_cancel_right₀ (zpow_ne_zero n hc0)]
    have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    have hb₀v : valuation K (b₀ : K) = 1 := by
      rw [hb₀_eq, map_mul, map_pow, hu1, one_pow, one_mul]
      exact valuation_one_sub_mul_add_mul_sq ht hc.mem_maximalIdeal v
    exact ⟨n, b₀, (mem_quadraticNormSubgroup_unit_iff_of_eisenstein_eq hπ ht hc ht_eq hc_eq
      hb₀v).mpr ⟨u, v, hb₀_eq⟩, hb₀v, by simp [b₀, zpow_neg, mul_left_comm]⟩

/-- **Integral-basis norm parametrization for a unit radicand of odd quadratic defect**
(O'Meara §63A). For a local unit `a` of valuation `1` whose defect exponent `d` is odd, there exist
`t ∈ 𝓂[K]` and an irreducible `c ∈ 𝒪[K]` such that:
1. the norms of valuation `1` in `quadraticNormSubgroup (a : K)` are `u² (1 - t v + c v²)` with
   `u ∈ 𝒪[K]ˣ` and `v ∈ 𝒪[K]`;
2. all elements of `quadraticNormSubgroup (a : K)` are `c ^ n * u² * (1 - t v + c v²)` with
   `n ∈ ℤ`, `u ∈ 𝒪[K]ˣ`, and `v ∈ 𝒪[K]`;
3. `unitQuadraticNormSquareClasses (a : K) = eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal`.
-/
theorem exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    ∃ (t c : 𝒪[K]) (ht : t ∈ 𝓂[K]) (hc : Irreducible c),
      (∀ b : Kˣ, valuation K (b : K) = 1 →
        (b ∈ quadraticNormSubgroup (a : K) ↔
          ∃ (u : 𝒪[K]ˣ) (v : 𝒪[K]),
            (b : K) = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2))) ∧
      (∀ b : Kˣ,
        b ∈ quadraticNormSubgroup (a : K) ↔
          ∃ (n : ℤ) (u : 𝒪[K]ˣ) (v : 𝒪[K]),
            (b : K) =
              (c : K) ^ n * (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2)) ∧
      unitQuadraticNormSquareClasses (a : K) =
        eisensteinNormSquareSubgroup K ht hc.mem_maximalIdeal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hd0 : 0 ≤ d := by
    have h := toAdd_normalizedValuation_le_defectExponent a
    rwa [hd, (normalizedValuation_eq_one_iff a).mpr ha, toAdd_one, WithTop.coe_le_coe] at h
  obtain ⟨m, hm⟩ := hodd
  have hd_eq : defectExponent a = ((2 * m.toNat + 1 : ℕ) : ℤ) := by
    have := Int.toNat_of_nonneg (a := m) (by omega)
    rw [hd]; congr 1; push_cast; omega
  obtain ⟨ξ, t, c, -, ht, hc, ht_eq, hc_eq⟩ :=
    exists_eisenstein_coefficients_of_defectExponent_eq_odd hπ ha hd_eq
  have hunit_iff := fun (b : Kˣ) (hb : valuation K (b : K) = 1) ↦
    mem_quadraticNormSubgroup_unit_iff_of_eisenstein_eq hπ ht hc ht_eq hc_eq hb
  refine ⟨t, c, ht, hc, hunit_iff,
    mem_quadraticNormSubgroup_iff_of_eisenstein_eq hπ ht hc ht_eq hc_eq, Subgroup.ext fun q ↦ ?_⟩
  rw [mem_unitQuadraticNormSquareClasses_iff,
    mem_eisensteinNormSquareSubgroup_iff_of_forall ht hc.mem_maximalIdeal hunit_iff]
  exact ⟨fun ⟨b, hb, hv, hq⟩ ↦ ⟨b, hv, hb, hq⟩, fun ⟨b, hv, hb, hq⟩ ↦ ⟨b, hb, hv, hq⟩⟩

end TauCeti
