/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Count

import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Eisenstein norm families and unit-norm square-class counts for odd-defect unit radicands

For a unit `a` of a nonarchimedean local field `K` whose quadratic defect exponent `d = 2k + 1` is
odd, an optimal square approximation `ξ²` of `a` with `v_K(a - ξ²) = 2k + 1` transforms the norm
equation `p² - a q² = b` on `QuadraticAlgebra K a 0` into the Eisenstein norm form
`X² - t X Y + c Y² = b`, where `t = 2ξ / π^k ∈ 𝓂[K]` and `c = (ξ² - a) / π^(2k)` is irreducible in
`𝒪[K]`.

Consequently, the norms of valuation one in `quadraticNormSubgroup (a : K)` have the integral normal
form `u² (1 - t v + c v²)`, every nonzero norm is `c ^ n * u² * (1 - t v + c v²)`, and
`TauCeti.unitQuadraticNormSquareClasses (a : K)` coincides with
`TauCeti.eisensteinNormSquareSubgroup K ht hc`. Combining this identification with
`TauCeti.natCard_eisensteinNormSquareSubgroup` yields the unit-norm square-class count
`#𝓀[K] ^ natCastValuation K 2 h2` and relative index `2` inside `TauCeti.unitSquareClasses K`.

## Main results

* `TauCeti.exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd`: Eisenstein
  parametrization of valuation-one norms, all nonzero norms, and `unitQuadraticNormSquareClasses`
  for a unit radicand of odd quadratic defect.
* `TauCeti.natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent`: for `2 ≠ 0` and an
  odd-defect unit `a`, `unitQuadraticNormSquareClasses (a : K)` has cardinality
  `#𝓀[K] ^ natCastValuation K 2 h2`.
* `TauCeti.relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent`: for `2 ≠ 0` and an
  odd-defect unit `a`, `unitQuadraticNormSquareClasses (a : K)` has index `2` inside
  `unitSquareClasses K`.

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

/-- **Integral-basis norm parametrization for a unit radicand of odd quadratic defect**
(O'Meara §63A). For a local unit `a` of valuation `1` whose defect exponent `d` is odd, there exist
`t ∈ 𝓂[K]` and an irreducible `c ∈ 𝒪[K]` such that:
1. the norms of valuation `1` in `quadraticNormSubgroup (a : K)` are `u² (1 - t v + c v²)` with
   `u ∈ 𝒪[K]ˣ` and `v ∈ 𝒪[K]`;
2. all elements of `quadraticNormSubgroup (a : K)` are `c ^ n * u² * (1 - t v + c v²)` with
   `n ∈ ℤ`, `u ∈ 𝒪[K]ˣ`, and `v ∈ 𝒪[K]`;
3. `unitQuadraticNormSquareClasses (a : K) = eisensteinNormSquareSubgroup K ht hc`. -/
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
      unitQuadraticNormSquareClasses (a : K) = eisensteinNormSquareSubgroup K ht hc := by
  have hnsq : ¬IsSquare a := not_isSquare_of_defectExponent_eq hd
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hπpos : 0 < valuation K (π : K) := Valuation.integer.v_irreducible_pos (v := valuation K) hπ
  -- Step 1: Write the odd defect exponent `d ≥ 0` as `2k + 1` and choose an attained `ξ²`.
  have hd0 : 0 ≤ d := by
    have h := toAdd_normalizedValuation_le_defectExponent a
    rwa [hd, (normalizedValuation_eq_one_iff a).mpr ha, toAdd_one, WithTop.coe_le_coe] at h
  obtain ⟨m, hm⟩ := hodd
  let k : ℕ := m.toNat
  have hk_eq : (k : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hd_eq : d = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; omega
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hnsq
  have hxadd : (normalizedValuation K x).toAdd = ((2 * k + 1 : ℕ) : ℤ) :=
    WithTop.coe_inj.mp (hxd.trans (hd.trans (congrArg WithTop.some hd_eq)))
  have hxv : valuation K (x : K) = valuation K (π : K) ^ (2 * k + 1) := by
    simpa only [Units.val_mk0, zpow_natCast] using
      (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
        (normalizedValuation_irreducible hπ) _ x).mp hxadd
  have hξv : valuation K ξ = 1 := by
    have hxlta : valuation K (x : K) < valuation K (a : K) :=
      ha ▸ hxv ▸ pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero _)
    have hξ_sub : ξ ^ 2 = (a : K) - (x : K) := by rw [hx]; ring
    have hξ2 : valuation K (ξ ^ 2) = 1 := by
      rw [hξ_sub, (valuation K).map_sub_eq_of_lt_left hxlta, ha]
    simpa only [map_pow, pow_eq_one_iff_left (by decide : 2 ≠ 0)] using hξ2
  -- Step 2: Construct `c = (ξ² - a) / π^(2k)` (irreducible) and `t = 2ξ / π^k ∈ 𝓂[K]`.
  have hcv : valuation K ((ξ ^ 2 - (a : K)) / (π : K) ^ (2 * k)) = valuation K (π : K) := by
    rw [map_div₀, ← neg_sub, Valuation.map_neg, ← hx, hxv, map_pow, pow_succ,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hπpos.ne')]
  let c : 𝒪[K] := ⟨(ξ ^ 2 - (a : K)) / (π : K) ^ (2 * k), hcv ▸ hπ1.le⟩
  have hc : Irreducible c := irreducible_of_valuation_eq hπ hcv
  have htv : valuation K (2 * ξ / (π : K) ^ k) < 1 := by
    by_cases h2 : (2 : K) = 0
    · simp [h2]
    · have hklt : k < natCastValuation K 2 h2 := by
        have h := defectExponent_le_two_mul_natCastValuation h2 ha hnsq
        rw [hd, hd_eq, WithTop.coe_le_coe, Nat.cast_le] at h
        omega
      have hv2 : valuation K (2 : K) = valuation K (π : K) ^ natCastValuation K 2 h2 := by
        simpa only [Nat.cast_ofNat] using valuation_natCast_eq_pow hπ 2 h2
      rw [map_div₀, map_mul, hv2, hξv, mul_one, map_pow, div_lt_one₀ (pow_pos hπpos k)]
      exact pow_lt_pow_right_of_lt_one₀ hπpos hπ1 hklt
  let t : 𝒪[K] := ⟨2 * ξ / (π : K) ^ k, htv.le⟩
  have ht : t ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.mpr htv
  have hπk0 : (π : K) ^ k ≠ 0 := pow_ne_zero k hπ0
  have hπ2k0 : (π : K) ^ (2 * k) ≠ 0 := pow_ne_zero (2 * k) hπ0
  have ht_mul : (t : K) * (π : K) ^ k = 2 * ξ := div_mul_cancel₀ _ hπk0
  have hc_mul : (c : K) * (π : K) ^ (2 * k) = ξ ^ 2 - (a : K) := div_mul_cancel₀ _ hπ2k0
  have hnorm : ∀ p q : K, (⟨p, q⟩ : QuadraticAlgebra K (a : K) 0).norm = p ^ 2 - (a : K) * q ^ 2 :=
    fun p q ↦ by
      simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero]
      ring
  have hpow2k : ((π : K) ^ k) ^ 2 = (π : K) ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  -- Step 3: Characterize the norms of valuation `1` as `u² (1 - t v + c v²)`.
  have hunit_iff : ∀ b : Kˣ, valuation K (b : K) = 1 →
      (b ∈ quadraticNormSubgroup (a : K) ↔
        ∃ (u : 𝒪[K]ˣ) (v : 𝒪[K]),
          (b : K) = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2)) := by
    intro b hb
    rw [mem_quadraticNormSubgroup_iff_exists_norm_eq]
    constructor
    · rintro ⟨z, hz⟩
      have hz' : z.re ^ 2 - (a : K) * z.im ^ 2 = (b : K) := by
        rw [← hnorm z.re z.im]
        exact hz
      let X : K := z.re + ξ * z.im
      let Y : K := (π : K) ^ k * z.im
      have hY2 : Y ^ 2 = (π : K) ^ (2 * k) * z.im ^ 2 := by
        dsimp only [Y]
        rw [mul_pow, hpow2k]
      have hXY : X ^ 2 - (t : K) * X * Y + (c : K) * Y ^ 2 = (b : K) := by
        calc X ^ 2 - (t : K) * X * Y + (c : K) * Y ^ 2
            = (z.re + ξ * z.im) ^ 2 - ((t : K) * (π : K) ^ k) * (z.re + ξ * z.im) * z.im +
                ((c : K) * (π : K) ^ (2 * k)) * z.im ^ 2 := by
              rw [hY2]
              dsimp only [X, Y]
              ring
          _ = z.re ^ 2 - (a : K) * z.im ^ 2 := by rw [ht_mul, hc_mul]; ring
          _ = (b : K) := hz'
      obtain ⟨hXv, hYv⟩ := (valuation_sq_sub_mul_add_mul_sq_eq_one_iff ht hc X Y).mp (hXY ▸ hb)
      have hX0 : X ≠ 0 := by intro h0; simp [h0] at hXv
      let xInt : 𝒪[K] := ⟨X, hXv.le⟩
      have hxu : IsUnit xInt :=
        (Valuation.integer.integers (valuation K)).isUnit_of_one' hXv
      let v : 𝒪[K] := ⟨Y / X,
        (Valuation.mem_integer_iff _ _).mpr (by simpa only [map_div₀, hXv, div_one] using hYv)⟩
      refine ⟨hxu.unit, v, ?_⟩
      have huK : ((hxu.unit : 𝒪[K]) : K) = X := congrArg ((↑) : 𝒪[K] → K) hxu.unit_spec
      rw [huK, ← hXY]
      dsimp only [v]
      field_simp
    · rintro ⟨u, v, hbuv⟩
      let β : K := ((u : K) * (v : K)) / (π : K) ^ k
      let α : K := (u : K) - ξ * β
      refine ⟨⟨α, β⟩, ?_⟩
      rw [hnorm, hbuv]
      dsimp only [α, β]
      calc ((u : K) - ξ * ((u : K) * (v : K) / (π : K) ^ k)) ^ 2 -
            (a : K) * ((u : K) * (v : K) / (π : K) ^ k) ^ 2
          = (u : K) ^ 2 - (2 * ξ) * (u : K) ^ 2 * (v : K) / (π : K) ^ k +
              (ξ ^ 2 - (a : K)) * (u : K) ^ 2 * (v : K) ^ 2 / ((π : K) ^ k) ^ 2 := by
            field_simp; ring
        _ = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
            rw [← ht_mul, ← hc_mul, hpow2k]
            field_simp
  -- Step 4: Scale by powers of the norm uniformizer `c` to describe all nonzero norms.
  have hc0 : (c : K) ≠ 0 := fun h0 ↦ hc.ne_zero (Subtype.ext h0)
  let cUnit : Kˣ := Units.mk0 (c : K) hc0
  have hc_mem : cUnit ∈ quadraticNormSubgroup (a : K) := by
    rw [mem_quadraticNormSubgroup_iff_exists_norm_eq]
    refine ⟨⟨ξ / (π : K) ^ k, 1 / (π : K) ^ k⟩, ?_⟩
    rw [hnorm]
    simp only [cUnit, Units.val_mk0, c]
    rw [← hpow2k]
    field_simp
  have hc_val : (normalizedValuation K cUnit).toAdd = 1 := by
    dsimp only [cUnit]
    rw [normalizedValuation_irreducible hc, toAdd_ofAdd]
  have hall_iff : ∀ b : Kˣ,
      b ∈ quadraticNormSubgroup (a : K) ↔
        ∃ (n : ℤ) (u : 𝒪[K]ˣ) (v : 𝒪[K]),
          (b : K) =
            (c : K) ^ n * (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
    intro b
    constructor
    · intro hb
      let n : ℤ := (normalizedValuation K b).toAdd
      let b₀ : Kˣ := b * cUnit ^ (-n)
      have hb₀_mem : b₀ ∈ quadraticNormSubgroup (a : K) :=
        (quadraticNormSubgroup _).mul_mem hb ((quadraticNormSubgroup _).zpow_mem hc_mem (-n))
      have hb₀_val : valuation K (b₀ : K) = 1 := by
        apply (normalizedValuation_eq_one_iff b₀).mp
        apply Multiplicative.toAdd.injective
        simp [b₀, n, map_zpow, hc_val]
      obtain ⟨u, v, hbuv⟩ := (hunit_iff b₀ hb₀_val).mp hb₀_mem
      refine ⟨n, u, v, ?_⟩
      have hb_eq : b = cUnit ^ n * b₀ := by simp [b₀, zpow_neg, mul_left_comm]
      rw [hb_eq, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hbuv, mul_assoc]
    · rintro ⟨n, u, v, hbuv⟩
      let b₀ : Kˣ := b * cUnit ^ (-n)
      have hb₀_inv : b₀ = b * (cUnit ^ n)⁻¹ := by simp [b₀, zpow_neg]
      have hb₀_eq : (b₀ : K) = (u : K) ^ 2 * (1 - (t : K) * (v : K) + (c : K) * (v : K) ^ 2) := by
        rw [hb₀_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
          Units.val_mk0, hbuv]
        field_simp
      have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
        (Valuation.integer.integers (valuation K)).valuation_unit u
      have hb₀_val : valuation K (b₀ : K) = 1 := by
        rw [hb₀_eq, map_mul, map_pow, hu1, one_pow, one_mul]
        exact valuation_one_sub_mul_add_mul_sq ht
          ((IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit) v
      have hb₀_mem : b₀ ∈ quadraticNormSubgroup (a : K) :=
        (hunit_iff b₀ hb₀_val).mpr ⟨u, v, hb₀_eq⟩
      have hb_eq : b = cUnit ^ n * b₀ := by simp [b₀, zpow_neg, mul_left_comm]
      rw [hb_eq]
      exact (quadraticNormSubgroup _).mul_mem
        ((quadraticNormSubgroup _).zpow_mem hc_mem n) hb₀_mem
  -- Step 5: Deduce `unitQuadraticNormSquareClasses (a : K) = eisensteinNormSquareSubgroup K ht hc`.
  have hsub_eq : unitQuadraticNormSquareClasses (a : K) = eisensteinNormSquareSubgroup K ht hc := by
    ext q
    rw [mem_unitQuadraticNormSquareClasses_iff, mem_eisensteinNormSquareSubgroup_iff]
    constructor
    · rintro ⟨b, hb_mem, hb_val, rfl⟩
      obtain ⟨u, v, hbuv⟩ := (hunit_iff b hb_val).mp hb_mem
      refine ⟨v, ?_⟩
      let uK : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u
      have hbu : b = uK ^ 2 * eisensteinNormUnit K ht hc v := by
        ext
        simpa only [Units.val_mul, Units.val_pow_eq_pow_val, uK, Units.coe_map,
          MonoidHom.coe_ofClass, Subring.coe_subtype, coe_eisensteinNormUnit] using hbuv
      rw [hbu, map_mul, (squareClassHom_eq_one_iff _).mpr ⟨uK, sq uK⟩, one_mul,
        eisensteinNormSquareClass_def]
    · rintro ⟨v, rfl⟩
      refine ⟨eisensteinNormUnit K ht hc v, ?_, valuation_eisensteinNormUnit ht hc v,
        (eisensteinNormSquareClass_def ht hc v).symm⟩
      exact (hunit_iff _ (valuation_eisensteinNormUnit ht hc v)).mpr
        ⟨1, v, by simp [coe_eisensteinNormUnit]⟩
  exact ⟨t, c, ht, hc, hunit_iff, hall_iff, hsub_eq⟩

/-- **Unit-norm square-class count for an odd-defect unit radicand.** Over a nonarchimedean local
field with `2 ≠ 0`, a unit `a` of valuation `1` and odd quadratic defect has
`#𝓀[K] ^ natCastValuation K 2 h2` unit-norm square classes. -/
theorem natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨t, c, ht, hc, -, -, heq⟩ :=
    exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd ha hd hodd
  rw [heq, natCard_eisensteinNormSquareSubgroup h2 ht hc]

/-- **Index of unit-norm square classes inside `unitSquareClasses K`.** Over a nonarchimedean local
field with `2 ≠ 0`, for a unit `a` of valuation `1` and odd quadratic defect,
`unitQuadraticNormSquareClasses (a : K)` has index `2` inside `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 := by
  obtain ⟨t, c, ht, hc, -, -, heq⟩ :=
    exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd ha hd hodd
  rw [heq, relIndex_eisensteinNormSquareSubgroup h2 ht hc]

end TauCeti
