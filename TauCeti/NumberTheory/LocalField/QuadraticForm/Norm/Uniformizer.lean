/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.Uniformizer

/-!
# Quadratic norms of a uniformizer

For a uniformizer `a`, the unit norms from `K(√a)` are exactly `u² (1 - a t²)` with
`u` a unit of the ring of integers and `t` integral. More generally every nonzero norm is
such a unit norm times an integer power of `-a`. This reduces the norm-index calculation
for a radicand of valuation one to the unit values of a binary quadratic form, including
in residue characteristic two.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For an odd-valuation radicand, the terms in a quadratic norm cannot cancel in valuation. -/
theorem valuation_sq_sub_mul_sq_of_odd {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) (x y : K) :
    valuation K (x ^ 2 - (a : K) * y ^ 2) =
      max (valuation K (x ^ 2)) (valuation K ((a : K) * y ^ 2)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hne : valuation K (x ^ 2) ≠ valuation K ((a : K) * y ^ 2) := by
    intro h
    let u := Units.mk0 x hx
    let v := Units.mk0 y hy
    have heq : (normalizedValuation K (u ^ 2)).toAdd =
        (normalizedValuation K (a * v ^ 2)).toAdd := by
      apply le_antisymm
      · exact (toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr h.ge
      · exact (toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr h.le
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul] at heq
    obtain ⟨n, hn⟩ := ha
    omega
  rcases hne.lt_or_gt with h | h
  · rw [(valuation K).map_sub_eq_of_lt_right h, max_eq_right h.le]
  · rw [(valuation K).map_sub_eq_of_lt_left h, max_eq_left h.le]

/-- A norm for a uniformizer radicand has valuation zero exactly when its first coordinate
is a local unit and its second coordinate is integral. -/
theorem valuation_sq_sub_mul_sq_eq_one_iff {a : Kˣ} (ha : IsUniformizer K a) (x y : K) :
    valuation K (x ^ 2 - (a : K) * y ^ 2) = 1 ↔
      valuation K x = 1 ∧ valuation K y ≤ 1 := by
  have ha' := (isUniformizer_def a).mp ha
  have haodd : Odd (normalizedValuation K a).toAdd := by simp [ha']
  have halt : valuation K (a : K) < 1 := by
    obtain ⟨π, hπ, hπa⟩ := (isUniformizer_iff_exists_irreducible K a).mp ha
    rw [← hπa]
    exact Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  rw [valuation_sq_sub_mul_sq_of_odd haodd]
  constructor
  · intro h
    have hy1 : valuation K y ≤ 1 := by
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have hv : 0 ≤ (normalizedValuation K (a * Units.mk0 y hy ^ 2)).toAdd := by
        apply (mem_integer_iff_toAdd_normalizedValuation_nonneg _).mp
        exact (Valuation.mem_integer_iff _ _).mpr ((le_max_right _ _).trans h.le)
      simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, ha', toAdd_ofAdd] at hv
      exact (Valuation.mem_integer_iff _ _).mp
        ((mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 y hy)).mpr (by omega))
    have hay : valuation K ((a : K) * y ^ 2) < 1 := by
      rw [map_mul, map_pow]
      exact (mul_le_mul' le_rfl (pow_le_one₀ zero_le hy1)).trans_lt (by simpa using halt)
    have hx2 : valuation K (x ^ 2) = 1 := ((max_eq_iff.mp h).resolve_right (fun h ↦ hay.ne h.1)).1
    exact ⟨by simpa only [map_pow, pow_eq_one_iff_left (by decide : 2 ≠ 0)] using hx2, hy1⟩
  · rintro ⟨hx, hy⟩
    rw [map_pow, hx, one_pow, max_eq_left]
    rw [map_mul, map_pow]
    exact (mul_le_mul' halt.le (pow_le_one₀ zero_le hy)).trans (by simp)

/-- A local unit is a norm for a uniformizer radicand exactly when it has the form
`u² (1 - a t²)`, with `u` an integral unit and `t` integral. -/
theorem mem_quadraticNormSubgroup_iff_of_isUniformizer {a b : Kˣ}
    (ha : IsUniformizer K a) (hb : valuation K (b : K) = 1) :
    b ∈ quadraticNormSubgroup (a : K) ↔
      ∃ (u : 𝒪[K]ˣ) (t : 𝒪[K]), (b : K) = (u : K) ^ 2 * (1 - (a : K) * (t : K) ^ 2) := by
  rw [mem_quadraticNormSubgroup_iff_exists_norm_eq]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.re ^ 2 - (a : K) * z.im ^ 2 = b := by
      simpa [QuadraticAlgebra.norm_def, sq, mul_assoc] using hz
    obtain ⟨hx, hy⟩ := (valuation_sq_sub_mul_sq_eq_one_iff ha z.re z.im).mp (hz' ▸ hb)
    let x : 𝒪[K] := ⟨z.re, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
    have hxu : IsUnit x := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr hx
    have hx0 : z.re ≠ 0 := by intro h; simp [h] at hx
    let t : 𝒪[K] := ⟨z.im / z.re, (Valuation.mem_integer_iff _ _).mpr
      (by simpa [map_div₀, hx] using hy)⟩
    refine ⟨hxu.unit, t, ?_⟩
    simp only [IsUnit.unit_spec, x, t]
    rw [← hz']
    field_simp
  · rintro ⟨u, t, hb⟩
    refine ⟨⟨(u : K), (u : K) * (t : K)⟩, ?_⟩
    simp only [QuadraticAlgebra.norm_def, hb]
    ring

/-- Every nonzero norm for a uniformizer radicand is an integer power of `-a` times
`u² (1 - a t²)`, and every such element is a norm. -/
theorem mem_quadraticNormSubgroup_iff_exists_zpow_mul {a b : Kˣ}
    (ha : IsUniformizer K a) :
    b ∈ quadraticNormSubgroup (a : K) ↔
      ∃ (n : ℤ) (u : 𝒪[K]ˣ) (t : 𝒪[K]),
        (b : K) = (-(a : K)) ^ n * (u : K) ^ 2 * (1 - (a : K) * (t : K) ^ 2) := by
  have hpow (n : ℤ) : (-a) ^ n ∈ quadraticNormSubgroup (a : K) :=
    (quadraticNormSubgroup _).zpow_mem (neg_radicand_mem_quadraticNormSubgroup a) n
  constructor
  · intro hb
    let n : ℤ := (normalizedValuation K b).toAdd
    let c : Kˣ := b * (-a) ^ (-n)
    have hc : c ∈ quadraticNormSubgroup (a : K) :=
      (quadraticNormSubgroup _).mul_mem hb (hpow (-n))
    have hcv : valuation K (c : K) = 1 := by
      apply (normalizedValuation_eq_one_iff c).mp
      apply Multiplicative.toAdd.injective
      simp [c, n, map_zpow, (isUniformizer_def a).mp ha]
    obtain ⟨u, t, hct⟩ := (mem_quadraticNormSubgroup_iff_of_isUniformizer ha hcv).mp hc
    refine ⟨n, u, t, ?_⟩
    have hb' : b = (-a) ^ n * c := by simp [c, zpow_neg, mul_left_comm]
    rw [hb']
    push_cast
    rw [hct]
    ring
  · rintro ⟨n, u, t, hb⟩
    let c : Kˣ := b * (-a) ^ (-n)
    have hcval : (c : K) = (u : K) ^ 2 * (1 - (a : K) * (t : K) ^ 2) := by
      dsimp [c]
      push_cast
      rw [hb, zpow_neg]
      field_simp
    have hc : c ∈ quadraticNormSubgroup (a : K) := by
      apply (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr
      refine ⟨⟨(u : K), (u : K) * (t : K)⟩, ?_⟩
      rw [hcval]
      simp only [QuadraticAlgebra.norm_def]
      ring
    have hb' : b = (-a) ^ n * c := by simp [c, zpow_neg, mul_left_comm]
    rw [hb']
    exact (quadraticNormSubgroup _).mul_mem (hpow n) hc

end TauCeti
