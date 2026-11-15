/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.Uniformizer

import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.Basic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Valuation

/-!
# Quadratic norms of a uniformizer

For a uniformizer `a`, the unit norms from `K(√a)` are exactly `u² (1 - a t²)` with
`u` a unit of the ring of integers and `t` integral. More generally every nonzero norm is
such a unit norm times an integer power of `-a`, via the general norm-uniformizer scaling lemma
`TauCeti.mem_quadraticNormSubgroup_iff_exists_zpow_mul_unit`. This reduces the norm-index
calculation for a radicand of valuation one to the unit values of a binary quadratic form,
including in residue characteristic two.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

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
        (normalizedValuation K (a * v ^ 2)).toAdd :=
      (toAdd_normalizedValuation_eq_iff_valuation_eq _ _).mpr (by simpa [u, v] using h)
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
  obtain ⟨π, hπ, hπa⟩ := (isUniformizer_iff_exists_irreducible K a).mp ha
  have h := valuation_sq_sub_mul_add_mul_sq_eq_one_iff (zero_mem 𝓂[K])
    (irreducible_of_valuation_eq (c := -π) hπ (by simp)) x y
  rwa [show x ^ 2 - ((0 : 𝒪[K]) : K) * x * y + ((-π : 𝒪[K]) : K) * y ^ 2 =
    x ^ 2 - (a : K) * y ^ 2 by rw [← hπa]; push_cast; ring] at h

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
  have hwv : (normalizedValuation K (-a)).toAdd = 1 := by simp [(isUniformizer_def a).mp ha]
  rw [mem_quadraticNormSubgroup_iff_exists_zpow_mul_unit
    (neg_radicand_mem_quadraticNormSubgroup a) hwv]
  constructor
  · rintro ⟨n, c, hc, hcv, rfl⟩
    obtain ⟨u, t, hct⟩ := (mem_quadraticNormSubgroup_iff_of_isUniformizer ha hcv).mp hc
    exact ⟨n, u, t, by push_cast; rw [hct]; ring⟩
  · rintro ⟨n, u, t, hb⟩
    let c : Kˣ := b * (-a) ^ (-n)
    have hcval : (c : K) = (u : K) ^ 2 * (1 - (a : K) * (t : K) ^ 2) := by
      dsimp [c]; push_cast; rw [hb, zpow_neg]; field_simp
    have hcv : valuation K (c : K) = 1 := by
      rw [show (c : K) = (u : K) ^ 2 - (a : K) * ((u : K) * (t : K)) ^ 2 by rw [hcval]; ring]
      exact (valuation_sq_sub_mul_sq_eq_one_iff ha (u : K) ((u : K) * (t : K))).mpr
        ⟨(Valuation.integer.integers (valuation K)).valuation_unit u,
          (Valuation.mem_integer_iff _ _).mp (mul_mem (u : 𝒪[K]).2 t.2)⟩
    exact ⟨n, c, (mem_quadraticNormSubgroup_iff_of_isUniformizer ha hcv).mpr ⟨u, t, hcval⟩, hcv,
      by simp [c, zpow_neg, mul_left_comm]⟩

end TauCeti
