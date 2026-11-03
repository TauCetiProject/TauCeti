/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.Quadratic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
import TauCeti.NumberTheory.LocalField.Uniformizer

/-!
# The integral basis of `K(√u)` for a unit of odd quadratic defect

Let `K` be a nonarchimedean local field, `π` a uniformizer, and `u` a unit of `𝒪[K]` whose defect
exponent `δ(u) = 2k + 1` is odd, so that `K(√u)/K` is ramified. An optimal square approximation
`b² ` of `u`, with `v_K(u - b²) = 2k + 1`, gives the element `ω = (√u - b)/π^k`. It is a root of
`X² + (2b/π^k) X + (b² - u)/π^{2k}`, which is Eisenstein: the constant coefficient has valuation
`1`, and the middle coefficient has valuation `v_K(2) - k > 0` because the possible defects of a
unit force `2k + 1 < 2 v_K(2)`. Hence `(1, ω)` is a basis of `𝒪[K(√u)]` over `𝒪[K]`.

This is the integral basis on which the unit norms of a ramified quadratic extension are read
off. Its trace and norm are `Tr ω = -2b/π^k` and `N ω = (b² - u)/π^{2k}`.

## Main results

* `TauCeti.exists_basis_integerRing_of_defectExponent_eq_odd`: the basis `(1, (√u - b)/π^k)`, with
  its trace and norm.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

/-- **The integral basis of `K(√u)` for a unit of odd defect** (O'Meara §63A). Let `π` be a
uniformizer of `K`, `u` a unit of `𝒪[K]` with defect exponent `2k + 1`, and `x ∈ L` a square root
of `u`. Then there is `b ∈ K` with `v_K(u - b²) = 2k + 1` such that `(1, ω)`, `ω = (x - b)/π^k`, is
a basis of `𝒪[L]` over `𝒪[K]`, with `Tr ω = -2b/π^k` and `N ω = (b² - u)/π^{2k}`. -/
theorem exists_basis_integerRing_of_defectExponent_eq_odd {π : 𝒪[K]} (hπ : Irreducible π)
    {u : Kˣ} (hu : valuation K (u : K) = 1) {k : ℕ}
    (hd : defectExponent u = ((2 * k + 1 : ℕ) : ℤ)) {x : L}
    (hx2 : x ^ 2 = algebraMap K L u) :
    ∃ b : K, valuation K ((u : K) - b ^ 2) = valuation K (π : K) ^ (2 * k + 1) ∧
      ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧
        (B 1 : L) = (x - algebraMap K L b) / algebraMap K L ((π : K) ^ k) ∧
        Algebra.trace K L (B 1 : L) = -(2 * b / (π : K) ^ k) ∧
        Algebra.norm K (B 1 : L) = (b ^ 2 - u) / (π : K) ^ (2 * k) := by
  have hsq := not_isSquare_of_defectExponent_eq hd
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hπk : (π : K) ^ k ≠ 0 := pow_ne_zero k hπ0
  -- An attained approximation `b²` of `u`, of order `2k + 1`.
  obtain ⟨b, y, hy, hyd⟩ := exists_defectExponent_eq hsq
  rw [hd, WithTop.coe_inj] at hyd
  have hyv : valuation K (y : K) = valuation K (π : K) ^ (2 * k + 1) := by
    have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) _ y).mp hyd
    simpa only [Units.val_mk0, zpow_natCast] using h
  refine ⟨b, hy ▸ hyv, ?_⟩
  -- The constant coefficient `c = (b² - u)/π^{2k}` is a uniformizer.
  have hcv : valuation K ((b ^ 2 - u) / (π : K) ^ (2 * k)) = valuation K (π : K) := by
    rw [map_div₀, ← neg_sub, Valuation.map_neg, ← hy, hyv, map_pow, pow_succ,
      mul_div_cancel_left₀ _ (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hπ0))]
  let c : 𝒪[K] := ⟨(b ^ 2 - u) / (π : K) ^ (2 * k), hcv ▸ hπ1.le⟩
  have hc : Irreducible c := irreducible_of_valuation_eq hπ hcv
  -- The middle coefficient `t = 2b/π^k` lies in the maximal ideal.
  have htv : valuation K (2 * b / (π : K) ^ k) < 1 := by
    by_cases h2 : (2 : K) = 0
    · simp [h2]
    -- `b` is a unit, since `v(u - b²) < 1 = v(u)`.
    have hb : valuation K b = 1 := by
      have hylt : valuation K (y : K) < valuation K (u : K) :=
        hu ▸ hyv ▸ pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero _)
      have hb2 : valuation K (b ^ 2) = 1 := by
        rw [show b ^ 2 = (u : K) - y by rw [hy]; ring,
          Valuation.map_sub_eq_of_lt_left _ hylt, hu]
      rw [map_pow, pow_eq_one_iff] at hb2
      exact hb2.resolve_right two_ne_zero
    -- The possible defects of a unit give `2k + 1 ≤ 2 v_K(2)`, so `k < v_K(2)`.
    have hk : k < natCastValuation K 2 h2 := by
      have h := defectExponent_le_two_mul_natCastValuation h2 hu hsq
      rw [hd, WithTop.coe_le_coe, Nat.cast_le] at h
      omega
    have hv2 := valuation_natCast_eq_pow hπ 2 h2
    push_cast at hv2
    rw [map_div₀, map_mul, hv2, hb, mul_one, map_pow,
      div_lt_one₀ (pow_pos ((Valuation.pos_iff _).mpr hπ0) k)]
    exact pow_lt_pow_right_of_lt_one₀ ((Valuation.pos_iff _).mpr hπ0) hπ1 hk
  let t : 𝒪[K] := ⟨2 * b / (π : K) ^ k, htv.le⟩
  have htm : t ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.2 htv
  obtain ⟨B, h0, h1, htr, hn⟩ := exists_basis_integerRing_of_sq_eq (t := t) (c := c)
    (b := b) hx2 hπk htm hc (by simp [t, mul_div_cancel₀ _ hπk])
    (by simp [c, ← pow_mul, mul_comm k 2, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)])
  exact ⟨B, h0, h1, htr, hn⟩

end TauCeti
