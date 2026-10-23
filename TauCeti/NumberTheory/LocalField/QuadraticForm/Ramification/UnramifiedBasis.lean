/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Quadratic

/-!
# The integral basis of `K(√u)` for a unit of maximal quadratic defect

Let `K` be a nonarchimedean local field with `2 ≠ 0`, `π` a uniformizer, `e = v_K(2)`, and `u` a
unit of `𝒪[K]` of maximal defect exponent `δ(u) = 2e`, that is `𝔡(u) = 4 𝒪[K]`. Such a `u` is not
a square, and `K(√u)/K` is the unramified quadratic extension. An attained square approximation
`b²` of `u`, with `v_K(u - b²) = 2e`, gives the element `ω = (√u - b)/π^e`. It is a root of
`X² + (2b/π^e) X + (b² - u)/π^{2e}`, whose coefficients are integral and whose discriminant
`4u/π^{2e}` is a unit. Hence `(1, ω)` is a basis of `𝒪[K(√u)]` over `𝒪[K]`, by
`TauCeti.exists_basis_integerRing_of_sq_eq_of_isUnit_discrim`.

In odd residue characteristic `e = 0`, every nonsquare unit has defect exponent `0`, and the
statement gives the basis `(1, √u - b)` for some `b` with `u - b²` a unit. The trace and norm of
`ω` are `Tr ω = -2b/π^e` and `N ω = (b² - u)/π^{2e}`, and the unit norms from `K(√u)` are read
off this basis by `Module.Basis.exists_norm_eq_iff_of_integerRing`.

## Main results

* `TauCeti.exists_basis_integerRing_of_defectExponent_eq_two_mul_natCastValuation`: the basis
  `(1, (√u - b)/π^e)`, with its trace and norm.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

/-- **The integral basis of `K(√u)` for a unit of maximal defect** (O'Meara §63A). Let `π` be a
uniformizer of `K`, `e = v_K(2)`, `u` a unit of `𝒪[K]` with defect exponent `2e`, and `x ∈ L` a
square root of `u`. Then there is `b ∈ K` with `v_K(u - b²) = 2e` such that `(1, ω)`,
`ω = (x - b)/π^e`, is a basis of `𝒪[L]` over `𝒪[K]`, with `Tr ω = -2b/π^e` and
`N ω = (b² - u)/π^{2e}`. -/
theorem exists_basis_integerRing_of_defectExponent_eq_two_mul_natCastValuation
    (h2 : (2 : K) ≠ 0) {π : 𝒪[K]} (hπ : Irreducible π) {u : Kˣ} (hu : valuation K (u : K) = 1)
    (hd : defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ)) {x : L}
    (hx2 : x ^ 2 = algebraMap K L u) :
    ∃ b : K, valuation K ((u : K) - b ^ 2) =
        valuation K (π : K) ^ (2 * natCastValuation K 2 h2) ∧
      ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧
        (B 1 : L) = (x - algebraMap K L b) / algebraMap K L ((π : K) ^ natCastValuation K 2 h2) ∧
        Algebra.trace K L (B 1 : L) = -(2 * b / (π : K) ^ natCastValuation K 2 h2) ∧
        Algebra.norm K (B 1 : L) = (b ^ 2 - u) / (π : K) ^ (2 * natCastValuation K 2 h2) := by
  set e := natCastValuation K 2 h2
  have hsq := not_isSquare_of_defectExponent_eq hd
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hvπ : valuation K (π : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
  have hπe : (π : K) ^ e ≠ 0 := pow_ne_zero e hπ0
  -- `x ∉ K`, because `u` is not a square.
  have hx : x ∉ Set.range (algebraMap K L) := by
    rintro ⟨y, rfl⟩
    rw [← map_pow, (algebraMap K L).injective.eq_iff] at hx2
    have hy : y ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simpa using hx2.symm)
    exact hsq ⟨Units.mk0 y hy, Units.ext (by simpa [sq] using hx2.symm)⟩
  -- An attained approximation `b²` of `u`, of order `2e`.
  obtain ⟨b, y, hy, hyd⟩ := exists_defectExponent_eq hsq
  rw [hd, WithTop.coe_inj] at hyd
  have hyv : valuation K (y : K) = valuation K (π : K) ^ (2 * e) := by
    have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) _ y).mp hyd
    simpa only [Units.val_mk0, zpow_natCast] using h
  refine ⟨b, hy ▸ hyv, ?_⟩
  have hv2 : valuation K 2 = valuation K (π : K) ^ e := by
    simpa using valuation_natCast_eq_pow hπ 2 h2
  -- `b` is integral, since `b² = u - (u - b²)` with both terms integral.
  have hb : valuation K b ≤ 1 := by
    have hyle : valuation K (y : K) ≤ 1 := hyv ▸ pow_le_one₀ zero_le
      (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ).le
    have hb2 : valuation K (b ^ 2) ≤ 1 := by
      rw [show b ^ 2 = (u : K) - y by rw [hy]; ring]
      exact (Valuation.map_sub _ _ _).trans (max_le hu.le hyle)
    rw [map_pow] at hb2
    exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).mp hb2
  -- The coefficients `t = 2b/π^e` and `c = (b² - u)/π^{2e}` are integral.
  have htv : valuation K (2 * b / (π : K) ^ e) = valuation K b := by
    rw [map_div₀, map_mul, hv2, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hvπ)]
  have hcv : valuation K ((b ^ 2 - u) / (π : K) ^ (2 * e)) = 1 := by
    rw [map_div₀, ← neg_sub, Valuation.map_neg, ← hy, hyv, map_pow,
      div_self (pow_ne_zero _ hvπ)]
  let t : 𝒪[K] := ⟨2 * b / (π : K) ^ e, htv.le.trans hb⟩
  let c : 𝒪[K] := ⟨(b ^ 2 - u) / (π : K) ^ (2 * e), hcv.le⟩
  -- The discriminant `t² - 4c = 4u/π^{2e}` is a unit.
  have hdisc : IsUnit (t ^ 2 - 4 * c) := by
    refine (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr ?_
    have hval : ((t ^ 2 - 4 * c : 𝒪[K]) : K) = 2 ^ 2 * u / ((π : K) ^ e) ^ 2 := by
      have h4 : ((4 : 𝒪[K]) : K) = 4 := map_ofNat (algebraMap 𝒪[K] K) 4
      simp only [t, c, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, MulMemClass.coe_mul, h4]
      field_simp
      ring
    rw [Algebra.algebraMap_ofSubsemiring_apply, hval, map_div₀, map_mul, hu, mul_one]
    simp only [map_pow, hv2]
    exact div_self (pow_ne_zero _ (pow_ne_zero _ hvπ))
  obtain ⟨B, h0, h1, htr, hn⟩ := exists_basis_integerRing_of_sq_eq_of_isUnit_discrim
    (s := (π : K) ^ e) (t := t) (c := c) hx hx2 hπe (mul_div_cancel₀ (2 * b) hπe).symm
    (by rw [← pow_mul, mul_comm e 2]; exact (mul_div_cancel₀ _ (pow_ne_zero _ hπ0)).symm) hdisc
  exact ⟨B, h0, h1, htr, hn⟩

end TauCeti
