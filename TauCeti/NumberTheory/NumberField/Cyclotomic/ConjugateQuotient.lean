/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.GroupTheory.OrderOfElement.NegOne
public import TauCeti.NumberTheory.NumberField.CMField.Basic

import TauCeti.NumberTheory.Cyclotomic.NormRelation

/-!
# Roots of unity as quotients of relative norm-one units

In a CM cyclotomic extension `E/K` with irreducible cyclotomic polynomial of order `n`,
where `4 ∣ n` and `n` is not a prime power, every `n`-th root of unity is `u / conj u` for
an algebraic integer unit of relative norm `1`. This supplies the unit condition used in
constructing splitting characters. For a primitive root `ζ`, use `ζ^(n/4) * (ζ - 1)`: its factors
have conjugate quotients `-1` and `-ζ`, so its quotient is `ζ`.

## References

* `lsernau/grh-lean`, `New/Derivatives/Field/WeilData.lean` at `72fead1`,
  `New.Parameters.exists_unit_prod_phi_eq_one_and_mul_star_eq`.
-/

public section

open NumberField Polynomial

namespace NumberField.IsCMField

/-- If `4 ∣ n` and `n` is not a prime power, every `n`-th root of unity in an `n`-th cyclotomic
extension that is CM is a quotient `u / conj u` with `u` a unit of the ring of integers of
relative norm `1`, provided `Φₙ` is irreducible over the base. -/
theorem exists_unit_norm_eq_one_and_div_complexConj_eq {K E : Type*} [Field K] [Field E]
    [Algebra K E] [CharZero E] [IsCMField E] [Algebra.IsIntegral ℚ E]
    {n : ℕ} [IsCyclotomicExtension {n} K E] {x : E}
    (hirr : Irreducible (cyclotomic n K)) (hfour : 4 ∣ n) (hpow : ¬ IsPrimePow n)
    (hx : x ^ n = 1) :
    ∃ u : (𝓞 E)ˣ, Algebra.norm K (u : E) = 1 ∧ (u : E) / complexConj E u = x := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hirr
  have : NeZero n := ⟨hn₀⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K E (Set.mem_singleton n) hn₀
  have := IsCyclotomicExtension.finiteDimensional {n} K E
  have := IsCyclotomicExtension.isGalois {n} K E
  have hn : 4 ≤ n := Nat.le_of_dvd (NeZero.pos n) hfour
  have hnormζ : Algebra.norm K ζ = 1 := hζ.norm_eq_one (by omega) hirr
  have hnormSub : Algebra.norm K (ζ - 1) = 1 :=
    hζ.sub_one_norm_eq_one_of_not_isPrimePow hirr (by omega) hpow
  -- Multiplying by the fourth root makes the quotient `ζ` rather than `-ζ`.
  let v : 𝓞 E := hζ.toInteger ^ (n / 4) * (hζ.toInteger - 1)
  have hv : (v : E) = ζ ^ (n / 4) * (ζ - 1) := by
    simp [v, IsPrimitiveRoot.coe_toInteger]
  have hvnorm : Algebra.norm K (v : E) = 1 := by
    simp [hv, hnormζ, hnormSub]
  have hvunit : IsUnit v := (NumberField.RingOfIntegers.isUnit_norm_of_isGalois K).mp <| by
    have h : NumberField.RingOfIntegers.norm K v = 1 :=
      RingOfIntegers.ext (by simpa using hvnorm)
    rw [h]
    exact isUnit_one
  have hhalf : ζ ^ (2 * (n / 4)) = -1 := by
    apply TauCeti.pow_eq_neg_one_of_orderOf_eq_two_mul _ (by omega : 2 * (n / 4) ≠ 0)
    rw [← hζ.eq_orderOf]
    omega
  have hconj : complexConj E ζ = ζ⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact mul_complexConj_eq_one_of_pow_eq hn₀ hζ.pow_eq_one (by simp)
  have hdiv : (v : E) / complexConj E v = ζ := by
    have hleft : ζ ^ (n / 4) / (ζ⁻¹) ^ (n / 4) = -1 := by
      rw [inv_pow, div_inv_eq_mul, ← pow_add, ← two_mul, hhalf]
    have hright : (ζ - 1) / (ζ⁻¹ - 1) = -ζ := by
      have hζ0 : ζ ≠ 0 := hζ.ne_zero hn₀
      have hden : ζ⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hζ.ne_one (by omega : 1 < n))
      apply (div_eq_iff hden).2
      rw [mul_sub, neg_mul, mul_inv_cancel₀ hζ0, mul_one]
      ring
    simp only [hv, map_mul, map_pow, map_sub, map_one, hconj, mul_div_mul_comm, hleft, hright,
      neg_one_mul, neg_neg]
  obtain ⟨k, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  refine ⟨hvunit.unit ^ k, ?_, ?_⟩
  · simp only [Units.coe_pow, ← Units.coe_coe, IsUnit.unit_spec, map_pow, hvnorm, one_pow]
  · simp only [Units.coe_pow, ← Units.coe_coe, IsUnit.unit_spec, map_pow, ← div_pow, hdiv]

end NumberField.IsCMField
