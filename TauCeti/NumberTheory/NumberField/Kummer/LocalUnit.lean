/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Integral radicals of local units

An `n`-th root of a local unit in a number field can be multiplied by an integer outside
the chosen prime to obtain an integral radical whose radicand is still a local unit.
This allows ramification and Frobenius criteria for integral radicals to apply to radicals
with denominators. The denominator is supplied by
`HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 6.3 and Appendix, Proposition A.5.
-/

public section

open NumberField

namespace IsDedekindDomain.HeightOneSpectrum

/-- A radical of a local unit becomes integral after multiplication by an integer outside
the chosen prime, and its new radicand remains outside that prime. -/
theorem exists_integral_pow_eq_of_valuation_eq_one
    {K M : Type*} [Field K] [NumberField K] [Field M] [Algebra K M]
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) {a : K} {α : M}
    (ha : v.valuation K a = 1) (hα : α ^ n = algebraMap K M a) :
    ∃ (d c : 𝓞 K) (β : 𝓞 M), d ∉ v.asIdeal ∧ c ∉ v.asIdeal ∧
      algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d ^ n * a ∧
      (β : M) = algebraMap (𝓞 K) M d * α ∧ β ^ n = algebraMap (𝓞 K) (𝓞 M) c := by
  obtain ⟨b, d, hbd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := K) a ha.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.2
  let c : 𝓞 K := (d : 𝓞 K) ^ (n - 1) * b
  have hc : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d ^ n * a := by
    rw [map_mul, map_pow, ← hbd, mul_comm a, ← mul_assoc, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
  have hcunit : c ∉ v.asIdeal := by
    rw [← valuation_eq_one_iff_notMem (K := K), hc, map_mul, map_pow, ha,
      (v.valuation_eq_one_iff_notMem (K := K)).mpr hd, one_pow, one_mul]
  have hβc : (algebraMap (𝓞 K) M d * α) ^ n = algebraMap (𝓞 K) M c := by
    rw [mul_pow, hα, IsScalarTower.algebraMap_apply (𝓞 K) K M,
      IsScalarTower.algebraMap_apply (𝓞 K) K M c, hc, map_mul, map_pow]
  have hβint : IsIntegral ℤ (algebraMap (𝓞 K) M d * α) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
      (hβc ▸ (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (IsScalarTower.toAlgHom ℤ (𝓞 K) M))
  let β : 𝓞 M := ⟨_, hβint⟩
  have hβ : (β : M) = algebraMap (𝓞 K) M d * α := rfl
  refine ⟨d, c, β, hd, hcunit, hc, hβ, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 M) M
  rw [map_pow, ← RingOfIntegers.coe_eq_algebraMap, hβ, hβc,
    ← IsScalarTower.algebraMap_apply]

end IsDedekindDomain.HeightOneSpectrum
