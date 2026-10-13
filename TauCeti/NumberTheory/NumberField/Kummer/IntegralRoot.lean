/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Integral radicals of `v`-units

Let `K` be a number field, `L/K` a field extension, `v` a finite place of `K`, and `α ∈ L` an
`n`-th root of an element `a ∈ K` that is a unit at `v`. Multiplying `α` by a suitable `d ∈ 𝓞 K`
outside `v` makes it integral: `d α ∈ 𝓞 L` is an `n`-th root of `c = dⁿ a ∈ 𝓞 K`, and `c` is still
outside `v` (`TauCeti.NumberField.exists_integral_pow_eq_of_valuation_eq_one`).

Statements at `v` about `n`-th roots of `v`-units, such as the `S`-units for `v ∉ S`, therefore
reduce to integral radicands with integral roots, which can be read in the residue field at `v`:
ramification of `K(α)` at `v`, and the action of a Frobenius element above `v` on `α`.

## Main results

* `TauCeti.NumberField.exists_integral_pow_eq_of_valuation_eq_one`: an `n`-th root of a `v`-unit
  becomes integral, with integral radicand outside `v`, after multiplication by an element of
  `𝓞 K` outside `v`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 6.3 and Proposition A.5.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L]

/-- **An `n`-th root of a `v`-unit is integral up to a factor prime to `v`.** Let `α ∈ L` satisfy
`αⁿ = a` for an element `a ∈ K` with `v(a) = 1` and `n ≠ 0`. Then there are `d, c ∈ 𝓞 K`, both
outside `v`, with `c = dⁿ a`, such that `d α` is integral, and so an integral `n`-th root of `c`. -/
theorem exists_integral_pow_eq_of_valuation_eq_one {n : ℕ} (hn : n ≠ 0) {α : L} {a : K}
    (hαa : α ^ n = algebraMap K L a) {v : HeightOneSpectrum (𝓞 K)} (ha : v.valuation K a = 1) :
    ∃ (d c : 𝓞 K) (β : 𝓞 L), d ∉ v.asIdeal ∧ c ∉ v.asIdeal ∧
      algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d ^ n * a ∧
      algebraMap (𝓞 L) L β = algebraMap (𝓞 K) L d * α ∧
      β ^ n = algebraMap (𝓞 K) (𝓞 L) c := by
  -- Clear the denominator of `a` by some `d ∉ v`: `a d = b` with `b ∈ 𝓞 K`.
  obtain ⟨b, d, hbd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := K) a ha.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.2
  have hb : b ∉ v.asIdeal := by
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K), ← hbd, map_mul, ha, one_mul,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hd
  -- Then `d α` is integral, since `(d α)ⁿ = dⁿ a = dⁿ⁻¹ b`.
  set c : 𝓞 K := (d : 𝓞 K) ^ (n - 1) * b
  have hc : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d ^ n * a := by
    rw [map_mul, map_pow, ← hbd, mul_comm a, ← mul_assoc, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
  have hβc : (algebraMap (𝓞 K) L d * α) ^ n = algebraMap (𝓞 K) L c := by
    rw [mul_pow, hαa, IsScalarTower.algebraMap_apply (𝓞 K) K L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L c, hc, map_mul, map_pow]
  have hβ : IsIntegral ℤ (algebraMap (𝓞 K) L d * α) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
      (hβc ▸ (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (IsScalarTower.toAlgHom ℤ (𝓞 K) L))
  set β : 𝓞 L := ⟨_, hβ⟩
  have hβL : algebraMap (𝓞 L) L β = algebraMap (𝓞 K) L d * α := RingOfIntegers.map_mk _ _
  refine ⟨d, c, β, hd, v.isPrime.mul_notMem (fun h ↦ hd (v.isPrime.mem_of_pow_mem _ h)) hb, hc,
    hβL, FaithfulSMul.algebraMap_injective (𝓞 L) L ?_⟩
  rw [map_pow, hβL, hβc, ← IsScalarTower.algebraMap_apply]

end TauCeti.NumberField
