/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic

/-!
# Exact multiplicities of homogeneous cyclotomic values

For a prime `p` not dividing the denominator, let `d` be the multiplicative order of the
ratio modulo `p`. The multiplicity of `p` in `Φ_n(a, b)` is the multiplicity in
`a ^ d - b ^ d` when `n = d`. At the other indices with `p`-free part `d`, it is one, except
at `p = n = 2`, where it is the multiplicity of `2` in `a + b`. At all remaining positive
indices it is zero. These formulas isolate the contribution of primitive prime divisors from
the possible nonprimitive prime divisor of a cyclotomic value.

The base-order formula is stated for integer bases and needs only that their ratio have the
prescribed positive order. The complete formula uses natural bases `b < a` and `p ∤ b`; it needs
neither coprimality of the bases nor `b > 0`. When `p ∣ a`, the order is zero, so the base-order
branch cannot occur at a positive index. Natural subtraction on the right-hand side does not
truncate because `b < a`.

## References

* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Annals of Mathematics (2) 5 (1904), 173–180, Theorem IV, p. 177.
* Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023), Lemmas 2.11–2.12, p. 4.
-/

public section

open TauCeti

namespace Nat.Prime

variable {p : ℕ}

/-- At the positive order of `a / b` modulo `p`, the cyclotomic factor accounts for the entire
multiplicity of `p` in the difference of powers. The positive order already guarantees that
the denominator is prime to `p`. -/
theorem multiplicity_homogeneousCyclotomic_of_orderOf_eq (hp : p.Prime) {a b : ℤ}
    {n : ℕ} (hn : n ≠ 0)
    (hord : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) :
    multiplicity (p : ℤ) (homogeneousCyclotomic n a b) =
      multiplicity (p : ℤ) (a ^ n - b ^ n) := by
  have := Fact.mk hp
  have hb : ¬(p : ℤ) ∣ b := by
    intro hpb
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd b p).2 hpb, inv_zero, mul_zero,
      orderOf_zero] at hord
    exact hn hord.symm
  have hp' := Nat.prime_iff_prime_int.1 hp
  -- Every proper-divisor factor has a smaller `p`-free part than the order of the ratio.
  have hprod : ¬(p : ℤ) ∣ ∏ m ∈ n.properDivisors, homogeneousCyclotomic m a b := by
    rw [hp'.dvd_finsetProd_iff]
    rintro ⟨m, hm, hpm⟩
    obtain ⟨hmn, hmlt⟩ := Nat.mem_properDivisors.1 hm
    have hm0 := ne_zero_of_dvd_ne_zero hn hmn
    have hmord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb hm0).1 hpm
    have : n ≤ m := by
      rw [hord] at hmord
      exact hmord ▸ Nat.ordCompl_le m p
    omega
  apply multiplicity_eq_of_emultiplicity_eq
  rw [← homogeneousCyclotomic_mul_prod_properDivisors (Nat.pos_of_ne_zero hn) a b,
    _root_.emultiplicity_mul hp', emultiplicity_eq_zero.2 hprod, add_zero]

/-- **Exact prime multiplicity of a homogeneous cyclotomic value.** Writing `d` for the order
of `a / b` modulo `p`, the base-order term is the multiplicity in `a ^ d - b ^ d`. The other
indices with `p`-free part `d` have multiplicity one, except for `p = n = 2`, whose value is
`a + b`. Only the denominator must be prime to `p`; the order may be zero. -/
theorem multiplicity_homogeneousCyclotomic_eq_ite (hp : p.Prime) {a b n : ℕ} (hba : b < a)
    (hb : ¬p ∣ b) (hn : n ≠ 0) :
    multiplicity (p : ℤ) (homogeneousCyclotomic n (a : ℤ) b) =
      if n = orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) then
        multiplicity p (a ^ n - b ^ n)
      else if p = 2 ∧ n = 2 then multiplicity 2 (a + b)
      else if orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = ordCompl[p] n then 1 else 0 := by
  have hb' : ¬(p : ℤ) ∣ (b : ℤ) := fun h => hb (Int.natCast_dvd_natCast.1 h)
  have hcriterion : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b ↔
      orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = ordCompl[p] n := by
    simpa only [Int.cast_natCast] using
      hp.dvd_homogeneousCyclotomic_iff_orderOf_eq (a := (a : ℤ)) hb' hn
  split_ifs with horder hexc hcompl
  · have hord : orderOf (((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹) = n := by
      simpa only [Int.cast_natCast] using horder.symm
    rw [hp.multiplicity_homogeneousCyclotomic_of_orderOf_eq hn hord,
      ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub (Nat.pow_le_pow_left hba.le n),
      Int.natCast_multiplicity]
  · obtain ⟨rfl, rfl⟩ := hexc
    rw [homogeneousCyclotomic_two, ← Nat.cast_add, Int.natCast_multiplicity]
  · have hpn : p ∣ n := by
      by_contra hpn
      rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).2 (Or.inr hpn)] at hcompl
      exact horder hcompl.symm
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact hexc ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpn, rfl⟩
    exact hp.multiplicity_homogeneousCyclotomic_eq_one hba hb hpn hn2 (hcriterion.2 hcompl)
  · exact multiplicity_eq_zero_of_not_dvd (hcriterion.not.2 hcompl)

end Nat.Prime
