/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly

import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# The cyclotomic factors on a quotient of the Iwasawa algebra by a distinguished polynomial

Let `p` be a prime, `O` a commutative ring, `I` an ideal of `O` with `I ^ e ⊆ (p)`, and `F` a
polynomial of degree `d` distinguished at `I`. The model case is a complete discrete valuation
ring `O` of residue characteristic `p` with maximal ideal `I = (ϖ)` and absolute ramification
index `e`, so that `p = u ϖ ^ e` with `u` a unit. Write

```text
ξ_{n+1} = Φ_{p ^ (n + 1)}(1 + T) = ∑_{i < p} (1 + T) ^ (i p ^ n)
```

for the cyclotomic factors of `ω_{n+1} = (1 + T) ^ p ^ (n + 1) - 1`. This file shows that once
`n > d e`, the factor `ξ_{n+1}` acts on `O⟦T⟧ ⧸ (F)` as `p` times a unit: in `O⟦T⟧ ⧸ (F)` the class
`t` of `T` satisfies `t ^ d ∈ I`, hence `p ∣ t ^ (d e)`
(`Polynomial.IsDistinguishedAt.natCast_dvd_pow_of_aeval_eq_zero`), so `(1 + t) ^ p ^ n ≡ 1`
modulo `p ^ 2` and `ξ_{n+1}(t) ≡ p` modulo `p ^ 2`
(`Polynomial.IsDistinguishedAt.sq_dvd_aeval_cyclotomic_prime_pow_comp_X_add_one_sub`). When `p`
lies in the Jacobson radical of `O`, the element `1 + p c` is a unit.

When `O` is moreover `I`-adically complete, `O⟦T⟧ ⧸ (F)` is free of rank `d` over `O`, so the
determinant of multiplication by `ξ_{n+1}`, its norm over `O`, is associated to `p ^ d`, and that of
the product `ξ_{n₀+1} ⋯ ξ_n` is associated to `p ^ (d (n - n₀))` for `n₀ > d e`. For `n₀ ≤ n`
this product is the transition `ω_n / ω_{n₀}`; for `n < n₀` it is empty, equal to `1`.
Over a discrete valuation ring this says that these determinants have `ϖ`-valuation `e d` per
step; this is the horizontal input to Iwasawa's formula for the orders of the quotients
`M / ω_n M` of a finitely generated torsion `O⟦T⟧`-module `M`.

## Main results

* `Polynomial.IsDistinguishedAt.exists_mk_cyclotomic_prime_pow_comp_X_add_one_eq_mul_unit`: on
  `O⟦T⟧ ⧸ (F)`, `ξ_{n+1}` is `p` times a unit for `n > d e`.
* `Polynomial.IsDistinguishedAt.associated_norm_mk_cyclotomic_prime_pow_comp_X_add_one`: its norm
  over `O` is associated to `p ^ d`.
* `Polynomial.IsDistinguishedAt.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one`: the
  norm of `ξ_{n₀+1} ⋯ ξ_n` is associated to `p ^ (d (n - n₀))` for `n₀ > d e`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, (5.3.17)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public section

namespace Polynomial.IsDistinguishedAt

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ} [hp : Fact p.Prime]

/-- **The cyclotomic factors act on `O⟦T⟧ ⧸ (F)` as `p` times units.** If `F` is distinguished at
`I`, `I ^ e ⊆ (p)` and `p` lies in the Jacobson radical of `O`, then for every `n > deg F * e` the
class of `ξ_{n+1} = Φ_{p ^ (n + 1)}(1 + T)` in `O⟦T⟧ ⧸ (F)` is `p` times a unit. Equivalently,
multiplication by `ξ_{n+1}` on `O⟦T⟧ ⧸ (F)` is `p` times an `O`-linear automorphism. -/
theorem exists_mk_cyclotomic_prime_pow_comp_X_add_one_eq_mul_unit (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson) {n : ℕ}
    (hn : F.natDegree * e < n) :
    ∃ u : (PowerSeries O ⧸ Ideal.span {(F : PowerSeries O)})ˣ,
      Ideal.Quotient.mk _ ((cyclotomic (p ^ (n + 1)) O).comp (X + 1) : PowerSeries O) =
        (p * u : PowerSeries O ⧸ Ideal.span {(F : PowerSeries O)}) := by
  set J := Ideal.span {(F : PowerSeries O)}
  -- The quotient map sends a polynomial `g`, read as a power series, to `g` evaluated at the
  -- class of `T`.
  have hmk (g : O[X]) :
      Ideal.Quotient.mk J (g : PowerSeries O) = aeval (Ideal.Quotient.mk J PowerSeries.X) g := by
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using
      PowerSeries.algHom_coe_eq_aeval (Ideal.Quotient.mkₐ O J) g
  have hroot : aeval (Ideal.Quotient.mk J PowerSeries.X) F = 0 := by
    rw [← hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := hF.sq_dvd_aeval_cyclotomic_prime_pow_comp_X_add_one_sub hI hroot hn
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  -- `1 + p c` is a unit of `O⟦T⟧`, since its constant coefficient `1 + p c₀` is a unit of `O`.
  have hunit : IsUnit (1 + (p : PowerSeries O) * c) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, map_one, map_natCast, add_comm]
    exact Ideal.mem_jacobson_bot.1 hpO _
  refine ⟨(hunit.map (Ideal.Quotient.mk J)).unit, ?_⟩
  rw [IsUnit.unit_spec, map_add, map_mul, map_one, map_natCast, hmk, sub_eq_iff_eq_add'.1 hc]
  ring

/-- **The determinant of a cyclotomic factor on `O⟦T⟧ ⧸ (F)`.** If `O` is `I`-adically complete,
`F` is distinguished at `I`, `I ^ e ⊆ (p)` and `p` lies in the Jacobson radical of `O`, then for
every `n > deg F * e` the norm over `O` of the class of `ξ_{n+1}` in the free `O`-module
`O⟦T⟧ ⧸ (F)` of rank `deg F`, that is, the determinant of multiplication by `ξ_{n+1}`, is
associated to `p ^ deg F`. Over a discrete valuation ring with `p = u ϖ ^ e`, it has
`ϖ`-valuation `e deg F`. -/
theorem associated_norm_mk_cyclotomic_prime_pow_comp_X_add_one [IsAdicComplete I O]
    (hF : F.IsDistinguishedAt I) (hI : I ^ e ≤ Ideal.span {(p : O)})
    (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson) {n : ℕ} (hn : F.natDegree * e < n) :
    Associated
      (Algebra.norm O (Ideal.Quotient.mk (Ideal.span {(F : PowerSeries O)})
        ((cyclotomic (p ^ (n + 1)) O).comp (X + 1) : PowerSeries O)))
      ((p : O) ^ F.natDegree) := by
  nontriviality O
  obtain ⟨u, hu⟩ := hF.exists_mk_cyclotomic_prime_pow_comp_X_add_one_eq_mul_unit hI hpO hn
  have H := hF.isWeierstrassFactorizationAt
  have := H.free_quotient
  rw [hu, map_mul, ← map_natCast (algebraMap O _), Algebra.norm_algebraMap, H.finrank_quotient]
  exact associated_mul_unit_left _ _ (u.isUnit.map _)

/-- **The determinant of a cyclotomic transition on `O⟦T⟧ ⧸ (F)` grows by `p ^ deg F` per
level.** Under the hypotheses of `associated_norm_mk_cyclotomic_prime_pow_comp_X_add_one`, for
`n₀ > deg F * e` the norm over `O` of the class of the product `ξ_{n₀+1} ξ_{n₀+2} ⋯ ξ_n` in
`O⟦T⟧ ⧸ (F)` is associated to `p ^ (deg F * (n - n₀))`. For `n₀ ≤ n` this product is the
transition `ω_n / ω_{n₀}`; for `n < n₀` it is the empty product `1` and both sides are units. -/
theorem associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one [IsAdicComplete I O]
    (hF : F.IsDistinguishedAt I) (hI : I ^ e ≤ Ideal.span {(p : O)})
    (hpO : (p : O) ∈ (⊥ : Ideal O).jacobson) {n₀ : ℕ} (hn₀ : F.natDegree * e < n₀) (n : ℕ) :
    Associated
      (Algebra.norm O (Ideal.Quotient.mk (Ideal.span {(F : PowerSeries O)})
        (∏ j ∈ Finset.Ico n₀ n, ((cyclotomic (p ^ (j + 1)) O).comp (X + 1) : PowerSeries O))))
      ((p : O) ^ (F.natDegree * (n - n₀))) := by
  rw [map_prod, map_prod, pow_mul, ← Nat.card_Ico n₀ n, ← Finset.prod_const]
  exact Associated.prod _ _ _ fun j hj ↦ hF.associated_norm_mk_cyclotomic_prime_pow_comp_X_add_one
    hI hpO (hn₀.trans_le (Finset.mem_Ico.1 hj).1)

end Polynomial.IsDistinguishedAt
