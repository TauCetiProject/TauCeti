/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly

import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# The vertical blocks of an elementary Iwasawa module

Let `O` be a discrete valuation ring with uniformiser `ϖ`, complete for its maximal ideal, with
residue field `k` of cardinality `q`, and let `Λ = O⟦X⟧`. The vertical factors of an elementary
`Λ`-module (`TauCeti.Iwasawa.Elementary`) are the blocks `Λ ⧸ (ϖ ^ m)`. This file computes how a
power series `g` with nonzero reduction modulo `ϖ` acts on such a block, where `d` is the degree
of the distinguished factor of `g` in its Weierstrass factorization:

* `g` acts injectively on `Λ ⧸ (ϖ ^ m)`, since `ϖ` is a prime of `Λ` not dividing `g`;
* the quotient `Λ ⧸ (ϖ ^ m, g)` has `q ^ (m d)` elements: it is the reduction modulo `ϖ ^ m` of
  `Λ ⧸ (g)`, which is free of rank `d` over `O`.

For `ω_n = (1 + X) ^ p ^ n - 1`, distinguished of degree `p ^ n` when `k` has characteristic `p`,
this says that `(Λ ⧸ (ϖ ^ m))[ω_n] = 0` and `#(Λ ⧸ (ϖ ^ m, ω_n)) = q ^ (m p ^ n)`. So the vertical
block has Euler quotient `#(M ⧸ ω_n M) / #M[ω_n] = q ^ (m p ^ n)`. This is the vertical
contribution `q ^ (μ p ^ n)` to the orders of the quotients `M ⧸ ω_n M` of a finitely generated
torsion `Λ`-module, in the Euler quotient at finite level and in Iwasawa's growth formula, where
`μ` is the sum of the vertical exponents `m`.

The torsion statements hold over any local domain and are in the power-series library:
`PowerSeries.torsionBy_quotient_span_C_pow_eq_bot` and its case `g = (1 + X) ^ N - 1`,
`PowerSeries.torsionBy_quotient_span_C_pow_one_add_X_pow_sub_one_eq_bot`.

## Main results

* `TauCeti.Iwasawa.natCard_quotSMulTop_quotient_span_C_pow`: for a Weierstrass factorization
  `g = f * h`, the quotient `Λ ⧸ (ϖ ^ m, g)` has `q ^ (m deg f)` elements.
* `TauCeti.Iwasawa.natCard_quotSMulTop_quotient_span_C_pow_one_add_X_pow_sub_one`: the case
  `g = ω_n`, with `#(Λ ⧸ (ϖ ^ m, ω_n)) = q ^ (m p ^ n)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, (5.3.11)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public section

open IsLocalRing PowerSeries
open scoped PowerSeries

namespace TauCeti.Iwasawa

variable {O : Type*} [CommRing O]

/-- **The order of a vertical block modulo a Weierstrass series.** Let `O` be a discrete valuation
ring with uniformiser `ϖ`, complete for its maximal ideal, and `g = f * h` a Weierstrass
factorization in `O⟦X⟧`. Then `O⟦X⟧ ⧸ (ϖ ^ m, g)` has `q ^ (m deg f)` elements, where `q` is the
cardinality of the residue field. -/
theorem natCard_quotSMulTop_quotient_span_C_pow [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {ϖ : O} (hϖ : Irreducible ϖ) {g h : O⟦X⟧}
    {f : Polynomial O} (H : g.IsWeierstrassFactorization f h) (m : ℕ) :
    Nat.card (QuotSMulTop g (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)})) =
      Nat.card (ResidueField O) ^ (m * f.natDegree) := by
  rw [H.natCard_quotSMulTop_quotient_span_C, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, pow_mul]

/-- **The cyclotomic quotient of a vertical block.** Let `O` be a discrete valuation ring with
uniformiser `ϖ`, complete for its maximal ideal, whose residue field has characteristic `p`, with
cardinality `q`. Then `O⟦X⟧ ⧸ (ϖ ^ m, ω_n)` has `q ^ (m p ^ n)` elements, where
`ω_n = (1 + X) ^ p ^ n - 1`. -/
theorem natCard_quotSMulTop_quotient_span_C_pow_one_add_X_pow_sub_one [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {ϖ : O} (hϖ : Irreducible ϖ)
    {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O) (m n : ℕ) :
    Nat.card (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)})) =
      Nat.card (ResidueField O) ^ (m * p ^ n) := by
  have H := (TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one hp hpO n
    ).isWeierstrassFactorizationAt
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X] at H
  rw [natCard_quotSMulTop_quotient_span_C_pow hϖ H,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]

/-! ### Checks -/

-- Over `ℤ_p` with `ϖ = p`, the block `Λ ⧸ (p ^ m)` modulo `ω_n` has `p ^ (m p ^ n)` elements; for
-- `m = 1` this is `#𝔽_p[X] ⧸ (X ^ p ^ n) = p ^ p ^ n`, the vertical block with `μ = 1`.
example (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    Nat.card (QuotSMulTop ((1 + X) ^ p ^ n - 1 : ℤ_[p]⟦X⟧)
      (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C ((p : ℤ_[p]) ^ m)})) = p ^ (m * p ^ n) := by
  rw [natCard_quotSMulTop_quotient_span_C_pow_one_add_X_pow_sub_one PadicInt.irreducible_p
    Fact.out (PadicInt.maximalIdeal_eq_span_p (p := p) ▸ Ideal.mem_span_singleton_self _),
    PadicInt.card_residueField]

-- The hypothesis on the reduction of `g` is needed: `p`, whose reduction is zero, kills the class
-- of `1` in `Λ ⧸ (p)`, so it has nonzero torsion there.
example (p : ℕ) [Fact p.Prime] :
    Submodule.torsionBy ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C ((p : ℤ_[p]) ^ 1)})
      (C (p : ℤ_[p])) ≠ ⊥ := by
  have : Nontrivial (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C ((p : ℤ_[p]) ^ 1)}) := by
    rw [Ideal.Quotient.nontrivial_iff, pow_one, ne_eq, Ideal.span_singleton_eq_top]
    exact (prime_C_iff.2 PadicInt.prime_p).not_isUnit
  refine (Submodule.ne_bot_iff _).2 ⟨1, ?_, one_ne_zero⟩
  rw [Submodule.mem_torsionBy_iff, ← map_one (Ideal.Quotient.mk _), ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one, pow_one]
  exact Ideal.mem_span_singleton_self _

end TauCeti.Iwasawa
