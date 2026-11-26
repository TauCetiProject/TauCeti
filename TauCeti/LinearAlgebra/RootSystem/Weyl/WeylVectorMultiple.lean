/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.MonoidAlgebra.Telescope
import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Characters at multiples of the Weyl vector

At a multiple `k ρ` of the Weyl vector the Weyl character formula can be divided out in closed
form: the character `ch` with `ch · Δ = N(k ρ)` is

`ch = e^{k ρ} ∏_{α>0} (1 + e^{-α} + ⋯ + e^{-k α})`,

a product of one geometric root string for each positive root. At an even multiple
`2 n ρ = n · 2ρ`, where `e^{2 n ρ} = ∏_{α>0} e^{n α}`, every string is centred:

`ch = ∏_{α>0} ∑_{j = -n}^{n} e^{j α}`.

This is a statement about the integral group algebra `ℤ[M]` of the weight space of a root pairing,
proved with no Lie algebra in sight. The argument is the dilation `e^x ↦ e^{(k + 1) x}` of `ℤ[M]`,
a ring endomorphism. The un-shifted numerator `e^{ρ} N(λ) = ∑_{w ∈ W} sgn(w) e^{w(λ + ρ)}` at
`λ = k ρ` is the dilation of `e^{ρ} N(0)`, because `w((k + 1) ρ) = (k + 1) w(ρ)`. Granting the
denominator identity `Δ = N(0)`, the dilation of `e^{ρ} Δ` is
`e^{(k + 1) ρ} ∏_{α>0} (1 - e^{-(k + 1) α})`, and each factor `1 - e^{-(k + 1) α}` is
`1 - e^{-α}` times a geometric sum. Cancelling the regular element `e^{ρ} Δ` leaves the product.

The denominator identity is taken as a hypothesis. It is proved for root pairings over ordered
rings (`TauCeti.weylDenominator_eq_weylNumerator_zero`), and for the root system of a semisimple
Lie algebra over an algebraically closed field from the character formula of the trivial module
(`TauCeti.weylDenominator_rootSystem_eq_weylNumerator_zero`); that is how the closed form reaches
the characters of Lie algebra modules. Cancelling `Δ` uses `TauCeti.isRegular_weylDenominator`.

## Main results

* `TauCeti.single_weylVector_mul_weylNumerator`: the un-shifted numerator,
  `e^{ρ} N(λ) = ∑_{w ∈ W} sgn(w) e^{w(λ + ρ)}`.
* `TauCeti.eq_single_nsmul_weylVector_mul_prod_of_mul_weylDenominator_eq`: if `f Δ = N(k ρ)` then
  `f = e^{k ρ} ∏_{α>0} ∑_{j=0}^{k} e^{-j α}`.
* `TauCeti.eq_prod_sum_Icc_of_mul_weylDenominator_eq`: if `f Δ = N(n · 2ρ)` then
  `f = ∏_{α>0} ∑_{j=-n}^{n} e^{j α}`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §24.3, for the
  character formula with the un-shifted numerator `∑_w sgn(w) e^{w(λ + ρ)}`.
* C. Fu, *Stability of elliptic Fargues–Scholze L-packets*, arXiv:2501.00652, Lemma 3.1.2, for the
  centred root-string product at the weights `2 n ρ`.
-/

public section

namespace TauCeti

open AddMonoidAlgebra Finset

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] (b : P.Base)

section Numerator

variable [CharZero R] [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [Fintype P.weylGroup]

/-- **The un-shifted Weyl numerator**: `e^{ρ} N(λ) = ∑_{w ∈ W} sgn(w) e^{w(λ + ρ)}`, the
alternating sum over the linear orbit of `λ + ρ`. -/
theorem single_weylVector_mul_weylNumerator (lam : M) :
    single (weylVector P b) 1 * weylNumerator P b lam =
      ∑ w : P.weylGroup, single (w • (lam + weylVector P b)) ((weylSign P b w : ℤ)) := by
  rw [weylNumerator_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [single_mul_single, one_mul, add_comm, dotAction_add_weylVector]

/-- The dilation `e^x ↦ e^{(k + 1) x}` carries `e^{ρ} N(0)` to `e^{ρ} N(k ρ)`. -/
private theorem mapDomainRingHom_single_weylVector_mul_weylNumerator_zero (k : ℕ) :
    mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M (k + 1))
        (single (weylVector P b) 1 * weylNumerator P b 0) =
      single (weylVector P b) 1 * weylNumerator P b (k • weylVector P b) := by
  rw [single_weylVector_mul_weylNumerator, single_weylVector_mul_weylNumerator, map_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [mapDomainRingHom_apply, mapDomain_single, DistribSMul.toAddMonoidHom_apply, zero_add,
    ← smul_comm w (k + 1), succ_nsmul]

variable {P b}

/-- **The character at a multiple of the Weyl vector.** If `f · Δ = N(k ρ)`, and the denominator
identity `Δ = N(0)` holds, then

`f = e^{k ρ} ∏_{α>0} ∑_{j=0}^{k} e^{-j α}`.

For a Lie algebra, `f` is the character of the irreducible module of highest weight `k ρ`, and
its dimension is `(k + 1)` to the number of positive roots. -/
theorem eq_single_nsmul_weylVector_mul_prod_of_mul_weylDenominator_eq
    {f : AddMonoidAlgebra ℤ M} {k : ℕ} (hΔ : weylDenominator P b = weylNumerator P b 0)
    (hf : f * weylDenominator P b = weylNumerator P b (k • weylVector P b)) :
    f = single (k • weylVector P b) 1 *
      ∏ i ∈ posRootsFinset P b, ∑ j ∈ range (k + 1), single (-(j • P.root i)) 1 := by
  set G : AddMonoidAlgebra ℤ M :=
    ∏ i ∈ posRootsFinset P b, ∑ j ∈ range (k + 1), single (-(j • P.root i)) 1
  -- The dilation of `e^{ρ} Δ` is `e^{(k + 1) ρ} ∏ (1 - e^{-(k + 1) α}) = e^{(k + 1) ρ} Δ G`.
  have hdil : mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M (k + 1))
      (single (weylVector P b) 1 * weylDenominator P b) =
        single ((k + 1) • weylVector P b) 1 * (weylDenominator P b * G) := by
    simp only [map_mul, weylDenominator_def, map_prod, map_sub, map_one, mapDomainRingHom_apply,
      mapDomain_single, DistribSMul.toAddMonoidHom_apply, smul_neg, G, ← prod_mul_distrib,
      one_sub_single_neg_nsmul_eq_mul_sum]
  have key : single (weylVector P b) 1 * f * weylDenominator P b =
      single (weylVector P b) 1 * (single (k • weylVector P b) 1 * G) * weylDenominator P b := by
    have hsplit : single ((k + 1) • weylVector P b) (1 : ℤ) =
        single (weylVector P b) 1 * single (k • weylVector P b) 1 := by
      rw [single_mul_single, one_mul, succ_nsmul']
    rw [mul_assoc, hf, ← mapDomainRingHom_single_weylVector_mul_weylNumerator_zero, ← hΔ, hdil,
      hsplit]
    ring
  have := (isRegular_weylDenominator P b).right key
  rw [← one_mul f, ← single_neg_mul_single (R := ℤ) (weylVector P b), mul_assoc, this,
    ← mul_assoc, single_neg_mul_single, one_mul]

/-- **The character at an even multiple of the Weyl vector is a product of centred root
strings.** If `f · Δ = N(n · 2ρ)`, and the denominator identity `Δ = N(0)` holds, then

`f = ∏_{α>0} ∑_{j=-n}^{n} e^{j α}`.

For a Lie algebra, `f` is the character of the irreducible module of highest weight `n · 2ρ`,
whose weights are the sums `∑_{α>0} j_α α` with every `|j_α| ≤ n`, counted with multiplicity. -/
theorem eq_prod_sum_Icc_of_mul_weylDenominator_eq
    {f : AddMonoidAlgebra ℤ M} {n : ℕ} (hΔ : weylDenominator P b = weylNumerator P b 0)
    (hf : f * weylDenominator P b = weylNumerator P b (n • twoWeylVector P b)) :
    f = ∏ i ∈ posRootsFinset P b, ∑ j ∈ Icc (-(n : ℤ)) n, single (j • P.root i) 1 := by
  rw [nsmul_twoWeylVector] at hf
  have hsingle : single (n • twoWeylVector P b) (1 : ℤ) =
      ∏ i ∈ posRootsFinset P b, single (n • P.root i) 1 := by
    rw [prod_single, prod_const_one, twoWeylVector_def, Finset.smul_sum]
  rw [eq_single_nsmul_weylVector_mul_prod_of_mul_weylDenominator_eq hΔ hf, ← nsmul_twoWeylVector,
    hsingle, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  -- Reindex the string `j ↦ n - j` from `0, …, 2 n` to `-n, …, n`.
  rw [Finset.mul_sum, sum_Icc_neg_natCast_eq_sum_range, ← sum_range_reflect]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [single_mul_single, one_mul, add_tsub_cancel_right, ← natCast_zsmul, ← natCast_zsmul,
    Nat.cast_sub (by omega), ← neg_smul, ← add_smul]
  congr 2
  push_cast
  ring

end Numerator

end TauCeti
