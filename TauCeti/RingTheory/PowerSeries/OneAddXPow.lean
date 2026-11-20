/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The power series `(1 + X) ^ pⁿ - 1`

For a prime `p`, the power series `ω_n = (1 + X) ^ pⁿ - 1` over a commutative ring `O` cut out the
finite levels of the Iwasawa algebra `O⟦X⟧`. This file collects facts about them that do not
depend on the level maps. In characteristic `p` the Frobenius identity gives `ω_n = X ^ pⁿ`. For
an ideal `I` of `O` containing `p`, `ω_n` lies in the `(n + 1)`-st power of the ideal
`I.comap constantCoeff` of series with constant coefficient in `I` (over a local ring in which `p`
is not a unit, the maximal ideal of `O⟦X⟧`), so when `O` is `I`-adically Hausdorff, for instance
when `O` is a complete local ring or, by Krull's intersection theorem, a noetherian local ring and
`I` its maximal ideal, the principal ideals `(ω_n)` meet in zero. Over a local domain with a prime
`ϖ`, every `(1 + X) ^ N - 1` with `N ≠ 0` acts injectively on `O⟦X⟧ ⧸ (ϖ ^ m)`.

The polynomial counterparts, in particular that `(1 + X) ^ pⁿ - 1` is distinguished at every ideal
containing `p`, are in `TauCeti.RingTheory.Polynomial.Distinguished`.

## Main results

* `PowerSeries.one_add_X_pow_sub_one_eq_X_pow`: in characteristic `p`, `ω_n = X ^ pⁿ`.
* `PowerSeries.torsionBy_quotient_span_C_pow_one_add_X_pow_sub_one_eq_bot`: for a prime `ϖ` of a
  local domain `O` and `N ≠ 0`, `(1 + X) ^ N - 1` has no nonzero torsion on `O⟦X⟧ ⧸ (ϖ ^ m)`.
* `PowerSeries.one_add_X_pow_sub_one_mem_comap_constantCoeff_pow`: `ω_n` lies in the
  `(n + 1)`-st power of `I.comap constantCoeff`, the ideal of series with constant coefficient in
  `I`, for an ideal `I` containing `p`.
* `PowerSeries.one_add_X_pow_sub_one_mem_maximalIdeal_pow`: `ω_n` lies in the `(n + 1)`-st power
  of the maximal ideal of `O⟦X⟧` when `p` is not a unit of the local ring `O`.
* `PowerSeries.iInf_span_one_add_X_pow_sub_one_eq_bot`: if `O` is `I`-adically Hausdorff for an
  ideal `I` containing `p`, then `⋂ₙ (ω_n) = 0`.
-/

public section

open IsLocalRing

namespace PowerSeries

variable {p : ℕ} {O : Type*} [CommRing O]

variable (p O) in
/-- **`ω_n = X ^ pⁿ` in characteristic `p`.** Over a ring of characteristic `p` the series
`(1 + X) ^ pⁿ - 1` is the monomial `X ^ pⁿ`, by the Frobenius identity. -/
theorem one_add_X_pow_sub_one_eq_X_pow [Fact p.Prime] [CharP O p] (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 = X ^ p ^ n := by
  have : CharP O⟦X⟧ p := charP_of_injective_ringHom C_injective p
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]

/-- Over a local domain `O` with a prime `ϖ`, `(1 + X) ^ N - 1` acts injectively on
`O⟦X⟧ ⧸ (ϖ ^ m)` for `N ≠ 0`; in particular `(O⟦X⟧ ⧸ (ϖ ^ m))[ω_n] = 0` for
`ω_n = (1 + X) ^ pⁿ - 1`. -/
theorem torsionBy_quotient_span_C_pow_one_add_X_pow_sub_one_eq_bot [IsDomain O] [IsLocalRing O]
    {ϖ : O} (hϖ : Prime ϖ) {N : ℕ} (hN : N ≠ 0) (m : ℕ) :
    Submodule.torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) ((1 + X) ^ N - 1) = ⊥ := by
  refine torsionBy_quotient_span_C_pow_eq_bot hϖ (fun h ↦ ?_) m
  -- Over the residue field, `(1 + X) ^ N - 1` is the image of a monic polynomial of degree `N`.
  refine (TauCeti.Polynomial.monic_one_add_X_pow_sub_one (R := ResidueField O) hN).ne_zero ?_
  rw [← Polynomial.coe_eq_zero_iff]
  simpa using h

/-- For an ideal `I` of `O` containing `p`, the series `ω_n = (1 + X) ^ pⁿ - 1` lies in the
`(n + 1)`-st power of the ideal `I.comap constantCoeff` of series with constant coefficient in `I`:
`ω_0 = X`, and `ω_{n+1} = ω_n · ∑_{i < p} (1 + X) ^ (i pⁿ)`, whose second factor has constant
coefficient `p`. -/
theorem one_add_X_pow_sub_one_mem_comap_constantCoeff_pow {I : Ideal O} (hI : (p : O) ∈ I)
    (n : ℕ) : (1 + X : O⟦X⟧) ^ p ^ n - 1 ∈ I.comap constantCoeff ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ p n, pow_mul, ← geom_sum_mul, pow_succ' (I.comap constantCoeff)]
    refine Ideal.mul_mem_mul ?_ ih
    rw [Ideal.mem_comap]
    simpa using hI

/-- The series `ω_n = (1 + X) ^ pⁿ - 1` lies in the `(n + 1)`-st power of the maximal ideal of
`O⟦X⟧` when `p` is not a unit of the local ring `O`, since that maximal ideal consists of the
series whose constant coefficient lies in the maximal ideal of `O`. -/
theorem one_add_X_pow_sub_one_mem_maximalIdeal_pow [IsLocalRing O]
    (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 ∈ maximalIdeal O⟦X⟧ ^ (n + 1) := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact one_add_X_pow_sub_one_mem_comap_constantCoeff_pow hp n

/-- **The ideals `(ω_n)` meet in zero.** If `O` is Hausdorff for an ideal `I` containing `p`, no
nonzero element of `O⟦X⟧` is divisible by every `ω_n = (1 + X) ^ pⁿ - 1`: `ω_n` lies in the
`(n + 1)`-st power of the ideal `I.comap constantCoeff` of series with constant coefficient in `I`,
for which `O⟦X⟧` is Hausdorff too. -/
theorem iInf_span_one_add_X_pow_sub_one_eq_bot {I : Ideal O} (hI : (p : O) ∈ I)
    [IsHausdorff I O] : ⨅ n : ℕ, Ideal.span {(1 + X : O⟦X⟧) ^ p ^ n - 1} = ⊥ := by
  refine eq_bot_iff.mpr <| (le_iInf fun n ↦ ?_).trans (by
    simpa using (IsHausdorff.iInf_pow_smul (isHausdorff_comap_constantCoeff I (R := O))).le)
  refine (iInf_le _ n).trans ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact Ideal.pow_le_pow_right n.le_succ (one_add_X_pow_sub_one_mem_comap_constantCoeff_pow hI n)

end PowerSeries
