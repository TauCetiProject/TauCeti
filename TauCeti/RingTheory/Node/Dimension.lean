/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Node.Localization
public import TauCeti.RingTheory.KrullDimension.Polynomial
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Krull dimension of a node at its closed point

Over a Noetherian local ring `R`, the local ring of `xy = πⁿ` at the image of `(𝔪_R, x, y)` has
Krull dimension `dim R + 1`; over a discrete valuation ring it has dimension two. The node
equation is a nonzerodivisor of the polynomial ring over any commutative ring, so it cuts the
dimension of the three-dimensional ambient local ring by one. No regularity is needed, and `π`
need only lie in the maximal ideal, not generate it.

## References

* The Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]

/-- The node equation `xy - c` is a nonzerodivisor of `R[x, y]` for every commutative ring `R`,
since its lexicographic leading coefficient is one. -/
theorem X_mul_X_sub_C_mem_nonZeroDivisors (c : R) :
    (X 0 * X 1 - C c : MvPolynomial (Fin 2) R) ∈ (MvPolynomial (Fin 2) R)⁰ := by
  nontriviality R
  let m : MonomialOrder (Fin 2) := MonomialOrder.lex
  have hm : m.Monic (X 0 * X 1 - C c : MvPolynomial (Fin 2) R) := by
    rw [sub_eq_add_neg, ← map_neg]
    refine (m.monic_X.mul m.monic_X).add_of_lt ?_
    rw [m.degree_C, m.degree_mul_of_left_mem_nonZeroDivisors (by simp) (X_ne_zero _),
      m.degree_X, m.degree_X, map_zero]
    refine (m.zero_le _).lt_of_ne' ?_
    rw [Ne, m.toSyn_eq_zero_iff]
    simp
  exact m.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
    (hm.leadingCoeff_eq_one ▸ one_mem _)

variable {π : R}

section IsNoetherianRing

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Over a Noetherian local ring, the local ring of the nodal equation at the image of
the base maximal ideal and the two coordinates has dimension one more than the base.
The primality hypothesis excludes the absent point when `n = 0`. -/
theorem ringKrullDim_localization_quotient_X_mul_X_sub_C_pow (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    ringKrullDim (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)))) = ringKrullDim R + 1 := by
  let 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)
  let B := Localization.AtPrime 𝔪
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  have hn : n ≠ 0 := (isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (IsLocalization.nonZeroDivisors_le_comap 𝔪.primeCompl B
      (X_mul_X_sub_C_mem_nonZeroDivisors (π ^ n)))
    (algebraMap_X_mul_X_sub_C_pow_mem_maximalIdeal hπ hn)
  have hquot : ringKrullDim (B ⧸ span {f}) = ringKrullDim R + 1 := by
    apply ENat.WithBot.add_one_cancel.mp
    convert hdrop using 1
    norm_num [𝔪, B, ringKrullDim_localization_comap_mvPolynomial_constantCoeff, add_assoc]
  rw [ringKrullDim_eq_of_ringEquiv (S := B ⧸ span {f}) (localizationQuotientXMulXSubCPowEquiv hπ n)]
  exact hquot

end IsNoetherianRing

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The local ring of a nodal equation over a DVR at the image of the maximal ideal
and both coordinates has Krull dimension two. -/
theorem ringKrullDim_localization_quotient_X_mul_X_sub_C_pow_of_isDiscreteValuationRing
    (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    ringKrullDim (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)))) = 2 := by
  rw [ringKrullDim_localization_quotient_X_mul_X_sub_C_pow hπ n,
    IsDiscreteValuationRing.ringKrullDim_eq_one]
  norm_num

end IsDiscreteValuationRing

end TauCeti
