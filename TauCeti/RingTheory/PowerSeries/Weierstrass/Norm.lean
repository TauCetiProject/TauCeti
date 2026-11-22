/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly

import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Norm.Basic
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Norm.Cokernel
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Multiplication by a series on a Weierstrass quotient

Let `A` be a commutative ring, complete for an ideal `I`, and let `g = f * h` be a Weierstrass
factorization in `A⟦X⟧`: `f` a polynomial distinguished at `I` and `h` a unit. The quotient
`N = A⟦X⟧ ⧸ (g)` is free of rank `deg f` over `A`
(`PowerSeries.IsWeierstrassFactorizationAt.powerBasis`), so multiplication by any series `φ` on
`N` is an `A`-linear endomorphism of a finite free module, whose determinant is the norm over `A` of
the class of `φ`. This file reads the kernel `N[φ]` and the cokernel `N ⧸ φ N` of multiplication by
`φ` off that norm:

* over a domain, `N[φ] = 0` exactly when the norm is nonzero;
* over a principal ideal domain, when the norm is nonzero, `N ⧸ φ N` has as many elements as
  `A ⧸ (norm)`;
* over an infinite domain, when the norm vanishes, `N ⧸ φ N` is infinite;
* for a polynomial `φ = P`, the norm is the resultant `Res(f, P)`.

The first two are the Weierstrass cases of the corresponding statements for any finite free
algebra (`TauCeti.Algebra.torsionBy_eq_bot_iff_norm_ne_zero` and its companion); the
infinite-cokernel statement is given directly by
`TauCeti.Algebra.infinite_quotSMulTop_of_norm_eq_zero`.

Over an infinite principal ideal domain with finite quotients, such as a discrete valuation ring
`O` with finite residue field, `N ⧸ φ N` is therefore finite exactly when the norm of `φ` is
nonzero. For a distinguished polynomial `G`, the module `O⟦X⟧ ⧸ (G)` is a
horizontal block of an elementary module over the Iwasawa algebra `Λ = O⟦X⟧`; this file computes
the kernel and cokernel of multiplication by an element of `Λ`, for instance
`ω_n = (1 + X) ^ p ^ n - 1`, on such a block: the kernel vanishes and the cokernel has
`#(O ⧸ Res(G, ω_n))` elements when `Res(G, ω_n) ≠ 0`, and the cokernel is infinite otherwise. These
are the contributions of the horizontal blocks to the orders of the coinvariants `M / ω_n M` of a
finitely generated torsion `Λ`-module `M`, read through a pseudo-isomorphism onto an elementary
module.

## Main results

* `PowerSeries.IsWeierstrassFactorizationAt.torsionBy_eq_bot_iff`: `N[φ] = 0` iff the norm of
  `φ` is nonzero.
* `PowerSeries.IsWeierstrassFactorizationAt.natCard_quotSMulTop`: if the norm of `φ` is nonzero,
  `#(N ⧸ φ N) = #(A ⧸ (norm φ))`.
* `PowerSeries.IsWeierstrassFactorizationAt.finite_quotSMulTop_iff`: over an infinite principal
  ideal domain with finite quotients, such as a discrete valuation ring with finite residue field,
  `N ⧸ φ N` is finite iff the norm of `φ` is nonzero.
* `PowerSeries.IsWeierstrassFactorizationAt.norm_mk_coe_eq_resultant`: the norm of a polynomial
  `P` is the resultant `Res(f, P)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (5.3.11)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public section

open IsLocalRing

namespace PowerSeries.IsWeierstrassFactorizationAt

variable {A : Type*} [CommRing A] {I : Ideal A} {g : A⟦X⟧} {f : Polynomial A} {h : A⟦X⟧}

variable (H : g.IsWeierstrassFactorizationAt f h I) [IsAdicComplete I A]
include H

/-- **The norm of a polynomial on a Weierstrass quotient is a resultant.** For a polynomial `P`,
the norm over `A` of the class of `P` in `A⟦X⟧ ⧸ (g)`, that is, the determinant of multiplication
by `P` on this free `A`-module, is the resultant `Res(f, P)` of the distinguished factor `f` of `g`
and `P`. -/
theorem norm_mk_coe_eq_resultant (P : Polynomial A) :
    Algebra.norm A (Ideal.Quotient.mk (Ideal.span {g}) (P : A⟦X⟧)) = f.resultant P := by
  have hP : H.algEquivQuotient (Ideal.Quotient.mk (Ideal.span {f}) P) =
      Ideal.Quotient.mk _ (P : A⟦X⟧) := by
    simp
  -- `AdjoinRoot.mk f` is by definition the quotient map `A[X] → A[X] ⧸ (f)`.
  rw [← hP, Algebra.norm_eq_of_algEquiv]
  exact AdjoinRoot.norm_mk_eq_resultant H.isDistinguishedAt.monic P

/-- **Kernel of multiplication on a Weierstrass quotient.** Over a domain, multiplication by a
series `φ` on `A⟦X⟧ ⧸ (g)` is injective exactly when the norm over `A` of the class of `φ`, the
determinant of multiplication by `φ` on this free `A`-module of rank `deg f`, is nonzero. -/
theorem torsionBy_eq_bot_iff [IsDomain A] (φ : A⟦X⟧) :
    Submodule.torsionBy A⟦X⟧ (A⟦X⟧ ⧸ Ideal.span {g}) φ = ⊥ ↔
      Algebra.norm A (Ideal.Quotient.mk (Ideal.span {g}) φ) ≠ 0 := by
  have := H.free_quotient
  have := H.finite_quotient
  exact TauCeti.Algebra.torsionBy_eq_bot_iff_norm_ne_zero φ

/-- **Cokernel of multiplication on a Weierstrass quotient.** Over a principal ideal domain, if the
norm over `A` of the class of a series `φ` is nonzero, then `A⟦X⟧ ⧸ (g)` modulo `φ` has as many
elements as `A` modulo that norm. -/
theorem natCard_quotSMulTop [IsDomain A] [IsPrincipalIdealRing A] {φ : A⟦X⟧}
    (hφ : Algebra.norm A (Ideal.Quotient.mk (Ideal.span {g}) φ) ≠ 0) :
    Nat.card (QuotSMulTop φ (A⟦X⟧ ⧸ Ideal.span {g})) =
      Nat.card (A ⧸ Ideal.span {Algebra.norm A (Ideal.Quotient.mk (Ideal.span {g}) φ)}) := by
  have := H.free_quotient
  have := H.finite_quotient
  exact TauCeti.Algebra.natCard_quotSMulTop_of_norm_ne_zero hφ

/-- **Finite cokernels on a Weierstrass quotient.** If `A` is an infinite principal ideal domain
whose quotients by nonzero ideals are finite, for instance a discrete valuation ring with finite
residue field, then `A⟦X⟧ ⧸ (g)` modulo a series `φ` is finite exactly when the norm over `A` of the
class of `φ` is nonzero. -/
theorem finite_quotSMulTop_iff [IsDomain A] [IsPrincipalIdealRing A] [Infinite A]
    [Ring.HasFiniteQuotients A] (φ : A⟦X⟧) :
    Finite (QuotSMulTop φ (A⟦X⟧ ⧸ Ideal.span {g})) ↔
      Algebra.norm A (Ideal.Quotient.mk (Ideal.span {g}) φ) ≠ 0 := by
  have := H.free_quotient
  have := H.finite_quotient
  exact TauCeti.Algebra.finite_quotSMulTop_iff_norm_ne_zero φ

end PowerSeries.IsWeierstrassFactorizationAt

/-! ### Examples over `ℤ_[p]`

On `Λ ⧸ (X - p)`, with `Λ = ℤ_[p]⟦X⟧` and `p` odd, `X` acts by `p`, so `ω_n = (1 + X) ^ p ^ n - 1`
acts injectively with cokernel of order `p ^ (n + 1)`: the resultant `Res(X - p, ω_n)` is
`(1 + p) ^ p ^ n - 1`, of `p`-adic valuation `n + 1`. On `Λ ⧸ (X)` the resultant `Res(X, ω_n)` is
`ω_n(0) = 0`, and the cokernel of `ω_n` is infinite. -/

section Examples

open Polynomial
open scoped PowerSeries

example (p : ℕ) [Fact p.Prime] (hp : Odd p) (n : ℕ) :
    Submodule.torsionBy ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {((X - C (p : ℤ_[p]) : ℤ_[p][X]) :
      ℤ_[p]⟦X⟧)}) (((X + 1) ^ p ^ n - 1 : ℤ_[p][X]) : ℤ_[p]⟦X⟧) = ⊥ ∧
    Nat.card (QuotSMulTop (((X + 1) ^ p ^ n - 1 : ℤ_[p][X]) : ℤ_[p]⟦X⟧)
      (ℤ_[p]⟦X⟧ ⧸ Ideal.span {((X - C (p : ℤ_[p]) : ℤ_[p][X]) : ℤ_[p]⟦X⟧)})) = p ^ (n + 1) := by
  have hG : (X - C (p : ℤ_[p])).IsDistinguishedAt (maximalIdeal ℤ_[p]) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_X_sub_C _⟩
    rw [natDegree_X_sub_C, Nat.lt_one_iff] at hk
    subst hk
    simp [PadicInt.maximalIdeal_eq_span_p]
  have H := hG.isWeierstrassFactorizationAt
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpos : 0 < (p + 1) ^ p ^ n - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (pow_ne_zero n hp0) (by omega))
  -- The norm of `ω_n` is the integer `(1 + p) ^ p ^ n - 1`.
  have hnorm : Algebra.norm ℤ_[p]
      (Ideal.Quotient.mk (Ideal.span {((X - C (p : ℤ_[p]) : ℤ_[p][X]) : ℤ_[p]⟦X⟧)})
        (((X + 1) ^ p ^ n - 1 : ℤ_[p][X]) : ℤ_[p]⟦X⟧)) = (((p + 1) ^ p ^ n - 1 : ℕ) : ℤ_[p]) := by
    rw [H.norm_mk_coe_eq_resultant, natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp
  -- Lifting the exponent: `v_p((1 + p) ^ p ^ n - 1) = v_p(p) + v_p(p ^ n) = 1 + n`.
  have hval : padicValNat p ((p + 1) ^ p ^ n - 1) = n + 1 := by
    have h := Nat.multiplicity_pow_sub_pow hp (x := p + 1) (y := 1) (by omega) (by simp)
      (by simp [Nat.dvd_add_right (dvd_refl p), (Fact.out : p.Prime).one_lt.ne'])
      (pow_ne_zero n hp0)
    rw [one_pow, Nat.add_sub_cancel, Nat.Prime.multiplicity_self,
      multiplicity_pow_self_of_prime (Nat.prime_iff.mp Fact.out)] at h
    rw [Nat.padicValNat_def, h, add_comm]
  have hne : (((p + 1) ^ p ^ n - 1 : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  refine ⟨(H.torsionBy_eq_bot_iff _).mpr (hnorm ▸ hne), ?_⟩
  rw [H.natCard_quotSMulTop (hnorm ▸ hne), hnorm, PadicInt.natCard_quotient_span hne,
    PadicInt.valuation_natCast, hval]

example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Infinite (QuotSMulTop (((X + 1) ^ p ^ n - 1 : ℤ_[p][X]) : ℤ_[p]⟦X⟧)
      (ℤ_[p]⟦X⟧ ⧸ Ideal.span {((X : ℤ_[p][X]) : ℤ_[p]⟦X⟧)})) := by
  have hG : (X : ℤ_[p][X]).IsDistinguishedAt (maximalIdeal ℤ_[p]) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_X⟩
    rw [natDegree_X, Nat.lt_one_iff] at hk
    simp [hk]
  have H := hG.isWeierstrassFactorizationAt
  refine TauCeti.Algebra.infinite_quotSMulTop_of_norm_eq_zero (A := ℤ_[p]) ?_
  have hres := resultant_X_pow_left (((X + 1) ^ p ^ n - 1 : ℤ_[p][X])) 1 _ le_rfl
  rw [pow_one] at hres
  rw [Ideal.Quotient.algebraMap_eq, H.norm_mk_coe_eq_resultant, natDegree_X, hres]
  simp [coeff_zero_eq_eval_zero]

end Examples
