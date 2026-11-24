/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.ReducedDivisor

import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.Polynomial.Eisenstein.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.OfQuotient
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Normalization of standard tame covers

This file proves two normalization results for standard tamely ramified covers along a divisor
`f`:

1. **Products of standard tame covers in their localization away from `f`.** If `f` is a
   nonzerodivisor and `A/(f)` is reduced, a finite product of standard tame covers is the integral
   closure of `A` in its localization at `f`. Thus normalization does not change the standard local
   models. Their finiteness and freeness over the base are proved in
   `TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic`, as
   `IsFiniteProductOfStandardTameCovers.finite` and `IsFiniteProductOfStandardTameCovers.free`.
   This normalization assertion does not require the base to be normal, regular, or Noetherian; it
   uses the reduced inverse image of `(f)`, whose ideal has a nonzerodivisor generator even when
   the exponents differ among the factors.

2. **Single-component normalization over a regular-divisor local base.** When `A` is a Noetherian
   local ring and `f ∈ 𝔪_A` is a nonzerodivisor with `A ⧸ (f)` regular, both `A` and every
   positive-degree cover `A[x]/(x^n − f)` are regular local rings (Stacks 00NU), hence integrally
   closed domains (Stacks 0567), and `(f)` is prime. By Eisenstein's criterion at `(f)`,
   `X^n − f` is the minimal polynomial over `A` of any `n`-th root `γ` of `f` generating a field
   extension `L = K(γ)` of a fraction field `K` of `A`, identifying `A[x]/(x^n − f)` with
   `A[γ] = integralClosure A L`.

## Main results

* `TauCeti.IsFiniteProductOfStandardTameCovers.isIntegralClosure`: a finite product of standard
  tame covers along a nonzerodivisor with reduced quotient is the integral closure of `A` in its
  localization away from `f`.
* `TauCeti.standardTameCoverIntegralClosureAlgEquiv`: canonical `A`-algebra equivalence
  `A[x]/(x^n − f) ≃ₐ[A] integralClosure A L` sending the root `x` to `γ`, together with its
  evaluation lemmas `TauCeti.coe_standardTameCoverIntegralClosureAlgEquiv_root` and
  `TauCeti.standardTameCoverIntegralClosureAlgEquiv_symm_mk`.

## References

* [The Stacks Project, Lemma 58.31.6](https://stacks.math.columbia.edu/tag/0EYH).
* [The Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU).
* [The Stacks Project, Lemma 10.157.5](https://stacks.math.columbia.edu/tag/0567).
-/

public section

open IntermediateField IsLocalRing Polynomial

namespace TauCeti

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {f : A}

/-- A finite product of standard tame covers along a nonzerodivisor with reduced quotient
is the integral closure of the base in its localization away from that element.
In particular, this applies to a regular divisor and allows different exponents in the
factors. -/
@[stacks 0EYH "normalization of the standard local models"]
theorem IsFiniteProductOfStandardTameCovers.isIntegralClosure
    (h : IsFiniteProductOfStandardTameCovers A C f) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span {f})] (Cf : Type*) [CommRing Cf] [Algebra C Cf]
    [IsLocalization.Away (algebraMap A C f) Cf] [Algebra A Cf] [IsScalarTower A C Cf] :
    IsIntegralClosure C A Cf := by
  have := h.finite
  obtain ⟨ι, _, g, hg, hrad, -⟩ := h.exists_radical_span_eq_and_quotient_algEquiv hf
  have : IsIntegrallyClosedIn C Cf :=
    IsIntegrallyClosedIn.of_isLocalization_away_of_radical_eq_span hg hrad
  exact IsIntegralClosure.of_isIntegrallyClosedIn

section SingleComponent

variable [IsNoetherianRing A] [IsLocalRing A] [IsRegularRing (A ⧸ Ideal.span {f})]
  {K L : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- **Single-component normalization along a regular divisor.** If `L = K(γ)` is generated over a
fraction field `K` of `A` by an `n`-th root `γ` of `f ∈ 𝔪_A`, then the standard cover
`A[x]/(x^n − f)` is canonically `A`-isomorphic to `integralClosure A L`, sending the root `x` to
`γ`. -/
noncomputable def standardTameCoverIntegralClosureAlgEquiv (hf : f ∈ maximalIdeal A)
    (hf₀ : f ∈ nonZeroDivisors A) {n : ℕ} {γ : L} (hγ : γ ^ n = algebraMap A L f)
    (hgen : K⟮γ⟯ = ⊤) :
    standardTameCover A f n ≃ₐ[A] integralClosure A L := by
  have hf_nu : ¬ IsUnit f := (mem_maximalIdeal f).mp hf
  have : _root_.IsRegularLocalRing A :=
    TauCeti.IsRegularLocalRing.of_isRegularRing_quotient_nonZeroDivisor A hf hf₀
  have : (Ideal.span {f}).IsPrime :=
    (Ideal.span {f}).isPrime_of_isRegularRing_quotient (Ideal.span_singleton_eq_top.not.mpr hf_nu)
  have := FaithfulSMul.trans A K L
  have hn : n ≠ 0 :=
    Algebra.ne_zero_of_pow_eq_algebraMap_of_injective (a := f)
      (FaithfulSMul.algebraMap_injective A L) (fun h1 ↦ hf_nu (h1 ▸ isUnit_one)) hγ
  have hγ_int : IsIntegral A γ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hγ ▸ isIntegral_algebraMap)
  have hf_notMem_sq : f ∉ Ideal.span {f} ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    exact hf_nu <| isUnit_iff_exists_inv.mpr ⟨c,
      mul_left_cancel₀ (nonZeroDivisors.ne_zero hf₀) (by rw [mul_one, ← mul_assoc, ← sq, ← hc])⟩
  have heis : (X ^ n - Polynomial.C f).IsEisensteinAt (Ideal.span {f}) :=
    isEisensteinAt_X_pow_sub_C (Ideal.mem_span_singleton_self f) hf_notMem_sq
      (Nat.pos_of_ne_zero hn)
  have hmin : X ^ n - Polynomial.C f = minpoly A γ :=
    (eq_of_monic_of_associated (minpoly.monic hγ_int) (monic_X_pow_sub_C f hn)
      (heis.associated_minpoly (by rw [(monic_X_pow_sub_C f hn).leadingCoeff]; exact isUnit_one)
        (by simp [Polynomial.IsRoot, hγ]))).symm
  have : Module.Finite A (Algebra.adjoin A ({γ} : Set L)) :=
    have : Module.Finite A (standardTameCover A f n) := (monic_X_pow_sub_C f hn).finite_adjoinRoot
    Module.Finite.equiv
      ((AdjoinRoot.algEquivOfEq A _ _ hmin).trans (minpoly.equivAdjoin hγ_int)).toLinearEquiv
  have : IsIntegrallyClosed (Algebra.adjoin A ({γ} : Set L)) :=
    have := standardTameCover_isIntegrallyClosed hf hf₀ hn
    IsIntegrallyClosed.of_equiv
      ((AdjoinRoot.algEquivOfEq A _ _ hmin).trans (minpoly.equivAdjoin hγ_int)).toRingEquiv
  have : IsFractionRing (Algebra.adjoin A ({γ} : Set L)) L :=
    IntermediateField.isFractionRing_algebra_adjoin_of_adjoin_eq_top hgen
  exact ((AdjoinRoot.algEquivOfEq A _ _ hmin).trans (minpoly.equivAdjoin hγ_int)).trans
    (IsIntegralClosure.equiv A (Algebra.adjoin A ({γ} : Set L)) L (integralClosure A L))

/-- `standardTameCoverIntegralClosureAlgEquiv` sends the root of `X^n − f` to `γ`. -/
@[simp]
theorem coe_standardTameCoverIntegralClosureAlgEquiv_root (hf : f ∈ maximalIdeal A)
    (hf₀ : f ∈ nonZeroDivisors A) {n : ℕ} {γ : L} (hγ : γ ^ n = algebraMap A L f)
    (hgen : K⟮γ⟯ = ⊤) :
    (standardTameCoverIntegralClosureAlgEquiv hf hf₀ hγ hgen (AdjoinRoot.root _) : L) = γ := by
  have h1 {_ : IsIntegralClosure (Algebra.adjoin A ({γ} : Set L)) A L}
      (x : Algebra.adjoin A ({γ} : Set L)) :
      (IsIntegralClosure.equiv A (Algebra.adjoin A ({γ} : Set L)) L (integralClosure A L) x : L) =
        (x : L) :=
    IsIntegralClosure.algebraMap_equiv A (Algebra.adjoin A ({γ} : Set L)) L (integralClosure A L) x
  rw [standardTameCoverIntegralClosureAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1,
    AdjoinRoot.algEquivOfEq_root]
  simp

/-- The inverse of `standardTameCoverIntegralClosureAlgEquiv` sends `⟨γ, hγ_mem⟩` to the root of
`X^n − f`. -/
@[simp]
theorem standardTameCoverIntegralClosureAlgEquiv_symm_mk (hf : f ∈ maximalIdeal A)
    (hf₀ : f ∈ nonZeroDivisors A) {n : ℕ} {γ : L} (hγ : γ ^ n = algebraMap A L f)
    (hgen : K⟮γ⟯ = ⊤) (hγ_mem : γ ∈ integralClosure A L) :
    (standardTameCoverIntegralClosureAlgEquiv hf hf₀ hγ hgen).symm ⟨γ, hγ_mem⟩ =
      AdjoinRoot.root _ := by
  rw [AlgEquiv.symm_apply_eq]
  exact Subtype.ext (coe_standardTameCoverIntegralClosureAlgEquiv_root hf hf₀ hγ hgen).symm

end SingleComponent

end TauCeti
