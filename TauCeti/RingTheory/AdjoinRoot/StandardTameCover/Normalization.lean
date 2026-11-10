/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.ReducedDivisor
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normalization in products of standard tame covers

A finite product of standard tame covers is finite free over the base. If `f` is a
nonzerodivisor and `A/(f)` is reduced, the product is also the integral closure of `A` in
its localization at `f`. Thus normalization does not change the standard local models,
and their structural morphisms are finite locally free.

The normalization assertion does not require the base to be normal, regular, or
Noetherian. It uses the reduced inverse image of `(f)`: its ideal has a nonzerodivisor
generator, even when the exponents differ among the factors.

## References

* The Stacks Project, Lemma 58.31.6, https://stacks.math.columbia.edu/tag/0EYH.
-/

public section

open Polynomial

namespace TauCeti

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {f : A}

/-- A finite product of standard tame covers is finite over the base. -/
theorem IsFiniteProductOfStandardTameCovers.finite
    (h : IsFiniteProductOfStandardTameCovers A C f) : Module.Finite A C := by
  obtain ⟨ι, _, e, he, -, ⟨σ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  have (i : ι) : Module.Finite A (standardTameCover A f (e i)) :=
    (monic_X_pow_sub_C f (Nat.ne_of_gt (he i))).finite_adjoinRoot
  exact Module.Finite.equiv σ.symm.toLinearEquiv

/-- A finite product of standard tame covers is free over the base, including the empty
product and the zero base ring. -/
theorem IsFiniteProductOfStandardTameCovers.free
    (h : IsFiniteProductOfStandardTameCovers A C f) : Module.Free A C := by
  obtain ⟨ι, _, e, he, -, ⟨σ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  have (i : ι) : Module.Free A (standardTameCover A f (e i)) :=
    (monic_X_pow_sub_C f (Nat.ne_of_gt (he i))).free_adjoinRoot
  exact Module.Free.of_equiv σ.symm.toLinearEquiv

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

end TauCeti
