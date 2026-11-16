/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.QuotSMulTop

import TauCeti.LinearAlgebra.FreeModule.CardQuotient

/-!
# Kernel and cokernel of multiplication in a finite free algebra

Let `S` be a commutative `A`-algebra that is free of finite rank as an `A`-module, and let `R` be
a commutative ring acting on `S` through an algebra map `R → S` compatible with `A`. Multiplication
by `r : R` on `S` is the `A`-linear endomorphism `Algebra.lmul A S` of the image of `r`, whose
determinant is the norm over `A` of that image. This file reads the kernel `S[r]` and the cokernel
`S ⧸ r S` off that norm:

* over a domain, `S[r] = 0` exactly when the norm is nonzero;
* over a principal ideal domain, when the norm is nonzero, `S ⧸ r S` has as many elements as
  `A ⧸ (norm)`;
* over an infinite domain, when the norm vanishes, `S ⧸ r S` is infinite;
* over an infinite principal ideal domain with finite quotients, such as a discrete valuation ring
  with finite residue field, `S ⧸ r S` is finite exactly when the norm is nonzero.

Taking `R = S` gives multiplication by an element of `S` itself; taking `S = R ⧸ J` gives
multiplication by an element of `R` on a quotient ring that is finite free over `A`.

## Main results

* `TauCeti.Algebra.restrictScalars_smul_top_eq_range_lmul`: the submodule `r S`, viewed over `A`,
  is the range of multiplication by the image of `r`.
* `TauCeti.Algebra.torsionBy_eq_bot_iff_norm_ne_zero`: `S[r] = 0` iff the norm of `r` is nonzero.
* `TauCeti.Algebra.natCard_quotSMulTop_of_norm_ne_zero`: if the norm of `r` is nonzero,
  `#(S ⧸ r S) = #(A ⧸ (norm r))`.
* `TauCeti.Algebra.infinite_quotSMulTop_of_norm_eq_zero`: if the norm of `r` vanishes and `A` is
  infinite, `S ⧸ r S` is infinite.
* `TauCeti.Algebra.finite_quotSMulTop_iff_norm_ne_zero`: over an infinite principal ideal domain
  with finite quotients, `S ⧸ r S` is finite iff the norm of `r` is nonzero.
-/

public section

open scoped Pointwise

namespace TauCeti.Algebra

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A S] [Algebra R S]

variable [Algebra A R] [IsScalarTower A R S] in
/-- The submodule `r S`, viewed over `A`, is the range of multiplication by the image of `r`. -/
theorem restrictScalars_smul_top_eq_range_lmul (r : R) :
    (r • ⊤ : Submodule R S).restrictScalars A =
      LinearMap.range (Algebra.lmul A S (algebraMap R S r)) := by
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, Algebra.smul_def, Ideal.mem_span_singleton',
    mul_comm]

variable [Module.Free A S] [Module.Finite A S]

/-- **Kernel of multiplication in a finite free algebra.** Over a domain `A`, multiplication by
`r` on a finite free `A`-algebra `S` is injective exactly when the norm over `A` of the image of
`r` in `S` is nonzero. -/
theorem torsionBy_eq_bot_iff_norm_ne_zero [IsDomain A] (r : R) :
    Submodule.torsionBy R S r = ⊥ ↔ Algebra.norm A (algebraMap R S r) ≠ 0 := by
  rw [Algebra.norm_apply, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot', Submodule.eq_bot_iff]
  simp [Submodule.mem_torsionBy_iff, Algebra.smul_def]

variable [Algebra A R] [IsScalarTower A R S]

/-- **Cokernel of multiplication in a finite free algebra.** Over a principal ideal domain `A`, if
the norm over `A` of the image of `r` in a finite free `A`-algebra `S` is nonzero, then `S` modulo
`r` has as many elements as `A` modulo that norm. -/
theorem natCard_quotSMulTop_of_norm_ne_zero [IsDomain A] [IsPrincipalIdealRing A] {r : R}
    (hr : Algebra.norm A (algebraMap R S r) ≠ 0) :
    Nat.card (QuotSMulTop r S) = Nat.card (A ⧸ Ideal.span {Algebra.norm A (algebraMap R S r)}) := by
  rw [Algebra.norm_apply] at hr ⊢
  rw [← LinearMap.card_quotient_range_eq_card_quotient_span_det hr,
    ← restrictScalars_smul_top_eq_range_lmul]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv A _).toEquiv.symm

omit [Module.Free A S] [Module.Finite A S] in
/-- **Infinite cokernel in an algebra.** Over an infinite domain `A`, if the norm over
`A` of the image of `r` in an `A`-algebra `S` vanishes, then `S` modulo `r` is infinite. -/
theorem infinite_quotSMulTop_of_norm_eq_zero [IsDomain A] [Infinite A] {r : R}
    (hr : Algebra.norm A (algebraMap R S r) = 0) : Infinite (QuotSMulTop r S) := by
  rw [Algebra.norm_apply] at hr
  have := LinearMap.infinite_quotient_range_of_det_eq_zero hr
  rw [← restrictScalars_smul_top_eq_range_lmul] at this
  exact Infinite.of_injective _ (Submodule.Quotient.restrictScalarsEquiv A _).injective

/-- **Finite cokernels in a finite free algebra.** If `A` is an infinite principal ideal domain
whose quotients by nonzero ideals are finite, for instance a discrete valuation ring with finite
residue field, then a finite free `A`-algebra `S` modulo `r` is finite exactly when the norm over
`A` of the image of `r` in `S` is nonzero. -/
theorem finite_quotSMulTop_iff_norm_ne_zero [IsDomain A] [IsPrincipalIdealRing A] [Infinite A]
    [Ring.HasFiniteQuotients A] (r : R) :
    Finite (QuotSMulTop r S) ↔ Algebra.norm A (algebraMap R S r) ≠ 0 := by
  refine ⟨fun hfin hr ↦ ?_, fun hr ↦ ?_⟩
  · exact not_finite_iff_infinite.mpr (infinite_quotSMulTop_of_norm_eq_zero hr) hfin
  · have := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hr)
    refine Nat.finite_of_card_ne_zero ?_
    rw [natCard_quotSMulTop_of_norm_ne_zero hr]
    exact Nat.card_pos.ne'

end TauCeti.Algebra
