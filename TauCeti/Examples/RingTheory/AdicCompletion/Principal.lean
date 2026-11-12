/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.AdicCompletion.Completeness
import TauCeti.RingTheory.AdicCompletion.Principal

/-!
# Checks for completeness for principal subideals

These examples exercise completeness for a product of two formal parameters, arbitrary
modules, and zero generators. In particular, the product of two parameters is not a
parameter for the original adic topology; cofinality is not the hypothesis of the theorem.
-/

open MvPowerSeries

namespace TauCeti.Examples

variable (A : Type*) [CommRing A]

-- A genuinely smaller principal ideal inside the two-variable ideal of definition.
example : IsAdicComplete
    (Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) : MvPowerSeries (Fin 2) A)})
    (MvPowerSeries (Fin 2) A) := by
  apply IsAdicComplete.span_singleton_of_mem
    (I := Ideal.span (Set.range (X (R := A) : Fin 2 → MvPowerSeries (Fin 2) A)))
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)

-- No nonzerodivisor assumption: multiplication by the new generator can be zero.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [IsAdicComplete I M] : IsAdicComplete (Ideal.span {(0 : R)}) M :=
  IsAdicComplete.span_singleton_of_mem (I.zero_mem)

-- The result is a module theorem, not just a theorem about rings.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {π a : R}
    [IsAdicComplete (Ideal.span {π}) M] : IsAdicComplete (Ideal.span {π * a}) M :=
  IsAdicComplete.span_singleton_of_dvd (dvd_mul_right π a)

-- The series statement gives divisibility of every remainder, not just an I-adic limit.
example {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {r : R} (hr : r ∈ I) (c : ℕ → R) : ∃ L : R, ∀ n,
      r ^ n ∣ L - ∑ j ∈ Finset.range n, r ^ j * c j := by
  obtain ⟨L, hL⟩ := IsAdicComplete.exists_smodEq_sum_range hr c
  refine ⟨L, fun n ↦ ?_⟩
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using (hL n).symm

end TauCeti.Examples
