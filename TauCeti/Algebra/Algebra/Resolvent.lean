/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Algebraic identities for the resolvent

For an element `a` of an `R`-algebra `A`, Mathlib's resolvent is `resolvent a r = (r1 - a)⁻¹`,
with the junk value `0` on the spectrum. This file records two algebraic identities used when
integrating resolvents: on the resolvent set, multiplication by the scalar `r` gives
`r (r1 - a)⁻¹ = 1 + a (r1 - a)⁻¹`, and every element commuting with `a` commutes with all
resolvents of `a`.
-/

public section

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

namespace spectrum

/-- On the resolvent set, `r (r1 - a)⁻¹ = 1 + a (r1 - a)⁻¹`. -/
theorem smul_resolvent_eq_one_add_mul_resolvent {a : A} {r : R} (hr : r ∈ resolventSet R a) :
    r • resolvent a r = 1 + a * resolvent a r := by
  have h := Ring.mul_inverse_cancel _ (mem_resolventSet_iff.mp hr)
  rw [← resolvent, sub_mul, ← Algebra.smul_def, sub_eq_iff_eq_add] at h
  exact h

end spectrum

/-- An element commuting with `a` commutes with every resolvent of `a`. -/
theorem Commute.resolvent_right {a b : A} (h : Commute b a) (r : R) :
    Commute b (resolvent a r) := by
  have h' : Commute b (algebraMap R A r - a) := (Algebra.commute_algebraMap_right r b).sub_right h
  rw [resolvent]
  by_cases hu : IsUnit (algebraMap R A r - a)
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at h' ⊢
    rw [Ring.inverse_unit]
    exact h'.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right b
