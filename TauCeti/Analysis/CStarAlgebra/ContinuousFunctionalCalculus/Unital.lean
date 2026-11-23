/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Products with the element in the continuous functional calculus

For an element `a` satisfying the predicate of a continuous functional calculus and a function `f`
continuous on its spectrum, multiplying `cfc f a` by `a` on either side is the functional calculus
of `f` multiplied by the identity on the same side. These are the cases `g = id` of Mathlib's
`cfc_mul`, stated in the form of `cfc_pow_id` and `cfc_smul_id`.

## Main results

* `TauCeti.cfc_id_mul`: `cfc (fun x ↦ x * f x) a = a * cfc f a`.
* `TauCeti.cfc_mul_id`: `cfc (fun x ↦ f x * x) a = cfc f a * a`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- The functional calculus of `x ↦ x * f x` at `a` is `a * cfc f a`. -/
theorem cfc_id_mul (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (fun x ↦ x * f x) a = a * cfc f a := by
  rw [cfc_mul (fun x ↦ x) f a, cfc_id' R a]

/-- The functional calculus of `x ↦ f x * x` at `a` is `cfc f a * a`. -/
theorem cfc_mul_id (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (fun x ↦ f x * x) a = cfc f a * a := by
  rw [cfc_mul f (fun x ↦ x) a, cfc_id' R a]

end TauCeti
