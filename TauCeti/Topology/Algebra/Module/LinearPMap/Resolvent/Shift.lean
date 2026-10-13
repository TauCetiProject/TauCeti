/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearPMap.Shift
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Scalar shifts of unbounded operators

For an unbounded operator `A`, subtracting the scalar operator `omega I` leaves its domain
unchanged and translates its resolvent:

`R(lambda, A - omega I) = R(lambda + omega, A)`.

This file develops the characteristic resolvent API of the generic scalar shift from
`TauCeti.LinearAlgebra.LinearPMap.Shift`. The results apply to modules over a commutative ring
with only a topology on the module; no norm or continuity assumptions on addition or scalar
multiplication are needed.
The construction is independent of semigroups; in particular, it can be used for an operator
not yet known to generate one.

## Main results

* `TauCeti.LinearPMap.mem_resolventSet_subScalar_iff`: translation of the resolvent set.
* `TauCeti.LinearPMap.resolvent_subScalar`: translation of the resolvent itself.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

open _root_.LinearPMap (
  IsResolventAt isResolventAt_resolvent mem_resolventSet_iff resolvent_eq_of_isResolventAt)

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]

/-- An inverse for `lambda I - (A - omega I)` is the same as an inverse for
`(lambda + omega) I - A`. -/
@[simp]
theorem isResolventAt_subScalar_iff {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜}
    {R : X →L[𝕜] X} :
    IsResolventAt (subScalar A omega) lambda R ↔ IsResolventAt A (lambda + omega) R := by
  have hshift (x : X) (hx : x ∈ (subScalar A omega).domain) :
      lambda • x - subScalar A omega ⟨x, hx⟩ =
        (lambda + omega) • x - A ⟨x, by simpa using hx⟩ := by
    rw [subScalar_apply]
    module
  constructor
  · intro h
    refine ⟨fun y => by simpa using h.mem_domain y, fun y => ?_, fun x => ?_⟩
    · simpa only [hshift] using h.smul_sub_apply y
    · rw [← hshift (x : X) (by simp)]
      exact h.apply_smul_sub ⟨x, by simp⟩
  · intro h
    refine ⟨fun y => by simpa using h.mem_domain y, fun y => ?_, fun x => ?_⟩
    · simpa only [hshift] using h.smul_sub_apply y
    · simpa only [hshift] using h.apply_smul_sub ⟨x, by simpa using x.property⟩

/-- Translation of the resolvent set under the scalar shift `A ↦ A - omega I`. -/
@[simp]
theorem mem_resolventSet_subScalar_iff {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜} :
    lambda ∈ (subScalar A omega).resolventSet ↔ lambda + omega ∈ A.resolventSet := by
  simp only [mem_resolventSet_iff, isResolventAt_subScalar_iff]

/-- Exact translation of the resolvent under the scalar shift `A ↦ A - omega I`. -/
@[simp]
theorem resolvent_subScalar {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜}
    (hlambda : lambda + omega ∈ A.resolventSet) :
    (subScalar A omega).resolvent lambda = A.resolvent (lambda + omega) := by
  apply resolvent_eq_of_isResolventAt
  have h := isResolventAt_resolvent hlambda
  exact (isResolventAt_subScalar_iff (A := A) (omega := omega)).mpr h

end TauCeti.LinearPMap

end
