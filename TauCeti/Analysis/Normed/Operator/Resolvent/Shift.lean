/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearPMap.Shift
public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Scalar shifts of unbounded operators

For an unbounded operator `A`, subtracting the scalar operator `omega I` leaves its domain
unchanged and translates its resolvent:

`R(lambda, A - omega I) = R(lambda + omega, A)`.

This file develops the characteristic resolvent API of the generic scalar shift from
`TauCeti.LinearAlgebra.LinearPMap.Shift`, over an arbitrary nontrivially normed field — the
generality of `TauCeti.LinearPMap.resolventSet` itself, so that a complex shift of a complex
unbounded operator is covered.  The construction is independent of semigroups; in particular, it
can be used for an operator not yet known to generate one.

## Main results

* `TauCeti.LinearPMap.mem_resolventSet_subScalar_iff`: translation of the resolvent set.
* `TauCeti.LinearPMap.resolvent_subScalar`: translation of the resolvent itself.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- An inverse for `lambda I - (A - omega I)` is the same as an inverse for
`(lambda + omega) I - A`. -/
@[simp]
theorem isResolventAt_subScalar_iff {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜}
    {R : X →L[𝕜] X} :
    IsResolventAt (subScalar A omega) lambda R ↔ IsResolventAt A (lambda + omega) R := by
  constructor
  · intro h
    refine
      { mem_domain := fun y => by simpa using h.mem_domain y
        smul_sub_apply := fun y => ?_
        apply_smul_sub := fun x => ?_ }
    · calc
        (lambda + omega) • R y - A ⟨R y, by simpa using h.mem_domain y⟩ =
            lambda • R y - subScalar A omega
              ⟨R y, h.mem_domain y⟩ := by
          rw [subScalar_apply]
          module
        _ = y := h.smul_sub_apply y
    · calc
        R ((lambda + omega) • (x : X) - A x) =
            R (lambda • (x : X) - subScalar A omega
              ⟨x, by simp⟩) := by
          congr 1
          rw [subScalar_apply]
          module
        _ = (x : X) := h.apply_smul_sub ⟨x, by simp⟩
  · intro h
    refine
      { mem_domain := fun y => by simpa using h.mem_domain y
        smul_sub_apply := fun y => ?_
        apply_smul_sub := fun x => ?_ }
    · calc
        lambda • R y - subScalar A omega ⟨R y, by simpa using h.mem_domain y⟩ =
            (lambda + omega) • R y - A ⟨R y, h.mem_domain y⟩ := by
          rw [subScalar_apply]
          module
        _ = y := h.smul_sub_apply y
    · calc
        R (lambda • (x : X) - subScalar A omega x) =
            R ((lambda + omega) • (x : X) - A ⟨x, by simpa using x.property⟩) := by
          congr 1
          rw [subScalar_apply]
          module
        _ = (x : X) := h.apply_smul_sub ⟨x, by simpa using x.property⟩

/-- Translation of the resolvent set under the scalar shift `A ↦ A - omega I`. -/
@[simp]
theorem mem_resolventSet_subScalar_iff {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜} :
    lambda ∈ resolventSet (subScalar A omega) ↔ lambda + omega ∈ resolventSet A := by
  rw [mem_resolventSet_iff, mem_resolventSet_iff]
  constructor <;> rintro ⟨R, hR⟩ <;> refine ⟨R, ?_⟩
  · exact isResolventAt_subScalar_iff.mp hR
  · exact isResolventAt_subScalar_iff.mpr hR

/-- Exact translation of the resolvent under the scalar shift `A ↦ A - omega I`. -/
@[simp]
theorem resolvent_subScalar {A : X →ₗ.[𝕜] X} {omega lambda : 𝕜}
    (hlambda : lambda + omega ∈ resolventSet A) :
    resolvent (subScalar A omega) lambda = resolvent A (lambda + omega) := by
  apply resolvent_eq_of_isResolventAt
  have h := isResolventAt_resolvent hlambda
  exact (isResolventAt_subScalar_iff (A := A) (omega := omega)).mpr h

end TauCeti.LinearPMap

end
