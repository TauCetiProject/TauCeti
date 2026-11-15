/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearPMap.Shift
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Negation and scalar shifts of unbounded operators

For an unbounded operator `A`, subtracting the scalar operator `omega I` leaves its domain
unchanged and translates its resolvent:

`R(lambda, A - omega I) = R(lambda + omega, A)`.

Negating an operator reflects its resolvent parameter and negates its resolvent.
This requires a topological additive group so that the negative of a continuous linear map
is continuous. The negation results hold over any ring.

This file also develops the characteristic resolvent API of the generic scalar shift from
`TauCeti.LinearAlgebra.LinearPMap.Shift`. The scalar-shift results apply to modules over a
commutative ring with only a topology on the module; no norm or continuity assumptions on
addition or scalar multiplication are needed.
The construction is independent of semigroups; in particular, it can be used for an operator
not yet known to generate one.

## Main results

* `LinearPMap.isResolventAt_neg_iff`: reflection of continuous inverses under negation.
* `LinearPMap.mem_resolventSet_neg_iff`: reflection of the resolvent set under negation.
* `LinearPMap.resolvent_neg`: reflection of the resolvent under negation.
* `TauCeti.LinearPMap.mem_resolventSet_subScalar_iff`: translation of the resolvent set.
* `TauCeti.LinearPMap.resolvent_subScalar`: translation of the resolvent itself.
-/

public section

noncomputable section

namespace LinearPMap

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X]

/-- Negating an operator and its resolvent parameter negates the continuous inverse. -/
@[simp]
theorem isResolventAt_neg_iff {A : X →ₗ.[𝕜] X} {z : 𝕜} {R : X →L[𝕜] X} :
    IsResolventAt (-A) (-z) R ↔ IsResolventAt A z (-R) := by
  have hneg {T : X →ₗ.[𝕜] X} {w : 𝕜} {S : X →L[𝕜] X}
      (h : IsResolventAt T w S) : IsResolventAt (-T) (-w) (-S) := by
    refine ⟨fun y => T.domain.neg_mem (h.mem_domain y), fun y => ?_, fun x => ?_⟩
    · have hT : T ⟨-S y, T.domain.neg_mem (h.mem_domain y)⟩ =
          -T ⟨S y, h.mem_domain y⟩ := T.map_neg ⟨_, h.mem_domain y⟩
      simpa only [_root_.neg_apply, LinearPMap.neg_apply, hT, neg_smul, smul_neg, neg_neg]
        using h.smul_sub_apply y
    · have heq : (-w) • (x : X) - (-T) x = -(w • (x : X) - T x) := by
        simp only [LinearPMap.neg_apply, neg_smul]
        abel
      simpa only [heq, _root_.neg_apply, _root_.map_neg, neg_neg] using
        h.apply_smul_sub x
  constructor <;> intro h <;> simpa only [neg_neg] using hneg h

/-- Negation reflects the resolvent set through zero. -/
@[simp]
theorem mem_resolventSet_neg_iff {A : X →ₗ.[𝕜] X} {z : 𝕜} :
    -z ∈ (-A).resolventSet ↔ z ∈ A.resolventSet := by
  simp only [mem_resolventSet_iff, isResolventAt_neg_iff]
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨-R, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨-R, by simpa only [neg_neg] using hR⟩

/-- The resolvent of the negative operator is the negative of the reflected resolvent. -/
@[simp]
theorem resolvent_neg {A : X →ₗ.[𝕜] X} {z : 𝕜} (hz : z ∈ A.resolventSet) :
    resolvent (-A) (-z) = -resolvent A z := by
  apply resolvent_eq_of_isResolventAt
  apply isResolventAt_neg_iff.mpr
  simpa only [neg_neg] using isResolventAt_resolvent hz

end LinearPMap

namespace TauCeti.LinearPMap

open _root_.LinearPMap (
  IsResolventAt isResolventAt_resolvent mem_resolventSet_iff resolvent_eq_of_isResolventAt
  subScalar subScalar_apply)

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
