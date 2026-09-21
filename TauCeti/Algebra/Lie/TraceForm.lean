/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm

/-!
# Identities for the trace form of a Lie module

Let `M` be a representation of a Lie algebra `L` over a commutative ring `R`. Its trace form
`B = LieModule.traceForm R L M` is symmetric and invariant, `B ⁅a, b⁆ c = B a ⁅b, c⁆`. Together
with the Leibniz rule those two properties give an identity in four elements,

```text
B ⁅a, b⁆ ⁅c, d⁆ + B ⁅b, c⁆ ⁅a, d⁆ + B ⁅c, a⁆ ⁅b, d⁆ = 0,
```

which is the Jacobi identity rewritten so that each summand pairs two brackets against each other
rather than iterating them. No hypothesis at all is needed on the four elements: this is a
consequence of invariance and symmetry, and it holds in every Lie algebra.

Its purpose is downstream: when `a`, `b`, `c`, `d` are root vectors of a split semisimple Lie
algebra and `B` is the Killing form, each summand evaluates to a product of two structure
constants weighted by the Killing pairing of an opposite pair of root vectors, and the identity
becomes the four-term relation between the structure constants. Grouping the brackets in pairs is
exactly what makes that evaluation possible, since a summand with an iterated bracket would mix
root spaces of three different roots.

A second, unrelated identity is collected here: over a reduced ring the trace form kills a pair
that brackets to zero as soon as one of the two acts nilpotently, because the composite of the two
actions is then nilpotent and a nilpotent scalar in a reduced ring is zero. Specialized to the
adjoint representation this says that an ad-nilpotent element is Killing-orthogonal to its own
centraliser.

## Main results

* `TauCeti.traceForm_lie_lie_cyclic_eq_zero`: the four-element cyclic identity above.
* `TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero`: elements bracketing to zero, one of
  them acting nilpotently, are orthogonal for the trace form.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.1.
-/

public section

namespace TauCeti

open LieModule

section Cyclic

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The four-element cyclic identity for an invariant trace form.** Pairing the three ways of
splitting `a`, `b`, `c`, `d` into two brackets, with `d` always in the second, gives zero. -/
theorem traceForm_lie_lie_cyclic_eq_zero (a b c d : L) :
    traceForm R L M ⁅a, b⁆ ⁅c, d⁆ + traceForm R L M ⁅b, c⁆ ⁅a, d⁆ +
      traceForm R L M ⁅c, a⁆ ⁅b, d⁆ = 0 := by
  have h₁ : traceForm R L M ⁅a, b⁆ ⁅c, d⁆ = traceForm R L M a ⁅b, ⁅c, d⁆⁆ :=
    traceForm_apply_lie_apply R L M a b ⁅c, d⁆
  have h₂ : traceForm R L M ⁅b, c⁆ ⁅a, d⁆ = traceForm R L M a ⁅d, ⁅b, c⁆⁆ := by
    rw [traceForm_comm R L M ⁅b, c⁆ ⁅a, d⁆, traceForm_apply_lie_apply]
  have h₃ : traceForm R L M ⁅c, a⁆ ⁅b, d⁆ = -traceForm R L M a ⁅c, ⁅b, d⁆⁆ := by
    rw [← lie_skew c a, map_neg, LinearMap.neg_apply, traceForm_apply_lie_apply]
  have hleib : ⁅b, ⁅c, d⁆⁆ + ⁅d, ⁅b, c⁆⁆ - ⁅c, ⁅b, d⁆⁆ = (0 : L) := by
    rw [leibniz_lie b c d, ← lie_skew d ⁅b, c⁆]
    abel
  have hmap := congrArg (traceForm R L M a) hleib
  rw [map_sub, map_add, map_zero] at hmap
  rw [h₁, h₂, h₃]
  linear_combination hmap

end Cyclic

section Nilpotent

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L M : Type*} [CommRing R] [IsReduced R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **An element acting nilpotently is orthogonal, for the trace form of any representation, to
everything it brackets to zero with.**  The trace form pairs `x` and `y` by the trace of the
composite of their actions; bracketing to zero in `L` makes those actions commute, since
`toEnd R L M` is a morphism of Lie rings, and the trace of a composite with a commuting nilpotent
factor vanishes over a reduced ring. -/
theorem traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero {x y : L}
    (hx : IsNilpotent (toEnd R L M x)) (hxy : ⁅x, y⁆ = 0) :
    traceForm R L M x y = 0 := by
  have hcomm : Commute (toEnd R L M y) (toEnd R L M x) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, ← lie_skew y x, hxy, neg_zero, map_zero]
  rw [traceForm_comm, traceForm_apply_apply,
    LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent 0 hcomm (by simpa using hx), zero_mul]

end Nilpotent

end TauCeti
