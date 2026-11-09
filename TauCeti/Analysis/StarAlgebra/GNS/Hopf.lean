/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# Faithfulness of positive invariant Hopf integrals

A nonzero positive invariant functional on a complex Hopf algebra has no GNS null vectors.
Either left or right invariance suffices: positivity turns a null vector into a radical
vector for the multiplication pairing, and algebraic faithfulness of invariant integrals
then makes it zero. Consequently the functional is strictly positive on every nonzero
square, and its algebraic GNS class map and representation are injective. These consequences
follow from the general results in `GNS.Basic`: compose either null-space theorem below with
`apply_star_mul_self_pos_of_nullSubmodule_eq_bot`, `classMap_injective_iff`, and
`representation_injective_of_classMap_injective`.

No norm, finite dimension, normalization, or compatibility between star and coproduct is
needed. In particular, the representation here is by algebraic endomorphisms, not asserted
to be bounded. These results supply the faithful inner product needed before algebraic
unitarization and construction of C*-completions.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, Proposition 2.2.4 and
  Remark 2.2.2(iv)(c), for algebraic faithfulness and its positive-integral consequence.
-/

public section

namespace TauCeti.StarPositiveFunctional

variable {H : Type*} [Ring H] [StarRing H] [HopfAlgebra ℂ H] [StarModule ℂ H]
  (φ : StarPositiveFunctional H)

/-- A nonzero positive left invariant integral has trivial GNS null space. -/
theorem nullSubmodule_eq_bot_of_isLeftInvariantIntegral
    (hh : φ.toLinearMap.IsLeftInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    φ.nullSubmodule = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  simp only [Submodule.mem_bot]
  apply hh.eq_zero_of_forall_mul_eq_zero h0
  intro b
  simpa using (φ.mem_nullSubmodule a).mp ha (star b)

/-- A nonzero positive right invariant integral also has trivial GNS null space. -/
theorem nullSubmodule_eq_bot_of_isRightInvariantIntegral
    (hh : φ.toLinearMap.IsRightInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    φ.nullSubmodule = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  simp only [Submodule.mem_bot]
  have hstar : star a = 0 := hh.eq_zero_of_forall_mul_eq_zero h0 fun b => by
    rw [toLinearMap_apply, ← φ.star_apply_star_mul b a,
      (φ.mem_nullSubmodule a).mp ha b, star_zero]
  simpa using congrArg star hstar

end TauCeti.StarPositiveFunctional
