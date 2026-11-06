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
square, and its algebraic GNS class map and representation are injective.

No norm, finite dimension, normalization, or compatibility between star and coproduct is
needed. In particular, the representation here is by algebraic endomorphisms, not asserted
to be bounded. These results supply the faithful inner product needed before algebraic
unitarization and construction of C*-completions.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, Proposition 2.2.4 and
  Remark 2.2.2(iv)(c), for algebraic faithfulness and its positive-integral consequence.
-/

public section

open scoped ComplexOrder InnerProductSpace

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

/-- Positive left invariant integrals detect zero by a single square. -/
@[simp]
theorem apply_star_mul_self_eq_zero_iff_of_isLeftInvariantIntegral
    (hh : φ.toLinearMap.IsLeftInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) (a : H) :
    φ (star a * a) = 0 ↔ a = 0 := by
  rw [← φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    φ.nullSubmodule_eq_bot_of_isLeftInvariantIntegral hh h0, Submodule.mem_bot]

/-- Positive right invariant integrals detect zero by a single square. -/
@[simp]
theorem apply_star_mul_self_eq_zero_iff_of_isRightInvariantIntegral
    (hh : φ.toLinearMap.IsRightInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) (a : H) :
    φ (star a * a) = 0 ↔ a = 0 := by
  rw [← φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    φ.nullSubmodule_eq_bot_of_isRightInvariantIntegral hh h0, Submodule.mem_bot]

/-- A nonzero positive left invariant integral is strictly positive on nonzero squares. -/
theorem apply_star_mul_self_pos_of_isLeftInvariantIntegral
    (hh : φ.toLinearMap.IsLeftInvariantIntegral) (h0 : φ.toLinearMap ≠ 0)
    {a : H} (ha : a ≠ 0) : 0 < φ (star a * a) :=
  (φ.square_nonneg a).lt_of_ne' fun hz =>
    ha ((φ.apply_star_mul_self_eq_zero_iff_of_isLeftInvariantIntegral hh h0 a).mp hz)

/-- A nonzero positive right invariant integral is strictly positive on nonzero squares. -/
theorem apply_star_mul_self_pos_of_isRightInvariantIntegral
    (hh : φ.toLinearMap.IsRightInvariantIntegral) (h0 : φ.toLinearMap ≠ 0)
    {a : H} (ha : a ≠ 0) : 0 < φ (star a * a) :=
  (φ.square_nonneg a).lt_of_ne' fun hz =>
    ha ((φ.apply_star_mul_self_eq_zero_iff_of_isRightInvariantIntegral hh h0 a).mp hz)

/-- The algebraic GNS class map of a nonzero positive left invariant integral is injective. -/
theorem classMap_injective_of_isLeftInvariantIntegral
    (hh : φ.toLinearMap.IsLeftInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    Function.Injective φ.classMap := by
  apply (injective_iff_map_eq_zero φ.classMap).mpr
  intro a ha
  exact (φ.apply_star_mul_self_eq_zero_iff_of_isLeftInvariantIntegral hh h0 a).mp
    ((φ.classMap_eq_zero_iff a).mp ha)

/-- The algebraic GNS class map of a nonzero positive right invariant integral is injective. -/
theorem classMap_injective_of_isRightInvariantIntegral
    (hh : φ.toLinearMap.IsRightInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    Function.Injective φ.classMap := by
  apply (injective_iff_map_eq_zero φ.classMap).mpr
  intro a ha
  exact (φ.apply_star_mul_self_eq_zero_iff_of_isRightInvariantIntegral hh h0 a).mp
    ((φ.classMap_eq_zero_iff a).mp ha)

/-- The algebraic GNS representation of a nonzero positive left invariant integral is
faithful. No boundedness of the representing endomorphisms is asserted. -/
theorem representation_injective_of_isLeftInvariantIntegral
    (hh : φ.toLinearMap.IsLeftInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    Function.Injective φ.representation := by
  intro a b hab
  apply φ.classMap_injective_of_isLeftInvariantIntegral hh h0
  simpa only [φ.representation_cyclicVector] using
    congrArg (fun T : Module.End ℂ φ.GNS => T φ.cyclicVector) hab

/-- The algebraic GNS representation of a nonzero positive right invariant integral is
faithful. No boundedness of the representing endomorphisms is asserted. -/
theorem representation_injective_of_isRightInvariantIntegral
    (hh : φ.toLinearMap.IsRightInvariantIntegral) (h0 : φ.toLinearMap ≠ 0) :
    Function.Injective φ.representation := by
  intro a b hab
  apply φ.classMap_injective_of_isRightInvariantIntegral hh h0
  simpa only [φ.representation_cyclicVector] using
    congrArg (fun T : Module.End ℂ φ.GNS => T φ.cyclicVector) hab

end TauCeti.StarPositiveFunctional
