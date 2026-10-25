/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Multiplication.Basic
public import Mathlib.Tactic.NormNum

/-!
# Resolvent checks for scalar decay

On bounded real functions on the discrete natural numbers, multiplication by `exp (-t)`
is a contraction semigroup with bounded generator `-I`. Its resolvent is `(λ + 1)⁻¹ I`.
The checks below compare the native resolvent with this expression, and exercise the
resolvent identity and the Hille–Yosida norm bound on this concrete Banach space.
-/

public section

noncomputable section

open TauCeti.Semigroups
open scoped BoundedContinuousFunction

namespace TauCeti.Examples.ScalarDecay

/-- Bounded continuous real functions on the discrete natural numbers. -/
abbrev Space := ℕ →ᵇ ℝ

private theorem one_nonneg : 0 ≤ (1 : Space) := fun _ => zero_le_one

/-- The contraction semigroup multiplying every function by `exp (-t)`. -/
def semigroup : ContractionSemigroup Space :=
  ContractionSemigroup.ofMultiplication 1 one_nonneg

/-- The scalar decay semigroup is the bounded-generator exponential for multiplication by `-1`. -/
theorem eq_ofBounded : semigroup.toStronglyContinuousSemigroup =
    StronglyContinuousSemigroup.ofBounded (ContinuousLinearMap.mul ℝ Space (-1)) := by
  rw [semigroup, ContractionSemigroup.ofMultiplication_toStronglyContinuousSemigroup,
    StronglyContinuousSemigroup.ofMultiplication_eq_ofBounded]

/-- The Laplace resolvent is the independently computed scalar inverse. -/
theorem resolvent_eq_smul_id (lambda : ℝ) (h : 0 < lambda) :
    semigroup.resolvent lambda h =
      (lambda + 1)⁻¹ • ContinuousLinearMap.id ℝ Space := by
  rw [semigroup, ContractionSemigroup.ofMultiplication_resolvent_eq]
  ext f n
  simp only [ContinuousLinearMap.mul_apply', BoundedContinuousFunction.coe_mul,
    BoundedContinuousFunction.coe_addInv, BoundedContinuousFunction.coe_one, Pi.one_apply,
    Pi.mul_apply, smul_apply, ContinuousLinearMap.id_apply, BoundedContinuousFunction.coe_smul,
    smul_eq_mul]

/-- The actual resolvents satisfy the first resolvent identity. -/
theorem resolvent_sub_resolvent (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    semigroup.resolvent lambda hlambda - semigroup.resolvent mu hmu =
      (mu - lambda) • (semigroup.resolvent lambda hlambda ∘L semigroup.resolvent mu hmu) :=
  semigroup.resolvent_sub_resolvent lambda mu hlambda hmu

/-- The actual resolvent obeys the contraction-generator norm bound. -/
theorem norm_resolvent_le (lambda : ℝ) (h : 0 < lambda) :
    ‖semigroup.resolvent lambda h‖ ≤ 1 / lambda :=
  semigroup.resolvent_norm_le lambda h

/-- At parameters one and two the resolvent difference is exactly one sixth of the identity. -/
theorem resolvent_one_sub_two :
    semigroup.resolvent 1 (by norm_num) - semigroup.resolvent 2 (by norm_num) =
      (1 / 6 : ℝ) • ContinuousLinearMap.id ℝ Space := by
  rw [resolvent_eq_smul_id, resolvent_eq_smul_id, ← sub_smul]
  norm_num

/-- The resolvent norm at one is exactly one half, rather than merely finite. -/
theorem norm_resolvent_one : ‖semigroup.resolvent 1 (by norm_num)‖ = (1 / 2 : ℝ) := by
  have : Nontrivial Space := ⟨⟨0, 1, fun h => by
    have := congrArg (fun f : Space => f 0) h
    norm_num at this⟩⟩
  rw [resolvent_eq_smul_id, norm_smul, ContinuousLinearMap.norm_id]
  norm_num

end TauCeti.Examples.ScalarDecay
