/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Single-support `Finsupp` lemmas

Integer-cast evaluation on `Finsupp.single` and injectivity of summing `Finsupp.single` over
finite subsets along an injective index map.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

/-- Summing `Finsupp.single (e i) (c i)` over a `Finset ι` is injective on `Finset ι` whenever `e`
is injective and every weight `c i` is nonzero. -/
theorem finsetSum_single_injective {ι α M : Type*} [AddCommMonoid M]
    {e : ι → α} (he : Function.Injective e) {c : ι → M} (hc : ∀ i, c i ≠ 0) :
    Function.Injective (fun T : Finset ι => ∑ i ∈ T, single (e i) (c i)) := by
  classical
  intro T₁ T₂ h
  ext i
  have hi := congrFun (congrArg DFunLike.coe h) (e i)
  simp only [finsetSum_apply, single_apply, he.eq_iff, Finset.sum_ite_eq'] at hi
  by_cases h1 : i ∈ T₁ <;> by_cases h2 : i ∈ T₂ <;> simp [h1, h2, hc i, (hc i).symm] at hi ⊢

end Finsupp
