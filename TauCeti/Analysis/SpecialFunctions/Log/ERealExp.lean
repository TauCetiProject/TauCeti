/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# Extended-real exponential of a finite sum

`TauCeti.EReal.exp_sum` expresses the exponential of a finite sum of extended reals
as the product of their exponentials, including infinite summands.
-/

public section

namespace TauCeti

/-- The extended-real exponential sends finite sums to products. -/
theorem EReal.exp_sum {ι : Type*} (s : Finset ι) (f : ι → EReal) :
    EReal.exp (∑ i ∈ s, f i) = ∏ i ∈ s, EReal.exp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, EReal.exp_add, ih]

end TauCeti
