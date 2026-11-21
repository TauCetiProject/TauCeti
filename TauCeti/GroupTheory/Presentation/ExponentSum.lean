/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import TauCeti.GroupTheory.Presentation.Relator
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Exponent sums of relators

`TauCeti.Relator.expSum i r` is the total exponent of the generator `i` in the relator `r`, that
is, the coefficient of `i` in the image of `r` in the free abelian group on the generators.
Commutators contribute nothing.

## Main results

* `TauCeti.Relator.eval_eq_prod_zpow`: in a commutative group, a relator evaluates to the
  product of the generator values raised to their exponent sums.
-/

public section

namespace TauCeti.Relator

variable {α : Type*} [DecidableEq α]

/-- The total exponent of the generator `i` in a relator. Commutators contribute nothing. -/
def expSum (i : α) : Relator α → ℤ
  | .gen x => if i = x then 1 else 0
  | .inv r => -expSum i r
  | .mul r s => expSum i r + expSum i s
  | .pow r n => expSum i r * n
  | .comm _ _ => 0

@[simp]
theorem expSum_gen (i x : α) : expSum i (.gen x) = if i = x then 1 else 0 := by rfl

@[simp]
theorem expSum_inv (i : α) (r : Relator α) : expSum i (.inv r) = -expSum i r := by rfl

@[simp]
theorem expSum_mul (i : α) (r s : Relator α) :
    expSum i (.mul r s) = expSum i r + expSum i s := by rfl

@[simp]
theorem expSum_pow (i : α) (r : Relator α) (n : ℕ) : expSum i (.pow r n) = expSum i r * n := by rfl

@[simp]
theorem expSum_comm (i : α) (r s : Relator α) : expSum i (.comm r s) = 0 := by rfl

/-- A conjugate `s⁻¹ r s` has the exponent sums of `r`. -/
@[simp]
theorem expSum_conj (i : α) (r s : Relator α) : expSum i (r.conj s) = expSum i r := by
  simp only [conj, expSum_mul, expSum_inv]
  omega

/-- The relator `r s⁻¹` has the exponent sums of `r` minus those of `s`. -/
@[simp]
theorem expSum_div (i : α) (r s : Relator α) :
    expSum i (r.div s) = expSum i r - expSum i s := by
  simp only [div, expSum_mul, expSum_inv]
  omega

/-- A commutator `r⁻¹ s⁻¹ r s` has exponent sum `0` at every generator. -/
@[simp]
theorem expSum_commInvInv (i : α) (r s : Relator α) : expSum i (r.commInvInv s) = 0 := by
  simp only [commInvInv, expSum_comm]

/-- In a commutative group, a relator evaluates to the product of the generator values raised to
their exponent sums. -/
theorem eval_eq_prod_zpow [Fintype α] {G : Type*} [CommGroup G] (f : α → G) (r : Relator α) :
    eval f r = ∏ i, f i ^ expSum i r := by
  induction r with
  | gen x =>
    rw [Finset.prod_eq_single x (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ x) h)]
    simp
  | inv r ih => simp [ih, Finset.prod_inv_distrib]
  | mul r s ihr ihs => simp [ihr, ihs, zpow_add, Finset.prod_mul_distrib]
  | pow r n ih => simp [ih, zpow_mul, Finset.prod_pow]
  | comm r s _ _ => simp [commutatorElement_eq_one_iff_mul_comm, mul_comm]

end TauCeti.Relator
