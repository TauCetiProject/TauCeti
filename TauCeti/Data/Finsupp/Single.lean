/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Int.Cast.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Single-support `Finsupp` lemmas

Integer-cast evaluation on `Finsupp.single`, injectivity of summing `Finsupp.single` over
finite subsets along an injective index map, and telescoping a `Fin`-indexed sum of
`Finsupp.single` terms with upper-tail weights into a weighted sum of prefix indicator sums.
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

/-- Rearrange a `Fin r`-indexed `Finsupp.single` sum with upper-tail weights
`c i = ∑ k ≥ i, w k` into a weighted sum of prefix indicator sums. -/
theorem finsetSum_single_eq_sum_smul_prefix {σ R : Type*} [Semiring R] {r : ℕ}
    (f : Fin r → σ) (c w : Fin r → R)
    (hw : ∀ i : Fin r, c i = ∑ k ∈ Finset.univ.filter (fun k : Fin r => i ≤ k), w k) :
    (∑ i : Fin r, single (f i) (c i)) =
      ∑ k : Fin r, w k • ∑ t : Fin ((k : ℕ) + 1),
        single (f (Fin.castLE (Nat.succ_le_of_lt k.isLt) t)) (1 : R) := by
  simp_rw [hw, ← singleAddHom_apply, map_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.smul_sum]
  simp only [singleAddHom_apply, smul_single, smul_eq_mul, mul_one]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun t _ => Fin.castLE (Nat.succ_le_of_lt k.isLt) t)
    (fun t _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.le_def.mpr (Nat.lt_succ_iff.mp t.isLt)⟩)
    (fun _ _ _ _ h => Fin.castLE_injective _ h)
    (fun i hi => ⟨⟨i, Nat.lt_succ_of_le (Fin.le_def.mp (Finset.mem_filter.mp hi).2)⟩,
      Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

end Finsupp
