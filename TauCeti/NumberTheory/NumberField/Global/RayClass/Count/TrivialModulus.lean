/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# The ray class ideal count at the trivial modulus

At the trivial modulus every nonzero integral ideal is prime to the modulus, and the ray class
group is the class group. Summing the ray class ideal counting function over the classes then
counts all nonzero integral ideals of norm at most `x`, exactly the quantity of Mathlib's
`NumberField.Ideal.tendsto_norm_le_div_atTop₀`, whose limit is the Dedekind zeta residue. This is
the agreement between the uniform ray class count and the classical ideal count: the total of the
class counts, divided by `x`, tends to `dedekindZeta_residue K`, the value that each class count
reaches in its share `rayClassIdealMainTerm (Modulus.one K) = dedekindZeta_residue K / h_K`.

## Main results

* `TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction_one`: at the trivial modulus,
  the class counts sum to the number of nonzero integral ideals of norm at most `x`.
* `TauCeti.GlobalNumberFields.tendsto_rayClassIdealCountingFunction_one`: at the trivial modulus
  the total count divided by `x` tends to `dedekindZeta_residue K`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §3.
-/

public section

open Filter Topology Asymptotics NumberField IsDedekindDomain
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- At the trivial modulus the ideals prime to the modulus are the nonzero ideals. -/
noncomputable def integralIdealsPrimeToOneEquiv :
    integralIdealsPrimeTo (Modulus.one K) ≃ (Ideal (𝓞 K))⁰ :=
  Equiv.subtypeEquiv (Equiv.refl _) fun I => by
    rw [Equiv.refl_apply, Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff,
      Modulus.support_one, mem_nonZeroDivisors_iff_ne_zero]
    simp

/-- The equivalence keeps the ideal. -/
@[simp] theorem integralIdealsPrimeToOneEquiv_apply_coe
    (I : integralIdealsPrimeTo (Modulus.one K)) :
    ((integralIdealsPrimeToOneEquiv I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = I := by
  rfl

/-- The inverse equivalence keeps the ideal. -/
@[simp] theorem integralIdealsPrimeToOneEquiv_symm_apply_coe (I : (Ideal (𝓞 K))⁰) :
    ((integralIdealsPrimeToOneEquiv.symm I : integralIdealsPrimeTo (Modulus.one K)) :
      Ideal (𝓞 K)) = I := by
  rfl

/-- **The class counts at the trivial modulus sum to the classical ideal count.** -/
@[simp]
theorem sum_rayClassIdealCountingFunction_one [Fintype (RayClassGroup (Modulus.one K))] (x : ℝ) :
    ∑ c : RayClassGroup (Modulus.one K), rayClassIdealCountingFunction (Modulus.one K) c x =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := by
  rw [sum_rayClassIdealCountingFunction]
  exact Nat.card_congr (Equiv.subtypeEquiv integralIdealsPrimeToOneEquiv fun I => by
    rw [integralIdealsPrimeToOneEquiv_apply_coe])

/-- **Agreement with the classical ideal count.** At the trivial modulus the total of the ray class
counts, divided by `x`, tends to the Dedekind zeta residue: the total is the classical count, and
Mathlib's `NumberField.Ideal.tendsto_norm_le_div_atTop₀` gives its limit. -/
theorem tendsto_rayClassIdealCountingFunction_one [Fintype (RayClassGroup (Modulus.one K))] :
    Tendsto (fun x : ℝ => (∑ c : RayClassGroup (Modulus.one K),
        (rayClassIdealCountingFunction (Modulus.one K) c x : ℝ)) / x) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue_def]
  refine (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).congr' ?_
  filter_upwards with x
  rw [← Nat.cast_sum, sum_rayClassIdealCountingFunction_one]

end TauCeti.GlobalNumberFields
