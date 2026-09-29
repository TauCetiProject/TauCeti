/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The ray class ideal count at the trivial modulus

At the trivial modulus every nonzero integral ideal is prime to the modulus, and the ray class
group is the class group. Summing the ray class ideal counting function over the classes then
counts all nonzero integral ideals of norm at most `x`, exactly the quantity of Mathlib's
`NumberField.tendsto_norm_le_div_atTop₀`, and the ray class asymptotic gives back its limit: the
total count divided by `x` tends to the Dedekind zeta residue, the constant of that Mathlib
theorem. This is the agreement between the uniform ray class count and the classical ideal
count.

## Main results

* `TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction_one`: at the trivial modulus,
  the class counts sum to the number of nonzero integral ideals of norm at most `x`.
* `TauCeti.GlobalNumberFields.tendsto_rayClassIdealCountingFunction_div`: in every ray class the
  count divided by `x` tends to the main term.
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

/-- **The class counts at the trivial modulus sum to the classical ideal count.** -/
theorem sum_rayClassIdealCountingFunction_one [Fintype (RayClassGroup (Modulus.one K))] (x : ℝ) :
    ∑ c : RayClassGroup (Modulus.one K), rayClassIdealCountingFunction (Modulus.one K) c x =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := by
  rw [sum_rayClassIdealCountingFunction]
  exact Nat.card_congr (Equiv.subtypeEquiv integralIdealsPrimeToOneEquiv fun I => by
    rw [integralIdealsPrimeToOneEquiv_apply_coe])

/-- **In every ray class the count divided by `x` tends to the main term.** -/
theorem tendsto_rayClassIdealCountingFunction_div (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Tendsto (fun x : ℝ => (rayClassIdealCountingFunction 𝔪 c x : ℝ) / x) atTop
      (𝓝 (rayClassIdealMainTerm 𝔪)) := by
  obtain ⟨δ, hδ, h⟩ := rayClassIdealCount 𝔪
  -- the power saving is negligible against `x`
  have hlittle : (fun x : ℝ => x ^ (1 - δ)) =o[atTop] (fun x : ℝ => x) := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx h0
      exact absurd h0 hx.ne'
    · refine (tendsto_rpow_neg_atTop hδ).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_neg hx.le]
      field_simp
  have h0 : Tendsto (fun x : ℝ =>
      ((rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x) / x) atTop
      (𝓝 0) :=
    ((h c).trans_isLittleO hlittle).tendsto_div_nhds_zero
  have := h0.add_const (rayClassIdealMainTerm 𝔪)
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [sub_div, mul_div_assoc, div_self hx.ne', mul_one, sub_add_cancel]

/-- **Agreement with the classical ideal count.** At the trivial modulus the total of the ray class
counts, divided by `x`, tends to the Dedekind zeta residue, the limit of Mathlib's
`NumberField.tendsto_norm_le_div_atTop₀`. -/
theorem tendsto_rayClassIdealCountingFunction_one [Fintype (RayClassGroup (Modulus.one K))] :
    Tendsto (fun x : ℝ => (∑ c : RayClassGroup (Modulus.one K),
        (rayClassIdealCountingFunction (Modulus.one K) c x : ℝ)) / x) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  have h := tendsto_finsetSum Finset.univ
    fun c (_ : c ∈ Finset.univ) => tendsto_rayClassIdealCountingFunction_div (Modulus.one K) c
  have hsum : ∑ _c : RayClassGroup (Modulus.one K), rayClassIdealMainTerm (Modulus.one K) =
      dedekindZeta_residue K := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rayClassIdealMainTerm_one,
      ← Nat.card_eq_fintype_card, Nat.card_congr oneEquivClassGroup.toEquiv]
    have : (Nat.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    field_simp
  rw [← hsum]
  refine h.congr' ?_
  filter_upwards with x
  rw [Finset.sum_div]

end TauCeti.GlobalNumberFields
