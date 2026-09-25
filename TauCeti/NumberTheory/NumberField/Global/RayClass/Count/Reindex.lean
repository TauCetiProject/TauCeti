/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Basic

/-!
# The ray class count, reindexed by a representative ideal

Counting the integral ideals of a fixed ray class is awkward directly, because the class
condition is not a divisibility condition.  Multiplying by an ideal `𝔞` whose class is the
inverse one turns it into two conditions that are: divisibility by `𝔞`, and triviality of the
class.  The norm bound is carried along, scaled by the norm of `𝔞`.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one`:
  the counting function as the number of multiples of `𝔞` of trivial class and bounded norm.

## Provenance

The reindexing follows Mathlib's class-group analogue
`NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₁`
(`Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean`) move for move: `subtypeEquiv`, then
`subtypeSubtypeEquivSubtypeInter`, then `Nat.card_congr`.  That lemma is `private`, is a
`Nat.card` equality rather than an `Equiv`, and is stated over `(Ideal (𝓞 K))⁰`, so it cannot be
called from here.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The ray class count, reindexed by a representative.**  For `𝔞` in the inverse class of `c`,
multiplication by `𝔞` matches the ideals of class `c` with norm at most `x` against the multiples
of `𝔞` of trivial class with norm at most `x * N 𝔞`. -/
private noncomputable def idealClassNormLEEquivDvdIdealClassOneNormLE (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪}
    (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    {I : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 I = c ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} ≃
      {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧ idealClass 𝔪 I = 1 ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  ((Equiv.dvd 𝔞).subtypeEquiv fun I ↦ by
    simp only [Equiv.dvd_apply, Submonoid.coe_mul, map_mul, h𝔞, Nat.cast_mul,
      inv_mul_eq_one, mul_comm x]
    -- `N 𝔞` is nonzero, so it cancels from the scaled norm bound
    exact and_congr eq_comm (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (mt Ideal.absNorm_eq_zero_iff.mp
        (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1)))).symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : integralIdealsPrimeTo 𝔪 ↦ 𝔞 ∣ I) _)

/-- **The counting function as a count of multiples of `𝔞`.**  For `𝔞` in the inverse class of
`c`, the count runs over the multiples of `𝔞` of trivial class, against a norm bound scaled by
`N 𝔞`; any `𝔞` of that class serves, as the left-hand side does not mention it.  This is the
rewrite that trades the class condition for a divisibility condition, where
`rayClassIdealCountingFunction_def` is the one that keeps the class condition. -/
theorem rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x = Nat.card {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧
      idealClass 𝔪 I = 1 ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  -- `rayClassIdealCountingFunction` is not `@[expose]`d, so the step onto the cardinality it is
  -- defined as goes through `rayClassIdealCountingFunction_def` rather than by `rfl`
  (rayClassIdealCountingFunction_def 𝔪 c x).trans <|
    Nat.card_congr <| idealClassNormLEEquivDvdIdealClassOneNormLE 𝔪 𝔞 h𝔞 x

end TauCeti.GlobalNumberFields
