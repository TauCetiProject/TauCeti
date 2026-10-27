/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import TauCeti.Order.Northcott.Basic

/-!
# Counting the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` and `c` a ray class of `𝔪`.  This file introduces
`rayClassIdealCountingFunction 𝔪 c x`, the number of nonzero integral ideals prime to the finite
part of `𝔪` that lie in the class `c` and have norm at most `x`, and proves the two facts that
make it a counting function at all: the sets being counted are finite, and summing over the ray
class group recovers the unrestricted count.

The carrier is `integralIdealsPrimeTo 𝔪`, the monoid on which `idealClass` is defined, so
coprimality and nonvanishing are forced by the type rather than imposed as side conditions; the
zero ideal and ideals sharing a prime with the finite part cannot enter the count.

Finiteness is not proved here. `TauCeti.Order.Northcott.Basic` already fixes the project's
convention
for counting by an *inclusive real* cutoff, and supplies `finite_setOf_natCast_le` for any
natural-valued Northcott function.  All this file adds is the `Northcott` instance for the absolute
norm on `integralIdealsPrimeTo 𝔪`; the finiteness, and with it `normLE`, `summatory` and
`Nat.card_coe_normLE`, then come from that shared layer.  The bound is taken in `ℝ` rather than `ℕ`
because the asymptotics that consume this count are.

The partition is stated first as an equivalence, `idealClassSigmaEquiv`, and only then in counting
form.  The equivalence needs no finiteness at all, and it is what a consumer weighting the classes
by a character reaches for; the counting statement is its `Nat.card` shadow.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction`: the number of nonzero integral ideals
  prime to `𝔪` in a fixed ray class with norm at most `x`.
* `TauCeti.GlobalNumberFields.idealClassSigmaEquiv`: the ideals prime to `𝔪` of norm at most `x`,
  partitioned into their ray classes.

## Main results

* `TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction`: the class counts sum to the
  unrestricted count of nonzero integral ideals prime to `𝔪` of norm at most `x`.
* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def`,
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_apply_coe` and
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_symm_apply_fst`: the characteristic lemmas of
  the two definitions, so that a consumer never has to unfold either.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* `CBirkbeck/AINTLIB` @ `2622c61d2502159c62865a1b59fc1de473519113` (Apache-2.0, Chris Birkbeck),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`:
  `card_norm_le_residue_eq_sum_class` is the corresponding partition step, stated there for the
  ordinary class group together with a norm-residue condition.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness of the sets being counted -/

/-- **The absolute norm is Northcott on the ideals prime to a modulus**: only finitely many have
norm below any bound. This mirrors `TauCeti.instNorthcottAbsNormNonZeroDivisors`, which does the
same for `(Ideal R)⁰`. -/
instance (𝔪 : Modulus K) :
    Northcott (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) where
  finite_le B :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 K) B).preimage Subtype.val_injective.injOn

/-- The nonzero integral ideals prime to `𝔪` of norm at most a real bound form a finite type. The
cutoff is real, and inclusive, per the convention `TauCeti.Order.Northcott.Basic` fixes. -/
instance (𝔪 : Modulus K) (x : ℝ) :
    Finite {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (TauCeti.finite_setOf_natCast_le _ x).to_subtype

/-- Restricting to a single ray class keeps the set finite. -/
instance (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    Finite {I : integralIdealsPrimeTo 𝔪 //
      idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  Finite.of_injective
    (β := {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x})
    (Subtype.map id fun _ ↦ And.right) (Subtype.map_injective _ Function.injective_id)

/-! ### The counting function and the class partition -/

/-- **The ray class ideal counting function.**  The number of nonzero integral ideals in the ray
class `c` of `𝔪`, prime to the finite part of `𝔪`, whose norm is at most `x`.  The carrier already
forces coprimality and nonvanishing, so the zero ideal and other classes cannot enter. -/
noncomputable def rayClassIdealCountingFunction
    (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) : ℕ :=
  Nat.card {I : integralIdealsPrimeTo 𝔪 //
    idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}

/-- **The counting function as the cardinality defining it.**  The rewrite rule turning
`rayClassIdealCountingFunction` into the set of ideals of class `c` whose norm is at most `x`. -/
theorem rayClassIdealCountingFunction_def (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x =
      Nat.card {I : integralIdealsPrimeTo 𝔪 //
        idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (rfl)

/-- **The ray classes partition the ideals of bounded norm.**  An ideal prime to `𝔪` of norm at
most `x` is the same thing as a ray class together with an ideal of that class and that norm
bound, because `idealClass 𝔪` is a function on the carrier and the summands are exactly its
fibres. -/
noncomputable def idealClassSigmaEquiv (𝔪 : Modulus K) (x : ℝ) :
    (Σ c : RayClassGroup 𝔪, {I : integralIdealsPrimeTo 𝔪 //
        idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}) ≃
      {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (Equiv.sigmaCongrRight fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ and_comm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans (Equiv.sigmaFiberEquiv _)

/-- The partition keeps the ideal: it only forgets which class the ideal was filed under. -/
@[simp]
theorem idealClassSigmaEquiv_apply_coe (𝔪 : Modulus K) (x : ℝ)
    (p : Σ c : RayClassGroup 𝔪, {I : integralIdealsPrimeTo 𝔪 //
      idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}) :
    (idealClassSigmaEquiv 𝔪 x p : integralIdealsPrimeTo 𝔪) = p.2 :=
  (rfl)

/-- Filing an ideal under its own ray class is the inverse of forgetting it: the class component is
`idealClass 𝔪 I` and the ideal component is `I` again. -/
@[simp]
theorem idealClassSigmaEquiv_symm_apply_fst (𝔪 : Modulus K) (x : ℝ)
    (I : {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}) :
    ((idealClassSigmaEquiv 𝔪 x).symm I).1 = idealClass 𝔪 I :=
  (rfl)

/-- **The class counts sum to the total.**  Summing `rayClassIdealCountingFunction` over the ray
class group recovers the number of nonzero integral ideals prime to `𝔪` of norm at most `x`.

The ray class group is always finite (`finite_rayClassGroup`), but it carries no canonical
`Fintype`, so the enumeration is taken as a hypothesis rather than fixed to `Fintype.ofFinite`
here; that keeps the statement usable against whichever enumeration the caller holds. -/
theorem sum_rayClassIdealCountingFunction (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] (x : ℝ) :
    ∑ c : RayClassGroup 𝔪, rayClassIdealCountingFunction 𝔪 c x =
      Nat.card {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  Nat.card_sigma.symm.trans (Nat.card_congr (idealClassSigmaEquiv 𝔪 x))

end TauCeti.GlobalNumberFields
