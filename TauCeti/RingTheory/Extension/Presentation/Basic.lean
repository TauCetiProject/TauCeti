/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Algebra homomorphisms out of a presented algebra

Let `P` be a presentation of an `R`-algebra `S`. An `R`-algebra homomorphism out of `S` is
determined by its values on the generators of `P`, and every family in an `R`-algebra `T`
satisfying the relations of `P` is the family of values on the generators of an `R`-algebra
homomorphism `S →ₐ[R] T`.

## Main definitions

* `Algebra.Presentation.lift P x hx`: the `R`-algebra homomorphism out of `S` sending the
  generators of `P` to a family `x` satisfying the relations of `P`.

## Main results

* `Algebra.Presentation.lift_val`: `P.lift x hx` sends the `i`-th generator to `x i`.
* `Algebra.Generators.algHom_ext`: two `R`-algebra homomorphisms out of `S` agreeing on a family
  of generators are equal.
-/

public section

open MvPolynomial

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Two `R`-algebra homomorphisms out of `S` that agree on the generators of `P` are equal. -/
theorem Generators.algHom_ext {ι : Type*} (P : Generators R S ι) {T : Type*} [Semiring T]
    [Algebra R T] {f g : S →ₐ[R] T} (h : ∀ i, f (P.val i) = g (P.val i)) : f = g :=
  (AlgHom.cancel_right P.aeval_val_surjective).1 <| MvPolynomial.algHom_ext fun i ↦ by simp [h]

namespace Presentation

variable {ι σ : Type*} (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]

/-- The `R`-algebra homomorphism out of `S` sending the generators of the presentation `P` to a
family `x` that satisfies the relations of `P`. -/
noncomputable def lift (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) : S →ₐ[R] T :=
  (aeval P.val).liftOfSurjective P.aeval_val_surjective (aeval x) <| by
    -- the kernel of `aeval P.val` is spanned by the relations, which `aeval x` kills
    simp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom]
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
    exact Set.range_subset_iff.2 hx

/-- `P.lift x hx` sends the `i`-th generator of `P` to `x i`. -/
@[simp]
theorem lift_val (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) (i : ι) :
    P.lift x hx (P.val i) = x i := by
  rw [lift, ← aeval_X (R := R) P.val i, AlgHom.liftOfSurjective_apply, aeval_X]

end Presentation

end Algebra
