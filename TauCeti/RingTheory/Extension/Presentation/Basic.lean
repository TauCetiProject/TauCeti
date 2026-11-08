/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Algebra homomorphisms out of a presented algebra

Let `P` be a presentation of an `R`-algebra `S`. Every family in an `R`-algebra `T` satisfying
the relations of `P` is the family of values on the generators of an `R`-algebra homomorphism
`S →ₐ[R] T`. This homomorphism is unique: an `R`-algebra homomorphism out of `S` is determined
by its values on the generators (`Algebra.Generators.algHom_ext`, in
`TauCeti.RingTheory.Extension.Generators`).

## Main definitions

* `Algebra.Presentation.lift P x hx`: the `R`-algebra homomorphism out of `S` sending the
  generators of `P` to a family `x` satisfying the relations of `P`.

## Main results

* `Algebra.Presentation.lift_val`: `P.lift x hx` sends the `i`-th generator to `x i`.
-/

public section

open MvPolynomial

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

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
