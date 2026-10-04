/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `Pi.evalAlgHom` and `AlgHom.eq_piEvalAlgHom` both occur in the statements below.
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The algebra homomorphisms out of a finite power of the base ring

Let `R` be a nontrivial commutative semiring without zero divisors and `ι` a finite index type.
Mathlib's `AlgHom.eq_piEvalAlgHom` says that every `R`-algebra homomorphism `(ι → R) →ₐ[R] R` is a
coordinate evaluation `Pi.evalAlgHom R _ s`. Distinct coordinates give distinct evaluations, since
they disagree on `Pi.single s 1`, so the evaluations enumerate those homomorphisms **without
repetition**: `Pi.evalAlgHomEquiv` packages that as an equivalence `ι ≃ ((ι → R) →ₐ[R] R)`.

The injectivity half, `Pi.evalAlgHom_injective`, is what Mathlib does not record, and it is what
makes the equivalence useful for counting: a split commutative algebra has exactly as many
characters as it has factors. The Burnside--Dixon--Schneider algorithm consumes it in that form, to
count the central characters of a group algebra whose centre has been split into coordinates.

## Main definitions

* `Pi.evalAlgHom_injective`: distinct coordinates give distinct evaluation homomorphisms.
* `Pi.evalAlgHomEquiv`: the coordinates of `ι → R` are exactly the `R`-algebra homomorphisms
  `(ι → R) →ₐ[R] R`.
* `Pi.pullback`: pull functions back along a map of types.
-/

public section

namespace Pi

variable (R ι : Type*) [CommSemiring R]

/-- Distinct coordinates give distinct evaluation homomorphisms out of a power of a nontrivial
commutative semiring. -/
theorem evalAlgHom_injective [Nontrivial R] :
    Function.Injective (Pi.evalAlgHom R fun _ : ι => R) := by
  classical
  intro s t hst
  by_contra hne
  have h := DFunLike.congr_fun hst (Pi.single s 1)
  rw [evalAlgHom_apply, evalAlgHom_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne)] at h
  exact one_ne_zero h

variable {α β : Type*}

/-- Pull functions back along a map of types. -/
def pullback (f : α → β) : (β → R) →ₐ[R] (α → R) where
  toFun a := a ∘ f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem pullback_apply (f : α → β) (a : β → R) (x : α) :
    pullback R f a x = a (f x) := by
  unfold pullback
  rfl

variable [NoZeroDivisors R] [Nontrivial R] [Finite ι]

/-- **The `R`-algebra homomorphisms out of `ι → R` are the coordinate evaluations, each occurring
once.** Surjectivity is Mathlib's `AlgHom.eq_piEvalAlgHom`; injectivity holds because the
evaluations at two distinct coordinates take the values `1` and `0` on `Pi.single`. -/
noncomputable def evalAlgHomEquiv : ι ≃ ((ι → R) →ₐ[R] R) :=
  Equiv.ofBijective (Pi.evalAlgHom R fun _ => R)
    ⟨evalAlgHom_injective R ι,
      fun φ => φ.eq_piEvalAlgHom.imp fun _ hs => hs.symm⟩

@[simp]
theorem evalAlgHomEquiv_apply (s : ι) :
    evalAlgHomEquiv R ι s = Pi.evalAlgHom R (fun _ => R) s :=
  (rfl)

end Pi
