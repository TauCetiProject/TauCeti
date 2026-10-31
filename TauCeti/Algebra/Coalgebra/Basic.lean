/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Elements whose comultiplication is a pure tensor

If the comultiplication of an element `a` of a coalgebra is a pure tensor `b ⊗ c`, then the
counit law `(ε ⊗ id) ∘ Δ = id` determines `a` from it: applying it to `Δ a = b ⊗ c` gives
`a = ε(b) • c`. In particular `Δ a = a ⊗ c` gives `a = ε(a) • c`, so in a bialgebra an element
fixed by the regular coaction, `Δ a = a ⊗ 1`, is the scalar multiple `ε(a) • 1` of the identity.

## Main declarations

* `TauCeti.Coalgebra.eq_counit_smul_of_comul_eq_tmul`: `Δ a = b ⊗ c` implies `a = ε(b) • c`.

## References

* M. E. Sweedler, *Hopf Algebras*, Chapter 1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- An element whose comultiplication is the pure tensor `b ⊗ c` is the scalar multiple of `c` by
the counit of `b`. -/
theorem eq_counit_smul_of_comul_eq_tmul {a b c : A}
    (h : Coalgebra.comul (R := R) a = b ⊗ₜ[R] c) :
    a = Coalgebra.counit (R := R) b • c := by
  simpa [h] using congr(TensorProduct.lid R A $(Coalgebra.rTensor_counit_comul (R := R) a)).symm

end TauCeti.Coalgebra
