/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Descent
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra

/-!
# Finiteness of faithfully flat Galois extensions

For a commutative comodule algebra `A` over a bialgebra `H`, a bijective Galois map identifies
`A ⊗[B] A` with `A ⊗[R] H`. If `A` is faithfully flat over `B`, finiteness and finite
presentation of `H` descend to `A/B`. In particular, a torsor under a finite locally free
affine group scheme has a finitely presented quotient projection, as required for the fppf
topology.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §8.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

section Finite

variable {R H A B : Type*} [CommSemiring R] [CommRing H] [Bialgebra R H] [CommRing A]
  [Algebra R A] [ComoduleAlgebra R H A] [CommRing B] [Algebra R B] [Algebra B A]
  [IsScalarTower R B A] [Module.FaithfullyFlat B A]

/-- A faithfully flat Galois extension for a module-finite bialgebra is module-finite. -/
theorem finite_of_bijective_galoisMap [Module.Finite R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) : Module.Finite B A := by
  let e := AlgEquiv.ofBijective (galoisMap B hB) hbij
  have : Module.Finite A (A ⊗[B] A) := .equiv e.symm.toLinearEquiv
  exact .of_finite_tensorProduct_of_faithfullyFlat A

end Finite

variable {R H A B : Type*} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing A]
  [Algebra R A] [ComoduleAlgebra R H A] [CommRing B] [Algebra R B] [Algebra B A]
  [IsScalarTower R B A] [Module.FaithfullyFlat B A]

/-- A faithfully flat Galois extension for a finitely presented bialgebra is finitely
presented as an algebra. No finiteness assumption on the underlying module is needed. -/
theorem finitePresentation_of_bijective_galoisMap [Algebra.FinitePresentation R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) : Algebra.FinitePresentation B A := by
  let e := AlgEquiv.ofBijective (galoisMap B hB) hbij
  have : Algebra.FinitePresentation A (A ⊗[B] A) := .equiv e.symm
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat A

end TauCeti.ComoduleAlgebra
