/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.ZMod.Basic
-- `IsSimpleRing (ZMod p)`, used to see the structure morphism of the prime field as injective.
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Characteristic of an algebra over a prime field

An algebra over `ZMod p` has characteristic `p` as soon as it is nontrivial: the prime field is a
field, so its structure morphism is injective. The trivial ring is the only obstruction, and an
algebra morphism back to `ZMod p` rules it out. A commutative Hopf algebra over `ZMod p` has one —
its counit — and so does a tensor product of two such, so the criterion below is what a
construction over the prime field uses to invoke the Frobenius or a characteristic-`p` identity on
its coordinate algebra.

## Main results

* `TauCeti.charP_of_nontrivial_zmodAlgebra`: a nontrivial algebra over `ZMod p` has characteristic
  `p`.
* `TauCeti.charP_of_algHom_zmod`: an algebra over `ZMod p` admitting an algebra morphism back to
  `ZMod p` has characteristic `p`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Algebra (ZMod p) A]

/-- **A nontrivial algebra over the prime field `ZMod p` has characteristic `p`.** -/
theorem charP_of_nontrivial_zmodAlgebra [Nontrivial A] : CharP A p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

variable {A}

/-- **An algebra over the prime field `ZMod p` with an algebra morphism back to `ZMod p` has
characteristic `p`.** The morphism makes the algebra nontrivial. -/
theorem charP_of_algHom_zmod (φ : A →ₐ[ZMod p] ZMod p) : CharP A p :=
  letI : Nontrivial A := (φ : A →+* ZMod p).domain_nontrivial
  charP_of_nontrivial_zmodAlgebra p A

end TauCeti
