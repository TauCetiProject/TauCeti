/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.RingTheory.FrobeniusAlgebra.Basic

/-!
# A Frobenius algebra is self-injective on both sides

A finite-dimensional algebra carrying a Frobenius functional is self-injective: its regular module
is injective, on the left and on the right. This is the criterion
`Function.Bijective.moduleBaer_self`, whose hypotheses are exactly associativity of the pairing and
bijectivity of its flip; a Frobenius functional supplies both, the second because on a
finite-dimensional algebra a nondegenerate pairing identifies the algebra with its dual.

The right-handed statement is the left-handed one for the opposite algebra, reached through
`TauCeti.FrobeniusFunctional.op`.
-/

public section

namespace TauCeti

namespace FrobeniusFunctional

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (F : FrobeniusFunctional k A)

include F

/-- **A Frobenius algebra is left self-injective**, in Baer's form: every linear map from a left
ideal to the regular module extends to the algebra. -/
theorem moduleBaer_self : Module.Baer A A :=
  Function.Bijective.moduleBaer_self F.bijective_pairing_flip F.pairing_mul_assoc

/-- **A Frobenius algebra is left self-injective**: its regular left module is injective. -/
theorem moduleInjective_self : Module.Injective A A :=
  Function.Bijective.moduleInjective_self F.bijective_pairing_flip F.pairing_mul_assoc

/-- **A Frobenius algebra is right self-injective**: the regular module of the opposite algebra,
which is the right regular module of `A`, is injective. -/
theorem moduleInjective_op : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ :=
  F.op.moduleInjective_self

end FrobeniusFunctional

end TauCeti
