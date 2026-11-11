/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Faithful scalars in an algebraic closure

If a ring `R` acts faithfully on a field `K`, it also acts faithfully on the algebraic closure
`AlgebraicClosure K`, since `K` embeds in it. In particular an integral domain `R` embeds in an
algebraic closure of its field of fractions, which is the usual way to pass from `R` to an
algebraically closed field.

## Main results

* `AlgebraicClosure.instFaithfulSMul`: `R` acts faithfully on `AlgebraicClosure K` when it acts
  faithfully on `K`.
-/

public section

namespace AlgebraicClosure

/-- A faithful action on a field `K` stays faithful on its algebraic closure. -/
instance instFaithfulSMul {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K] :
    FaithfulSMul R (AlgebraicClosure K) :=
  FaithfulSMul.trans R K _

end AlgebraicClosure
