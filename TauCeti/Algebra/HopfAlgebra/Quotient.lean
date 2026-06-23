/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# The quotient Hopf algebra of a Hopf ideal

For a Hopf algebra `H` over a commutative ring `R` and a Hopf ideal `I` of `H`, Mathlib equips the
quotient ring `H ⧸ I` with the structure of a Hopf algebra over `R`, descending the
comultiplication, counit and antipode from `H` (see
`Mathlib.RingTheory.{Coalgebra,Bialgebra,HopfAlgebra}.Quotient`). Mathlib's instances fire on an
`Ideal` once it is known to be two-sided, a coideal, and antipode-stable. The **bridge** turning a
`TauCeti.HopfIdeal` into those Mathlib hypotheses lives in `TauCeti.Algebra.HopfAlgebra.HopfIdeal`
(`HopfIdeal.instIsCoideal`, `HopfIdeal.instIsHopfIdeal`), so that Mathlib's
`Coalgebra`/`Bialgebra`/`HopfAlgebra` instances apply to `H ⧸ I.toIdeal`.

The quotient coalgebra/bialgebra/Hopf-algebra structure maps and the quotient bialgebra morphism
are Mathlib's own `Bialgebra.Quotient.comulAlgHom`, `Bialgebra.Quotient.counitAlgHom`,
`Bialgebra.Quotient.mkBialgHom`, and `HopfAlgebra.antipode`; use them directly on
`H ⧸ I.toIdeal`. In the commutative quotient case, Mathlib also provides the antipode as the
algebra hom `HopfAlgebra.antipodeAlgHom`. For the universal property of the quotient bialgebra,
use `Bialgebra.Quotient.liftBialgHom I.toIdeal` and its companion lemmas directly; it needs only
the bialgebra quotient hypotheses, not the antipode-stability part of a Hopf ideal.

## References

This follows the standard construction of the quotient Hopf algebra; see Sweedler,
*Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine Group Schemes*, §16. It
builds on the `TauCeti.HopfIdeal` API and Mathlib's quotient Hopf-algebra machinery
(`Mathlib.RingTheory.HopfAlgebra.Quotient`, due to Robert Hawkins).
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace HopfIdeal

universe u v

end HopfIdeal

end TauCeti
