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
`Coalgebra`/`Bialgebra`/`HopfAlgebra` instances apply to `H ⧸ I.toIdeal`. On top of that bridge this
file provides the part Mathlib lacks: the **universal property** `liftBialgHom` of the quotient
bialgebra.

The quotient coalgebra/bialgebra/Hopf-algebra structure maps and the quotient bialgebra morphism
are Mathlib's own `Bialgebra.Quotient.comulAlgHom`, `Bialgebra.Quotient.counitAlgHom`,
`Bialgebra.Quotient.mkBialgHom`, `HopfAlgebra.antipode`, and `HopfAlgebra.antipodeAlgHom`; use them
directly on `H ⧸ I.toIdeal`.

## Main definitions

* `TauCeti.HopfIdeal.liftBialgHom`: the specialization to the underlying ideal of a Hopf ideal of
  the generic bialgebra-quotient universal property `Bialgebra.Quotient.liftBialgHom` (which needs
  only a two-sided coideal, not an antipode, and lives in `TauCeti.Algebra.Bialgebra.Quotient`),
  namely the bialgebra morphism induced from a bialgebra morphism which kills the Hopf ideal,
  together with its computation and uniqueness lemmas.

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

variable {R : Type u} {H : Type v}
variable [CommRing R]

section Ring

variable [Ring H] [HopfAlgebra R H]
variable (I : HopfIdeal R H)
variable {K : Type*} [Semiring K] [Bialgebra R K]

/-- A bialgebra morphism out of `H` which kills a Hopf ideal factors through the quotient
bialgebra.

This is the specialization to `I.toIdeal` of the general bialgebra-quotient universal property
`Bialgebra.Quotient.liftBialgHom`, which only needs a two-sided coideal. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ I.toIdeal →ₐc[R] K :=
  Bialgebra.Quotient.liftBialgHom I.toIdeal f hf

/-- The quotient lift, evaluated on a quotient class. -/
@[simp]
theorem liftBialgHom_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHom I f hf (Ideal.Quotient.mkₐ R I.toIdeal h) = f h :=
  Bialgebra.Quotient.liftBialgHom_mk I.toIdeal f hf h

/-- The quotient lift composed with the quotient map is the original bialgebra morphism. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHom I f hf).comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom I.toIdeal f hf

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ I.toIdeal →ₐc[R] K)
    (hg : g.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f) :
    g = liftBialgHom I f hf :=
  Bialgebra.Quotient.liftBialgHom_unique I.toIdeal f hf g hg

end Ring

end HopfIdeal

end TauCeti
