/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.LongGauss

/-!
# Long-root Gauss relations for the F₄ carrier over 𝔽₂

The two multiplication orders of opposite long simple-root points admit Gauss
factorizations over every commutative 𝔽₂-algebra. The parameters and simple-coroot
torus factors are those of the integral short-root carrier, transported using
`PrimeField.coe_rootSubgroupPoints` and `PrimeField.coe_weightTorusPoints`.
No equality between the generated carrier and the specialization of the integral
toral closure is needed or asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

universe v

/-- The lower-torus-upper Gauss factorization at a long simple node of the
characteristic-two carrier, valid also over nonreduced value algebras. -/
theorem rootSubgroupPoints_inl_mul_inr_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2)
    {A : Type v} [CommRing A] [Algebra (ZMod 2) A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  have h := congrArg (fun g : F4ShortRoot.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 26) A))
    (F4ShortRoot.rootSubgroupPoints_inl_mul_inr_of_lt_two i hi a b u hu)
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using h

/-- The upper-torus-lower Gauss factorization at a long simple node of the
characteristic-two carrier, with inverse simple-coroot torus factor. -/
theorem rootSubgroupPoints_inr_mul_inl_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2)
    {A : Type v} [CommRing A] [Algebra (ZMod 2) A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  apply Subtype.ext
  have h := congrArg (fun g : F4ShortRoot.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 26) A))
    (F4ShortRoot.rootSubgroupPoints_inr_mul_inl_of_lt_two i hi a b u hu)
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using h

end TauCeti.F4ShortRoot.PrimeField
