/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.WeylSquare
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Squares of the pinned rank-one words in the characteristic-three G₂ carrier

At every unit `u`, the word `nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` in the short-root
carrier generated over `𝔽₃` squares to the simple-coroot value `αᵢ∨(-1)`.
This supplies the rank-one square relation for the numbered root subgroups over
every commutative `𝔽₃`-algebra.

The proof transfers the integral identity through the faithful matrix realizations.
It does not identify the carrier generated over the prime field with the base change
of the integral toral closure, nor with an independently constructed pinned group.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

/-- The square of the pinned rank-one word is the simple-coroot value at `-1`,
also over nonreduced coefficient algebras. -/
@[simp↓]
theorem rootSubgroupPoints_weylWord_sq (i : Fin 2) (A : Type*) [CommRing A]
    [Algebra (ZMod 3) A] (u : Aˣ) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A)) *
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 2 =
      weightTorusPoints A (Pi.mulSingle i (-1)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_rootSubgroupPoints,
    coe_weightTorusPoints] using
    congrArg (fun g : IntegralToralClosure.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 7) A))
      (IntegralToralClosure.rootSubgroupPoints_weylWord_sq i A u)

end TauCeti.G2ShortRoot.PrimeField
