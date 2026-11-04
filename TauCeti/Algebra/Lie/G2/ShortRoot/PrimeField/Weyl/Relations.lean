/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Weyl.Relations
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# The six-term braid relation on the characteristic-three short-root G₂ carrier

The numbered simple-root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` of the carrier generated over
`𝔽₃` satisfy `(n₀ n₁)³ = (n₁ n₀)³` over every commutative value algebra, including
nonreduced algebras. This permits a braid move in Weyl-word root transport, without asserting
independence of arbitrary root-subgroup presentations.

The proof transfers the integral relation through the existing comparison of root matrices,
not through an identification with the specialization of the integral toral closure. The carrier
is not identified here with an independently constructed pinned simply connected group scheme;
constructions transfer to such a group only along a separately proved identification.

## Main result

* `TauCeti.G2ShortRoot.PrimeField.rootSubgroupPoints_braid`: the six-term braid relation.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, the relations for the elements `nᵢ`.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

universe v

namespace TauCeti.G2ShortRoot.PrimeField

/-- The pinned simple-root words of the carrier generated over `𝔽₃` satisfy the six-term
braid relation, including over nonreduced value algebras. -/
theorem rootSubgroupPoints_braid (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  dsimp only
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_rootSubgroupPoints] using
    congrArg (fun g : IntegralToralClosure.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 7) A))
      (IntegralToralClosure.rootSubgroupPoints_braid A)

end TauCeti.G2ShortRoot.PrimeField
