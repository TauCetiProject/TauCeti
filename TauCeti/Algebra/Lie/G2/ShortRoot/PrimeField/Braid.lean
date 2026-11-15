/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Braid

/-!
# The six-term braid relation in the characteristic-three G₂ carrier

The pinned root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy the type-G₂ braid relation
`(n₀ n₁)³ = (n₁ n₀)³` in the short-root carrier generated over `𝔽₃`, over every
commutative `𝔽₃`-algebra. This controls the relation between the two numbered reflections,
not only their separate actions on simple root subgroups.

The equality is transferred through the faithful matrix inclusions from the integral
root-word calculation. It does not assert that the generated carrier is the base change of
the integral toral closure, or identify it with an independently pinned group scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Section 3.
* R. W. Carter, *Simple Groups of Lie Type*, Section 7.2.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

/-- The pinned simple-root words in the characteristic-three short-root G₂ carrier satisfy
the six-term braid relation. The value algebra need not be a field or reduced. -/
theorem rootSubgroupPoints_braid (A : Type*) [CommRing A] [Algebra (ZMod 3) A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  dsimp only
  apply Subtype.ext
  have h := congrArg (fun g : IntegralToralClosure.points A =>
    (g : Matrix.GeneralLinearGroup (Fin 7) A))
      (IntegralToralClosure.rootSubgroupPoints_braid A)
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_rootSubgroupPoints] using h

end TauCeti.G2ShortRoot.PrimeField
