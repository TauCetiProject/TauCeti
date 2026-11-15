/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.Nested
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# A highest-root commutator in the characteristic-three G₂ carrier

The integral long-long-short commutator relation transfers to the short-root carrier
generated over `𝔽₃`. Its highest-root parameter is `-a³bc`, with the sign determined by
conjugating the numbered long simple-root subgroup by the actual root word `n₂ n₁`.
The cubic must not be replaced by `a`: test algebras need not be the prime field.

The transfer uses the proved matrix comparison for simple root points, not an equality
between the generated carrier and the specialization of the integral toral closure.
The carrier is not identified with the pinned simply connected group scheme of type G₂;
transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The integral calculation is in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.Nested`.
-/

public section

universe v

open scoped commutatorElement

namespace TauCeti.G2ShortRoot.PrimeField

variable (A : Type v) [CommRing A] [Algebra (ZMod 3) A]

local notation "x" => rootSubgroupPoints (Sum.inl 0) A
local notation "y" => rootSubgroupPoints (Sum.inl 1) A
local notation "n₀" =>
  (x (Multiplicative.ofAdd 1) * rootSubgroupPoints (Sum.inr 0) A (Multiplicative.ofAdd (-1)) *
    x (Multiplicative.ofAdd 1))
local notation "n₁" =>
  (y (Multiplicative.ofAdd 1) * rootSubgroupPoints (Sum.inr 1) A (Multiplicative.ofAdd (-1)) *
    y (Multiplicative.ofAdd 1))

/-- The long-long-short commutator in the generated characteristic-three carrier is the
highest-root point of parameter `-a³bc`, in the parametrization transported by `n₂ n₁`. -/
theorem commutatorElement_long_commutatorElement_long_short (a b c : A) :
    ⁅y (Multiplicative.ofAdd b),
      ⁅y (Multiplicative.ofAdd c), x (Multiplicative.ofAdd a)⁆⁆ =
      (n₁ * n₀) * y (Multiplicative.ofAdd (-(a ^ 3 * b * c))) * (n₁ * n₀)⁻¹ := by
  apply (points A).subtype_injective
  simpa only [map_commutatorElement, map_mul, map_inv, Subgroup.subtype_apply,
    coe_rootSubgroupPoints] using
    congrArg (IntegralToralClosure.points A).subtype
      (IntegralToralClosure.commutatorElement_long_commutatorElement_long_short A a b c)

end TauCeti.G2ShortRoot.PrimeField
