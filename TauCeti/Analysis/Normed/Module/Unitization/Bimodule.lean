/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Unitization.Basic

/-!
# Unitizing bounded bimodule actions

A bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E` extends uniquely to a bounded
bilinear action of the external ℓ¹ unitization, with `(λ,a)` acting as `λ • id + M a`.
This construction does not require an associativity law. It therefore applies to both
left and right actions, with the algebra argument first in both cases.

The left associativity, reversed right associativity (`unitizationActionL_mul_rev_iff`),
and commuting-action laws hold for the extensions exactly when they hold for the original
actions. Thus a bounded bimodule
over a possibly nonunital algebra is equivalently a compatible unital bounded bimodule
over its unitization. No contractivity or completeness assumption is needed. The
uniqueness and intertwining results allow module maps to pass between these descriptions.

The single-action extension, uniqueness, left associativity, and intertwining results live in
`TauCeti.Analysis.Normed.Module.Unitization.Basic`. Its
`ContinuousLinearMap.unitizationAction` is the algebra-homomorphism form of the same extension
for associative left actions.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3 and 2.8.
-/

public section

open Unitization WithLp

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Right associativity is preserved and reflected by unitization. Here `R a x`
means `x · a`, so the order of the nested actions is reversed. -/
theorem unitizationActionL_mul_rev_iff (R : A →L[𝕜] E →L[𝕜] E) :
    (∀ u v x, R.unitizationActionL (u * v) x =
      R.unitizationActionL v (R.unitizationActionL u x)) ↔
    ∀ a b x, R (a * b) x = R b (R a x) := by
  constructor
  · intro h a b x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) (toLp 1 (b : Unitization 𝕜 A)) x
  · intro h u v x
    simp [unitizationActionL_apply, snd_mul, map_add, map_smul, smul_add,
      smul_smul, h, add_assoc, add_comm, add_left_comm]

/-- The extended left and right actions commute exactly when the original ones do. -/
theorem unitizationActionL_comm_iff (L R : A →L[𝕜] E →L[𝕜] E) :
    (∀ u v x, L.unitizationActionL u (R.unitizationActionL v x) =
      R.unitizationActionL v (L.unitizationActionL u x)) ↔
    ∀ a b x, L a (R b x) = R b (L a x) := by
  constructor
  · intro h a b x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) (toLp 1 (b : Unitization 𝕜 A)) x
  · intro h u v x
    simp [map_add, map_smul, smul_add, smul_smul, h,
      mul_comm, add_assoc, add_comm, add_left_comm]

end ContinuousLinearMap
