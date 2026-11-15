/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth algebraic structures on additive and multiplicative type tags

The type tags retain the topology, atlas and smooth structure of their original carrier.
Smooth addition and negation become smooth multiplication and inversion on `Multiplicative`,
and the reverse transfer equips `Additive` with its additive Lie-group structure.
The transfers preserve the field, model with corners, universes and regularity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 7,
  Example 7.3(f), pp.151–152, for vector spaces viewed as additive Lie groups.
* Mathlib, `Geometry/Manifold/Algebra/LieGroup.lean`, for the smooth algebraic structures.
-/

public section

open scoped Manifold ContDiff

universe u v w

namespace Multiplicative

/-- The type tag retains the original charts. -/
instance chartedSpace {H : Type v} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] : ChartedSpace H (Multiplicative M) :=
  inferInstanceAs (ChartedSpace H M)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The type tag retains the original smooth structure at the same regularity. -/
instance isManifold [IsManifold I n M] : IsManifold I n (Multiplicative M) :=
  inferInstanceAs (IsManifold I n M)

/-- Smooth addition is smooth multiplication on the multiplicative type tag. -/
instance contMDiffMul [Add M] [ContMDiffAdd I n M] : ContMDiffMul I n (Multiplicative M) where
  contMDiff_mul := contMDiff_add (I := I) (n := n) (G := M)

/-- An additive Lie group is a multiplicative Lie group after changing its type tag. -/
instance lieGroup [AddGroup M] [LieAddGroup I n M] : LieGroup I n (Multiplicative M) where
  contMDiff_inv := contMDiff_neg (I := I) (n := n) (G := M)

end Multiplicative

namespace Additive

/-- The type tag retains the original charts. -/
instance chartedSpace {H : Type v} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] : ChartedSpace H (Additive M) :=
  inferInstanceAs (ChartedSpace H M)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The type tag retains the original smooth structure at the same regularity. -/
instance isManifold [IsManifold I n M] : IsManifold I n (Additive M) :=
  inferInstanceAs (IsManifold I n M)

/-- Smooth multiplication is smooth addition on the additive type tag. -/
instance contMDiffAdd [Mul M] [ContMDiffMul I n M] : ContMDiffAdd I n (Additive M) where
  contMDiff_add := contMDiff_mul (I := I) (n := n) (G := M)

/-- A multiplicative Lie group is an additive Lie group after changing its type tag. -/
instance lieAddGroup [Group M] [LieGroup I n M] : LieAddGroup I n (Additive M) where
  contMDiff_neg := contMDiff_inv (I := I) (n := n) (G := M)

end Additive
