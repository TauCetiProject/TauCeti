/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Checks for normality under separably generated base change of the ground field

`TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparablyGenerated` applies to every
finite extension of `ℚ`, such as `ℚ(i)`, where the base change of `Spec ℚ(i)` is two reduced points,
and to transcendental extensions such as `k(s)` over a perfect field `k`, which are not algebraic,
so that `Algebra.IsSeparable k k(s)` fails: the hypothesis is separable generation, not
separability. In both cases the separable-generation hypothesis is found by instance search from
the perfectness of the ground field.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.NormalBaseChangeExample

-- Base change of a normal `ℚ`-scheme along a finite extension of `ℚ` (such as `ℚ(i)`) is normal.
example {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) [IsNormalScheme X] (K : Type) [Field K]
    [Algebra ℚ K] [FiniteDimensional ℚ K] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

-- Base change along the purely transcendental extension `k(s) / k` of a perfect field: not an
-- algebraic extension, but separably generated.
example (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsNormalScheme X] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k)))))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

-- The extension `k(s) / k` is not algebraic, so `Algebra.IsSeparable` fails for it.
example (k : Type u) [Field k] : ¬ Algebra.IsSeparable k (FractionRing (Polynomial k)) :=
  fun _ ↦ Polynomial.transcendental_X k <| (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k)))
    (IsFractionRing.injective _ _)).mp (Algebra.IsAlgebraic.isAlgebraic _)

end TauCeti.NormalBaseChangeExample
