/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.FieldTheory.Separable.FractionRingPolynomial
public import Mathlib.Algebra.Field.ZMod

/-!
# Check: purely transcendental base change over an imperfect field

`TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparablyGenerated` applies to the purely
transcendental extension `k(s) / k` of every field `k`, perfect or not, since `{s}` is a separating
transcendence basis (`TauCeti.instIsSeparablyGeneratedFractionRingPolynomial`). In particular, for
`k = 𝔽_p(t)` and `W = Spec k[y]`, the base change `W_{k(s)} = Spec k(s)[y]` is normal, though
`k(s) / k` is not algebraic, so not `Algebra.IsSeparable`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.NormalBaseChangeTranscendentalExample

-- Base change along `k(s) / k` preserves normality, for every field `k`.
example (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsNormalScheme X] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k)))))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

/-- For every field `k` and `W = Spec k[y]`, the base change of `W` along `k(s) / k` is normal. -/
theorem isNormalScheme_pullback_polynomial (k : Type u) [Field k] :
    IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing (Polynomial k)))))) :=
  haveI : IsNormalScheme (Spec (.of (Polynomial k))) := isNormalScheme_Spec _
  isNormalScheme_pullback_of_isSeparablyGenerated _

-- For `k = 𝔽_p(t)` (as `FractionRing (ZMod p)[t]`), an imperfect field, and `W = Spec k[y]`, the
-- base change of `W` along `k(s) / k` is normal.
example (p : ℕ) [Fact p.Prime] :
    IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (FractionRing (Polynomial (ZMod p))) (Polynomial (FractionRing (Polynomial (ZMod p)))))))
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (Polynomial (ZMod p)))
        (FractionRing (Polynomial (FractionRing (Polynomial (ZMod p))))))))) :=
  isNormalScheme_pullback_polynomial _

end TauCeti.NormalBaseChangeTranscendentalExample
