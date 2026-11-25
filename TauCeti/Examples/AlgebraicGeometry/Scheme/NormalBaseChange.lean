/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.FieldTheory.Separable.FractionRingPolynomial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Complex.IsIntegral

/-!
# Checks for normality under separably generated base change of the ground field

`TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparablyGenerated` applies to every
finite extension of `ℚ`, such as `ℚ(i)`, where the base change of `Spec ℚ(i)` is two reduced points,
and to the purely transcendental extension `k(s)` of every field `k`, perfect or not, which is not
algebraic, so that `Algebra.IsSeparable k k(s)` fails: the hypothesis is separable generation, not
separability. Over `ℚ` the separable-generation hypothesis is found by instance search from the
perfectness of the ground field; for `k(s)` it comes from the separating transcendence basis `{s}`
(`TauCeti.instIsSeparablyGeneratedFractionRingPolynomial`). In particular, for the imperfect field
`k = 𝔽_p(t)` and `W = Spec k[y]`, the base change `W_{k(s)} = Spec k(s)[y]` is normal.

The conclusion concerns the local rings and cannot be strengthened, nor the hypothesis dropped:

* For `k'/k` containing an element `a ∉ k` with `a * a ∈ k`, such as `i` with `i² = -1`, the ring
  `k' ⊗[k] k'` is not a domain (`(a ⊗ 1 - 1 ⊗ a)(a ⊗ 1 + 1 ⊗ a) = 0`), so the base change of
  `Spec k'` along `k'` is not integral (`not_isIntegral_pullback_of_mul_self_mem_range`). For
  `k' = ℚ(i)` it is normal but not integral (`isNormalScheme_pullback_rat_adjoin_I`,
  `not_isIntegral_pullback_rat_adjoin_I`).
* For `k` of characteristic `p` and `k'/k` containing an element `a ∉ k` with `a ^ p ∈ k` (such as
  `k(t ^ (1 / p))` over `𝔽_p(t)`), `a ⊗ 1 - 1 ⊗ a` is a nonzero nilpotent of `k' ⊗[k] k'`, so the
  base change of the normal scheme `Spec k'` along the inseparable `k'/k` is not reduced
  (`not_isReduced_pullback_of_pow_char_mem_range`), hence not normal: separability cannot be
  dropped.
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

-- Base change along the purely transcendental extension `k(s) / k` of every field `k`: not an
-- algebraic extension, but separably generated.
example (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsNormalScheme X] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k)))))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

-- For `k = 𝔽_p(t)` (as `FractionRing (ZMod p)[t]`), an imperfect field, and `W = Spec k[y]`, the
-- base change of `W` along `k(s) / k` is normal.
example (p : ℕ) [Fact p.Prime] :
    IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (FractionRing (Polynomial (ZMod p))) (Polynomial (FractionRing (Polynomial (ZMod p)))))))
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (Polynomial (ZMod p)))
        (FractionRing (Polynomial (FractionRing (Polynomial (ZMod p))))))))) :=
  haveI := isNormalScheme_Spec (.of (Polynomial (FractionRing (Polynomial (ZMod p)))))
  isNormalScheme_pullback_of_isSeparablyGenerated _

-- The extension `k(s) / k` is not algebraic, so `Algebra.IsSeparable` fails for it.
example (k : Type u) [Field k] : ¬ Algebra.IsSeparable k (FractionRing (Polynomial k)) :=
  fun _ ↦ Polynomial.transcendental_X k <| (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k)))
    (IsFractionRing.injective _ _)).mp (Algebra.IsAlgebraic.isAlgebraic _)

section GaussianRationals

open IntermediateField

/-- `ℚ(i)` is a finite extension of `ℚ`. -/
instance instFiniteDimensionalRatAdjoinI : FiniteDimensional ℚ ℚ⟮Complex.I⟯ :=
  adjoin.finiteDimensional (Complex.isIntegral_I ℚ)

/-- The generator `i` of `ℚ(i)` is not rational. -/
theorem gen_rat_adjoin_I_notMem_range_algebraMap :
    (AdjoinSimple.gen ℚ Complex.I) ∉ Set.range (algebraMap ℚ ℚ⟮Complex.I⟯) := by
  rintro ⟨q, hq⟩
  have := congrArg (fun x : ℚ⟮Complex.I⟯ ↦ ((x : ℂ)).im) hq
  simp at this

/-- **Check.** Base change of `Spec ℚ(i)` along `ℚ(i) / ℚ` is normal. -/
theorem isNormalScheme_pullback_rat_adjoin_I :
    IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated _

/-- **Check.** Base change of `Spec ℚ(i)` along `ℚ(i) / ℚ`, which is `Spec (ℚ(i) × ℚ(i))`, is not
integral: the conclusion of `isNormalScheme_pullback_of_isSeparablyGenerated` concerns the local
rings and cannot be strengthened to integrality. -/
theorem not_isIntegral_pullback_rat_adjoin_I :
    ¬ IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))) :=
  not_isIntegral_pullback_of_mul_self_mem_range gen_rat_adjoin_I_notMem_range_algebraMap
    ⟨-1, Subtype.ext (by simp)⟩

end GaussianRationals

end TauCeti.NormalBaseChangeExample
