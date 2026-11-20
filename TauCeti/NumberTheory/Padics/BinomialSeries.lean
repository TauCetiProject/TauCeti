/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.RingTheory.PowerSeries.Substitution

import TauCeti.RingTheory.PowerSeries.Binomial

/-!
# The `p`-adic binomial series depends continuously on its exponent

For a `p`-adic integer `u`, the binomial series `(1 + X) ^ u = ∑ₖ (u choose k) Xᵏ` is a power
series over any semiring `A` with a scalar action of `ℤ_[p]`. Its coefficients
`u ↦ (u choose k) • 1` are continuous functions of `u` (`PadicInt.continuous_choose`) as soon as
the scalar action is continuous, so for the product topology on `A⟦X⟧` the series itself depends
continuously on `u`. This is the continuity that lets an identity between `(1 + X) ^ u` and a
`p`-adic power, valid for natural exponents, be extended to all `p`-adic exponents by density of
`ℕ` in `ℤ_[p]`. This file proves one such identity, the composition law of binomial
substitutions: over every `ℤ_p`-algebra, substituting `(1 + X) ^ a - 1` into `(1 + X) ^ b` gives
`(1 + X) ^ (a b)`. For natural `b` it reads `((1 + X) ^ a) ^ b = (1 + X) ^ (a b)`.

## Main results

* `PadicInt.continuous_binomialSeries`: `u ↦ binomialSeries A u` is continuous for the product
  topology on `A⟦X⟧`.
* `Continuous.powerSeries_subst_binomialSeries_sub_one`: binomial substitution depends
  continuously on both the exponent and the outer series, in any topological p-adic algebra
  with continuous scalar action. This permits dilation identities to extend from natural to
  p-adic parameters.
* `PadicInt.binomialSeries_subst_binomialSeries_sub_one`: `((1 + X) ^ b)((1 + X) ^ a - 1)` is
  `(1 + X) ^ (a b)` over any `ℤ_p`-algebra.
-/

public section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **The binomial series `(1 + X) ^ u` is a continuous function of the exponent `u ∈ ℤ_[p]`**, for
the product topology on `A⟦X⟧`: each coefficient `u ↦ (u choose k) • 1` is continuous. -/
theorem continuous_binomialSeries {A : Type*} [Semiring A] [SMul ℤ_[p] A] [TopologicalSpace A]
    [ContinuousSMul ℤ_[p] A] :
    Continuous fun u : ℤ_[p] ↦ binomialSeries A u := by
  refine continuous_iff_continuousAt.mpr fun u ↦
    (WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
  simp only [binomialSeries_coeff]
  exact ((continuous_choose n).smul continuous_const).continuousAt

end PadicInt

/-- Binomial substitution `F s ↦ (F s)((1 + X) ^ (a s) - 1)` depends continuously on both the
exponent `a s` and an independently varying outer series `F s`, for the coefficientwise
topologies. -/
theorem Continuous.powerSeries_subst_binomialSeries_sub_one {p : ℕ} [Fact p.Prime]
    {R S A : Type*} [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] [Algebra R S] [ContinuousSMul R S] [Algebra ℤ_[p] S]
    [ContinuousSMul ℤ_[p] S] [TopologicalSpace A]
    {F : A → R⟦X⟧} {a : A → ℤ_[p]} (hF : Continuous F) (ha : Continuous a) :
    Continuous fun s ↦ (F s).subst (binomialSeries S (a s) - 1) :=
  hF.powerSeries_subst
    (((PadicInt.continuous_binomialSeries (A := S)).comp' ha).sub continuous_const) fun s ↦ by simp

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Composition law of binomial substitutions.** Over any `ℤ_p`-algebra `O`, substituting
`(1 + X) ^ a - 1` into `(1 + X) ^ b` gives `(1 + X) ^ (a b)`, for all `a b ∈ ℤ_p`. -/
theorem binomialSeries_subst_binomialSeries_sub_one {O : Type*} [CommRing O] [Algebra ℤ_[p] O]
    (a b : ℤ_[p]) :
    (binomialSeries O b).subst (binomialSeries O a - 1) = binomialSeries O (a * b) := by
  have hl : Continuous fun b : ℤ_[p] ↦
      (binomialSeries ℤ_[p] b).subst (binomialSeries ℤ_[p] a - 1) :=
    continuous_binomialSeries.powerSeries_subst_binomialSeries_sub_one continuous_const
  have hr : Continuous fun b : ℤ_[p] ↦ binomialSeries ℤ_[p] (a * b) :=
    continuous_binomialSeries.comp (continuous_const.mul continuous_id)
  -- Over `ℤ_p` both sides are continuous in `b`, and they agree on the dense subset `ℕ`, where
  -- the identity is `((1 + X) ^ a) ^ n = (1 + X) ^ (a n)`.
  have h := congrFun (denseRange_natCast.equalizer hl hr (funext fun n ↦ ?_)) b
  · -- transport the identity over `ℤ_p` to `O` along the algebra map
    have hs : map (algebraMap ℤ_[p] O)
        ((binomialSeries ℤ_[p] b).subst (binomialSeries ℤ_[p] a - 1)) =
        (map (algebraMap ℤ_[p] O) (binomialSeries ℤ_[p] b)).subst
          (map (algebraMap ℤ_[p] O) (binomialSeries ℤ_[p] a - 1)) :=
      PowerSeries.map_subst (TauCeti.hasSubst_binomialSeries_sub_one a) _
    rw [h, map_sub, map_one, ← Algebra.toRingHom_ofId,
      map_binomialSeries, map_binomialSeries, map_binomialSeries] at hs
    exact hs.symm
  · simp only [Function.comp_apply, binomialSeries_nat, mul_comm a, ← nsmul_eq_mul,
      binomialSeries_nsmul, ← coe_substAlgHom (TauCeti.hasSubst_binomialSeries_sub_one a), map_pow,
      map_add, map_one, substAlgHom_X, add_sub_cancel]

end PadicInt
