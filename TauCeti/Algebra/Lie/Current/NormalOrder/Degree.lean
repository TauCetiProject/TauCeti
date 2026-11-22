/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CompletedDerivation
public import TauCeti.Algebra.Lie.Current.NormalOrder.Basic

import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Degree of normally ordered modes in the completed enveloping algebra

Over any commutative ring `R`, the completed degree derivation `t d/dt`
(`TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation`) multiplies every normally
ordered summand of `:x y:_n` by `n`, so by continuity it sends `:x y:_n` to `n • :x y:_n`
(`TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode`).

## Main results

* `TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode`:
  the completed degree derivation `t d/dt` acts by `n` on `:x y:_n`.
-/

public section

noncomputable section

open TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

section Degree

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : R}

local notation "UK" => CentralQuotient R (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a

/-- On the uncompleted level algebra, the degree derivation `t d/dt` multiplies every summand of
`:x y:_n` at any cut `p` by `n`. -/
private theorem vectorFieldEnvelopingDerivation_single_one_normalOrderedSummand
    (p n m : ℤ) (x y : L) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End R UK)
        (normalOrderedSummand Φ hΦ hΦs a p n m x y) =
      n • normalOrderedSummand Φ hΦ hΦs a p n m x y := by
  simp only [normalOrderedSummand_apply]
  split_ifs <;>
  · rw [derivationLieAlgebra.leibniz,
      vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul,
      vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul,
      smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1
    ring

/-- **The completed degree derivation multiplies `:x y:_n` by `n`**, over any commutative ring and
at every central value `a`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode
    (n : ℤ) (x y : L) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End R Û)
        (normalOrderedMode Φ hΦ hΦs a n x y) =
      n • normalOrderedMode Φ hΦ hΦs a n x y := by
  let D := (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) :
    Module.End R Û)
  have hterm (m : ℤ) :
      D (toCompletedEnveloping Φ hΦ hΦs a (normalOrderedSummand Φ hΦ hΦs a 0 n m x y)) =
        n • toCompletedEnveloping Φ hΦ hΦs a (normalOrderedSummand Φ hΦ hΦs a 0 n m x y) := by
    simp only [D, coe_toCompletedEnveloping,
      vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
      vectorFieldEnvelopingDerivation_single_one_normalOrderedSummand, map_zsmul]
  have h₁ := (hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) n x y).map
    D.toAddMonoidHom
    (continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1))
  simp only [Function.comp_def, LinearMap.toAddMonoidHom_coe, hterm] at h₁
  exact h₁.unique ((hasSum_normalOrderedMode n x y).const_smul n)

end Degree

end TauCeti.CurrentAlgebra
