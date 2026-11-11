/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import TauCeti.RingTheory.Huber.CompleteRankOneBase
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Valuation.AdicSeparated

/-!
# Examples of complete rank-one valuation bases

`ℤ_[p]` with pseudouniformiser `p` satisfies `TauCeti.Huber.IsCompleteRankOneBase`. The element
`0` never does, and neither does a unit, even over a field: the class records that `ϖ` is a
genuine pseudouniformiser rather than only that the topology is adic.
-/

open IsLocalRing TauCeti.Huber

-- The `p`-adic integers form a complete rank-one valuation base with pseudouniformiser `p`.
example (p : ℕ) [Fact p.Prime] : IsCompleteRankOneBase ℤ_[p] (p : ℤ_[p]) where
  ringKrullDim_eq_one := IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]
  ne_zero := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  not_isUnit := (mem_maximalIdeal _).mp
    (PadicInt.maximalIdeal_eq_span_p (p := p) ▸ Ideal.mem_span_singleton_self _)
  isAdic := PadicInt.maximalIdeal_eq_span_p (p := p) ▸ PadicInt.isAdic_maximalIdeal
  isAdicComplete := PadicInt.maximalIdeal_eq_span_p (p := p) ▸ inferInstance

-- The element `0` is not a pseudouniformiser.
example (O : Type*) [CommRing O] [TopologicalSpace O] : ¬ IsCompleteRankOneBase O 0 :=
  fun h ↦ h.ne_zero rfl

-- A unit is not a pseudouniformiser, even over a field.
example (k : Type*) [Field k] [TopologicalSpace k] : ¬ IsCompleteRankOneBase k 1 :=
  fun h ↦ h.not_isUnit isUnit_one

-- Over a separated valuation ring, a nonzero element divides a power of the pseudouniformiser.
example {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O] (ϖ : O)
    [IsCompleteRankOneBase O ϖ] {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ ϖ ^ n :=
  TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff ha
