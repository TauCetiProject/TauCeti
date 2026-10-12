/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Symmetry notions under a coordinatewise almost-everywhere change of process

Every symmetry predicate in this file is a statement about the finite-dimensional laws of `X`, or
— for `FullyExchangeable` — about its path law, so each sees the coordinates only modulo
`μ`-a.e. equality. This file records that replacing each `X i` by a coordinatewise a.e. equal
`Y i` changes none of `ExchangeableAt`, `Exchangeable`, `FullyExchangeable` and `Contractable`.
The underlying congruence API for `blockLaw`, `prefixLaw` and `pathLaw` lives with those generic
process constructions in `Probability/Process/PathLaw/Basic.lean`.

Changing a random variable on a null set is routine — most often to replace an a.e. measurable
coordinate by a measurable version — and without these lemmas a valid process becomes unusable at
the interfaces that demand exact measurability. The representation predicates get the same treatment
beside their own definitions, in `MixedIID/Congr.lean` and `ConditionallyIID/Congr.lean`.

## Main results

* `ExchangeableAt.congr`, `Exchangeable.congr`, `FullyExchangeable.congr`, `Contractable.congr` —
  the symmetry predicates transport.

## Implementation

The generic path-law congruence lemmas reduce to `Measure.map_congr`; the symmetry predicates then
transport by rewriting their defining law equalities.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Exchangeability at a fixed length transports along a coordinatewise a.e. change of process. -/
theorem ExchangeableAt.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} {n : ℕ}
    (hX : ExchangeableAt μ X n) (h : ∀ i, X i =ᵐ[μ] Y i) : ExchangeableAt μ Y n := fun σ => by
  rw [← blockLaw_congr h, ← prefixLaw_congr h]
  exact hX σ

/-- Exchangeability transports along a coordinatewise a.e. change of process. -/
theorem Exchangeable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : Exchangeable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : Exchangeable μ Y := fun n => (hX n).congr h

/-- Full exchangeability transports along a coordinatewise a.e. change of process. -/
theorem FullyExchangeable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : FullyExchangeable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : FullyExchangeable μ Y := fun σ => by
  rw [← pathLaw_congr h, ← hX σ]
  exact Measure.map_congr
    (by filter_upwards [ae_all_iff.2 fun i => (h (σ i)).symm] with ω hω using funext hω)

/-- Contractability transports along a coordinatewise a.e. change of process. -/
theorem Contractable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : Contractable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : Contractable μ Y := fun m k hk => by
  rw [← blockLaw_congr h, ← prefixLaw_congr h]
  exact hX m k hk

end Probability

end TauCeti
