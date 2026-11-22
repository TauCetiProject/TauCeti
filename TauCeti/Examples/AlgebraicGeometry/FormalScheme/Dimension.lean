/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Dimension
public import TauCeti.AlgebraicGeometry.FormalScheme.Regular
public import TauCeti.RingTheory.AdicRing.Quotient
public import TauCeti.RingTheory.Huber.Padic.Basic

import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Examples of the dimension and regularity of formal schemes

The formal spectrum of `ℤ_[p]`, with its `p`-adic topology, has a single point, the maximal
ideal `(p)`. Its underlying space therefore has Krull dimension `0`, while the formal scheme has
dimension `1`, the dimension of its local ring `ℤ_[p]`. It is regular, as `ℤ_[p]` is a discrete
valuation ring, and its unique point is closed.
-/

public section

open AlgebraicGeometry IsLocalRing
open TauCeti TauCeti.FormalScheme

namespace TauCeti.Examples.FormalScheme

-- The dimension of `Spf (A ⧸ 𝔞)` is that of `A ⧸ 𝔞`, with the quotient topology.
example (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [IsNoetherianRing A] (𝔞 : Ideal A) : (ofSpf (A ⧸ 𝔞)).dim = ringKrullDim (A ⧸ 𝔞) :=
  dim_ofSpf _

variable (p : ℕ) [Fact p.Prime]

-- The one-point formal spectrum `Spf ℤ_[p]` has dimension `1`, not `0`.
example : (ofSpf ℤ_[p]).dim = 1 := by
  rw [dim_ofSpf, IsDiscreteValuationRing.ringKrullDim_eq_one]

-- `Spf ℤ_[p]` is regular and hence Cohen–Macaulay.
example : (ofSpf ℤ_[p]).IsRegular := inferInstance

example : (ofSpf ℤ_[p]).IsCohenMacaulay := inferInstance

/-- Every point of `Spf ℤ_[p]` is the maximal ideal `(p)`. -/
theorem asIdeal_eq_maximalIdeal (x : Spf.carrier ℤ_[p]) :
    (x : PrimeSpectrum ℤ_[p]).asIdeal = maximalIdeal ℤ_[p] :=
  ((maximalIdeal.isMaximal _).eq_of_le (x : PrimeSpectrum ℤ_[p]).isPrime.ne_top
    ((Spf.mem_carrier_iff_le Huber.PadicInt.isAdic_maximalIdeal).mp x.property)).symm

-- Hence the underlying space of `Spf ℤ_[p]` has Krull dimension `0`.
example : topologicalKrullDim (Spf.carrier ℤ_[p]) ≤ 0 :=
  have : Subsingleton (Spf.carrier ℤ_[p]) := ⟨fun x y ↦ Subtype.ext <| PrimeSpectrum.ext <|
    (asIdeal_eq_maximalIdeal p x).trans (asIdeal_eq_maximalIdeal p y).symm⟩
  topologicalKrullDim_zero_of_discreteTopology _

-- The point of `Spf ℤ_[p]` is closed.
example (x : Spf.carrier ℤ_[p]) : IsClosed ({x} : Set (Spf.carrier ℤ_[p])) :=
  (Spf.isClosed_singleton_iff_isMaximal Huber.PadicInt.isAdic_maximalIdeal).mpr
    (asIdeal_eq_maximalIdeal p x ▸ maximalIdeal.isMaximal _)

end TauCeti.Examples.FormalScheme
