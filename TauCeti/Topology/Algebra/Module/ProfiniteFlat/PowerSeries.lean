/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.PiTopology
public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic

/-!
# Power series over profinite flat modules

Over a coherent ring `R`, multivariate and univariate formal power series (`MvPowerSeries σ S`
and `PowerSeries S`) with coefficients in a profinite flat `R`-module ring `S`, equipped with the
coefficientwise product topology, are profinite flat `R`-modules
(`TauCeti.IsProfiniteFlat.mvPowerSeries`, `TauCeti.IsProfiniteFlat.powerSeries`).
-/

public section

namespace TauCeti.IsProfiniteFlat

open scoped MvPowerSeries.WithPiTopology PowerSeries.WithPiTopology

variable {R S : Type*} [CommRing R] [TauCeti.IsCoherentRing R] [TopologicalSpace R]
  [Ring S] [Module R S] [TopologicalSpace S]

/-- Over a coherent ring `R`, multivariate formal power series `MvPowerSeries σ S` with
coefficients in a profinite flat `R`-module ring `S`, equipped with the coefficientwise product
topology, form a profinite flat `R`-module. -/
theorem mvPowerSeries (hS : IsProfiniteFlat R S) (σ : Type*) :
    IsProfiniteFlat R (MvPowerSeries σ S) :=
  -- `MvPowerSeries σ S` is definitionally `(σ →₀ ℕ) → S` with the product `Module` and
  -- `WithPiTopology` instances.
  pi fun _ : σ →₀ ℕ ↦ hS

/-- Over a coherent ring `R`, formal power series `PowerSeries S` with coefficients in a
profinite flat `R`-module ring `S`, equipped with the coefficientwise product topology, form a
profinite flat `R`-module. -/
theorem powerSeries (hS : IsProfiniteFlat R S) : IsProfiniteFlat R (PowerSeries S) :=
  (pi fun _ : ℕ ↦ hS).of_continuousLinearEquiv
    (PowerSeries.WithPiTopology.continuousLinearEquivPi R S).symm

end TauCeti.IsProfiniteFlat
