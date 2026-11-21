/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.PiTopology
public import TauCeti.RingTheory.PowerSeries.PiTopology
public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic

/-!
# Power series over profinite flat modules

Over a Dedekind domain `R`, multivariate and univariate formal power series (`MvPowerSeries σ S`
and `PowerSeries S`) with coefficients in a profinite flat `R`-module ring `S`, equipped with the
coefficientwise product topology, are profinite flat `R`-modules
(`TauCeti.IsProfiniteFlat.mvPowerSeries`, `TauCeti.IsProfiniteFlat.powerSeries`).
-/

public section

namespace TauCeti.IsProfiniteFlat

open scoped MvPowerSeries.WithPiTopology PowerSeries.WithPiTopology

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [TopologicalSpace R]
  [Ring S] [Module R S] [TopologicalSpace S]

/-- Over a Dedekind domain `R`, multivariate formal power series `MvPowerSeries σ S` with
coefficients in a profinite flat `R`-module ring `S`, equipped with the coefficientwise product
topology, form a profinite flat `R`-module. -/
theorem mvPowerSeries (hS : IsProfiniteFlat R S) (σ : Type*) :
    IsProfiniteFlat R (MvPowerSeries σ S) :=
  (pi fun _ : σ →₀ ℕ ↦ hS).of_continuousLinearEquiv
    (MvPowerSeries.WithPiTopology.continuousLinearEquivPi σ R S).symm

/-- Over a Dedekind domain `R`, formal power series `PowerSeries S` with coefficients in a
profinite flat `R`-module ring `S`, equipped with the coefficientwise product topology, form a
profinite flat `R`-module. -/
theorem powerSeries (hS : IsProfiniteFlat R S) : IsProfiniteFlat R (PowerSeries S) :=
  (pi fun _ : ℕ ↦ hS).of_continuousLinearEquiv
    (PowerSeries.WithPiTopology.continuousLinearEquivPi R S).symm

end TauCeti.IsProfiniteFlat
