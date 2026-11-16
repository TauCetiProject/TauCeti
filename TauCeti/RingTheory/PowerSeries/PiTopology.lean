/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Coefficientwise topology on power series: functoriality, compactness, and infinite products

This file supplements Mathlib's `PowerSeries.WithPiTopology` with coefficientwise continuity of
`PowerSeries.map`, compactness of `R⟦X⟧` over a compact ring `R`, and convergence of infinite
products whose factors agree with `1` to increasing powers of `X`.

## Main results

* `PowerSeries.WithPiTopology.continuous_map`: `PowerSeries.map φ` is continuous whenever `φ` is.
* `PowerSeries.WithPiTopology.instCompactSpace`: `R⟦X⟧` is compact in the coefficientwise topology
  when `R` is compact.
* `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`: convergence and finite-cutoff
  coefficients for products whose factors approach `1` modulo increasing powers of `X`.
-/

public section

open Finset

namespace PowerSeries.WithPiTopology

open scoped PowerSeries.WithPiTopology

/-- Coefficientwise change of base ring `PowerSeries.map φ` is continuous in the product topology
whenever `φ` is continuous. -/
theorem continuous_map {R S : Type*} [Semiring R] [Semiring S]
    [TopologicalSpace R] [TopologicalSpace S] {φ : R →+* S} (hφ : Continuous φ) :
    Continuous (PowerSeries.map φ) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro d
  simpa only [coeff_map, Function.comp_def] using
    (hφ.continuousAt.comp (continuous_coeff R d).continuousAt).tendsto

/-- Power series over a compact semiring form a compact space in the coefficientwise topology. -/
@[scoped instance]
theorem instCompactSpace {R : Type*} [Semiring R] [TopologicalSpace R] [CompactSpace R] :
    CompactSpace R⟦X⟧ := by
  have hmk : Continuous (PowerSeries.mk : (ℕ → R) → R⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro a
    rw [ContinuousAt, tendsto_iff_coeff_tendsto]
    intro d
    simpa only [coeff_mk] using (continuous_apply d).continuousAt.tendsto
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr fun f : R⟦X⟧ ↦ ⟨fun n ↦ coeff n f, ext fun n ↦ coeff_mk n _⟩]
  exact isCompact_range hmk

variable {R ι : Type*} [CommRing R] [TopologicalSpace R]

/-- **Infinite products through finite cutoffs.** If, for each `n`, every factor `g i` with
`i ∉ F n` is congruent to `1` modulo `X ^ (n + 1)`, then the product of all the `g i` converges
in the coefficientwise topology, and its `n`-th coefficient is that of `∏ i ∈ F n, g i`. -/
theorem hasProd_of_X_pow_dvd_sub_one {g : ι → R⟦X⟧} (F : ℕ → Finset ι)
    (hF : ∀ n i, i ∉ F n → X ^ (n + 1) ∣ g i - 1) :
    HasProd g (mk fun n ↦ coeff n (∏ i ∈ F n, g i)) := by
  classical
  rw [HasProd, tendsto_iff_coeff_tendsto]
  refine fun n ↦ tendsto_atTop_of_eventually_const (i₀ := F n) fun s hs ↦ ?_
  rw [coeff_mk]
  exact coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one hs fun i hi ↦ hF n i (mem_sdiff.1 hi).2

end PowerSeries.WithPiTopology
