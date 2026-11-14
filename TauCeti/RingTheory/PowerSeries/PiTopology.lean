/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.RingTheory.MvPowerSeries.PiTopology
public import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Power series in the coefficientwise topology

This file provides two general tools for `R⟦X⟧` equipped with `PowerSeries.WithPiTopology`:

* `PowerSeries.WithPiTopology.continuousLinearEquivPi`: the coefficient map identifies `R⟦X⟧` with
  `ℕ → R` as a topological `R`-module.
* `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`: if all but finitely many factors agree
  with `1` modulo each power `X ^ (n + 1)`, their infinite product converges coefficientwise and
  each coefficient is computed from the corresponding finite cutoff.
-/

public section

open Finset

namespace PowerSeries.WithPiTopology

open scoped PowerSeries.WithPiTopology

section Semiring

variable (R : Type*) [Semiring R] [TopologicalSpace R]

/-- With the product topology on coefficients, `R⟦X⟧` is continuously `R`-linearly isomorphic to
`ℕ → R` via `PowerSeries.coeff` and `PowerSeries.mk`. -/
noncomputable def continuousLinearEquivPi : R⟦X⟧ ≃L[R] (ℕ → R) where
  toFun f n := PowerSeries.coeff n f
  map_add' f g := by ext n; simp
  map_smul' r f := by ext n; simp
  invFun := PowerSeries.mk
  left_inv f := by ext n; simp
  right_inv c := by ext n; simp
  continuous_toFun := continuous_pi (continuous_coeff R)
  continuous_invFun := continuous_iff_continuousAt.mpr fun _ ↦
    (tendsto_iff_coeff_tendsto R _ _ _).mpr fun n ↦ by
      simpa [PowerSeries.coeff_mk] using (continuous_apply n).continuousAt.tendsto

@[simp]
theorem continuousLinearEquivPi_apply (f : R⟦X⟧) (n : ℕ) :
    continuousLinearEquivPi R f n = PowerSeries.coeff n f :=
  (rfl)

@[simp]
theorem continuousLinearEquivPi_symm_apply (c : ℕ → R) :
    (continuousLinearEquivPi R).symm c = PowerSeries.mk c :=
  (rfl)

end Semiring

section CommRing

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

end CommRing

end PowerSeries.WithPiTopology
