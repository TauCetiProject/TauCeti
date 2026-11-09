/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Scalar extension of the integral Monsky–Washnitzer algebra

Inverting a nonzero scalar of norm less than one in `K°⟨X⟩†` gives `K⟨X⟩†`.
Consequently the natural map `K ⊗[K°] K°⟨X⟩† → K⟨X⟩†` is an isomorphism of
`K`-algebras. This is the basic generic-fibre comparison for integral overconvergent
power series. Neither completeness nor discreteness of the valuation is needed,
and the variable type may be infinite.

`isLocalizationAway` gives access to Mathlib's localization API for extending maps
out of the integral algebra after inverting the chosen scalar. The comparison
`scalarExtensionEquiv` sends `c ⊗ f` to `c • f` by `scalarExtensionEquiv_tmul`;
`scalarExtensionEquiv_symm_toWashnitzerAlgebra` sends an included integral series
back to `1 ⊗ f`.

## References

* M. van der Put, *The cohomology of Monsky and Washnitzer*,
  Mém. Soc. Math. France 23 (1986), §2.
* Formal constructions: the denominator-clearing criterion
  `TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem` and Mathlib's
  `Algebra.isPushout_of_isLocalization`.
-/

public section

namespace TauCeti.Dagger.intWashnitzerAlgebra

open _root_.MvPowerSeries
open scoped TensorProduct

variable {σ K : Type*}

local notation "K°" => Subring.unitClosedBall K
local notation "W°" => intWashnitzerAlgebra σ K
local notation "W" => washnitzerAlgebra σ K

section NormedField

variable [NormedField K] [IsUltrametricDist K]

/-- Inverting any nonzero scalar of norm less than one in the integral
Monsky–Washnitzer algebra recovers all overconvergent series. -/
theorem isLocalizationAway (π : K°) (hπ0 : (π : K) ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsLocalization.Away (algebraMap K° W° π) W := by
  refine IsLocalization.Away.mk _ ?_ (fun f ↦ ?_) (fun a b hab ↦ ?_)
  · have h : algebraMap W° W (algebraMap K° W° π) = algebraMap K W (π : K) := by
      apply Subtype.ext
      simp [MvPowerSeries.algebraMap_apply]
    rw [h]
    exact (isUnit_iff_ne_zero.mpr hπ0).map _
  · obtain ⟨n, hn⟩ :=
      (mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem hπ0 hπ1).mp f.2
    refine ⟨n, ⟨_, hn⟩, Subtype.ext ?_⟩
    simp [mul_comm, MvPowerSeries.algebraMap_apply]
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa using congrArg (fun f : W ↦ (f : MvPowerSeries σ K)) hab

end NormedField

variable [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The square from integral scalars and integral overconvergent series to
`K` and `K⟨X⟩†` is a pushout of commutative algebras. -/
instance isPushout : Algebra.IsPushout K° K W° W := by
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one K
  let p : K° := ⟨π, Subring.mem_unitClosedBall.mpr hπ1.le⟩
  have : IsLocalization.Away p K :=
    (Subring.unitClosedBall K).isLocalizationAway_of_isOpen
      (Subring.isOpen_unitClosedBall K) p
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1)
      (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hπ0))
  have : IsLocalization (Algebra.algebraMapSubmonoid W° (Submonoid.powers p)) W := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      isLocalizationAway (σ := σ) p (norm_pos_iff.mp hπ0) hπ1
  exact (Algebra.isPushout_of_isLocalization (Submonoid.powers p) K W° W).symm

variable (σ K) in
/-- Extending scalars from `K°` to `K` turns integral overconvergent series
into the Monsky–Washnitzer algebra. -/
noncomputable def scalarExtensionEquiv : K ⊗[K°] W° ≃ₐ[K] W :=
  Algebra.IsPushout.equiv K° K W° W

/-- The comparison sends a pure tensor to scalar multiplication of the included series. -/
@[simp]
theorem scalarExtensionEquiv_tmul (c : K) (f : W°) :
    scalarExtensionEquiv σ K (c ⊗ₜ[K°] f) = c • toWashnitzerAlgebra σ K f := by
  simp [scalarExtensionEquiv, Algebra.IsPushout.equiv_tmul, Algebra.smul_def]

/-- The inverse comparison sends an integral series to its scalar-extension class. -/
@[simp]
theorem scalarExtensionEquiv_symm_toWashnitzerAlgebra (f : W°) :
    (scalarExtensionEquiv σ K).symm (toWashnitzerAlgebra σ K f) = 1 ⊗ₜ[K°] f := by
  apply (scalarExtensionEquiv σ K).injective
  simp

end TauCeti.Dagger.intWashnitzerAlgebra
