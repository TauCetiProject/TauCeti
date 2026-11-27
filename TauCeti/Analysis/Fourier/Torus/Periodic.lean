/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Fourier.Torus.UnitCube
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# Periodic functions on `ℝᵈ` integrated over the unit cube

A function `g : ℝᵈ → E` is *periodic* if `g (x + n) = g x` for all integer vectors `n`. Such a
function is a function on the torus `ℝᵈ / ℤᵈ`, and its integral over the unit cube `[0, 1]ᵈ` is its
mean over the torus. This file records the two facts about these means that are used when a
function is given in the coordinates of a lattice basis rather than on the torus itself:

* the mean is invariant under translation
  (`TauCeti.UnitAddTorus.setIntegral_unitCube_comp_add_right`), as the Haar measure of the torus
  is;
* a continuous periodic function whose Fourier coefficients
  `∫ exp (-2πi ⟨n, x⟩) g(x) dx` over the cube all vanish is zero
  (`TauCeti.UnitAddTorus.eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero`). This is
  `Continuous.eq_of_mFourierCoeff_eq` for the function that `g` induces on the torus
  (`TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq`), whose Fourier coefficients are these
  integrals.
-/

public section

open MeasureTheory Set
open _root_.UnitAddTorus

namespace TauCeti.UnitAddTorus

variable {d : Type*} {E : Type*}

-- Mathlib's Fourier basis `mFourierBasis` lives on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; it is the measure of
-- `TauCeti.UnitAddTorus.measurePreserving_coe_measurableEquivPiIoc`.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable [Fintype d] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Translation invariance of means over the torus.** For a periodic function `g` on `ℝᵈ` and any
`c`, the integral of `x ↦ g (x + c)` over the unit cube is that of `g`. -/
theorem setIntegral_unitCube_comp_add_right {g : (d → ℝ) → E}
    (hg : ∀ (x : d → ℝ) (n : d → ℤ), g (x + fun i ↦ (n i : ℝ)) = g x) (c : d → ℝ) :
    ∫ x in univ.pi (fun _ ↦ Icc (0 : ℝ) 1), g (x + c) =
      ∫ x in univ.pi (fun _ ↦ Icc (0 : ℝ) 1), g x := by
  set T := fun x : UnitAddTorus d ↦ ((measurableEquivPiIoc 0 x : _) : d → ℝ)
  have hT : MeasurePreserving T volume _ := measurePreserving_coe_measurableEquivPiIoc
  have hTe : MeasurableEmbedding T := measurableEmbedding_coe_measurableEquivPiIoc
  have hTx (x : UnitAddTorus d) (i : d) : (T x i : UnitAddCircle) = x i := by simp [T]
  -- On the torus, `x ↦ g (T x + c)` is the translate of `g ∘ T` by the image of `c`.
  have h_shift (x : UnitAddTorus d) :
      g (T x + c) = g (T ((fun i ↦ (c i : UnitAddCircle)) + x)) := by
    have h : ((fun i ↦ ((T x + c) i : UnitAddCircle)) : UnitAddTorus d) =
        fun i ↦ (T ((fun i ↦ (c i : UnitAddCircle)) + x) i : UnitAddCircle) := by
      ext i
      simp [hTx, add_comm]
    obtain ⟨m, hm⟩ := coe_eq_coe_iff.1 h
    rw [hm, hg]
  have : (volume : Measure UnitAddCircle).IsAddLeftInvariant :=
    inferInstanceAs (AddCircle.haarAddCircle (T := 1)).IsAddLeftInvariant
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))
  have : (volume : Measure (UnitAddTorus d)).IsAddLeftInvariant :=
    inferInstanceAs (Measure.pi fun _ : d ↦ (volume : Measure UnitAddCircle)).IsAddLeftInvariant
  rw [← hT.integral_comp hTe (fun x ↦ g (x + c)), ← hT.integral_comp hTe g]
  simp only [h_shift]
  exact integral_add_left_eq_self (fun x ↦ g (T x)) _

/-- **A continuous periodic function is determined by its Fourier coefficients.** If `g` is
continuous and periodic on `ℝᵈ` and `∫ exp (-2πi ⟨n, x⟩) g(x) dx = 0` over the unit cube for every
`n ∈ ℤᵈ`, then `g = 0`. -/
theorem eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero {g : (d → ℝ) → ℂ} (hc : Continuous g)
    (hg : ∀ (x : d → ℝ) (n : d → ℤ), g (x + fun i ↦ (n i : ℝ)) = g x)
    (h : ∀ n : d → ℤ, ∫ x in univ.pi fun _ ↦ Icc (0 : ℝ) 1,
      mFourier (-n) (fun i ↦ (x i : UnitAddCircle)) * g x = 0) :
    g = 0 := by
  -- `g` descends to a continuous function `G` on the torus, whose Fourier coefficients are the
  -- integrals over the cube.
  obtain ⟨G, hGc, hG⟩ := exists_continuous_comp_coe_eq hc fun n x ↦ hg x n
  set T := fun x : UnitAddTorus d ↦ ((measurableEquivPiIoc 0 x : _) : d → ℝ)
  have hT : MeasurePreserving T volume _ := measurePreserving_coe_measurableEquivPiIoc
  have hTe : MeasurableEmbedding T := measurableEmbedding_coe_measurableEquivPiIoc
  have hTx (x : UnitAddTorus d) : (fun i ↦ (T x i : UnitAddCircle)) = x := by
    ext i; simp [T]
  have hG_zero : G = 0 := hGc.eq_of_mFourierCoeff_eq continuous_zero fun n ↦ by
    rw [show mFourierCoeff (0 : UnitAddTorus d → ℂ) n = 0 by simp [mFourierCoeff], ← h n,
      ← hT.integral_comp hTe]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [smul_eq_mul, ← hG, hTx]
  funext x
  rw [← hG, hG_zero, Pi.zero_apply, Pi.zero_apply]

end TauCeti.UnitAddTorus
