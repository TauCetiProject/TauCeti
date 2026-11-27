/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Fourier.Torus.UnitCube

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
  `TauCeti.UnitAddTorus.ae_eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero` for continuous
  functions, read on all of `ℝᵈ` by periodicity.
-/

public section

open MeasureTheory Set
open _root_.UnitAddTorus

namespace TauCeti.UnitAddTorus

variable {d : Type*} {E : Type*}

/-- A periodic function takes the same value at two points that have the same image in the torus.
-/
theorem apply_eq_apply_of_coe_eq {g : (d → ℝ) → E}
    (hg : ∀ (x : d → ℝ) (n : d → ℤ), g (x + fun i ↦ (n i : ℝ)) = g x) {x y : d → ℝ}
    (h : ∀ i, (x i : UnitAddCircle) = y i) : g x = g y := by
  have hn (i : d) : ∃ k : ℤ, y i = x i + k := by
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp (h i))
    exact ⟨k, by simp only [zsmul_eq_mul, mul_one] at hk; linarith⟩
  choose n hn using hn
  rw [show y = x + fun i ↦ (n i : ℝ) from funext hn, hg]

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
      g (T x + c) = g (T ((fun i ↦ (c i : UnitAddCircle)) + x)) :=
    apply_eq_apply_of_coe_eq hg fun i ↦ by
      rw [hTx]
      simp [hTx, add_comm]
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
  set Q : Set (d → ℝ) := univ.pi fun _ ↦ Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_univ_pi fun _ ↦ isCompact_Icc
  -- `g` is bounded on the cube, hence square integrable there.
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
  have hmem : MemLp g 2 ((volume : Measure (d → ℝ)).restrict Q) := by
    have : IsFiniteMeasure ((volume : Measure (d → ℝ)).restrict Q) :=
      isFiniteMeasure_restrict.mpr hQ.measure_lt_top.ne
    exact (memLp_top_of_bound hc.aestronglyMeasurable C
      ((ae_restrict_iff' (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)).mpr
        (ae_of_all _ hC))).mono_exponent le_top
  have h_ae := ae_eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero hmem h
  -- The cube is the closure of its interior, so `g` vanishes on the cube.
  have h_closure : Q ⊆ closure (interior Q) := by
    rw [interior_pi_set finite_univ, closure_pi_set]
    intro x hx i _
    simpa [closure_Ioo zero_ne_one] using hx i (mem_univ i)
  have h_on : EqOn g 0 Q :=
    Measure.eqOn_of_ae_eq h_ae hc.continuousOn continuousOn_const h_closure
  -- Every point is congruent to a point of the cube.
  funext x
  have hfract : (fun i ↦ Int.fract (x i)) ∈ Q := fun i _ ↦
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hx : x = (fun i ↦ Int.fract (x i)) + fun i ↦ ((⌊x i⌋ : ℤ) : ℝ) := by
    funext i; simp [Int.fract_add_floor]
  rw [hx, hg]
  exact h_on hfract

end TauCeti.UnitAddTorus
