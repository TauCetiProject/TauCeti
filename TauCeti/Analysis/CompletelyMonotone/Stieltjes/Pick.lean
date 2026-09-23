/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Nevanlinna
import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Holomorphic
import TauCeti.Analysis.Complex.Pick.Boundary

/-!
# The Pick characterization of complete Bernstein functions

A function continuous on `[0, ∞)` is complete Bernstein exactly when it is nonnegative on
`(0, ∞)`, extends holomorphically to the slit plane `ℂ \ (-∞, 0]`, and maps the upper
half-plane into its closure.  This is the analytic characterization of complete Bernstein
functions.

The forward direction is the holomorphic extension constructed from complete-Bernstein
representing data.  For the converse, the Pick function has a Nevanlinna representation whose
measure is carried by `(-∞, 0]`.  The remaining boundary step is to pass that representation
from the upper half-plane to a positive real parameter.  The Nevanlinna kernel is uniformly
bounded near such a parameter on `(-∞, 0]`, so dominated convergence makes its integral
continuous there.  The resulting real-axis representation converts directly into
complete-Bernstein representing data.

## Main declarations

* The Pick characterization of complete Bernstein functions.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 6.2.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

/-- **Pick characterization of complete Bernstein functions** (Schilling--Song--Vondraček,
Theorem 6.2).  A real function continuous on `[0, ∞)` is complete Bernstein exactly when it is
nonnegative on `(0, ∞)` and has a holomorphic extension to the slit plane that maps the upper
half-plane into its closure. -/
theorem isCompleteBernsteinFunction_iff_continuousAtZero_nonneg_exists_analytic_slitPlane_im_nonneg
    (f : ℝ → ℝ) :
    IsCompleteBernsteinFunction f ↔
      ContinuousWithinAt f (Ici 0) 0 ∧ (∀ t : ℝ, 0 < t → 0 ≤ f t) ∧
        ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitPlane ∧
          (∀ t : ℝ, 0 < t → F t = f t) ∧
          ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im := by
  constructor
  · intro hf
    obtain ⟨F, hF, hFf, him⟩ := hf.exists_analyticOnNhd_slitPlane
    refine ⟨hf.isBernsteinFunction.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl),
      fun t ht => hf.isBernsteinFunction.nonneg ht.le, F, hF, hFf, fun z hz => ?_⟩
    have hzim : 0 < z.im := hz
    have hzslit : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hzim.ne')
    have hprod := him z hzslit
    nlinarith
  · rintro ⟨hfcont, hpos, F, hF, hFf, him⟩
    have hzero : ∀ t : ℝ, 0 < t → (F (t : ℂ)).im = 0 := fun t ht => by
      rw [hFf t ht]
      simp
    obtain ⟨rho, b, hrhoFinite, hb, hrho, hrep⟩ :=
      exists_isFiniteMeasure_eq_nevanlinnaKernel_add_of_im_eq_zero
        hF.differentiableOn him hzero
    let _ : IsFiniteMeasure rho := hrhoFinite
    obtain ⟨g, hg, hgf⟩ :=
      exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_nevanlinnaKernel
        hrho hb (f := f) (fun t ht => by
          rw [← hFf t ht]
          exact eq_integral_nevanlinnaKernel_add_of_eqOn_upperHalfPlane
            (hF.continuousOn.continuousAt
              (isOpen_slitPlane.mem_nhds (ofReal_mem_slitPlane.mpr ht)))
            hrho ht hrep) hpos
    have hzero : g 0 = f 0 := by
      have hgt : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
        ((hg.isBernsteinFunction.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)).mono
          Ioi_subset_Ici_self).tendsto
      have hft : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
        (continuousWithinAt_Ioi_iff_Ici.mpr hfcont).tendsto
      exact tendsto_nhds_unique' (nhdsGT_neBot (0 : ℝ))
        (hgt.congr' (hgf.eventuallyEq_of_mem self_mem_nhdsWithin)) hft
    have hgf' : EqOn g f (Ici 0) := by
      intro t ht
      rcases (mem_Ici.mp ht).eq_or_lt with rfl | ht
      · exact hzero
      · exact hgf ht
    exact hg.congr hgf'.symm

end TauCeti

end
