/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Strip.SliceAverage
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import TauCeti.Analysis.Calculus.IntervalIntegral.Slice
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

/-!
# The slice average on the cylinder

The zero Fourier mode of a section `f : ℝ × ℝ → E` of the trivial bundle over the cylinder
`ℝ × S¹` is its slice average `s ↦ ∫₀¹ f(s, t) dt` (`TauCeti.StripSobolev.sliceAverage`), read as a
section that does not depend on `t`. Operators on the cylinder whose coefficients do not depend
on `t`, such as the linearized Floer operator along a time-independent cylinder, preserve the
splitting of a section into its zero mode and the rest. The slice average on `L²` of the strip,
`TauCeti.StripSobolev.sliceAverageLp`, is in `TauCeti.Analysis.Sobolev.Strip.SliceAverage`. This
file realizes the splitting on the Sobolev space `W^{1,2}(ℝ × S¹, V)`.

The slice average of a test section is a test section
(`TauCeti.CylinderSobolev.sliceAverage_mem_testSection`), and the slice average of its jet
`(ξ, ∂s ξ, ∂t ξ)` is the jet of its slice average (`TauCeti.CylinderSobolev.jet_sliceAverage`):
averaging commutes with `∂s`, and the average of `∂t ξ` over a period vanishes. Hence
`sliceAverageLp` preserves the closure `H1` of the jets of test sections, and restricts to an
idempotent operator `TauCeti.CylinderSobolev.sliceAverageL` on `W^{1,2}(ℝ × S¹, V)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 10, on the Fourier decomposition of operators on
  cylindrical ends.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the zero Fourier mode of the
  linearized operator along time-independent solutions.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {ξ : ℝ × ℝ → V}

omit [CompleteSpace V] in
/-- The slice average of a test section is a test section. -/
theorem sliceAverage_mem_testSection (hξ : ξ ∈ testSection V) : sliceAverage ξ ∈ testSection V := by
  obtain ⟨hξ2, -, R, hR⟩ := mem_testSection_iff.1 hξ
  refine mem_testSection_iff.2 ⟨?_, fun s t ↦ (sliceAverage_mk ξ s _).trans
    (sliceAverage_mk ξ s t).symm, R, fun s t hs ↦ ?_⟩
  · rw [funext (sliceAverage_apply ξ)]
    exact (ContDiff.parametric_intervalIntegral (μ := volume) (a := 0) (b := 1) hξ2).comp
      contDiff_fst
  rw [sliceAverage_apply, intervalIntegral.integral_congr (g := fun _ ↦ (0 : V))
    fun t _ ↦ hR s t hs, intervalIntegral.integral_zero]

/-- The average of the jet over a slice is the jet of the averages of its components. -/
private theorem intervalIntegral_jet {s : ℝ}
    (hint : IntervalIntegrable (fun t ↦ jet ξ (s, t)) volume 0 1) :
    ∫ t in (0 : ℝ)..1, jet ξ (s, t) = (∫ t in (0 : ℝ)..1, ξ (s, t),
      ∫ t in (0 : ℝ)..1, fderiv ℝ ξ (s, t) (1, 0),
      ∫ t in (0 : ℝ)..1, fderiv ℝ ξ (s, t) (0, 1)) := by
  have h := hint.1
  simp only [jet_apply] at h ⊢
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_pair h.fst h.snd, integral_pair h.snd.fst h.snd.snd]

/-- **Averaging commutes with taking jets.** The jet `(ξ, ∂s ξ, ∂t ξ)` of the slice average of a
test section `ξ` is the slice average of its jet: averaging commutes with `∂s`, and both the
`t`-derivative of the average and the average of `∂t ξ` over a period vanish. -/
theorem jet_sliceAverage (hξ : ξ ∈ testSection V) (z : ℝ × ℝ) :
    jet (sliceAverage ξ) z = sliceAverage (jet ξ) z := by
  obtain ⟨hξ2, hξp, -, -⟩ := mem_testSection_iff.1 hξ
  have hξ1 : ContDiff ℝ 1 ξ := hξ2.of_le one_le_two
  have hg := (hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ hξ1.contDiffOn
    (x₀ := z.1) (a := 0) (b := 1) (subset_univ _)).2
  have hF : HasFDerivAt (sliceAverage ξ) ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (∫ t in (0 : ℝ)..1, fderiv ℝ ξ (z.1, t) (1, 0))).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
    rw [funext (sliceAverage_apply ξ)]
    exact hg.hasFDerivAt.comp z hasFDerivAt_fst
  have hint : IntervalIntegrable (fun t ↦ jet ξ (z.1, t)) volume 0 1 :=
    ((continuous_jet hξ1).comp (.prodMk_right z.1)).intervalIntegrable 0 1
  rw [jet_apply, hF.fderiv, sliceAverage_apply (jet ξ), intervalIntegral_jet hint,
    integral_fderiv_apply_zero_one_eq_zero hξ1 hξp z.1]
  simp [sliceAverage_apply]

/-- The `L²` slice average of the jet of a test section is the jet of its slice average. -/
theorem sliceAverageLp_jetLp (ξ : testSection V) :
    sliceAverageLp (jetLp (testSection V) ξ) =
      jetLp (testSection V) ⟨sliceAverage ξ, sliceAverage_mem_testSection ξ.property⟩ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sliceAverageLp (jetLp (testSection V) ξ),
    sliceAverage_congr_ae (coeFn_jetLp ξ),
    coeFn_jetLp (⟨sliceAverage ξ, sliceAverage_mem_testSection ξ.property⟩ : testSection V)]
    with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, jet_sliceAverage ξ.property]

/-- The `L²` slice average preserves the Sobolev space `W^{1,2}(ℝ × S¹, V)`. -/
theorem sliceAverageLp_mem_H1 {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 V) :
    sliceAverageLp x ∈ H1 V := by
  have hsub : (H1 V : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ sliceAverageLp ⁻¹' (H1 V) :=
    jetClosure_subset_of_isClosed ((isClosed_jetClosure _).preimage sliceAverageLp.continuous)
      (by
        rintro _ ⟨ξ, rfl⟩
        simp only [mem_preimage, SetLike.mem_coe, sliceAverageLp_jetLp]
        exact jetLp_mem_jetClosure _)
  exact hsub hx

/-- The slice average on the Sobolev space `W^{1,2}(ℝ × S¹, V)`: the restriction of
`TauCeti.StripSobolev.sliceAverageLp` to `H1`, the projection onto the zero Fourier mode. -/
def sliceAverageL : H1 V →L[ℝ] H1 V :=
  (sliceAverageLp.comp (H1 V).subtypeL).codRestrict (H1 V) fun x ↦ sliceAverageLp_mem_H1 x.property

/-- The slice average on `H1` is the `L²` slice average of the jet. -/
@[simp]
theorem coe_sliceAverageL (x : H1 V) :
    (sliceAverageL x : Lp (V × V × V) 2 stripMeasure) = sliceAverageLp x :=
  (rfl)

/-- The slice average on `H1` is idempotent. -/
@[simp]
theorem sliceAverageL_sliceAverageL (x : H1 V) :
    sliceAverageL (sliceAverageL x) = sliceAverageL x :=
  Subtype.ext (by simp)

/-- The slice average on `H1` does not increase the norm. -/
theorem norm_sliceAverageL_le (x : H1 V) : ‖sliceAverageL x‖ ≤ ‖x‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe x, coe_sliceAverageL]
  exact norm_sliceAverageLp_le _

/-- The slice average on `H1` maps the jet of a test section to the jet of its slice average. -/
theorem sliceAverageL_jetLp (ξ : testSection V) :
    sliceAverageL ⟨jetLp (testSection V) ξ, jetLp_mem_jetClosure ξ⟩ =
      ⟨jetLp (testSection V) ⟨sliceAverage ξ, sliceAverage_mem_testSection ξ.property⟩,
        jetLp_mem_jetClosure _⟩ :=
  Subtype.ext (sliceAverageLp_jetLp ξ)

/-- The value of the slice average of an element of `H1` is the slice average of its value. -/
theorem valueL_sliceAverageL (x : H1 V) :
    valueL (sliceAverageL x) = sliceAverageLp (valueL x) := by
  rw [valueL_eq_compLpL, valueL_eq_compLpL, coe_sliceAverageL, sliceAverageLp_compLpL]

end TauCeti.CylinderSobolev
