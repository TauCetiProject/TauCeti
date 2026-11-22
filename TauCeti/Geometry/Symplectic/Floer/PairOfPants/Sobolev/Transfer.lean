/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev
public import TauCeti.Analysis.Sobolev.JetOperator
public import TauCeti.Analysis.Sobolev.Conformal
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Transfer between the cylinder and the pair of pants along an end chart

The linearized Floer operator on the pair of pants `S = ℂ ∖ {0, 1}` is realized on the Sobolev space
`W^{1,2}_0(S, V)` of the cylindrical metric (`TauCeti.ConformalSobolev.H1 V S ρ` for the cylindrical
weight `ρ = TauCeti.Floer.cylindricalWeight`), written in the coordinate `w` of `ℂ`, while the model
operators of its ends, the linearized operators at the stationary cylinders over the asymptotic
orbits, live on `W^{1,2}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.H1`). A parametrix of the operator
on `S` is spliced from inverses of the end models, and this file supplies the change of
coordinates it needs: it moves `L²` functions and `W^{1,2}` sections between the strip
`ℝ × [0, 1]` and `S` along the positive end chart `φ'_q` of an end `q`
(`TauCeti.Floer.positiveEndChart`), and identifies the first-order operators on the two sides.

The positive end chart is holomorphic, of period one in the angular coordinate, and maps the band
`ℝ × [0, 1)` bijectively onto the plane with the center `c_q` of the end removed
(`TauCeti.Floer.image_positiveEndChart_band`); for `c_q = 0` this is the whole cylinder, including
the part `s < 0` that covers the rest of `S` up to one point. Its inverse on the band is given by
the **band coordinates** `TauCeti.Floer.endBandCoord`, the positive end coordinates with the
angular coordinate reduced to `[0, 1)`. The derivative of `φ'_q` at `ζ` is a rotation followed by
multiplication by the **conformal scale** `r(ζ) = 2π |φ'_q(ζ) - c_q|`
(`TauCeti.Floer.positiveEndChartScale`), whose square is the Jacobian.

* **The `L²` isometry.** By the change of variables formula
  (`TauCeti.Floer.lintegral_thricePuncturedSphereReal_eq`), `h ↦ (h / r) ∘ ψ`, for the band
  coordinates `ψ`, is a linear isometric equivalence `TauCeti.Floer.endChartLp` from `L²` of the
  strip onto `L²(S)`, with inverse `g ↦ r · (g ∘ φ'_q)`. Since the `L²` norm of `D ξ` for a
  first-order operator `D = ∂s + J ∂t + C` is conformally invariant, this is the change of variables
  for the values of first-order operators.
* **Transfer of sections.** For a cutoff `β` on the plane vanishing near every point outside `S`
  other than `c_q`, a test section `ξ` of the cylinder becomes the test section
  `β · (ξ ∘ ψ)` of `S` (`TauCeti.Floer.endTransferSection`,
  `TauCeti.Floer.endTransferSection_mem_testSection`). By the chain rule its conformal jet
  `(√ρ ξ', ∂s ξ', ∂t ξ')` at `φ'_q(ζ)` is `1 / r(ζ)` times a linear image of the jet
  `(ξ, ∂s ξ, ∂t ξ)` of `ξ` at `ζ`, under the **jet coefficient of the transfer**
  `TauCeti.Floer.endTransferCoeff` (`jet_smul_comp_positiveEndCoord_positiveEndChart`).
* **Transfer of `W^{1,2}`.** If `|β|`, `|w - c_q| √ρ |β|` and `|w - c_q| ‖dβ‖` are bounded, the jet
  coefficient is essentially bounded (`TauCeti.Floer.memLp_endTransferCoeff`), and its first-order
  operator followed by the `L²` isometry, `TauCeti.Floer.endTransfer`, sends the jet of every test
  section of the cylinder to the conformal jet of its transfer
  (`TauCeti.Floer.endTransfer_jetLp_ae_eq`). Hence it maps `W^{1,2}(ℝ × S¹, V)` into
  `W^{1,2}_0(S, V)` (`TauCeti.Floer.endTransfer_mem_H1`).
* **Operators along the transfer.** A first-order operator on `S` with an essentially bounded
  coefficient field `M` on conformal jets, applied after the transfer, is the `L²` isometry applied
  after the first-order operator on the strip with coefficient field
  `ζ ↦ M(φ'_q(ζ)) ∘ endTransferCoeff q β ζ` (`TauCeti.Floer.jetOperator_endTransfer`). This holds
  for every `L²` jet, so the operator on `S` read along an end chart is an operator on the cylinder
  to which the cylinder theory (invertible models, compactness of zeroth-order terms vanishing at
  the ends) applies.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on punctured Riemann surfaces with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator through its cylindrical
  ends.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Topology

namespace TauCeti.Floer

/-! ### The band coordinates of an end -/

/-- The **band coordinates** of a point `z` in the positive end chart of `q`: its positive end
coordinates `(s, t)` (`TauCeti.Floer.positiveEndCoord`) with the angular coordinate reduced to
`[0, 1)`. Away from the center of the end they invert the positive end chart on the band
`ℝ × [0, 1)` (`positiveEndChart_endBandCoord`, `endBandCoord_positiveEndChart`). -/
def endBandCoord (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((positiveEndCoord q z).1, Int.fract (positiveEndCoord q z).2)

theorem endBandCoord_apply (q : Puncture) (z : ℝ × ℝ) :
    endBandCoord q z = ((positiveEndCoord q z).1, Int.fract (positiveEndCoord q z).2) :=
  (rfl)

/-- The band coordinates lie in the band `ℝ × [0, 1)`. -/
theorem endBandCoord_mem (q : Puncture) (z : ℝ × ℝ) :
    endBandCoord q z ∈ (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 :=
  ⟨mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- A map of period one in the angular coordinate is unchanged by integer shifts of it. -/
theorem apply_add_intCast_of_periodic {α : Type*} {ξ : ℝ × ℝ → α}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (ζ : ℝ × ℝ) (k : ℤ) :
    ξ (ζ + (0, (k : ℝ))) = ξ ζ := by
  have hp : Periodic (fun t ↦ ξ (ζ.1, t)) 1 := hξp ζ.1
  rw [show ζ + (0, (k : ℝ)) = (ζ.1, ζ.2 + k) by ext <;> simp]
  simpa using hp.int_mul k ζ.2

/-- The positive end chart is unchanged by integer shifts of the angular coordinate. -/
theorem positiveEndChart_add_intCast (q : Puncture) (s t : ℝ) (k : ℤ) :
    positiveEndChart q (s, t + k) = positiveEndChart q (s, t) := by
  simpa using apply_add_intCast_of_periodic (positiveEndChart_add_one q) (s, t) k

/-- Away from the center of the end, the positive end chart inverts the band coordinates. -/
theorem positiveEndChart_endBandCoord (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    positiveEndChart q (endBandCoord q z) = z := by
  have h := positiveEndChart_add_intCast q (positiveEndCoord q z).1 (Int.fract
    (positiveEndCoord q z).2) ⌊(positiveEndCoord q z).2⌋
  rw [Int.fract_add_floor] at h
  rw [endBandCoord_apply, ← h, Prod.mk.eta, positiveEndChart_positiveEndCoord q hz]

/-- The band coordinates invert the positive end chart on the band `ℝ × [0, 1)`. -/
theorem endBandCoord_positiveEndChart (q : Puncture) {ζ : ℝ × ℝ} (hζ : ζ.2 ∈ Ico (0 : ℝ) 1) :
    endBandCoord q (positiveEndChart q ζ) = ζ := by
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  rw [endBandCoord_apply, hk]
  ext
  · simp
  · simp [Int.fract_eq_self.2 hζ]

/-- The image of the band `ℝ × [0, 1)` under the positive end chart is the plane with the center
of the end removed. -/
theorem image_positiveEndChart_band (q : Puncture) :
    positiveEndChart q '' ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) =
      {z | Complex.equivRealProdCLM.symm z ≠ q.endCenter} := by
  ext z
  constructor
  · rintro ⟨ζ, -, rfl⟩
    rw [positiveEndChart_apply]
    exact equivRealProdCLM_symm_endChart_ne_endCenter q _
  · intro hz
    exact ⟨_, endBandCoord_mem q z, positiveEndChart_endBandCoord q hz⟩

/-- The positive end coordinates are measurable. -/
theorem measurable_positiveEndCoord (q : Puncture) : Measurable (positiveEndCoord q) := by
  have h : Measurable fun z : ℝ × ℝ ↦ q.endCoord (Complex.equivRealProdCLM.symm z) := by
    simp_rw [endCoord_def]
    exact ((Complex.measurable_log.comp ((Complex.equivRealProdCLM.symm.continuous.sub
      continuous_const).div_const _).measurable).neg.div_const _)
  have he : positiveEndCoord q =
      fun z ↦ q.endSign • Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)) :=
    funext (positiveEndCoord_apply q)
  rw [he]
  exact (Complex.equivRealProdCLM.continuous.measurable.comp h).const_smul q.endSign

/-- The band coordinates are measurable. -/
theorem measurable_endBandCoord (q : Puncture) : Measurable (endBandCoord q) :=
  (measurable_positiveEndCoord q).fst.prodMk
    (measurable_fract.comp (measurable_positiveEndCoord q).snd)


/-! ### The conformal scale of an end chart and the change of variables -/

/-- The **conformal scale** `2π |φ'_q(ζ) - c_q|` of the positive end chart `φ'_q` at `ζ`, where
`c_q` is the center of the end: the derivative of `φ'_q` at `ζ` is a rotation followed by
multiplication by this scale, whose square is the Jacobian (`sq_positiveEndChartScale`). -/
def positiveEndChartScale (q : Puncture) (ζ : ℝ × ℝ) : ℝ :=
  2 * π * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖

theorem positiveEndChartScale_apply (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ =
      2 * π * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ :=
  (rfl)

theorem positiveEndChartScale_pos (q : Puncture) (ζ : ℝ × ℝ) : 0 < positiveEndChartScale q ζ := by
  have h := sub_ne_zero.2 (equivRealProdCLM_symm_endChart_ne_endCenter q (q.endSign • ζ))
  rw [positiveEndChartScale_apply, positiveEndChart_apply]
  positivity

/-- The square of the conformal scale of the positive end chart is its Jacobian. -/
theorem sq_positiveEndChartScale (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ ^ 2 = (fderiv ℝ (positiveEndChart q) ζ).det := by
  rw [det_fderiv_positiveEndChart, positiveEndChartScale_apply]
  ring

theorem continuous_positiveEndChartScale (q : Puncture) : Continuous (positiveEndChartScale q) := by
  have := (contDiff_positiveEndChart q 0).continuous
  unfold positiveEndChartScale
  fun_prop

/-- The strip measure is Lebesgue measure on the band `ℝ × [0, 1)`. -/
theorem stripMeasure_eq_restrict_band :
    StripSobolev.stripMeasure = volume.restrict ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) := by
  rw [CylinderSobolev.stripMeasure_eq_prod, Measure.restrict_congr_set (μ := volume (α := ℝ))
    (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- Lebesgue measure on `S` is Lebesgue measure on the plane with the center of an end removed:
the two sets differ by at most one point. -/
theorem volume_restrict_thricePuncturedSphereReal_eq (q : Puncture) :
    volume.restrict thricePuncturedSphereReal =
      volume.restrict {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter} := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun z hz ↦ hz.2 (ne_endCenter hz.1 q)) measure_empty
  · refine measure_mono_null (t := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1})
      (fun z hz ↦ ?_) ((Set.toFinite _).measure_zero volume)
    obtain ⟨-, hz⟩ := hz
    rw [mem_thricePuncturedSphereReal_iff, not_and_or, not_not, not_not] at hz
    rcases hz with h | h
    · exact Or.inl (by rw [← h, ContinuousLinearEquiv.apply_symm_apply])
    · exact Or.inr (mem_singleton_iff.2 (by rw [← h, ContinuousLinearEquiv.apply_symm_apply]))

/-- **Change of variables along an end chart.** The integral of a function over `S` is the
integral over the strip `ℝ × [0, 1]` of the function read in the positive end chart `φ'_q`, times
the Jacobian of `φ'_q`. -/
theorem lintegral_thricePuncturedSphereReal_eq (q : Puncture) (G : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ z in thricePuncturedSphereReal, G z =
      ∫⁻ ζ, ENNReal.ofReal (positiveEndChartScale q ζ ^ 2) * G (positiveEndChart q ζ)
        ∂StripSobolev.stripMeasure := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [volume_restrict_thricePuncturedSphereReal_eq q, ← image_positiveEndChart_band,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (MeasurableSet.univ.prod
      measurableSet_Ico) (fun ζ _ ↦ ((contDiff_positiveEndChart q 1).differentiable one_ne_zero
      ζ).hasFDerivAt.hasFDerivWithinAt) (injOn_positiveEndChart q 0 |>.mono (by simp)),
    stripMeasure_eq_restrict_band]
  refine lintegral_congr fun ζ ↦ ?_
  rw [sq_positiveEndChartScale, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]

/-- The positive end chart is quasi-measure-preserving from the strip to `S`. -/
theorem quasiMeasurePreserving_positiveEndChart (q : Puncture) :
    QuasiMeasurePreserving (positiveEndChart q) StripSobolev.stripMeasure
      (volume.restrict thricePuncturedSphereReal) := by
  have hm : Measurable (positiveEndChart q) := (contDiff_positiveEndChart q 0).continuous.measurable
  refine ⟨hm.aemeasurable, Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_⟩
  rw [Measure.map_apply hm hA]
  have h := lintegral_thricePuncturedSphereReal_eq q (A.indicator 1)
  rw [lintegral_indicator_one hA, h0] at h
  have hmeas : Measurable fun ζ ↦
      ENNReal.ofReal (positiveEndChartScale q ζ ^ 2) * A.indicator 1 (positiveEndChart q ζ) :=
    (ENNReal.measurable_ofReal.comp ((continuous_positiveEndChartScale q).pow 2).measurable).mul
      ((measurable_one.indicator hA).comp hm)
  have hae := (lintegral_eq_zero_iff hmeas).1 h.symm
  refine measure_eq_zero_iff_ae_notMem.2 (hae.mono fun ζ hζ hζA ↦ ?_)
  rw [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero,
    indicator_of_mem (mem_preimage.1 hζA), Pi.one_apply] at hζ
  rcases hζ with h | h
  · exact (pow_pos (positiveEndChartScale_pos q ζ) 2).not_ge h
  · exact one_ne_zero h

/-- The band coordinates of an end are quasi-measure-preserving from `S` to the strip. -/
theorem quasiMeasurePreserving_endBandCoord (q : Puncture) :
    QuasiMeasurePreserving (endBandCoord q) (volume.restrict thricePuncturedSphereReal)
      StripSobolev.stripMeasure := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine ⟨(measurable_endBandCoord q).aemeasurable,
    Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_⟩
  rw [Measure.map_apply (measurable_endBandCoord q) hA, Measure.restrict_apply'
    isOpen_thricePuncturedSphereReal.measurableSet]
  set B : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1
  have hAB : volume (A ∩ B) = 0 := by
    rw [stripMeasure_eq_restrict_band, Measure.restrict_apply hA] at h0
    exact h0
  refine measure_mono_null (t := positiveEndChart q '' (A ∩ B)) (fun z hz ↦
    ⟨endBandCoord q z, ⟨hz.1, endBandCoord_mem q z⟩,
      positiveEndChart_endBandCoord q (ne_endCenter hz.2 q)⟩)
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun ζ _ ↦ ((contDiff_positiveEndChart q 1).differentiable one_ne_zero
        ζ).differentiableWithinAt) hAB)


/-! ### The `L²` isometry between the strip and `S` -/

section Lp

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `‖c‖ₑ ^ 2 = ofReal (c ^ 2)` for a nonnegative real `c`. -/
private theorem enorm_rpow_two_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    ‖c‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) := by
  rw [Real.eNorm_eq_ofReal hc, ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two]

/-- Reading a function on `S` in the positive end chart and multiplying by the conformal scale
preserves its `L²` norm. -/
theorem eLpNorm_smul_comp_positiveEndChart (q : Puncture) {g : ℝ × ℝ → W}
    (hg : AEStronglyMeasurable g (volume.restrict thricePuncturedSphereReal)) :
    eLpNorm (fun ζ ↦ positiveEndChartScale q ζ • g (positiveEndChart q ζ)) 2
        StripSobolev.stripMeasure = eLpNorm g 2 (volume.restrict thricePuncturedSphereReal) := by
  have hm : AEStronglyMeasurable (fun ζ ↦ positiveEndChartScale q ζ • g (positiveEndChart q ζ))
      StripSobolev.stripMeasure :=
    (continuous_positiveEndChartScale q).aestronglyMeasurable.smul
      (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_positiveEndChart q))
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg,
    lintegral_thricePuncturedSphereReal_eq q]
  congr 1
  refine lintegral_congr fun ζ ↦ ?_
  rw [ENNReal.toReal_ofNat, eNorm_smul, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
    enorm_rpow_two_of_nonneg (positiveEndChartScale_pos q ζ).le]

/-- Reading a function on the strip in the band coordinates of an end and dividing by the
conformal scale preserves its `L²` norm. -/
theorem eLpNorm_inv_smul_comp_endBandCoord (q : Puncture) {h : ℝ × ℝ → W}
    (hh : AEStronglyMeasurable h StripSobolev.stripMeasure) :
    eLpNorm (fun z ↦ (positiveEndChartScale q (endBandCoord q z))⁻¹ • h (endBandCoord q z)) 2
        (volume.restrict thricePuncturedSphereReal) = eLpNorm h 2 StripSobolev.stripMeasure := by
  have hm : AEStronglyMeasurable
      (fun z ↦ (positiveEndChartScale q (endBandCoord q z))⁻¹ • h (endBandCoord q z))
      (volume.restrict thricePuncturedSphereReal) :=
    ((continuous_positiveEndChartScale q).measurable.comp
      (measurable_endBandCoord q)).inv.aestronglyMeasurable.smul
      (hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_endBandCoord q))
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hh,
    lintegral_thricePuncturedSphereReal_eq q]
  congr 1
  rw [stripMeasure_eq_restrict_band]
  refine setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico) fun ζ hζ ↦ ?_
  have hpos := positiveEndChartScale_pos q ζ
  rw [endBandCoord_positiveEndChart q hζ.2, ENNReal.toReal_ofNat, eNorm_smul,
    ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, enorm_rpow_two_of_nonneg (inv_pos.2 hpos).le,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_pow, mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

/-- Reading an `L²` function on `S` in the positive end chart and multiplying by the conformal scale
gives an `L²` function on the strip. -/
theorem memLp_smul_comp_positiveEndChart (q : Puncture) {g : ℝ × ℝ → W}
    (hg : MemLp g 2 (volume.restrict thricePuncturedSphereReal)) :
    MemLp (fun ζ ↦ positiveEndChartScale q ζ • g (positiveEndChart q ζ)) 2
      StripSobolev.stripMeasure := by
  rw [memLp_iff, eLpNorm_smul_comp_positiveEndChart q hg.aestronglyMeasurable]
  exact hg

/-- Reading an `L²` function on the strip in the band coordinates of an end and dividing by the
conformal scale gives an `L²` function on `S`. -/
theorem memLp_inv_smul_comp_endBandCoord (q : Puncture) {h : ℝ × ℝ → W}
    (hh : MemLp h 2 StripSobolev.stripMeasure) :
    MemLp (fun z ↦ (positiveEndChartScale q (endBandCoord q z))⁻¹ • h (endBandCoord q z)) 2
      (volume.restrict thricePuncturedSphereReal) := by
  rw [memLp_iff, eLpNorm_inv_smul_comp_endBandCoord q hh.aestronglyMeasurable]
  exact hh

/-- Reading an `L²` function on `S` in the positive end chart, multiplied by the conformal scale,
as a linear isometry into `L²` of the strip. Its inverse is `endChartLp`. -/
private def endChartLpPull (q : Puncture) :
    Lp W 2 (volume.restrict thricePuncturedSphereReal) →ₗᵢ[ℝ] Lp W 2 StripSobolev.stripMeasure where
  toFun g := (memLp_smul_comp_positiveEndChart q (Lp.memLp g)).toLp _
  map_add' g h := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp (g + h))),
      Lp.coeFn_add ((memLp_smul_comp_positiveEndChart q (Lp.memLp g)).toLp _)
        ((memLp_smul_comp_positiveEndChart q (Lp.memLp h)).toLp _),
      MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp g)),
      MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp h)),
      (quasiMeasurePreserving_positiveEndChart q).ae (Lp.coeFn_add g h)] with ζ h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.add_apply, h₃, h₄, h₅, Pi.add_apply, smul_add]
  map_smul' c g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp (c • g))),
      Lp.coeFn_smul c ((memLp_smul_comp_positiveEndChart q (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp g)),
      (quasiMeasurePreserving_positiveEndChart q).ae (Lp.coeFn_smul c g)] with ζ h₁ h₂ h₃ h₄
    rw [RingHom.id_apply, h₂, h₁, Pi.smul_apply, h₃, h₄, Pi.smul_apply, smul_comm]
  norm_map' g := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      eLpNorm_smul_comp_positiveEndChart q (Lp.aestronglyMeasurable g), Lp.norm_def]

private theorem coeFn_endChartLpPull (q : Puncture)
    (g : Lp W 2 (volume.restrict thricePuncturedSphereReal)) :
    endChartLpPull q g =ᵐ[StripSobolev.stripMeasure]
      fun ζ ↦ positiveEndChartScale q ζ • g (positiveEndChart q ζ) :=
  MemLp.coeFn_toLp (memLp_smul_comp_positiveEndChart q (Lp.memLp g))

private theorem endChartLpPull_toLp (q : Puncture) (h : Lp W 2 StripSobolev.stripMeasure) :
    endChartLpPull q ((memLp_inv_smul_comp_endBandCoord q (Lp.memLp h)).toLp _) = h := by
  refine Lp.ext ?_
  filter_upwards [coeFn_endChartLpPull q ((memLp_inv_smul_comp_endBandCoord q (Lp.memLp h)).toLp _),
    (quasiMeasurePreserving_positiveEndChart q).ae
      (MemLp.coeFn_toLp (memLp_inv_smul_comp_endBandCoord q (Lp.memLp h))),
    stripMeasure_eq_restrict_band ▸
      ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with ζ h₁ h₂ hζ
  rw [h₁, h₂, endBandCoord_positiveEndChart q hζ.2, smul_inv_smul₀
    (positiveEndChartScale_pos q ζ).ne']

/-- **The `L²` isometry along an end chart.** The positive end chart `φ'_q` of the end `q`
identifies `L²` of the strip `ℝ × [0, 1]` isometrically with `L²(S)`: a function `h` on the strip
goes to `z ↦ h(ζ) / |dφ'_q(ζ)|` for the band coordinates `ζ` of `z`
(`coeFn_endChartLp`), and the inverse multiplies a function on `S` read in the chart by the
conformal scale `|dφ'_q|` (`coeFn_endChartLp_symm`). This is the change of variables for the
values of first-order operators, whose `L²` norm is conformally invariant. -/
def endChartLp (q : Puncture) :
    Lp W 2 StripSobolev.stripMeasure ≃ₗᵢ[ℝ] Lp W 2 (volume.restrict thricePuncturedSphereReal) :=
  (LinearIsometryEquiv.ofSurjective (endChartLpPull q) fun h ↦ ⟨_, endChartLpPull_toLp q h⟩).symm

/-- The inverse of the `L²` isometry along an end chart reads a function on `S` in the positive end
chart and multiplies it by the conformal scale. -/
theorem coeFn_endChartLp_symm (q : Puncture)
    (g : Lp W 2 (volume.restrict thricePuncturedSphereReal)) :
    (endChartLp q).symm g =ᵐ[StripSobolev.stripMeasure]
      fun ζ ↦ positiveEndChartScale q ζ • g (positiveEndChart q ζ) := by
  rw [endChartLp, LinearIsometryEquiv.symm_symm]
  exact coeFn_endChartLpPull q g

/-- The `L²` isometry along an end chart reads a function on the strip in the band coordinates and
divides it by the conformal scale. -/
theorem coeFn_endChartLp (q : Puncture) (h : Lp W 2 StripSobolev.stripMeasure) :
    endChartLp q h =ᵐ[volume.restrict thricePuncturedSphereReal]
      fun z ↦ (positiveEndChartScale q (endBandCoord q z))⁻¹ • h (endBandCoord q z) := by
  have heq : endChartLp q h = (memLp_inv_smul_comp_endBandCoord q (Lp.memLp h)).toLp _ := by
    refine (endChartLp q).symm.injective ?_
    rw [LinearIsometryEquiv.symm_apply_apply, endChartLp, LinearIsometryEquiv.symm_symm]
    exact (endChartLpPull_toLp q h).symm
  rw [heq]
  exact MemLp.coeFn_toLp _

end Lp

/-! ### Jets read along an end chart -/

section Jet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The derivative of the positive end chart is multiplication by a complex number: it sends
`(0, 1)` to the image of `(1, 0)` rotated by a quarter turn. -/
theorem fderiv_positiveEndChart_apply_zero_one (q : Puncture) (ζ : ℝ × ℝ) :
    fderiv ℝ (positiveEndChart q) ζ (0, 1) =
      (-(fderiv ℝ (positiveEndChart q) ζ (1, 0)).2, (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1) :=
  (isComplexLinearMap_fderiv_positiveEndChart q ζ).apply_stdComplexLineImag_eq

/-- The square of the conformal scale is the squared norm of the image of `(1, 0)` under the
derivative of the positive end chart. -/
theorem sq_positiveEndChartScale_eq (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ ^ 2 =
      (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 ^ 2 +
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 ^ 2 := by
  rw [sq_positiveEndChartScale, ContinuousLinearMap.det,
    (isComplexLinearMap_fderiv_positiveEndChart q ζ).det_eq_sq_add_sq]
  rfl

/-- The **jet coefficient of the transfer along an end chart.** For a cutoff `β` on the plane and a
point `ζ` of the cylinder, with `w = φ'_q(ζ)`, conformal scale `r = |dφ'_q(ζ)|` and
`(a, b) = dφ'_q(ζ)(1, 0)`, it sends the jet `(x, y, z) = (ξ, ∂s ξ, ∂t ξ)` of a section `ξ` of the
cylinder at `ζ` to `r` times the conformal jet `(√ρ ξ', ∂s ξ', ∂t ξ')` at `w` of `ξ' = β · (ξ ∘ ψ)`,
for the inverse `ψ` of the chart (`jet_smul_comp_positiveEndCoord_positiveEndChart`):

`(r √ρ(w) β(w) x, r ∂sβ(w) x + β(w) (a y - b z) / r, r ∂tβ(w) x + β(w) (b y + a z) / r)`. -/
def endTransferCoeff (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) :
    V × V × V →L[ℝ] V × V × V :=
  let w := positiveEndChart q ζ
  let r := positiveEndChartScale q ζ
  let a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  let b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  let P₀ := ContinuousLinearMap.fst ℝ V (V × V)
  let P₁ := (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  let P₂ := (ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  let I₀ := ContinuousLinearMap.inl ℝ V (V × V)
  let I₁ := (ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V)
  let I₂ := (ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inr ℝ V V)
  (r * (√(cylindricalWeight w) * β w)) • I₀.comp P₀ +
    ((r * fderiv ℝ β w (1, 0)) • I₁.comp P₀ + (β w * a / r) • I₁.comp P₁ -
      (β w * b / r) • I₁.comp P₂) +
    ((r * fderiv ℝ β w (0, 1)) • I₂.comp P₀ + (β w * b / r) • I₂.comp P₁ +
      (β w * a / r) • I₂.comp P₂)

theorem endTransferCoeff_apply (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) (v : V × V × V) :
    endTransferCoeff q β ζ v =
      ((positiveEndChartScale q ζ *
          (√(cylindricalWeight (positiveEndChart q ζ)) * β (positiveEndChart q ζ))) • v.1,
        (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (1, 0)) • v.1 +
          (β (positiveEndChart q ζ) * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 /
            positiveEndChartScale q ζ) • v.2.1 -
          (β (positiveEndChart q ζ) * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 /
            positiveEndChartScale q ζ) • v.2.2,
        (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (0, 1)) • v.1 +
          (β (positiveEndChart q ζ) * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 /
            positiveEndChartScale q ζ) • v.2.1 +
          (β (positiveEndChart q ζ) * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 /
            positiveEndChartScale q ζ) • v.2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [endTransferCoeff]

/-- A map of period one in the angular coordinate, read in the positive end coordinates of an end
and then in its positive end chart, is the map itself. -/
theorem comp_positiveEndCoord_positiveEndChart {α : Type*} {ξ : ℝ × ℝ → α}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (q : Puncture) :
    (ξ ∘ positiveEndCoord q) ∘ positiveEndChart q = ξ := by
  funext ζ
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  simp only [comp_apply, hk, apply_add_intCast_of_periodic hξp]

/-- **Derivatives along an end chart.** Let `ξ` be a `C¹` section of the cylinder, of period one in
the angular coordinate, read in the positive end coordinates `ψ` of the end `q`. At `w = φ'_q(ζ)`,
with conformal scale `r` and `(a, b) = dφ'_q(ζ)(1, 0)`, the partial derivatives of `ξ ∘ ψ` are
`(a ∂s ξ - b ∂t ξ) / r²` and `(b ∂s ξ + a ∂t ξ) / r²`, the derivatives of `ξ` at `ζ` read through
the inverse of the rotation and dilation `dφ'_q(ζ)`. -/
theorem fderiv_comp_positiveEndCoord_positiveEndChart (q : Puncture) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (ζ : ℝ × ℝ) :
    fderiv ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ) (1, 0) =
        (positiveEndChartScale q ζ ^ 2)⁻¹ •
          ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • fderiv ℝ ξ ζ (1, 0) -
            (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • fderiv ℝ ξ ζ (0, 1)) ∧
      fderiv ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ) (0, 1) =
        (positiveEndChartScale q ζ ^ 2)⁻¹ •
          ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • fderiv ℝ ξ ζ (1, 0) +
            (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • fderiv ℝ ξ ζ (0, 1)) := by
  set L := fderiv ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ)
  have hwc : Complex.equivRealProdCLM.symm (positiveEndChart q ζ) ≠ q.endCenter := by
    rw [positiveEndChart_apply]
    exact equivRealProdCLM_symm_endChart_ne_endCenter q _
  have hFd : DifferentiableAt ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ) :=
    (contDiffAt_comp_positiveEndCoord q hξ
      (fun p ↦ by simpa using apply_add_intCast_of_periodic hξp p 1) hwc).differentiableAt
      one_ne_zero
  -- The chain rule for `(ξ ∘ ψ) ∘ φ'_q = ξ` expresses the derivatives of `ξ` through `L`.
  have hchain (v : ℝ × ℝ) : fderiv ℝ ξ ζ v = L (fderiv ℝ (positiveEndChart q) ζ v) := by
    have h := fderiv_comp ζ hFd ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
    rw [comp_positiveEndCoord_positiveEndChart hξp q] at h
    rw [h, ContinuousLinearMap.comp_apply]
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  have hr2 : positiveEndChartScale q ζ ^ 2 = a ^ 2 + b ^ 2 := sq_positiveEndChartScale_eq q ζ
  have h2 : a ^ 2 + b ^ 2 ≠ 0 := hr2 ▸ pow_ne_zero 2 (positiveEndChartScale_pos q ζ).ne'
  have hlin (c d : ℝ) : L (c, d) = c • L (1, 0) + d • L (0, 1) := by
    rw [show ((c, d) : ℝ × ℝ) = c • (1, 0) + d • (0, 1) by ext <;> simp, map_add, map_smul,
      map_smul]
  have hs : fderiv ℝ ξ ζ (1, 0) = a • L (1, 0) + b • L (0, 1) := by
    rw [hchain, show fderiv ℝ (positiveEndChart q) ζ (1, 0) = (a, b) from rfl, hlin]
  have ht : fderiv ℝ ξ ζ (0, 1) = -b • L (1, 0) + a • L (0, 1) := by
    rw [hchain, fderiv_positiveEndChart_apply_zero_one, hlin]
  rw [hs, ht, hr2]
  constructor <;> rw [eq_inv_smul_iff₀ h2] <;> module

/-- **Jets along an end chart.** Let `ξ` be a `C¹` section of the cylinder, of period one in the
angular coordinate, and `β` a function differentiable at `w = φ'_q(ζ)`. Then the conformal jet of
`β · (ξ ∘ ψ)` at `w`, for the positive end coordinates `ψ` of the end `q`, is the image of the jet
of `ξ` at `ζ` under the jet coefficient of the transfer, divided by the conformal scale. -/
theorem jet_smul_comp_positiveEndCoord_positiveEndChart (q : Puncture) {β : ℝ × ℝ → ℝ}
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (ζ : ℝ × ℝ)
    (hβ : DifferentiableAt ℝ β (positiveEndChart q ζ)) :
    ConformalSobolev.jet cylindricalWeight (fun z ↦ β z • ξ (positiveEndCoord q z))
        (positiveEndChart q ζ) =
      (positiveEndChartScale q ζ)⁻¹ • endTransferCoeff q β ζ (StripSobolev.jet ξ ζ) := by
  have hwc : Complex.equivRealProdCLM.symm (positiveEndChart q ζ) ≠ q.endCenter := by
    rw [positiveEndChart_apply]
    exact equivRealProdCLM_symm_endChart_ne_endCenter q _
  have hFd : DifferentiableAt ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ) :=
    (contDiffAt_comp_positiveEndCoord q hξ
      (fun p ↦ by simpa using apply_add_intCast_of_periodic hξp p 1) hwc).differentiableAt
      one_ne_zero
  have hFw : ξ (positiveEndCoord q (positiveEndChart q ζ)) = ξ ζ :=
    congrFun (comp_positiveEndCoord_positiveEndChart hξp q) ζ
  -- The Leibniz rule for `β · (ξ ∘ ψ)`.
  have hβF (v : ℝ × ℝ) :
      fderiv ℝ (fun z ↦ β z • ξ (positiveEndCoord q z)) (positiveEndChart q ζ) v =
      fderiv ℝ β (positiveEndChart q ζ) v • ξ ζ +
        β (positiveEndChart q ζ) • fderiv ℝ (ξ ∘ positiveEndCoord q) (positiveEndChart q ζ) v := by
    rw [show (fun z ↦ β z • ξ (positiveEndCoord q z)) = β • (ξ ∘ positiveEndCoord q) from rfl,
      (hβ.hasFDerivAt.smul hFd.hasFDerivAt).fderiv, ← hFw]
    simp [add_comm]
  obtain ⟨hX, hY⟩ := fderiv_comp_positiveEndCoord_positiveEndChart q hξ hξp ζ
  have hr : positiveEndChartScale q ζ ≠ 0 := (positiveEndChartScale_pos q ζ).ne'
  rw [ConformalSobolev.jet_apply, StripSobolev.jet_apply, endTransferCoeff_apply, hβF, hβF, hX, hY,
    hFw]
  simp only [Prod.smul_mk, smul_add, smul_sub, smul_smul, inv_mul_cancel_left₀ hr]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> module

/-- The derivative of the positive end chart has norm at most the conformal scale on `(1, 0)`, in
each coordinate. -/
theorem abs_fderiv_positiveEndChart_fst_le (q : Puncture) (ζ : ℝ × ℝ) :
    |(fderiv ℝ (positiveEndChart q) ζ (1, 0)).1| ≤ positiveEndChartScale q ζ ∧
      |(fderiv ℝ (positiveEndChart q) ζ (1, 0)).2| ≤ positiveEndChartScale q ζ := by
  have h := sq_positiveEndChartScale_eq q ζ
  have hr := (positiveEndChartScale_pos q ζ).le
  constructor <;> refine abs_le_of_sq_le_sq ?_ hr <;>
    nlinarith [sq_nonneg (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1,
      sq_nonneg (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2]

/-- A bound on the jet coefficient of the transfer along an end chart, at `w = φ'_q(ζ)` with
conformal scale `r`: `r √ρ(w) |β(w)| + r ‖dβ(w)‖ + 2 |β(w)|`. -/
theorem norm_endTransferCoeff_le (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) :
    ‖endTransferCoeff (V := V) q β ζ‖ ≤
      positiveEndChartScale q ζ * (√(cylindricalWeight (positiveEndChart q ζ)) *
          |β (positiveEndChart q ζ)|) +
        positiveEndChartScale q ζ * ‖fderiv ℝ β (positiveEndChart q ζ)‖ +
        2 * |β (positiveEndChart q ζ)| := by
  set w := positiveEndChart q ζ with hw_def
  set r := positiveEndChartScale q ζ with hr_def
  have hr : 0 < r := positiveEndChartScale_pos q ζ
  obtain ⟨ha, hb⟩ := abs_fderiv_positiveEndChart_fst_le q ζ
  have hd (v : ℝ × ℝ) (hv : ‖v‖ = 1) : |fderiv ℝ β w v| ≤ ‖fderiv ℝ β w‖ := by
    simpa [hv] using (fderiv ℝ β w).le_opNorm v
  have h10 := hd (1, 0) (by simp [Prod.norm_def])
  have h01 := hd (0, 1) (by simp [Prod.norm_def])
  have hcoef (c : ℝ) (hc : |c| ≤ r) : |β w * c / r| ≤ |β w| := by
    rw [abs_div, abs_mul, abs_of_pos hr, div_le_iff₀ hr]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hβa := hcoef _ ha
  have hβb := hcoef _ hb
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have h₁ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h₂ : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h₃ : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have hv := norm_nonneg v
  have hκ : 0 ≤ √(cylindricalWeight w) := Real.sqrt_nonneg _
  rw [endTransferCoeff_apply, Prod.norm_def, Prod.norm_def, ← hw_def, ← hr_def]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr, abs_mul, abs_of_nonneg hκ]
    nlinarith [mul_le_mul_of_nonneg_left h₁ (mul_nonneg hr.le (mul_nonneg hκ (abs_nonneg (β w)))),
      mul_nonneg (mul_nonneg hr.le (norm_nonneg (fderiv ℝ β w))) hv,
      mul_nonneg (abs_nonneg (β w)) hv]
  · refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
    nlinarith [mul_le_mul h10 h₁ (norm_nonneg _) (norm_nonneg _),
      mul_le_mul hβa h₂ (norm_nonneg _) (abs_nonneg _), mul_le_mul hβb h₃ (norm_nonneg _)
      (abs_nonneg _), mul_nonneg (mul_nonneg hr.le hκ) (abs_nonneg (β w)),
      mul_nonneg hr.le (norm_nonneg (fderiv ℝ β w)), abs_nonneg (β w),
      abs_nonneg (β w * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 / r),
      abs_nonneg (β w * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 / r)]
  · refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
    nlinarith [mul_le_mul h01 h₁ (norm_nonneg _) (norm_nonneg _),
      mul_le_mul hβa h₃ (norm_nonneg _) (abs_nonneg _), mul_le_mul hβb h₂ (norm_nonneg _)
      (abs_nonneg _), mul_nonneg (mul_nonneg hr.le hκ) (abs_nonneg (β w)),
      mul_nonneg hr.le (norm_nonneg (fderiv ℝ β w)), abs_nonneg (β w),
      abs_nonneg (β w * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 / r),
      abs_nonneg (β w * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 / r)]

/-- If a continuous function `β` vanishes near every point of the plane outside `S` other than the
center of the end `q`, then `√ρ β` is continuous away from that center. -/
theorem continuousAt_sqrt_cylindricalWeight_mul {q : Puncture} {β : ℝ × ℝ → ℝ}
    (hβ : Continuous β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ContinuousAt (fun z ↦ √(cylindricalWeight z) * β z) z := by
  by_cases hzS : z ∈ thricePuncturedSphereReal
  · exact (Real.continuous_sqrt.continuousAt.comp
      (isWeight_cylindricalWeight.continuousOn.continuousAt
        (isOpen_thricePuncturedSphereReal.mem_nhds hzS))).mul hβ.continuousAt
  · have hzβ : z ∉ tsupport β := fun h ↦ hzS (hβS z h hz)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzβ] with y hy
    simp [show β y = 0 from hy]

/-- The jet coefficient of the transfer along an end chart is continuous, for a `C¹` cutoff
vanishing near the points of the plane outside `S` other than the center of the end. -/
theorem continuous_endTransferCoeff {q : Puncture} {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal) :
    Continuous (endTransferCoeff (V := V) q β) := by
  have hφ := (contDiff_positiveEndChart q 1).continuous
  have hr := continuous_positiveEndChartScale q
  have hr0 (ζ : ℝ × ℝ) : positiveEndChartScale q ζ ≠ 0 := (positiveEndChartScale_pos q ζ).ne'
  have hκ : Continuous fun ζ ↦ √(cylindricalWeight (positiveEndChart q ζ)) *
      β (positiveEndChart q ζ) :=
    continuous_iff_continuousAt.2 fun ζ ↦
      (continuousAt_sqrt_cylindricalWeight_mul hβ.continuous hβS (by
        rw [positiveEndChart_apply]
        exact equivRealProdCLM_symm_endChart_ne_endCenter q _)).comp hφ.continuousAt
  have hβφ : Continuous fun ζ ↦ β (positiveEndChart q ζ) := hβ.continuous.comp hφ
  have hdβ (v : ℝ × ℝ) : Continuous fun ζ ↦ fderiv ℝ β (positiveEndChart q ζ) v :=
    ((hβ.continuous_fderiv one_ne_zero).comp hφ).clm_apply continuous_const
  have hdφ : Continuous fun ζ ↦ fderiv ℝ (positiveEndChart q) ζ (1, 0) :=
    ((contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have ha := hdφ.fst
  have hb := hdφ.snd
  unfold endTransferCoeff
  refine (((hr.mul hκ).smul continuous_const).add ((((hr.mul (hdβ _)).smul continuous_const).add
    (((hβφ.mul ha).div hr hr0).smul continuous_const)).sub
    (((hβφ.mul hb).div hr hr0).smul continuous_const))).add ((((hr.mul (hdβ _)).smul
    continuous_const).add (((hβφ.mul hb).div hr hr0).smul continuous_const)).add
    (((hβφ.mul ha).div hr hr0).smul continuous_const))

end Jet

/-! ### Transfer of sections and jets -/

section Transfer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A map of period one in the angular coordinate takes the same value at the positive end
coordinates and at the band coordinates of a point. -/
theorem apply_positiveEndCoord_eq_apply_endBandCoord {α : Type*} {ξ : ℝ × ℝ → α}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (q : Puncture) (z : ℝ × ℝ) :
    ξ (positiveEndCoord q z) = ξ (endBandCoord q z) := by
  have h : endBandCoord q z =
      positiveEndCoord q z + (0, ((-⌊(positiveEndCoord q z).2⌋ : ℤ) : ℝ)) := by
    rw [endBandCoord_apply, Int.fract]
    ext <;> simp [sub_eq_add_neg]
  rw [h, apply_add_intCast_of_periodic hξp]

/-- The **transfer of a section along an end chart**: a section `ξ` of the cylinder read in the
positive end coordinates of the end `q` and cut off by `β`, as a section of the plane. It is `0` at
the center of the end, where the end coordinates are not defined. -/
def endTransferSection (q : Puncture) (β : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  open Classical in
  if Complex.equivRealProdCLM.symm z = q.endCenter then 0 else β z • ξ (positiveEndCoord q z)

/-- Away from the center of the end, the transferred section is `β · (ξ ∘ ψ)` near every point. -/
theorem endTransferSection_eventuallyEq (q : Puncture) (β : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V)
    {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    endTransferSection q β ξ =ᶠ[𝓝 z] fun z ↦ β z • ξ (positiveEndCoord q z) := by
  filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds
    hz] with y hy
  simp [endTransferSection, hy]

/-- The transferred section of a section vanishing for `|s| ≥ R` vanishes outside the image of
`[-R, R] × [0, 1]` under the positive end chart. -/
theorem endTransferSection_eq_zero_of_notMem (q : Puncture) (β : ℝ × ℝ → ℝ) {ξ : ℝ × ℝ → V}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0)
    {z : ℝ × ℝ} (hz : z ∉ positiveEndChart q '' (Icc (-R) R ×ˢ Icc (0 : ℝ) 1)) :
    endTransferSection q β ξ z = 0 := by
  by_cases hzc : Complex.equivRealProdCLM.symm z = q.endCenter
  · simp [endTransferSection, hzc]
  simp only [endTransferSection, hzc, ↓reduceIte]
  rw [apply_positiveEndCoord_eq_apply_endBandCoord hξp]
  by_cases hs : R ≤ |(endBandCoord q z).1|
  · rw [show endBandCoord q z = ((endBandCoord q z).1, (endBandCoord q z).2) from rfl,
      hR _ _ hs, smul_zero]
  · refine absurd ⟨endBandCoord q z, ⟨abs_le.1 (not_le.1 hs).le, Ico_subset_Icc_self
      (endBandCoord_mem q z).2⟩, positiveEndChart_endBandCoord q hzc⟩ hz

/-- **Transferred test sections.** Let `β` be a `C²` cutoff vanishing near every point of the plane
outside `S` other than the center of the end `q`. The transfer along the end chart of `q` of a test
section of the cylinder is a test section of `S`. -/
theorem endTransferSection_mem_testSection (q : Puncture) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {ξ : ℝ × ℝ → V} (hξ : ξ ∈ CylinderSobolev.testSection V) :
    endTransferSection q β ξ ∈ ConformalSobolev.testSection V thricePuncturedSphereReal := by
  obtain ⟨hξ2, hξp, R, hR⟩ := CylinderSobolev.mem_testSection_iff.1 hξ
  set K := positiveEndChart q '' (Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (contDiff_positiveEndChart q 0).continuous
  have hKc (z : ℝ × ℝ) (hz : z ∈ K) : Complex.equivRealProdCLM.symm z ≠ q.endCenter := by
    obtain ⟨ζ, -, rfl⟩ := hz
    rw [positiveEndChart_apply]
    exact equivRealProdCLM_symm_endChart_ne_endCenter q _
  have hsuppK : tsupport (endTransferSection q β ξ) ⊆ K :=
    closure_minimal (fun z hz ↦ by_contra fun h ↦ hz
      (endTransferSection_eq_zero_of_notMem q β hξp hR h)) hK.isClosed
  have hsuppβ : tsupport (endTransferSection q β ξ) ⊆ tsupport β :=
    closure_mono fun z hz ↦ by
      by_contra h
      refine hz ?_
      rw [endTransferSection]
      split_ifs <;> simp [show β z = 0 from not_not.1 h]
  have hper (p : ℝ × ℝ) : ξ (p + (0, 1)) = ξ p := by
    simpa using apply_add_intCast_of_periodic hξp p 1
  refine ConformalSobolev.mem_testSection_iff.2 ⟨contDiff_iff_contDiffAt.2 fun z ↦ ?_,
    hK.of_isClosed_subset (isClosed_tsupport _) hsuppK,
    fun z hz ↦ hβS z (hsuppβ hz) (hKc z (hsuppK hz))⟩
  by_cases hzc : Complex.equivRealProdCLM.symm z = q.endCenter
  · -- Near the center the transferred section vanishes.
    have hzK : z ∉ K := fun h ↦ hKc z h hzc
    refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with y hy
    exact endTransferSection_eq_zero_of_notMem q β hξp hR hy
  · exact (hβ.contDiffAt.smul
      (contDiffAt_comp_positiveEndCoord q hξ2 hper hzc)).congr_of_eventuallyEq
      (endTransferSection_eventuallyEq q β ξ hzc)

/-- The jet coefficient of the transfer along an end chart is essentially bounded, for a `C¹` cutoff
`β` vanishing near every point of the plane outside `S` other than the center `c_q` of the end, if
`|β|`, `|w - c_q| √ρ |β|` and `|w - c_q| ‖dβ‖` are bounded by `B` away from `c_q`. -/
theorem memLp_endTransferCoeff (q : Puncture) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {B : ℝ} (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
        (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B) :
    MemLp (endTransferCoeff (V := V) q β) ∞ StripSobolev.stripMeasure := by
  refine memLp_top_of_bound (continuous_endTransferCoeff hβ hβS).aestronglyMeasurable
    (2 * π * B + 2 * π * B + 2 * B) (ae_of_all _ fun ζ ↦ ?_)
  have hc : Complex.equivRealProdCLM.symm (positiveEndChart q ζ) ≠ q.endCenter := by
    rw [positiveEndChart_apply]
    exact equivRealProdCLM_symm_endChart_ne_endCenter q _
  obtain ⟨h₁, h₂, h₃⟩ := hB _ hc
  refine (norm_endTransferCoeff_le q β ζ).trans ?_
  rw [positiveEndChartScale_apply]
  nlinarith [Real.pi_pos]

/-- The **transfer of `L²` jets along an end chart**: a jet `(ξ, ∂s ξ, ∂t ξ)` on the strip is sent
by the jet coefficient of the transfer (`endTransferCoeff`) and then by the `L²` isometry
(`endChartLp`) to `S`. On the jet of a test section `ξ` of the cylinder it is the conformal jet of
the transferred section (`endTransfer_jetLp`), so it maps `W^{1,2}` of the cylinder into
`W^{1,2}_0(S)` (`endTransfer_mem_H1`). -/
def endTransfer (q : Puncture) (β : ℝ × ℝ → ℝ) :
    Lp (V × V × V) 2 StripSobolev.stripMeasure →L[ℝ]
      Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal) :=
  (endChartLp (W := V × V × V) q).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (jetOperator StripSobolev.stripMeasure (endTransferCoeff q β))

theorem endTransfer_apply (q : Puncture) (β : ℝ × ℝ → ℝ)
    (f : Lp (V × V × V) 2 StripSobolev.stripMeasure) :
    endTransfer q β f =
      endChartLp q (jetOperator StripSobolev.stripMeasure (endTransferCoeff q β) f) :=
  (rfl)

/-- The transfer of an `L²` jet along an end chart reads it in the band coordinates. -/
theorem coeFn_endTransfer (q : Puncture) {β : ℝ × ℝ → ℝ}
    (hN : MemLp (endTransferCoeff (V := V) q β) ∞ StripSobolev.stripMeasure)
    (f : Lp (V × V × V) 2 StripSobolev.stripMeasure) :
    endTransfer q β f =ᵐ[volume.restrict thricePuncturedSphereReal]
      fun z ↦ (positiveEndChartScale q (endBandCoord q z))⁻¹ •
        endTransferCoeff q β (endBandCoord q z) (f (endBandCoord q z)) := by
  filter_upwards [coeFn_endChartLp q (jetOperator StripSobolev.stripMeasure
      (endTransferCoeff q β) f),
    (quasiMeasurePreserving_endBandCoord q).ae (coeFn_jetOperator hN f)] with z h₁ h₂
  rw [endTransfer_apply, h₁, h₂]

/-- **The transfer of the jet of a test section** is the conformal jet of the transferred
section. -/
theorem endTransfer_jetLp_ae_eq (q : Puncture) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hN : MemLp (endTransferCoeff (V := V) q β) ∞ StripSobolev.stripMeasure)
    (ξ : CylinderSobolev.testSection V) :
    endTransfer q β (StripSobolev.jetLp (CylinderSobolev.testSection V) ξ)
      =ᵐ[volume.restrict thricePuncturedSphereReal]
        ConformalSobolev.jet cylindricalWeight (endTransferSection q β ξ) := by
  obtain ⟨hξ2, hξp, -⟩ := CylinderSobolev.mem_testSection_iff.1 ξ.property
  filter_upwards [coeFn_endTransfer q hN _,
    (quasiMeasurePreserving_endBandCoord q).ae (StripSobolev.coeFn_jetLp ξ),
    ae_restrict_mem isOpen_thricePuncturedSphereReal.measurableSet] with z h₁ h₂ hz
  have hzc := ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q
  set ζ := endBandCoord q z
  have hφ : positiveEndChart q ζ = z := positiveEndChart_endBandCoord q hzc
  -- The jet of the transferred section only depends on the section near `z`.
  have hjet : ConformalSobolev.jet cylindricalWeight (endTransferSection q β ξ) z =
      ConformalSobolev.jet cylindricalWeight (fun z ↦ β z • (ξ : ℝ × ℝ → V) (positiveEndCoord q z))
        z := by
    have he := endTransferSection_eventuallyEq q β (ξ : ℝ × ℝ → V) hzc
    rw [ConformalSobolev.jet_apply, ConformalSobolev.jet_apply, he.eq_of_nhds, he.fderiv_eq]
  rw [h₁, h₂, hjet, ← hφ, jet_smul_comp_positiveEndCoord_positiveEndChart q
    (hξ2.of_le one_le_two) hξp ζ (hβ.differentiable one_ne_zero _)]

/-- **The transfer along an end chart maps `W^{1,2}` of the cylinder into `W^{1,2}_0(S)`.** For a
`C²` cutoff `β` vanishing near every point of the plane outside `S` other than the center `c_q` of
the end, with `|β|`, `|w - c_q| √ρ |β|` and `|w - c_q| ‖dβ‖` bounded away from `c_q`, the transfer
of an element of `W^{1,2}(ℝ × S¹, V)` lies in `W^{1,2}_0(S, V)` for the cylindrical weight. -/
theorem endTransfer_mem_H1 (q : Puncture) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {B : ℝ} (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
        (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B)
    {f : Lp (V × V × V) 2 StripSobolev.stripMeasure} (hf : f ∈ CylinderSobolev.H1 V) :
    endTransfer q β f ∈ ConformalSobolev.H1 V thricePuncturedSphereReal cylindricalWeight := by
  have hN := memLp_endTransferCoeff (V := V) q (hβ.of_le one_le_two) hβS hB
  refine StripSobolev.jetClosure_subset_of_isClosed
    (s := endTransfer q β ⁻¹' (ConformalSobolev.H1 V thricePuncturedSphereReal cylindricalWeight :
      Set (Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal))))
    (ConformalSobolev.isClosed_H1.preimage (endTransfer q β).continuous) ?_ hf
  rintro _ ⟨ξ, rfl⟩
  exact ConformalSobolev.jetSubmodule_le_H1 (ConformalSobolev.mem_jetSubmodule_iff.2
    ⟨_, endTransferSection_mem_testSection q hβ hβS ξ.property,
      endTransfer_jetLp_ae_eq q (hβ.of_le one_le_two) hN ξ⟩)

/-- **First-order operators read along an end chart.** A first-order operator on `S` with an
essentially bounded coefficient field `M` on conformal jets, applied to the transfer of an `L²` jet
`f` along the end chart of `q`, is the transfer, by the `L²` isometry, of the first-order operator
on the strip whose coefficient field at `ζ` is `M(φ'_q(ζ))` composed with the jet coefficient of the
transfer. -/
theorem jetOperator_endTransfer {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (q : Puncture) {β : ℝ × ℝ → ℝ}
    (hN : MemLp (endTransferCoeff (V := V) q β) ∞ StripSobolev.stripMeasure)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    (f : Lp (V × V × V) 2 StripSobolev.stripMeasure) :
    jetOperator (volume.restrict thricePuncturedSphereReal) M (endTransfer q β f) =
      endChartLp q (jetOperator StripSobolev.stripMeasure
        (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) f) := by
  have hMφ : MemLp (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) ∞
      StripSobolev.stripMeasure := by
    have hCM := ae_le_lpNorm_exponent_top hM
    have hCN := ae_le_lpNorm_exponent_top hN
    refine memLp_top_of_bound
      ((ContinuousLinearMap.compL ℝ (V × V × V) (V × V × V) W).aestronglyMeasurable_comp₂
      (hM.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_positiveEndChart q)) hN.aestronglyMeasurable)
      (lpNorm M ∞ (volume.restrict thricePuncturedSphereReal) *
        lpNorm (endTransferCoeff (V := V) q β) ∞ StripSobolev.stripMeasure) ?_
    filter_upwards [(quasiMeasurePreserving_positiveEndChart q).ae hCM, hCN] with ζ h₁ h₂
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁))
  refine Lp.ext ?_
  filter_upwards [coeFn_jetOperator hM (endTransfer q β f), coeFn_endTransfer q hN f,
    coeFn_endChartLp q (jetOperator StripSobolev.stripMeasure
      (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) f),
    (quasiMeasurePreserving_endBandCoord q).ae (coeFn_jetOperator hMφ f),
    ae_restrict_mem isOpen_thricePuncturedSphereReal.measurableSet] with z h₁ h₂ h₃ h₄ hz
  rw [h₁, h₂, h₃, h₄, map_smul, ContinuousLinearMap.comp_apply,
    positiveEndChart_endBandCoord q (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)]

end Transfer

end TauCeti.Floer
