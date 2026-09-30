/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Between
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The area of a hyperbolic triangle with a vertex at infinity

`idealRegion a b` is the region of `ℍ` above the unit semicircle and between the vertical lines
`re = a` and `re = b`. For `-1 < a ≤ b < 1` it is a hyperbolic triangle with vertices
`a + i √(1 - a²)`, `b + i √(1 - b²)` and the point at infinity, and its invariant area is
`arccos a - arccos b` (`volume_idealRegion`); this is the base case of the Gauss–Bonnet formula,
in which the two finite angles are `arccos (-a)` and `arccos b`. `idealRegionAbove c r a b` is
the same region for the semicircle of centre `c` and radius `r > 0`, obtained from `idealRegion`
by the affine map `z ↦ r z + c` (`idealRegionAbove_eq_smul`); its area is the same formula in
the rescaled endpoints when `c - r < a ≤ b < c + r` (`volume_idealRegionAbove`). The two
one-variable integrals of the computation are `TauCeti.lintegral_Ioi_inv_sq` and
`TauCeti.integral_one_div_sqrt_one_sub_sq`.

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 8 (2008), §5: the area
`μ(A) = ∫_A dx dy / y²` (5.1) and its invariance (Theorem 5.3), p. 18; the computation
`μ(Δ) = ∫_a^b dx / √(1 - x²) = π - α - β` for a triangle with a vertex at `∞`, p. 19–20.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups NNReal ENNReal Pointwise Real

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (dilation)

/-- The region above the unit semicircle between the verticals `re = a` and `re = b`. -/
def idealRegion (a b : ℝ) : Set ℍ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ Complex.normSq (z : ℂ)}

-- The body of `idealRegion` is not `@[expose]`d; downstream modules use this membership test.
/-- Membership in `idealRegion a b`. -/
@[simp]
theorem mem_idealRegion_iff (a b : ℝ) (z : ℍ) :
    z ∈ idealRegion a b ↔ a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ Complex.normSq (z : ℂ) := Iff.rfl

/-- `idealRegion a b` is measurable. -/
theorem measurableSet_idealRegion (a b : ℝ) : MeasurableSet (idealRegion a b) := by
  have hre : Measurable fun z : ℍ ↦ z.re := UpperHalfPlane.continuous_re.measurable
  have hn : Measurable fun z : ℍ ↦ Complex.normSq (z : ℂ) :=
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_le hre measurable_const).inter (measurableSet_le measurable_const hn))

/-- **The area of a hyperbolic triangle with a vertex at infinity**, in normal form: the region
above the unit semicircle between the verticals `re = a` and `re = b` has invariant area
`arccos a - arccos b`. -/
theorem volume_idealRegion {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    volume (idealRegion a b) = ENNReal.ofReal (Real.arccos a - Real.arccos b) := by
  have hsqrt : ∀ x ∈ Icc a b, 0 < Real.sqrt (1 - x ^ 2) := fun x hx ↦
    Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
  -- the region in real coordinates: `a ≤ x ≤ b` and `√(1 - x²) ≤ y`
  set R : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ Real.sqrt (1 - p.1 ^ 2) ≤ p.2} with hR
  have hRm : MeasurableSet R :=
    (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_le (by fun_prop) measurable_snd)
  have himage : (↑) '' idealRegion a b = Complex.measurableEquivRealProd ⁻¹' R := by
    ext w
    simp only [Set.mem_image, Set.mem_preimage, Complex.measurableEquivRealProd_apply, hR,
      Set.mem_ofPred_eq, idealRegion]
    constructor
    · rintro ⟨z, ⟨hza, hzb, hz1⟩, rfl⟩
      refine ⟨⟨hza, hzb⟩, ?_⟩
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Real.sqrt_le_left z.im_pos.le]
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hz1
      nlinarith [hz1]
    · rintro ⟨⟨hwa, hwb⟩, hw⟩
      have him : 0 < w.im := (hsqrt _ ⟨hwa, hwb⟩).trans_le hw
      refine ⟨⟨w, him⟩, ⟨hwa, hwb, ?_⟩, rfl⟩
      rw [Real.sqrt_le_left him.le] at hw
      rw [Complex.normSq_apply]
      nlinarith [hw]
  -- the integrand and its integral in `y` over `[√(1 - x²), ∞)`
  set F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) with hF
  have hFm : Measurable F := by fun_prop
  have hinner : ∀ x, ∫⁻ y, R.indicator F (x, y) =
      (Icc a b).indicator (fun x ↦ ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) x := by
    intro x
    by_cases hx : x ∈ Icc a b
    · have h : (fun y ↦ R.indicator F (x, y)) = (Ici (Real.sqrt (1 - x ^ 2))).indicator
          fun y ↦ (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        funext y
        simp only [Set.indicator_apply, hR, Set.mem_ofPred_eq, Set.mem_Ici, hF, hx, true_and]
      rw [h, lintegral_indicator measurableSet_Ici, Set.indicator_of_mem hx,
        ← setLIntegral_congr Ioi_ae_eq_Ici, lintegral_Ioi_inv_sq (hsqrt x hx), one_div]
    · have h : (fun y ↦ R.indicator F (x, y)) = fun _ ↦ 0 := by
        funext y
        simp only [Set.indicator_apply, hR, Set.mem_ofPred_eq, hx, false_and, ite_false]
      rw [h, lintegral_zero, Set.indicator_of_notMem hx]
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ 2)) (Icc a b) :=
    ContinuousOn.div continuousOn_const (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
      fun x hx ↦ (hsqrt x hx).ne'
  rw [volume_eq_lintegral, himage]
  refine (Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding F _).trans ?_
  rw [Measure.volume_eq_prod, ← lintegral_indicator hRm, lintegral_prod _
    (hFm.indicator hRm).aemeasurable]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal
    (hcont.integrableOn_Icc) (ae_restrict_of_forall_mem measurableSet_Icc fun x _ ↦ by positivity),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_one_div_sqrt_one_sub_sq ha hab hb, Real.arccos_eq_pi_div_two_sub_arcsin,
    Real.arccos_eq_pi_div_two_sub_arcsin]
  ring_nf

/-- The region above the semicircle of centre `c` and radius `r` between the verticals `re = a`
and `re = b`. -/
def idealRegionAbove (c r a b : ℝ) : Set ℍ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ r ^ 2 ≤ Complex.normSq ((z : ℂ) - c)}

-- The body of `idealRegionAbove` is not `@[expose]`d; downstream modules use this membership test.
/-- Membership in `idealRegionAbove c r a b`. -/
@[simp]
theorem mem_idealRegionAbove_iff (c r a b : ℝ) (z : ℍ) :
    z ∈ idealRegionAbove c r a b ↔
      a ≤ z.re ∧ z.re ≤ b ∧ r ^ 2 ≤ Complex.normSq ((z : ℂ) - c) := Iff.rfl

/-- `idealRegionAbove c r a b` is measurable. -/
theorem measurableSet_idealRegionAbove (c r a b : ℝ) :
    MeasurableSet (idealRegionAbove c r a b) := by
  have hre : Measurable fun z : ℍ ↦ z.re := UpperHalfPlane.continuous_re.measurable
  have hn : Measurable fun z : ℍ ↦ Complex.normSq ((z : ℂ) - c) :=
    (Complex.continuous_normSq.comp (UpperHalfPlane.continuous_coe.sub continuous_const)).measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_le hre measurable_const).inter (measurableSet_le measurable_const hn))

/-- `idealRegionAbove c r a b` is the image of `idealRegion` under the affine map
`z ↦ r z + c`. -/
theorem idealRegionAbove_eq_smul {c r : ℝ} (hr : 0 < r) (a b : ℝ) :
    idealRegionAbove c r a b =
      (upperRightHom c * ↑(dilation (Real.log r))) • idealRegion ((a - c) / r) ((b - c) / r) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, mul_smul, ← QuotientGroup.mk_inv,
    Matrix.SpecialLinearGroup.dilation_inv, ← AddChar.map_neg_eq_inv, upperRightHom_smul,
    UpperHalfPlane.pslMk_smul]
  -- the inverse map sends `z` to `(z - c) / r`
  have hre : (dilation (-Real.log r) • (-c +ᵥ z) : ℍ).re = (z.re - c) / r := by
    rw [← UpperHalfPlane.coe_re, coe_dilation_smul, Real.exp_neg, Real.exp_log hr,
      UpperHalfPlane.coe_vadd, Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re,
      UpperHalfPlane.coe_re, div_eq_inv_mul, sub_eq_neg_add]
  have hn : Complex.normSq ((dilation (-Real.log r) • (-c +ᵥ z) : ℍ) : ℂ) =
      Complex.normSq ((z : ℂ) - c) / r ^ 2 := by
    rw [coe_dilation_smul, Real.exp_neg, Real.exp_log hr, UpperHalfPlane.coe_vadd, map_mul,
      Complex.normSq_ofReal, Complex.ofReal_neg, neg_add_eq_sub, div_eq_mul_inv, ← inv_pow]
    ring
  simp only [idealRegionAbove, idealRegion, Set.mem_ofPred_eq, hre, hn]
  rw [div_le_div_iff_of_pos_right hr, div_le_div_iff_of_pos_right hr, sub_le_sub_iff_right,
    sub_le_sub_iff_right, le_div_iff₀ (by positivity), one_mul]

/-- The area of a hyperbolic triangle with a vertex at infinity, for a general semicircle. -/
theorem volume_idealRegionAbove {c r a b : ℝ} (hr : 0 < r) (ha : c - r < a) (hab : a ≤ b)
    (hb : b < c + r) :
    volume (idealRegionAbove c r a b) =
      ENNReal.ofReal (Real.arccos ((a - c) / r) - Real.arccos ((b - c) / r)) := by
  rw [idealRegionAbove_eq_smul hr, MeasureTheory.measure_smul, volume_idealRegion]
  · rw [lt_div_iff₀ hr]
    linarith
  · exact (div_le_div_iff_of_pos_right hr).2 (by linarith)
  · rw [div_lt_one hr]
    linarith

/-- A geodesic line is a null set. -/
theorem volume_range_geodesicLine (g : PSL(2, ℝ)) : volume (Set.range (geodesicLine g)) = 0 := by
  rw [range_geodesicLine, MeasureTheory.measure_smul]
  have h : {z : ℍ | z.re = 0} = UpperHalfPlane.coe ⁻¹' {w : ℂ | w.re = 0} := by
    ext z
    simp [UpperHalfPlane.coe_re]
  rw [h]
  refine volume_preimage_coe_null ?_
  have h' : {w : ℂ | w.re = 0} = Complex.measurableEquivRealProd ⁻¹' ({0} ×ˢ univ) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply]
  rw [h', Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton 0).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

end TauCeti.UpperHalfPlane
