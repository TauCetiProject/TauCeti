/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The area of a hyperbolic triangle with a vertex at infinity

`idealRegion a b` is the region of `ℍ` above the unit semicircle and between the vertical lines
`re = a` and `re = b`. For `-1 ≤ a ≤ b ≤ 1` it is a hyperbolic triangle with vertices
`a + i √(1 - a²)`, `b + i √(1 - b²)` and the point at infinity, and its invariant area is
`arccos a - arccos b` (`volume_idealRegion`); this is the base case of the Gauss–Bonnet formula,
in which the two finite angles are `arccos (-a)` and `arccos b`. For `a = -1` (respectively
`b = 1`) the left (respectively right) vertex is the ideal point `-1` (respectively `1`), with
angle `0`; in particular the ideal triangle with vertices `-1`, `1` and `∞` has area `π`
(`volume_idealRegion_neg_one_one`). Vertical lines are null (`volume_setOf_re_eq`).

`idealRegionAbove c r a b` is the same region for the semicircle of centre `c` and radius
`r > 0`, obtained from `idealRegion` by the affine map `z ↦ r z + c` (`idealRegionAbove_eq_smul`);
its area is the same formula in the rescaled endpoints when `c - r ≤ a ≤ b ≤ c + r`
(`volume_idealRegionAbove`). The two one-variable integrals of the computation are
`TauCeti.lintegral_Ioi_inv_sq` and `TauCeti.integral_one_div_sqrt_one_sub_sq`.

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010), §5: the area
`μ(A) = ∫_A dx dy / y²` (5.1) and its invariance (Theorem 5.3), p. 18; the computation
`μ(Δ) = ∫_a^b dx / √(1 - x²) = π - α - β` for a triangle with a vertex at `∞`, p. 19–20.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open Filter
open scoped MatrixGroups NNReal ENNReal Pointwise Real Topology

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

/-- A vertical line is a null set. -/
theorem volume_setOf_re_eq (x : ℝ) : volume {z : ℍ | z.re = x} = 0 := by
  have h : {z : ℍ | z.re = x} = UpperHalfPlane.coe ⁻¹' {w : ℂ | w.re = x} := by
    ext z
    simp [UpperHalfPlane.coe_re]
  rw [h]
  refine volume_preimage_coe_null ?_
  have h' : {w : ℂ | w.re = x} = Complex.measurableEquivRealProd ⁻¹' ({x} ×ˢ univ) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply]
  rw [h', Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton x).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- `volume_idealRegion` for `-1 < a` and `b < 1`, where the integrand `1 / √(1 - x²)` is
continuous on `[a, b]`; for `b < a` both sides vanish. -/
private theorem volume_idealRegion_of_lt {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    volume (idealRegion a b) = ENNReal.ofReal (Real.arccos a - Real.arccos b) := by
  rcases lt_or_ge b a with hba | hab
  · have h : idealRegion a b = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz ↦ (hz.1.trans hz.2.1).not_gt hba
    rw [h, measure_empty, ENNReal.ofReal_of_nonpos
      (sub_nonpos.2 (Real.arccos_le_arccos hba.le))]
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
    hcont.integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc fun x _ ↦ by positivity),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_one_div_sqrt_one_sub_sq ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩,
    Real.arccos_eq_pi_div_two_sub_arcsin,
    Real.arccos_eq_pi_div_two_sub_arcsin]
  ring_nf

/-- **The area of a hyperbolic triangle with a vertex at infinity**, in normal form: the region
above the unit semicircle between the verticals `re = a` and `re = b` has invariant area
`arccos a - arccos b`, for `-1 ≤ a ≤ b ≤ 1`. For `a = -1` (respectively `b = 1`) the left
(respectively right) vertex is the ideal point `-1` (respectively `1`), with angle `0`. -/
theorem volume_idealRegion {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    volume (idealRegion a b) = ENNReal.ofReal (Real.arccos a - Real.arccos b) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [sub_self, ENNReal.ofReal_zero]
    exact measure_mono_null (fun z hz ↦ hz.1.antisymm' hz.2.1) (volume_setOf_re_eq a)
  -- exhaust `idealRegion a b` by the regions between `A m = max a (-1 + δ m)` and
  -- `B m = min b (1 - δ m)`, up to the null verticals `re = -1` and `re = 1`
  set δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  set A : ℕ → ℝ := fun m ↦ max a (-1 + δ m)
  set B : ℕ → ℝ := fun m ↦ min b (1 - δ m)
  have hδ0 (m : ℕ) : 0 < δ m := by positivity
  have hδanti : Antitone δ := fun m n hmn ↦
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmono : Monotone fun m ↦ idealRegion (A m) (B m) := fun m n hmn z hz ↦
    ⟨(max_le_max le_rfl (by linarith [hδanti hmn])).trans hz.1,
      hz.2.1.trans (min_le_min le_rfl (by linarith [hδanti hmn])), hz.2.2⟩
  have hvol (m : ℕ) : volume (idealRegion (A m) (B m)) =
      ENNReal.ofReal (Real.arccos (A m) - Real.arccos (B m)) :=
    volume_idealRegion_of_lt (lt_max_of_lt_right (by linarith [hδ0 m]))
      (min_lt_of_right_lt (by linarith [hδ0 m]))
  have hAlim : Tendsto A atTop (𝓝 a) := by
    have h := (tendsto_const_nhds (x := a)).max ((tendsto_const_nhds (x := (-1 : ℝ))).add hδlim)
    rwa [add_zero, max_eq_left ha] at h
  have hBlim : Tendsto B atTop (𝓝 b) := by
    have h := (tendsto_const_nhds (x := b)).min ((tendsto_const_nhds (x := (1 : ℝ))).sub hδlim)
    rwa [sub_zero, min_eq_left hb] at h
  have hU : volume (⋃ m, idealRegion (A m) (B m)) =
      ENNReal.ofReal (Real.arccos a - Real.arccos b) := by
    refine tendsto_nhds_unique (tendsto_measure_iUnion_atTop hmono) ?_
    simp_rw [Function.comp_def, hvol]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((Real.continuous_arccos.tendsto _).comp hAlim).sub
        ((Real.continuous_arccos.tendsto _).comp hBlim))
  rw [← hU]
  refine le_antisymm ?_ (measure_mono (iUnion_subset fun m z hz ↦
    ⟨(le_max_left _ _).trans hz.1, hz.2.1.trans (min_le_left _ _), hz.2.2⟩))
  have hsub : idealRegion a b ⊆
      (⋃ m, idealRegion (A m) (B m)) ∪ ({z : ℍ | z.re = -1} ∪ {z : ℍ | z.re = 1}) := by
    intro z hz
    by_cases hl : z.re = -1
    · exact Or.inr (Or.inl hl)
    by_cases hr : z.re = 1
    · exact Or.inr (Or.inr hr)
    have hl' : 0 < z.re + 1 := by linarith [lt_of_le_of_ne (ha.trans hz.1) (Ne.symm hl)]
    have hr' : 0 < 1 - z.re := by linarith [lt_of_le_of_ne (hz.2.1.trans hb) hr]
    obtain ⟨m, hm₁, hm₂⟩ :=
      ((hδlim.eventually (gt_mem_nhds hl')).and (hδlim.eventually (gt_mem_nhds hr'))).exists
    exact Or.inl (mem_iUnion.2 ⟨m, max_le hz.1 (by linarith), le_min hz.2.1 (by linarith),
      hz.2.2⟩)
  calc volume (idealRegion a b) ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [measure_union_null (volume_setOf_re_eq _) (volume_setOf_re_eq _), add_zero]

/-- **The area of the ideal triangle** with vertices `-1`, `1` and `∞` is `π`. -/
theorem volume_idealRegion_neg_one_one : volume (idealRegion (-1) 1) = ENNReal.ofReal π := by
  rw [volume_idealRegion le_rfl (by norm_num) le_rfl, Real.arccos_neg_one, Real.arccos_one,
    sub_zero]

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

/-- The area of a hyperbolic triangle with a vertex at infinity, for a general semicircle, for
`c - r ≤ a ≤ b ≤ c + r`. -/
theorem volume_idealRegionAbove {c r a b : ℝ} (hr : 0 < r) (ha : c - r ≤ a) (hab : a ≤ b)
    (hb : b ≤ c + r) :
    volume (idealRegionAbove c r a b) =
      ENNReal.ofReal (Real.arccos ((a - c) / r) - Real.arccos ((b - c) / r)) := by
  rw [idealRegionAbove_eq_smul hr, MeasureTheory.measure_smul, volume_idealRegion]
  · rw [le_div_iff₀ hr]
    linarith
  · exact (div_le_div_iff_of_pos_right hr).2 (by linarith)
  · rw [div_le_one hr]
    linarith

/-- A geodesic line is a null set. -/
theorem volume_range_geodesicLine (g : PSL(2, ℝ)) : volume (Set.range (geodesicLine g)) = 0 := by
  rw [range_geodesicLine, MeasureTheory.measure_smul, volume_setOf_re_eq]

end TauCeti.UpperHalfPlane
