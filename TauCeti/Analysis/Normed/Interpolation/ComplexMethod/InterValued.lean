/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# Intersection-valued functions approximate the `[X₀, X₁]_θ` norm on `X₀ ∩ X₁` from above

For a Banach couple `(X₀, X₁)` and `0 < θ < 1`, every `x ∈ X₀ ∩ X₁` with `‖x‖_θ < r` is the value
at `θ` of a function `Φ` with values in `X₀ ∩ X₁`, holomorphic on the open strip and continuous and
bounded on the closed strip, whose boundary values have norm less than `r`
(`ComplexMethodSpace.exists_inter_of_norm_ofInter_lt`). So every bound `r > ‖x‖_θ` on `X₀ ∩ X₁` is
witnessed by an intersection-valued function. Only this upper approximation is proved here, and
the admissibility of `Φ` is not part of the statement. Calderón's duality estimate
(`ComplexMethod/Duality.lean`) pairs such functions with upper strip functions of the dual couple.

## The argument

Let `F` be admissible with `F θ = x`. Then `F - exp ((z - θ)²) x` vanishes at `θ`, so it is `B • H`
for the bounded factor `B z = (z - θ) / (z + 1)`, of modulus at most one on the strip, and an
admissible `H = (z + 1) • dslope (F - exp ((z - θ)²) x) θ`. By Calderón's density lemma
(`dense_elementaryStripTraces`) `H` is approximated by elementary admissible functions, which take
values in `X₀ ∩ X₁`; replacing `H` by such an approximation changes the boundary values of
`exp ((z - θ)²) x + B • H` by little and keeps its value `x` at `θ`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.5.
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.
-/

public noncomputable section

open Bornology Complex Complex.HadamardThreeLines Filter Metric Set Topology
open TauCeti.Complex.HadamardThreeLines
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Intersection-valued admissible functions -/

section InterValued

/-- Every elementary admissible trace is the trace of an entire function with values in
`X₀ ∩ X₁`, bounded on the closed strip. -/
private theorem exists_inter_of_mem_elementaryStripTraces {g : C.stripTraces}
    (hg : g ∈ C.elementaryStripTraces) :
    ∃ Ψ : ℂ → C.inter, Differentiable ℂ Ψ ∧ IsBounded (Ψ '' verticalClosedStrip 0 1) ∧
      (∀ t : ℝ, C.interFst (Ψ (t * I)) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) ∧
      ∀ t : ℝ, C.interSnd (Ψ (1 + t * I)) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t := by
  induction hg using elementaryStripTraces_induction with
  | @expGaussian δ hδ ω x =>
    refine ⟨fun z => exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) • x, by fun_prop,
      isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ + |ω|) * ‖x‖, ?_⟩, fun t => by simp,
      fun t => by simp⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_exp_ofReal_mul_sq_add_ofReal_mul_le hδ.le ω hz)
      (norm_nonneg x)
  | zero => exact ⟨0, differentiable_const 0,
      isBounded_iff_forall_norm_le.2 ⟨0, by rintro _ ⟨z, -, rfl⟩; simp⟩, fun t => by simp,
      fun t => by simp⟩
  | add g h _ _ ihg ihh =>
    obtain ⟨Ψ, hΨd, hΨb, hΨ₀, hΨ₁⟩ := ihg
    obtain ⟨Χ, hΧd, hΧb, hΧ₀, hΧ₁⟩ := ihh
    refine ⟨Ψ + Χ, hΨd.add hΧd, ?_, fun t => by rw [Pi.add_apply, map_add, hΨ₀, hΧ₀]; simp,
      fun t => by rw [Pi.add_apply, map_add, hΨ₁, hΧ₁]; simp⟩
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hΨb
    obtain ⟨N, hN⟩ := isBounded_iff_forall_norm_le.1 hΧb
    refine isBounded_iff_forall_norm_le.2 ⟨M + N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hM _ (mem_image_of_mem _ hz))
      (hN _ (mem_image_of_mem _ hz)))
  | smul c g _ ih =>
    obtain ⟨Ψ, hΨd, hΨb, hΨ₀, hΨ₁⟩ := ih
    refine ⟨c • Ψ, hΨd.const_smul c, ?_, fun t => by rw [Pi.smul_apply, map_smul, hΨ₀]; simp,
      fun t => by rw [Pi.smul_apply, map_smul, hΨ₁]; simp⟩
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hΨb
    refine isBounded_iff_forall_norm_le.2 ⟨‖c‖ * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hM _ (mem_image_of_mem _ hz)) (norm_nonneg c)

end InterValued

/-! ### Dividing out a zero at `θ` -/

section Factor

/-- The bounded factor `B z = (z - θ) / (z + 1)`, which vanishes exactly at `θ` on the closed
strip. -/
private def stripFactor (θ : ℝ) (z : ℂ) : ℂ := (z - θ) / (z + 1)

private theorem stripFactor_self (θ : ℝ) : stripFactor θ θ = 0 := by simp [stripFactor]

private theorem add_one_ne_zero_of_mem {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : z + 1 ≠ 0 :=
  fun h => by have := congrArg re h; simp at this; linarith [hz.1]

private theorem differentiableOn_stripFactor (θ : ℝ) :
    DifferentiableOn ℂ (stripFactor θ) (verticalClosedStrip 0 1) :=
  ((differentiableOn_id.sub_const _).div (differentiableOn_id.add_const _)) fun _ hz =>
    add_one_ne_zero_of_mem hz

/-- `|B z| ≤ 1` on the closed strip, for `0 ≤ θ ≤ 1`. -/
private theorem norm_stripFactor_le {θ : ℝ} (hθ : θ ∈ Icc 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖stripFactor θ z‖ ≤ 1 := by
  rw [stripFactor, norm_div, div_le_one (norm_pos_iff.2 (add_one_ne_zero_of_mem hz))]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero, add_re, one_re, add_im, one_im,
    add_zero]
  nlinarith [hz.1, hθ.1, hθ.2]

/-- The reciprocal `(z + 1) / (z - θ)` of `B` is bounded away from `θ`. -/
private theorem norm_div_sub_le {θ : ℝ} (hθ : θ ∈ Icc 0 1) {z : ℂ} {m : ℝ} (hm : 0 < m)
    (hzm : m ≤ ‖z - θ‖) : ‖(z + 1) / (z - θ)‖ ≤ 1 + 2 / m := by
  have hpos : 0 < ‖z - θ‖ := hm.trans_le hzm
  rw [norm_div, div_le_iff₀ hpos]
  calc ‖z + 1‖ = ‖(z - θ) + (θ + 1 : ℂ)‖ := by ring_nf
    _ ≤ ‖z - θ‖ + 2 := (norm_add_le _ _).trans (add_le_add_right
        (by rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_of_nonneg (by linarith [hθ.1])]
            linarith [hθ.2]) _)
    _ ≤ (1 + 2 / m) * ‖z - θ‖ := by
        have : 2 ≤ 2 / m * ‖z - θ‖ := by rw [div_mul_eq_mul_div, le_div_iff₀ hm]; linarith
        linarith

/-- The coefficient `(z + 1) / (z - θ)` along the line `re z = a`, as a family of operators on
`X`. -/
private def lineCoeff (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (θ a : ℝ) (t : ℝ) :
    X →L[ℂ] X :=
  ((a + t * I + 1) / (a + t * I - θ)) • ContinuousLinearMap.id ℂ X

private theorem lineCoeff_apply (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (θ a t : ℝ)
    (x : X) : lineCoeff X θ a t x = ((a + t * I + 1) / (a + t * I - θ)) • x := (rfl)

private theorem continuous_lineCoeff_apply (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ a : ℝ} (ha : a ≠ θ) (x : X) : Continuous fun t => lineCoeff X θ a t x := by
  simp only [lineCoeff_apply]
  refine Continuous.smul (Continuous.div (by fun_prop) (by fun_prop) fun t h => ha ?_)
    continuous_const
  exact sub_eq_zero.1 (by simpa using congrArg re h)

private theorem exists_norm_lineCoeff_apply_le (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] {θ a : ℝ} (hθ : θ ∈ Icc 0 1) (ha : a ≠ θ) :
    ∃ K, ∀ t (x : X), ‖lineCoeff X θ a t x‖ ≤ K * ‖x‖ := by
  refine ⟨1 + 2 / |a - θ|, fun t x => ?_⟩
  rw [lineCoeff_apply, norm_smul]
  refine mul_le_mul_of_nonneg_right (norm_div_sub_le hθ (abs_pos.2 (sub_ne_zero.2 ha)) ?_)
    (norm_nonneg x)
  simpa using abs_re_le_norm (a + t * I - θ)

/-- The coefficient `(z + 1) / (z - θ)` applied to a function vanishing at infinity on the line
`re z = a ≠ θ`. -/
private def lineCoeffMap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] {θ a : ℝ}
    (hθ : θ ∈ Icc 0 1) (ha : a ≠ θ) : C₀(ℝ, X) →L[ℂ] C₀(ℝ, X) :=
  ZeroAtInftyContinuousMap.compLeftFamily (lineCoeff X θ a) (continuous_lineCoeff_apply X ha)
    (exists_norm_lineCoeff_apply_le X hθ ha)

private theorem lineCoeffMap_apply (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ a : ℝ} (hθ : θ ∈ Icc 0 1) (ha : a ≠ θ) (f : C₀(ℝ, X)) (t : ℝ) :
    lineCoeffMap X hθ ha f t = ((a + t * I + 1) / (a + t * I - θ)) • f t := by
  simp [lineCoeffMap, lineCoeff_apply]

/-- `B z • ((z + 1) / (z - θ)) • x = x` for `z ≠ θ` on the closed strip. -/
private theorem stripFactor_smul_div_smul {θ : ℝ} {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1)
    (hzθ : z ≠ θ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (x : X) :
    stripFactor θ z • ((z + 1) / (z - θ)) • x = x := by
  rw [smul_smul, stripFactor, div_mul_div_comm, mul_comm (z - θ), div_self
    (mul_ne_zero (add_one_ne_zero_of_mem hz) (sub_ne_zero.2 hzθ)), one_smul]

/-- Away from a zero `θ` of `F`, `(z + 1) • dslope F θ z = ((z + 1) / (z - θ)) • F z`. -/
private theorem add_one_smul_dslope_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {θ : ℝ} {F : ℂ → E} (hFθ : F θ = 0) {z : ℂ} (hz : z ≠ θ) :
    (z + 1) • dslope F θ z = ((z + 1) / (z - θ)) • F z := by
  rw [dslope_of_ne _ hz, slope_def_module, hFθ, sub_zero, smul_smul, div_eq_mul_inv]

/-- `(z + 1) • dslope F θ z` is bounded on the closed strip if it is continuous there and `F` is
bounded and vanishes at `θ ∈ (0, 1)`: near `θ` by compactness, and away from `θ` because it equals
`((z + 1) / (z - θ)) • F z`. -/
private theorem isBounded_add_one_smul_dslope {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {F : ℂ → E} (hFθ : F θ = 0) {M : ℝ}
    (hM : ∀ z, ‖F z‖ ≤ M)
    (hcont : ContinuousOn (fun z => (z + 1) • dslope F θ z) (verticalClosedStrip 0 1)) :
    IsBounded ((fun z => (z + 1) • dslope F θ z) '' verticalClosedStrip 0 1) := by
  set m := min θ (1 - θ) / 2 with hm_def
  have hm : 0 < m := by have := hθ.1; have := hθ.2; positivity
  have hball : closedBall (θ : ℂ) m ⊆ verticalClosedStrip 0 1 := fun z hz => by
    have := (abs_re_le_norm (z - θ)).trans (mem_closedBall_iff_norm.1 hz)
    simp only [sub_re, ofReal_re] at this
    constructor <;> linarith [(abs_le.1 this).1, (abs_le.1 this).2, min_le_left θ (1 - θ),
      min_le_right θ (1 - θ)]
  obtain ⟨K, hK⟩ := (isCompact_closedBall (θ : ℂ) m).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine isBounded_iff_forall_norm_le.2 ⟨max K ((1 + 2 / m) * M), ?_⟩
  rintro _ ⟨z, -, rfl⟩
  rcases le_or_gt ‖z - θ‖ m with hzm | hzm
  · exact (hK z (mem_closedBall_iff_norm.2 hzm)).trans (le_max_left _ _)
  · have hzθ : z ≠ θ := fun h => by simp [h] at hzm; linarith
    refine le_max_of_le_right ?_
    simp only
    rw [add_one_smul_dslope_of_ne hFθ hzθ, norm_smul]
    exact mul_le_mul (norm_div_sub_le (Ioo_subset_Icc_self hθ) hm hzm.le) (hM z) (norm_nonneg _)
      (by positivity)

/-- **Division by `B`.** For `0 < θ < 1`, an admissible function `f` vanishing at `θ` is `B • h`
for an admissible `h`: on the boundary lines, `f₀ t = B (i t) • h₀ t` and
`f₁ t = B (1 + i t) • h₁ t`. -/
private theorem exists_stripTraces_eq_stripFactor_smul [CompleteSpace X₀] [CompleteSpace X₁]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {f : C.stripTraces} (hf : C.stripEval θ f = 0) : ∃ h : C.stripTraces, ∀ t : ℝ,
      (f : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
          stripFactor θ (t * I) • (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t ∧
        (f : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
          stripFactor θ (1 + t * I) • (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t := by
  have hθI : θ ∈ Icc 0 1 := Ioo_subset_Icc_self hθ
  have h₀θ : (0 : ℝ) ≠ θ := hθ.1.ne
  have h₁θ : (1 : ℝ) ≠ θ := hθ.2.ne'
  set F := C.stripFunction f
  have hF : C.IsStripFunction F f := C.isStripFunction_stripFunction f
  have hFθ : F θ = 0 := by simpa [F] using hf
  -- `H = (z + 1) • dslope F θ` is admissible, with traces `((z + 1) / (z - θ)) • f`.
  set H : ℂ → C.SumSpace := fun z => (z + 1) • dslope F θ z
  have hH : ∀ z : ℂ, z ≠ θ → H z = ((z + 1) / (z - θ)) • F z := fun z hz =>
    add_one_smul_dslope_of_ne hFθ hz
  set h₀ := lineCoeffMap X₀ hθI (by simpa using h₀θ) (f : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
  set h₁ := lineCoeffMap X₁ hθI h₁θ (f : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  have hne₀ : ∀ t : ℝ, (t * I : ℂ) ≠ θ := fun t h => h₀θ (by simpa using congrArg re h)
  have hne₁ : ∀ t : ℝ, (1 + t * I : ℂ) ≠ θ := fun t h => h₁θ (by simpa using congrArg re h)
  have hθmem : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa using hθ
  have hnhds : verticalStrip 0 1 ∈ 𝓝 (θ : ℂ) := (isOpen_verticalStrip 0 1).mem_nhds hθmem
  have hnhds' : verticalClosedStrip 0 1 ∈ 𝓝 (θ : ℂ) :=
    mem_of_superset hnhds (verticalStrip_subset_verticalClosedStrip 0 1)
  have hcont : ContinuousOn H (verticalClosedStrip 0 1) :=
    (continuousOn_id.add continuousOn_const).smul ((continuousOn_dslope hnhds').2
      ⟨closure_verticalStrip zero_lt_one ▸ hF.diffContOnCl.continuousOn,
        hF.diffContOnCl.differentiableAt (isOpen_verticalStrip 0 1) hθmem⟩)
  have hHF : IsStripFunction C H (h₀, h₁) := by
    refine ⟨⟨(differentiableOn_id.add_const 1).smul
      ((Complex.differentiableOn_dslope hnhds).2 hF.diffContOnCl.differentiableOn),
      closure_verticalStrip zero_lt_one ▸ hcont⟩, ?_, fun t => ?_, fun t => ?_⟩
    · exact isBounded_add_one_smul_dslope hθ hFθ (C.norm_stripFunction_le f) hcont
    · rw [hH _ (hne₀ t), hF.apply_mul_I, ← map_smul]
      simp [h₀, lineCoeffMap_apply]
    · rw [hH _ (hne₁ t), hF.apply_one_add_mul_I, ← map_smul]
      simp [h₁, lineCoeffMap_apply]
  refine ⟨⟨(h₀, h₁), mem_stripTraces_iff.2 ⟨H, hHF⟩⟩, fun t => ⟨?_, ?_⟩⟩
  · simpa [h₀, lineCoeffMap_apply] using
      (stripFactor_smul_div_smul (z := t * I) (by simp) (hne₀ t) _).symm
  · simpa [h₁, lineCoeffMap_apply] using
      (stripFactor_smul_div_smul (z := 1 + t * I) (by simp) (hne₁ t) _).symm

/-- `‖a + B z • b‖ < r` on the closed strip when `‖a‖ ≤ s`, `‖b‖ ≤ d` and `s + d < r`. -/
private theorem norm_add_stripFactor_smul_lt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) {a b : X}
    {s d r : ℝ} (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ d) (hr : s + d < r) : ‖a + stripFactor θ z • b‖ < r := by
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul]
  nlinarith [norm_stripFactor_le hθ hz, norm_nonneg (stripFactor θ z), norm_nonneg b]

omit [ContinuousAdd V] [T1Space V] in
/-- `exp ((z - θ)²) x + B z • Ψ z` is holomorphic and bounded on the strip for a bounded entire
`Ψ`. -/
private theorem diffContOnCl_stripGaussian_smul_add_stripFactor_smul {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (x : C.inter) {Ψ : ℂ → C.inter} (hΨd : Differentiable ℂ Ψ)
    (hΨb : IsBounded (Ψ '' verticalClosedStrip 0 1)) :
    DiffContOnCl ℂ (fun z => stripGaussian 1 θ z • x + stripFactor θ z • Ψ z)
        (verticalStrip 0 1) ∧
      IsBounded ((fun z => stripGaussian 1 θ z • x + stripFactor θ z • Ψ z) ''
        verticalClosedStrip 0 1) := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hΨb
  refine ⟨DifferentiableOn.diffContOnCl ?_, isBounded_iff_forall_norm_le.2
    ⟨Real.exp (1 * (|θ| + 1) ^ 2) * ‖x‖ + 1 * K, ?_⟩⟩
  · rw [closure_verticalStrip zero_lt_one]
    exact ((differentiable_stripGaussian 1 θ).differentiableOn.smul_const x).add
      ((differentiableOn_stripFactor θ).smul hΨd.differentiableOn)
  · rintro _ ⟨z, hz, rfl⟩
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul]
    · exact mul_le_mul_of_nonneg_right (norm_stripGaussian_le zero_le_one θ hz) (norm_nonneg x)
    · exact mul_le_mul (norm_stripFactor_le hθ hz) (hK _ (mem_image_of_mem _ hz))
        (norm_nonneg _) zero_le_one

/-- On a boundary point `z`, where `g = f + exp ((z - θ)²) L x`, `f = B z • h` and `L ψ = h'`, the
map `L` sends `exp ((z - θ)²) x + B z • ψ` to `g + B z • (h' - h)`. -/
private theorem map_stripGaussian_smul_add_stripFactor_smul {W X F : Type*} [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] [FunLike F W X] [LinearMapClass F ℂ W X] (L : F)
    {θ : ℝ} {z : ℂ} {x ψ : W} {g f h h' : X} (hg : g = f + stripGaussian 1 θ z • L x)
    (hf : f = stripFactor θ z • h) (hψ : L ψ = h') :
    L (stripGaussian 1 θ z • x + stripFactor θ z • ψ) = g + stripFactor θ z • (h' - h) := by
  rw [map_add, map_smul, map_smul, hψ, hg, hf, smul_sub]
  abel

end Factor

namespace ComplexMethodSpace

variable {C}

/-- **Intersection-valued functions approximate `‖x‖_θ` from above.** For `0 < θ < 1`, an
element `x ∈ X₀ ∩ X₁` with `‖x‖_θ < r` is the value at `θ` of a function `Φ` with values in
`X₀ ∩ X₁`, holomorphic on the open strip and continuous and bounded on the closed strip, whose
boundary values have norm less than `r`: in `X₀` on the line `re z = 0` and in `X₁` on the line
`re z = 1`. -/
theorem exists_inter_of_norm_ofInter_lt [CompleteSpace X₀] [CompleteSpace X₁] {θ : ℝ}
    (hθ : θ ∈ Ioo 0 1) {x : C.inter} {r : ℝ} (hr : ‖ofInter θ x‖ < r) :
    ∃ Φ : ℂ → C.inter, DiffContOnCl ℂ Φ (verticalStrip 0 1) ∧
      IsBounded (Φ '' verticalClosedStrip 0 1) ∧ Φ θ = x ∧
      (∀ t : ℝ, ‖C.interFst (Φ (t * I))‖ < r) ∧ ∀ t : ℝ, ‖C.interSnd (Φ (1 + t * I))‖ < r := by
  have hθI : θ ∈ Icc 0 1 := Ioo_subset_Icc_self hθ
  obtain ⟨g, hg, hgr⟩ := norm_lt_iff.1 hr
  have hgθ : C.stripEval θ g = C.fstToSum (C.interFst x) := by
    simpa [toSum_ofInter hθI] using congrArg toSum hg
  -- `f = g - exp ((z - θ)²) x` vanishes at `θ`, so `f = B • h`; approximate `h` by an elementary
  -- `h'`, the trace of an intersection-valued `Ψ`, and take `Φ = exp ((z - θ)²) x + B • Ψ`.
  set f := g - C.gaussianTrace one_pos θ x
  have hf : C.stripEval θ f = 0 := by
    rw [map_sub, hgθ, C.stripEval_gaussianTrace one_pos θ x (z := θ) (by simpa using hθI)]
    simp
  obtain ⟨h, hh⟩ := C.exists_stripTraces_eq_stripFactor_smul hθ hf
  obtain ⟨h', hh'mem, hhh'⟩ := C.dense_elementaryStripTraces.exists_dist_lt h (sub_pos.2 hgr)
  obtain ⟨Ψ, hΨd, hΨb, hΨ₀, hΨ₁⟩ := C.exists_inter_of_mem_elementaryStripTraces hh'mem
  have hdist : ‖h' - h‖ < r - ‖g‖ := by rwa [← dist_eq_norm, dist_comm]
  have hgf : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) =
      (f : C₀(ℝ, X₀) × C₀(ℝ, X₁)) + C.gaussianTrace one_pos θ x := by simp [f]
  obtain ⟨hΦd, hΦb⟩ := C.diffContOnCl_stripGaussian_smul_add_stripFactor_smul hθI x hΨd hΨb
  refine ⟨fun z => stripGaussian 1 θ z • x + stripFactor θ z • Ψ z, hΦd, hΦb,
    by simp [stripGaussian_self, stripFactor_self], fun t => ?_, fun t => ?_⟩
  · rw [map_stripGaussian_smul_add_stripFactor_smul C.interFst (g := g.val.1 t)
      (by simp [hgf, stripGaussian_apply]) (hh t).1 (hΨ₀ t)]
    exact norm_add_stripFactor_smul_lt hθI (by simp) (C.norm_stripTraces_fst_apply_le g t)
      (d := ‖h' - h‖) (by simpa using C.norm_stripTraces_fst_apply_le (h' - h) t) (by linarith)
  · rw [map_stripGaussian_smul_add_stripFactor_smul C.interSnd (g := g.val.2 t)
      (by simp [hgf, stripGaussian_apply]) (hh t).2 (hΨ₁ t)]
    exact norm_add_stripFactor_smul_lt hθI (by simp) (C.norm_stripTraces_snd_apply_le g t)
      (d := ‖h' - h‖) (by simpa using C.norm_stripTraces_snd_apply_le (h' - h) t) (by linarith)

end ComplexMethodSpace

end TauCeti.CompatibleCouple
