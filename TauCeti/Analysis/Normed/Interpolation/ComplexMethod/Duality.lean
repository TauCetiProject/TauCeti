/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Basic
public import TauCeti.Analysis.Normed.Interpolation.Regular
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# The upper space of the dual couple embeds in the dual of the complex method

Let `(X₀, X₁)` be a regular couple of complex Banach spaces and `0 < θ < 1`. The dual couple
`(X₀*, X₁*)` (`CompatibleCouple.dual`) lives in `(X₀ ∩ X₁)*`, so every element `u` of its sum
space pairs with every `x ∈ X₀ ∩ X₁`. Calderón's duality theorem identifies the dual of the
complex interpolation space `[X₀, X₁]_θ` isometrically with the upper complex interpolation space
`[X₀*, X₁*]^θ` of the dual couple. This file proves one of its two inequalities: the pairing
satisfies

`|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ` for `u ∈ [X₀*, X₁*]^θ` and `x ∈ X₀ ∩ X₁`,

so, `X₀ ∩ X₁` being dense in `[X₀, X₁]_θ`, each `u` extends to a continuous functional on
`[X₀, X₁]_θ` of norm at most `‖u‖^[θ]`. The resulting map
`UpperComplexMethodSpace.toStrongDual : [X₀*, X₁*]^θ →L[ℂ] ([X₀, X₁]_θ)*` is injective and does
not increase norms. Its surjectivity and the reverse inequality `‖u‖^[θ] ≤ ‖⟨u, ·⟩‖`, which
make it an isometric isomorphism, are not proved here.

## The argument

Let `G` be an upper strip function of the dual couple with `deriv G θ = u` and boundary
difference quotients `q`. For an admissible function `Φ` with values in `X₀ ∩ X₁` and real
`h ≠ 0`, the scalar function `z ↦ ⟨(h i)⁻¹ (G (z + h i) - G z), Φ z⟩` is holomorphic and bounded
on the strip, and on the line `re z = j` it pairs a difference quotient of `G` in `Xⱼ*` with
`Φ z ∈ Xⱼ`. The maximum principle bounds its value at `θ` by `‖q‖` times the boundary norms of
`Φ`, and letting `h → 0` gives `|⟨u, Φ θ⟩| ≤ ‖q‖ sup_j sup_t ‖Φ (j + i t)‖_j`
(`IsUpperStripFunction.norm_sumSpaceEmbed_deriv_apply_le`).

It remains to see that these intersection-valued functions are enough to approach `‖x‖_θ`
(`ComplexMethodSpace.exists_inter_of_norm_ofInter_lt`). Let `F` be admissible with `F θ = x`. Then
`F - exp ((z - θ)²) x` vanishes at `θ`, so it is `B • H` for the bounded factor
`B z = (z - θ) / (z + 1)`, of modulus at most one on the strip, and an admissible `H`. By
Calderón's density lemma `H` is approximated by elementary admissible functions, which take values
in `X₀ ∩ X₁`; replacing `H` by such an approximation changes the boundary values of
`exp ((z - θ)²) x + B • H` by little and keeps its value `x` at `θ`.

## Main declarations

* `IsUpperStripFunction.norm_sumSpaceEmbed_deriv_apply_le`: the pairing estimate for an upper
  strip function of the dual couple and an intersection-valued admissible function.
* `ComplexMethodSpace.exists_inter_of_norm_ofInter_lt`: an `x ∈ X₀ ∩ X₁` with `‖x‖_θ < r` is the
  value at `θ` of a bounded holomorphic function with values in `X₀ ∩ X₁` whose boundary values
  have norm less than `r`.
* `UpperComplexMethodSpace.norm_sumSpaceEmbed_toSum_apply_le`: `|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ`.
* `UpperComplexMethodSpace.toStrongDual`: the injective contraction
  `[X₀*, X₁*]^θ →L[ℂ] ([X₀, X₁]_θ)*`, characterized by `toStrongDual_apply_ofInter`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.5
  (Theorem 4.5.1).
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2
  (Theorem 2.2).
-/

public noncomputable section

open Bornology Complex Complex.HadamardThreeLines Filter Metric Set Topology
open TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction ZeroAtInfty

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
    rw [dslope_of_ne _ hzθ, slope_def_module, hFθ, sub_zero, smul_smul, ← div_eq_mul_inv,
      norm_smul]
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
  have hH : ∀ z : ℂ, z ≠ θ → H z = ((z + 1) / (z - θ)) • F z := fun z hz => by
    simp only [H]
    rw [dslope_of_ne _ hz, slope_def_module, hFθ, sub_zero, smul_smul, div_eq_mul_inv]
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

private theorem norm_stripTraces_fst_apply_le (g : C.stripTraces) (t : ℝ) :
    ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ ≤ ‖g‖ :=
  (ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans ((norm_fst_le _).trans_eq
    (Submodule.norm_coe g))

private theorem norm_stripTraces_snd_apply_le (g : C.stripTraces) (t : ℝ) :
    ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ ≤ ‖g‖ :=
  (ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans ((norm_snd_le _).trans_eq
    (Submodule.norm_coe g))

end Factor

namespace ComplexMethodSpace

variable {C}

/-- **Intersection-valued functions compute the norm of the intersection.** For `0 < θ < 1`, an
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
  · have key : C.interFst (stripGaussian 1 θ (t * I) • x + stripFactor θ (t * I) • Ψ (t * I)) =
        (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t +
          stripFactor θ (t * I) • ((h' - h : C.stripTraces) : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t := by
      rw [hgf, Prod.fst_add, add_apply, (hh t).1,
        gaussianTrace_apply_fst, map_add, map_smul, map_smul, hΨ₀, stripGaussian_apply]
      simp only [Submodule.coe_sub, Prod.fst_sub, sub_apply, smul_sub,
        ofReal_one]
      abel
    rw [key]
    exact norm_add_stripFactor_smul_lt hθI (by simp) (C.norm_stripTraces_fst_apply_le g t)
      (C.norm_stripTraces_fst_apply_le _ t) (by linarith)
  · have key : C.interSnd (stripGaussian 1 θ (1 + t * I) • x +
          stripFactor θ (1 + t * I) • Ψ (1 + t * I)) =
        (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t +
          stripFactor θ (1 + t * I) • ((h' - h : C.stripTraces) : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t := by
      rw [hgf, Prod.snd_add, add_apply, (hh t).2,
        gaussianTrace_apply_snd, map_add, map_smul, map_smul, hΨ₁, stripGaussian_apply]
      simp only [Submodule.coe_sub, Prod.snd_sub, sub_apply, smul_sub,
        ofReal_one]
      abel
    rw [key]
    exact norm_add_stripFactor_smul_lt hθI (by simp) (C.norm_stripTraces_snd_apply_le g t)
      (C.norm_stripTraces_snd_apply_le _ t) (by linarith)

end ComplexMethodSpace

/-! ### The pairing estimate -/

section Pairing

omit [ContinuousAdd V] [T1Space V]

variable {C} {hC : C.IsRegular}

/-- The pairing of an element `v` of the dual sum space with `y ∈ X₀ ∩ X₁` is bounded by
`‖v‖ ‖y‖`. -/
private theorem norm_dual_sumSpaceEmbed_apply_le (v : (C.dual hC).SumSpace) (y : C.inter) :
    ‖(C.dual hC).sumSpaceEmbed v y‖ ≤ ‖v‖ * ‖y‖ :=
  (((C.dual hC).sumSpaceEmbed v).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (C.norm_dual_sumSpaceEmbed_le hC v) (norm_nonneg y))

/-- `(h i)⁻¹ ((t + h) - t) = i⁻¹` has norm one. -/
private theorem norm_inv_mul_I_mul_sub {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    ‖((h : ℂ) * I)⁻¹ * (((t + h : ℝ) : ℂ) - t)‖ = 1 := by
  rw [norm_mul, norm_inv, norm_mul, norm_I, mul_one, ofReal_add, add_sub_cancel_left, norm_real,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hh)]

namespace IsUpperStripFunction

variable {G : ℂ → (C.dual hC).SumSpace}
  {q : (offDiag (univ : Set ℝ) →ᵇ StrongDual ℂ X₀) × (offDiag (univ : Set ℝ) →ᵇ StrongDual ℂ X₁)}

-- The instance arguments are given explicitly: `IsUpperStripFunction` sees the sum space of the
-- dual couple through its quotient instances, the calculus lemmas through its normed ones.
/-- Paired with a fixed `y ∈ X₀ ∩ X₁`, an upper strip function of the dual couple has derivative
`⟨deriv G z, y⟩` at every point `z` of the open strip. -/
private theorem hasDerivAt_sumSpaceEmbed_apply (hG : (C.dual hC).IsUpperStripFunction G q)
    (y : C.inter) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    HasDerivAt (fun w => (C.dual hC).sumSpaceEmbed (G w) y)
      ((C.dual hC).sumSpaceEmbed (deriv G z) y) z :=
  HasFDerivAt.comp_hasDerivAt (𝕜 := ℂ) (F := (C.dual hC).SumSpace) (E := ℂ) z
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := (C.dual hC).SumSpace) (F := ℂ)
      ((ContinuousLinearMap.apply ℂ ℂ y).comp (C.dual hC).sumSpaceEmbed))
    (DifferentiableAt.hasDerivAt (𝕜 := ℂ) (F := (C.dual hC).SumSpace) (hG.differentiableAt hz))

/-- On the closed strip, the vertical difference quotients of `G` pair with `y` to at most
`‖q‖ ‖y‖`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (z + h * I) - G z) y‖ ≤ ‖q‖ * ‖y‖ := by
  have hsub := hG.norm_sub_le (z := z + h * I) (by simpa using hz) hz
  rw [add_sub_cancel_left] at hsub
  calc _ ≤ ‖((h : ℂ) * I)⁻¹‖ * (‖G (z + h * I) - G z‖ * ‖y‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_dual_sumSpaceEmbed_apply_le _ _) (norm_nonneg _)
    _ ≤ ‖((h : ℂ) * I)⁻¹‖ * ((‖q‖ * ‖(h : ℂ) * I‖) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖q‖ * ‖y‖ := by
        rw [norm_inv, ← mul_assoc, mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.2
          (mul_ne_zero (ofReal_ne_zero.2 hh) I_ne_zero)), mul_one]

/-- On the line `re z = 0` the difference quotients of `G` lie in `X₀*`, so their pairing with
`y` is at most `‖q‖ ‖y‖_{X₀}`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_mul_I_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) (t : ℝ) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (t * I + h * I) - G (t * I)) y‖ ≤
      ‖q‖ * ‖C.interFst y‖ := by
  have hzt : (t * I + h * I : ℂ) = ((t + h : ℝ) : ℂ) * I := by push_cast; ring
  rw [hzt, hG.sub_mul_I (show t + h ≠ t by simpa using hh), map_smul, smul_apply, smul_eq_mul,
    ← mul_assoc, norm_mul, norm_inv_mul_I_mul_sub hh t, one_mul, sumSpaceEmbed_fstToSum,
    dual_embed₀]
  exact ((q.1 _).le_opNorm (C.interFst y)).trans (mul_le_mul_of_nonneg_right
    ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans (norm_fst_le q)) (norm_nonneg _))

/-- On the line `re z = 1` the difference quotients of `G` lie in `X₁*`, so their pairing with
`y` is at most `‖q‖ ‖y‖_{X₁}`. -/
private theorem norm_inv_mul_sumSpaceEmbed_sub_apply_one_add_mul_I_le
    (hG : (C.dual hC).IsUpperStripFunction G q) {h : ℝ} (hh : h ≠ 0) (t : ℝ) (y : C.inter) :
    ‖((h : ℂ) * I)⁻¹ * (C.dual hC).sumSpaceEmbed (G (1 + t * I + h * I) - G (1 + t * I)) y‖ ≤
      ‖q‖ * ‖C.interSnd y‖ := by
  have hzt : (1 + t * I + h * I : ℂ) = 1 + ((t + h : ℝ) : ℂ) * I := by push_cast; ring
  rw [hzt, hG.sub_one_add_mul_I (show t + h ≠ t by simpa using hh), map_smul, smul_apply,
    smul_eq_mul, ← mul_assoc, norm_mul, norm_inv_mul_I_mul_sub hh t, one_mul,
    sumSpaceEmbed_sndToSum, dual_embed₁]
  exact ((q.2 _).le_opNorm (C.interSnd y)).trans (mul_le_mul_of_nonneg_right
    ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans (norm_snd_le q)) (norm_nonneg _))

/-- **The pairing estimate.** Let `(X₀, X₁)` be a regular couple and `0 < θ < 1`. Let `G` be an
upper strip function of the dual couple `(X₀*, X₁*)` with boundary difference quotients `q`, and
let `Φ` be a function with values in `X₀ ∩ X₁`, holomorphic on the open strip and continuous and
bounded on the closed strip, whose boundary values are bounded by `M` in `X₀` on `re z = 0` and in
`X₁` on `re z = 1`. Then `|⟨deriv G θ, Φ θ⟩| ≤ ‖q‖ M`. -/
theorem norm_sumSpaceEmbed_deriv_apply_le (hG : (C.dual hC).IsUpperStripFunction G q) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 1) {Φ : ℂ → C.inter} (hΦ : DiffContOnCl ℂ Φ (verticalStrip 0 1))
    (hΦb : IsBounded (Φ '' verticalClosedStrip 0 1)) {M : ℝ}
    (h₀ : ∀ t : ℝ, ‖C.interFst (Φ (t * I))‖ ≤ M)
    (h₁ : ∀ t : ℝ, ‖C.interSnd (Φ (1 + t * I))‖ ≤ M) :
    ‖(C.dual hC).sumSpaceEmbed (deriv G θ) (Φ θ)‖ ≤ ‖q‖ * M := by
  set P := (C.dual hC).sumSpaceEmbed
  have hqM : 0 ≤ ‖q‖ * M := mul_nonneg (norm_nonneg q) ((norm_nonneg _).trans (h₀ 0))
  have hcl : closure (verticalStrip 0 1) = re ⁻¹' Icc 0 1 := closure_verticalStrip zero_lt_one
  have hGc : ContinuousOn G (re ⁻¹' Icc 0 1) := hcl ▸ hG.diffContOnCl.continuousOn
  -- `φ h z = ⟨(h i)⁻¹ (G (z + h i) - G z), Φ z⟩`, a bounded holomorphic function on the strip.
  set φ : ℝ → ℂ → ℂ := fun h z => ((h : ℂ) * I)⁻¹ * (P (G (z + h * I)) (Φ z) - P (G z) (Φ z))
  have hbound : ∀ h : ℝ, h ≠ 0 → ‖φ h θ‖ ≤ ‖q‖ * M := by
    intro h hh
    have hmaps (s : Set ℝ) : MapsTo (fun z : ℂ => z + h * I) (re ⁻¹' s) (re ⁻¹' s) :=
      fun z hz => by simpa using hz
    have hd : DiffContOnCl ℂ (φ h) (verticalStrip 0 1) :=
      ⟨(((P.differentiable.comp_differentiableOn (hG.diffContOnCl.differentiableOn.comp
          (differentiableOn_id.add_const _) (hmaps _))).clm_apply hΦ.differentiableOn).fun_sub
          ((P.differentiable.comp_differentiableOn hG.diffContOnCl.differentiableOn).clm_apply
            hΦ.differentiableOn)).const_mul _,
        hcl ▸ ((((P.continuous.comp_continuousOn (hGc.comp (continuousOn_id.add continuousOn_const)
          (hmaps _))).clm_apply (hcl ▸ hΦ.continuousOn)).fun_sub
          ((P.continuous.comp_continuousOn hGc).clm_apply (hcl ▸ hΦ.continuousOn))).const_mul _)⟩
    have hφ : ∀ z, φ h z = ((h : ℂ) * I)⁻¹ * P (G (z + h * I) - G z) (Φ z) := fun z => by
      rw [map_sub, sub_apply]
    obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hΦb
    have hB : BddAbove ((norm ∘ φ h) '' verticalClosedStrip 0 1) := ⟨‖q‖ * K, by
      rintro _ ⟨z, hz, rfl⟩
      exact (hφ z ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_le hG hh hz (Φ z)).trans
        (mul_le_mul_of_nonneg_left (hK _ (mem_image_of_mem _ hz)) (norm_nonneg q))⟩
    have ha : ∀ z ∈ re ⁻¹' {0}, ‖φ h z‖ ≤ ‖q‖ * M := fun z hz => by
      obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = t * I := ⟨z.im, Complex.ext (by simpa using hz) (by simp)⟩
      exact (hφ _ ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_mul_I_le hG hh t _).trans
        (mul_le_mul_of_nonneg_left (h₀ t) (norm_nonneg q))
    have hb : ∀ z ∈ re ⁻¹' {1}, ‖φ h z‖ ≤ ‖q‖ * M := fun z hz => by
      obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = 1 + t * I :=
        ⟨z.im, Complex.ext (by simpa using hz) (by simp)⟩
      exact (hφ _ ▸ norm_inv_mul_sumSpaceEmbed_sub_apply_one_add_mul_I_le hG hh t _).trans
        (mul_le_mul_of_nonneg_left (h₁ t) (norm_nonneg q))
    have := norm_le_interp_of_mem_verticalClosedStrip₀₁' (φ h) (z := (θ : ℂ))
      (by simpa using Ioo_subset_Icc_self hθ) hd hB ha hb
    rwa [← Real.rpow_add' hqM (by simp), ofReal_re, sub_add_cancel, Real.rpow_one] at this
  -- Letting `h → 0`, the difference quotients at `θ` tend to the derivative.
  have hmap : Tendsto (fun h : ℝ => (h : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun h : ℝ => (h : ℂ) * I).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun h hh => mul_ne_zero (ofReal_ne_zero.2 hh) I_ne_zero)
  have hderiv : HasDerivAt (fun w => P (G w) (Φ θ)) (P (deriv G θ) (Φ θ)) θ :=
    hasDerivAt_sumSpaceEmbed_apply hG (Φ θ) (by simpa using hθ)
  have hlim : Tendsto (fun h : ℝ => φ h θ) (𝓝[≠] 0) (𝓝 (P (deriv G θ) (Φ θ))) :=
    hderiv.tendsto_slope_zero.comp hmap
  exact le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall hbound)

end IsUpperStripFunction

end Pairing

/-! ### The upper space of the dual couple in the dual of the complex method -/

namespace UpperComplexMethodSpace

variable {C} [CompleteSpace X₀] [CompleteSpace X₁] {hC : C.IsRegular} {θ : ℝ}

/-- **Calderón's duality estimate.** For a regular Banach couple `(X₀, X₁)`, the pairing of
`u ∈ [X₀*, X₁*]^θ` with `x ∈ X₀ ∩ X₁` satisfies `|⟨u, x⟩| ≤ ‖u‖^[θ] ‖x‖_θ`. -/
theorem norm_sumSpaceEmbed_toSum_apply_le (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    ‖(C.dual hC).sumSpaceEmbed (toSum u) x‖ ≤ ‖u‖ * ‖ComplexMethodSpace.ofInter θ x‖ := by
  by_cases hθ : θ ∈ Ioo 0 1
  swap
  · simp [eq_zero_of_notMem hθ u]
  have key : ∀ ε > 0, ‖(C.dual hC).sumSpaceEmbed (toSum u) x‖ ≤
      (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε) := fun ε hε => by
    obtain ⟨q, rfl, hq⟩ := norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hε)
    obtain ⟨Φ, hΦ, hΦb, hΦθ, h₀, h₁⟩ := ComplexMethodSpace.exists_inter_of_norm_ofInter_lt hθ
      (lt_add_of_pos_right ‖ComplexMethodSpace.ofInter θ x‖ hε)
    have hG := (C.dual hC).isUpperStripFunction_upperStripFunction q
    have hA := hG.norm_sumSpaceEmbed_deriv_apply_le hθ hΦ hΦb (fun t => (h₀ t).le)
      (fun t => (h₁ t).le)
    rw [hΦθ] at hA
    rw [toSum_mk, (C.dual hC).upperStripDerivEval_apply (z := θ) (by simpa using hθ) q]
    exact hA.trans (mul_le_mul_of_nonneg_right ((Submodule.norm_coe q).trans_lt hq).le
      (by positivity))
  have hlim : Tendsto (fun ε : ℝ => (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε))
      (𝓝[>] 0) (𝓝 (‖u‖ * ‖ComplexMethodSpace.ofInter θ x‖)) :=
    ((by fun_prop : Continuous fun ε : ℝ =>
      (‖u‖ + ε) * (‖ComplexMethodSpace.ofInter θ x‖ + ε)).tendsto' 0 _ (by simp)).mono_left
        nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- Continuous functionals on `[X₀, X₁]_θ` agreeing on `X₀ ∩ X₁` are equal. -/
private theorem strongDual_ext_ofInter {f g : StrongDual ℂ (C.ComplexMethodSpace θ)}
    (h : ∀ x : C.inter, f (ComplexMethodSpace.ofInter θ x) = g (ComplexMethodSpace.ofInter θ x)) :
    f = g :=
  DFunLike.coe_injective <| (ComplexMethodSpace.denseRange_ofInter θ).equalizer f.continuous
    g.continuous (funext h)

variable (hC θ) in
/-- The extension of `x ↦ ⟨u, x⟩` from `X₀ ∩ X₁` to `[X₀, X₁]_θ`. -/
private def pairingExtension (u : (C.dual hC).UpperComplexMethodSpace θ) :
    StrongDual ℂ (C.ComplexMethodSpace θ) :=
  LinearMap.extendOfNorm ((C.dual hC).sumSpaceEmbed (toSum u)).toLinearMap
    (ComplexMethodSpace.ofInter θ).toLinearMap

private theorem pairingExtension_apply_ofInter (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    pairingExtension hC θ u (ComplexMethodSpace.ofInter θ x) =
      (C.dual hC).sumSpaceEmbed (toSum u) x :=
  LinearMap.extendOfNorm_eq (ComplexMethodSpace.denseRange_ofInter θ)
    ⟨_, norm_sumSpaceEmbed_toSum_apply_le u⟩ x

variable (hC θ) in
/-- **The upper space of the dual couple in the dual of the complex method (Calderón).** For a
regular Banach couple `(X₀, X₁)`, each `u ∈ [X₀*, X₁*]^θ` defines the continuous functional on
`[X₀, X₁]_θ` extending `x ↦ ⟨u, x⟩` from the dense subspace `X₀ ∩ X₁`
(`toStrongDual_apply_ofInter`). The map `u ↦ ⟨u, ·⟩` is injective (`toStrongDual_injective`) and
does not increase norms (`norm_toStrongDual_le`). -/
def toStrongDual :
    (C.dual hC).UpperComplexMethodSpace θ →L[ℂ] StrongDual ℂ (C.ComplexMethodSpace θ) :=
  LinearMap.mkContinuous
    { toFun := pairingExtension hC θ
      map_add' u v := strongDual_ext_ofInter fun x => by
        simp only [add_apply, pairingExtension_apply_ofInter, map_add]
      map_smul' c u := strongDual_ext_ofInter fun x => by
        simp only [smul_apply, pairingExtension_apply_ofInter, map_smul, RingHom.id_apply] }
    1 fun u => by
      rw [one_mul]
      exact LinearMap.opNorm_extendOfNorm_le (ComplexMethodSpace.denseRange_ofInter θ)
        (norm_nonneg u) (norm_sumSpaceEmbed_toSum_apply_le u)

/-- On `X₀ ∩ X₁`, the functional `toStrongDual hC θ u` is the pairing with `u`. -/
@[simp] theorem toStrongDual_apply_ofInter (u : (C.dual hC).UpperComplexMethodSpace θ)
    (x : C.inter) :
    toStrongDual hC θ u (ComplexMethodSpace.ofInter θ x) =
      (C.dual hC).sumSpaceEmbed (toSum u) x :=
  pairingExtension_apply_ofInter u x

/-- `toStrongDual hC θ u` is the only continuous functional on `[X₀, X₁]_θ` that pairs with
`X₀ ∩ X₁` as `u` does. -/
theorem eq_toStrongDual_iff {u : (C.dual hC).UpperComplexMethodSpace θ}
    {f : StrongDual ℂ (C.ComplexMethodSpace θ)} :
    f = toStrongDual hC θ u ↔
      ∀ x : C.inter, f (ComplexMethodSpace.ofInter θ x) = (C.dual hC).sumSpaceEmbed (toSum u) x :=
  ⟨fun h x => h ▸ toStrongDual_apply_ofInter u x, fun h =>
    strongDual_ext_ofInter fun x => by rw [h, toStrongDual_apply_ofInter]⟩

/-- `toStrongDual` does not increase norms. -/
theorem norm_toStrongDual_le (u : (C.dual hC).UpperComplexMethodSpace θ) :
    ‖toStrongDual hC θ u‖ ≤ ‖u‖ :=
  LinearMap.opNorm_extendOfNorm_le (ComplexMethodSpace.denseRange_ofInter θ) (norm_nonneg u)
    (norm_sumSpaceEmbed_toSum_apply_le u)

theorem opNorm_toStrongDual_le : ‖toStrongDual (C := C) hC θ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_toStrongDual_le u

/-- `toStrongDual` is injective: an element of `[X₀*, X₁*]^θ` is determined by its pairing with
`X₀ ∩ X₁`. -/
theorem toStrongDual_injective : Function.Injective (toStrongDual (C := C) hC θ) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => toSum_injective ?_
  refine (C.dual hC).sumSpaceEmbed_injective ?_
  ext x
  simpa using congrArg (fun f => f (ComplexMethodSpace.ofInter θ x)) hu

end UpperComplexMethodSpace

end TauCeti.CompatibleCouple
