/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Bounded boundary traces and Calderón's density lemma in the complex method

Calderón's complex interpolation space `[X₀, X₁]_θ` is defined in
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic` using admissible functions on the closed
strip `0 ≤ re z ≤ 1` whose boundary traces lie in `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. This file proves the
bounded-boundary equivalence and density theorems of Bergh–Löfström §4.2:

1. **Bounded-boundary formulation (Bergh–Löfström, Lemma 4.2.1).** Dropping vanishing at infinity
   yields `CompatibleCouple.IsBoundedStripFunction`, with traces in `(ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)`.
   Damping by `exp (δ (z - θ)²)` as `δ → 0⁺` shows that bounded-boundary strip functions define the
   same space `[X₀, X₁]_θ` and quotient norm (`exists_toSum_eq_iff_isBoundedStripFunction`,
   `norm_lt_iff_exists_isBoundedStripFunction`) without completeness hypotheses.

2. **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** For a Banach couple `(X₀, X₁)`, the
   `ℂ`-linear span `elementaryStripTraces` of the elementary intersection-valued traces
   `z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω ∈ ℝ`, `x ∈ X₀ ∩ X₁`) is dense in `stripTraces`
   (`dense_elementaryStripTraces`), proved by vertical `T * I`-periodization of `exp (δ z²) F z`,
   Cauchy's rectangle theorem on `[0, 1] × [0, T]`, and convolution on `AddCircle T` against a
   scalar trigonometric polynomial.

3. **Intersection density (Bergh–Löfström, Theorem 4.2.2 (a)).** For a Banach couple `(X₀, X₁)`,
   `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` for every `θ : ℝ` (`ComplexMethodSpace.denseRange_ofInter`).

Endpoint inclusions and regularization invariance (`[X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`) are deduced in
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Regularize`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§3–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.2 (Lemma 4.2.1, Theorem 4.2.2 (a), Lemma 4.2.3).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Set Topology AddCircle
open scoped ZeroAtInfty BoundedContinuousFunction

namespace TauCeti.CompatibleCouple

private theorem tendsto_exp_sub_sq_cocompact {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (c - δ * t ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun _ => by simp
  refine Real.tendsto_exp_atBot.comp ?_
  simpa [sub_eq_add_neg] using
    tendsto_atBot_add_const_left _ c ((tendsto_neg_atTop_atBot.comp hsq).const_mul_atBot hδ)

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Bounded-boundary strip functions (Bergh–Löfström, Lemma 4.2.1) -/

/-- `F` is a *bounded-boundary strip function* for `C`, with bounded continuous boundary traces
`g = (g₀, g₁) : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)`: it is bounded on `0 ≤ re z ≤ 1`, holomorphic on the open
strip and continuous on its closure, with `F (t * I) = g₀ t` and `F (1 + t * I) = g₁ t` without
requiring `g₀` or `g₁` to vanish at infinity. -/
structure IsBoundedStripFunction (F : ℂ → C.SumSpace)
    (g : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)) : Prop where
  /-- `F` is holomorphic on the open strip and continuous on its closure. -/
  diffContOnCl : DiffContOnCl ℂ F (verticalStrip 0 1)
  /-- `F` is bounded on the closed strip. -/
  isBounded : Bornology.IsBounded (F '' verticalClosedStrip 0 1)
  /-- On `re z = 0`, `F` takes the values of `g₀` in `X₀`. -/
  apply_mul_I (t : ℝ) : F (t * I) = C.fstToSum (g.1 t)
  /-- On `re z = 1`, `F` takes the values of `g₁` in `X₁`. -/
  apply_one_add_mul_I (t : ℝ) : F (1 + t * I) = C.sndToSum (g.2 t)

variable {C} in
/-- Every admissible strip function with traces in `C₀` is a bounded-boundary strip function. -/
theorem IsStripFunction.isBoundedStripFunction {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) :
    C.IsBoundedStripFunction F (g.1.toBCF, g.2.toBCF) where
  diffContOnCl := hF.diffContOnCl
  isBounded := hF.isBounded
  apply_mul_I := hF.apply_mul_I
  apply_one_add_mul_I := hF.apply_one_add_mul_I

namespace IsBoundedStripFunction

variable {C} {F : ℂ → C.SumSpace} {g : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)}

theorem exists_norm_le (hF : C.IsBoundedStripFunction F g) :
    ∃ M, ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hF.isBounded
  exact ⟨M, fun z hz => hM _ (mem_image_of_mem F hz)⟩

/-- **Three-lines bound** for bounded-boundary strip functions. -/
theorem norm_le_rpow_mul_rpow (hF : C.IsBoundedStripFunction F g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖F z‖ ≤ ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re := by
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    obtain ⟨M, hM⟩ := hF.exists_norm_le; exact ⟨M, by rintro _ ⟨w, hw, rfl⟩; exact hM w hw⟩
  refine norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hF.diffContOnCl hB
    (fun w hw => ?_) (fun w hw => ?_)
  · rw [← re_add_im w, hw, ofReal_zero, zero_add, hF.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (g.1.norm_coe_le_norm _)
  · rw [← re_add_im w, hw, ofReal_one, hF.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (g.2.norm_coe_le_norm _)

/-- **Maximum principle** for bounded-boundary strip functions. -/
theorem norm_le (hF : C.IsBoundedStripFunction F g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F z‖ ≤ ‖g‖ :=
  (hF.norm_le_rpow_mul_rpow hz).trans <| by
    calc ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re ≤ ‖g‖ ^ (1 - z.re) * ‖g‖ ^ z.re := by
          gcongr
          · exact sub_nonneg.2 hz.2
          · exact norm_fst_le g
          · exact hz.1
          · exact norm_snd_le g
      _ = ‖g‖ := by rw [← Real.rpow_add' (norm_nonneg g) (by simp), sub_add_cancel, Real.rpow_one]

private theorem norm_exp_sub_sq (δ θ : ℝ) (z : ℂ) :
    ‖exp ((δ : ℂ) * (z - θ) ^ 2)‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

private theorem norm_exp_sub_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ} (hz : z.re ∈ Icc 0 1) :
    ‖exp ((δ : ℂ) * (z - θ) ^ 2)‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_exp_sub_sq]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

private def dampBCF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {δ : ℝ} (hδ : 0 < δ)
    (θ a : ℝ) (f : ℝ →ᵇ E) : C₀(ℝ, E) :=
  ⟨⟨fun t => exp ((δ : ℂ) * ((a : ℂ) + t * I - θ) ^ 2) • f t,
    (by fun_prop : Continuous fun t : ℝ => exp ((δ : ℂ) * ((a : ℂ) + t * I - θ) ^ 2)).smul
      f.continuous⟩,
    squeeze_zero_norm
      (fun t => (norm_smul _ _).trans_le
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _)))
      (by simpa using ((tendsto_exp_sub_sq_cocompact hδ (δ * (a - θ) ^ 2)).congr fun t => by
        rw [norm_exp_sub_sq]; congr 1; simp [mul_sub]).mul_const ‖f‖)⟩

/-- Damping a bounded-boundary strip function by `exp (δ (z - θ)²)` (`δ > 0`) yields an admissible
strip function with `C₀` boundary traces of norm at most `exp (δ (|θ| + 1)²) ‖g‖`. -/
theorem exists_isStripFunction_gaussianDamp (hF : C.IsBoundedStripFunction F g) {δ : ℝ}
    (hδ : 0 < δ) (θ : ℝ) :
    ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁),
      C.IsStripFunction (fun z => exp ((δ : ℂ) * (z - θ) ^ 2) • F z) g' ∧
        ‖g'‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖ := by
  have hc : Differentiable ℂ (fun z : ℂ => exp ((δ : ℂ) * (z - θ) ^ 2)) := by fun_prop
  refine ⟨(dampBCF hδ θ 0 g.1, dampBCF hδ θ 1 g.2), ⟨hc.diffContOnCl.smul hF.diffContOnCl, ?_,
    fun t => by simp [dampBCF, hF.apply_mul_I],
    fun t => by simp [dampBCF, hF.apply_one_add_mul_I]⟩, ?_⟩
  · obtain ⟨M, hM⟩ := hF.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ * (|θ| + 1) ^ 2) * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩; rw [norm_smul]
    exact mul_le_mul (norm_exp_sub_sq_le hδ.le θ hz) (hM z hz) (norm_nonneg _) (by positivity)
  · refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_,
      (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_⟩
    · exact (norm_smul _ _).trans_le (mul_le_mul
        (norm_exp_sub_sq_le hδ.le θ (z := (0 : ℝ) + t * I) (by simp))
        ((g.1.norm_coe_le_norm t).trans (norm_fst_le g)) (norm_nonneg _) (by positivity))
    · exact (norm_smul _ _).trans_le (mul_le_mul
        (norm_exp_sub_sq_le hδ.le θ (z := (1 : ℝ) + t * I) (by simp))
        ((g.2.norm_coe_le_norm t).trans (norm_snd_le g)) (norm_nonneg _) (by positivity))

end IsBoundedStripFunction

namespace ComplexMethodSpace

variable {C} {θ : ℝ}

/-- **Bergh–Löfström, Lemma 4.2.1.** For `0 ≤ θ ≤ 1`, a bounded-boundary strip function `F` with
traces `g` and `F θ = toSum u` bounds `‖u‖_θ` by `‖g‖`. -/
theorem norm_le_of_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {F : ℂ → C.SumSpace} {g : (ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)} (hF : C.IsBoundedStripFunction F g)
    (hu : toSum u = F θ) : ‖u‖ ≤ ‖g‖ := by
  have key (δ : ℝ) (hδ : 0 < δ) : ‖u‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖ := by
    obtain ⟨g', hg', hnorm⟩ := hF.exists_isStripFunction_gaussianDamp hδ θ
    exact (norm_le_of_toSum_eq hθ hg' (by simp [hu])).trans hnorm
  have hcont : Continuous fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖ := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖) (𝓝[>] 0) (𝓝 ‖g‖) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- **Bergh–Löfström, Lemma 4.2.1.** An element of `X₀ + X₁` belongs to `[X₀, X₁]_θ` (`0 ≤ θ ≤ 1`)
iff it is `F θ` for a bounded-boundary strip function `F`. -/
theorem exists_toSum_eq_iff_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.SumSpace} :
    (∃ v : C.ComplexMethodSpace θ, toSum v = u) ↔
      ∃ F g, C.IsBoundedStripFunction F g ∧ F θ = u := by
  rw [exists_toSum_eq_iff hθ]
  refine ⟨fun ⟨F, g, hF, h⟩ => ⟨F, (g.1.toBCF, g.2.toBCF), hF.isBoundedStripFunction, h⟩, ?_⟩
  rintro ⟨F, g, hF, rfl⟩
  obtain ⟨g', hg', -⟩ := hF.exists_isStripFunction_gaussianDamp one_pos θ
  exact ⟨_, g', hg', by simp⟩

/-- **Bergh–Löfström, Lemma 4.2.1.** For `0 ≤ θ ≤ 1`, the quotient norm on `[X₀, X₁]_θ` coincides
with the infimum over bounded-boundary strip functions. -/
theorem norm_lt_iff_exists_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {r : ℝ} :
    ‖u‖ < r ↔ ∃ F g, C.IsBoundedStripFunction F g ∧ toSum u = F θ ∧ ‖g‖ < r := by
  refine ⟨fun hr => ?_, fun ⟨F, g, hF, hu, hg⟩ =>
    (norm_le_of_isBoundedStripFunction hθ hF hu).trans_lt hg⟩
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  refine ⟨C.stripFunction g, ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.toBCF,
    (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.toBCF),
    (C.isStripFunction_stripFunction g).isBoundedStripFunction,
    by rw [toSum_mk, stripEval_apply], ?_⟩
  simpa [Prod.norm_def, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using hg

end ComplexMethodSpace

/-! ### Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3) -/

section ElementaryTraces

private def expGaussianScalar (δ ω : ℝ) (z : ℂ) : ℂ := exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z)

private theorem differentiable_expGaussianScalar (δ ω : ℝ) :
    Differentiable ℂ (expGaussianScalar δ ω) := by unfold expGaussianScalar; fun_prop

private theorem norm_expGaussianScalar (δ ω : ℝ) (z : ℂ) :
    ‖expGaussianScalar δ ω z‖ = Real.exp (δ * (z.re ^ 2 - z.im ^ 2) + ω * z.re) := by
  rw [expGaussianScalar, Complex.norm_exp]; congr 1; simp [sq]

private theorem norm_expGaussianScalar_le {δ : ℝ} (hδ : 0 ≤ δ) (ω : ℝ) {z : ℂ}
    (hz : z.re ∈ Icc 0 1) : ‖expGaussianScalar δ ω z‖ ≤ Real.exp (δ + |ω|) := by
  rw [norm_expGaussianScalar]
  refine Real.exp_le_exp.2 ?_
  have hre : z.re ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hω : ω * z.re ≤ |ω| := by nlinarith [hz.1, hz.2, le_abs_self ω, neg_abs_le ω, abs_nonneg ω]
  nlinarith [sq_nonneg z.im]

private def expGaussianC0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {δ : ℝ}
    (hδ : 0 < δ) (ω : ℝ) (z : ℝ → ℂ) (hz : Continuous z) (a : ℝ)
    (hza : ∀ t, z t = (a : ℂ) + t * I) (e : E) : C₀(ℝ, E) :=
  ⟨⟨fun t => expGaussianScalar δ ω (z t) • e,
    ((differentiable_expGaussianScalar δ ω).continuous.comp hz).smul continuous_const⟩,
    squeeze_zero_norm (fun _ => (norm_smul _ _).le)
      (by simpa using ((tendsto_exp_sub_sq_cocompact hδ (δ * a ^ 2 + ω * a)).congr fun t => by
        rw [hza, norm_expGaussianScalar]; congr 1; simp; ring).mul_const ‖e‖)⟩

private def expGaussianTracePair {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C₀(ℝ, X₀) × C₀(ℝ, X₁) :=
  (expGaussianC0 hδ ω (fun t => t * I) (by fun_prop) 0 (by simp) (C.interFst x),
    expGaussianC0 hδ ω (fun t => 1 + t * I) (by fun_prop) 1 (by simp) (C.interSnd x))

private theorem isStripFunction_expGaussian {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C.IsStripFunction (fun z => expGaussianScalar δ ω z • C.fstToSum (C.interFst x))
      (C.expGaussianTracePair hδ ω x) where
  diffContOnCl := ((differentiable_expGaussianScalar δ ω).smul_const _).diffContOnCl
  isBounded := isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ + |ω|) * ‖C.fstToSum (C.interFst x)‖,
    by rintro _ ⟨z, hz, rfl⟩; rw [norm_smul]
       exact mul_le_mul_of_nonneg_right (norm_expGaussianScalar_le hδ.le ω hz) (norm_nonneg _)⟩
  apply_mul_I t := by simp [expGaussianTracePair, expGaussianC0]
  apply_one_add_mul_I t := by
    simpa [expGaussianTracePair, expGaussianC0] using
      congrArg (expGaussianScalar δ ω (1 + t * I) • ·) (C.fstToSum_interFst x)

/-- The admissible boundary trace of the elementary intersection-valued function
`z ↦ exp (δ z² + ω z) x` for `δ > 0`, `ω : ℝ`, and `x : C.inter`. -/
def expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) : C.stripTraces :=
  ⟨C.expGaussianTracePair hδ ω x, mem_stripTraces_iff.2 ⟨_, C.isStripFunction_expGaussian hδ ω x⟩⟩

@[simp]
theorem expGaussianTrace_apply_fst {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      exp ((δ : ℂ) * (t * I) ^ 2 + (ω : ℂ) * (t * I)) • C.interFst x := (rfl)

@[simp]
theorem expGaussianTrace_apply_snd {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) (t : ℝ) :
    (C.expGaussianTrace hδ ω x : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      exp ((δ : ℂ) * (1 + t * I) ^ 2 + (ω : ℂ) * (1 + t * I)) • C.interSnd x := (rfl)

theorem stripEval_expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    C.stripEval z (C.expGaussianTrace hδ ω x) =
      exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) • C.fstToSum (C.interFst x) := by
  rw [stripEval_apply, stripFunction_eq (C.isStripFunction_expGaussian hδ ω x) hz]; rfl

/-- The submodule of `C.stripTraces` spanned over `ℂ` by the elementary intersection-valued traces
`exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`, `x : C.inter`). -/
def elementaryStripTraces : Submodule ℂ C.stripTraces :=
  Submodule.span ℂ
    {g | ∃ (δ : ℝ) (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x = g}

theorem expGaussianTrace_mem_elementaryStripTraces {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C.expGaussianTrace hδ ω x ∈ C.elementaryStripTraces :=
  Submodule.subset_span ⟨δ, hδ, ω, x, rfl⟩

theorem elementaryStripTraces_le {S : Submodule ℂ C.stripTraces}
    (h : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x ∈ S) :
    C.elementaryStripTraces ≤ S :=
  Submodule.span_le.2 fun _ ⟨_, hδ, ω, x, heq⟩ => heq ▸ h hδ ω x

/-! #### Analytical helpers for `dense_elementaryStripTraces` -/

private theorem closure_verticalStrip_zero_one :
    closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]; rfl

private theorem pow_neg_succ_natAbs (r : ℝ) :
    (fun n : ℕ => r ^ (-(n + 1 : ℤ)).natAbs) = fun n : ℕ => r * r ^ n := by
  ext n; rw [(by omega : (-(n + 1 : ℤ)).natAbs = n + 1), pow_succ']

private theorem summable_pow_natAbs {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable fun k : ℤ => r ^ k.natAbs :=
  Summable.of_nat_of_neg_add_one (summable_geometric_of_lt_one hr₀ hr₁)
    (pow_neg_succ_natAbs r ▸ (summable_geometric_of_lt_one hr₀ hr₁).mul_left r)

private theorem tsum_pow_natAbs_ite_eq {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    (∑' k : ℤ, if k = 0 then (0 : ℝ) else r ^ k.natAbs) = 2 * (r * (1 - r)⁻¹) := by
  have h1 : (fun n : ℕ => r ^ (n : ℤ).natAbs) = fun n : ℕ => r ^ n := by ext n; simp
  have h2 := pow_neg_succ_natAbs r
  have hite : (∑' k : ℤ, r ^ k.natAbs) =
      (1 : ℝ) + ∑' k : ℤ, if k = 0 then (0 : ℝ) else r ^ k.natAbs := by
    simpa using (summable_pow_natAbs hr₀ hr₁).tsum_eq_add_tsum_ite (0 : ℤ)
  have htot : (∑' k : ℤ, r ^ k.natAbs) = (1 - r)⁻¹ + r * (1 - r)⁻¹ := by
    rw [tsum_of_nat_of_neg_add_one (h1 ▸ summable_geometric_of_lt_one hr₀ hr₁)
      (h2 ▸ (summable_geometric_of_lt_one hr₀ hr₁).mul_left r), h1, h2,
      tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
  have halg : (1 - r)⁻¹ + r * (1 - r)⁻¹ = 1 + 2 * (r * (1 - r)⁻¹) := by
    have : 1 - r ≠ 0 := sub_ne_zero.2 hr₁.ne'; field_simp; ring
  linarith

/-- Small-`δ` Gaussian multiplication `t ↦ exp (2 δ (a + i t)²) • f t` approximates `f` uniformly
on `ℝ` for any `f : C₀(ℝ, E)`. -/
private theorem exists_gaussian_smul_approx_single {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (a : ℝ) (f : C₀(ℝ, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ {δ : ℝ}, 0 < δ → δ < δ₀ →
      ∀ t : ℝ, ‖exp ((2 * δ : ℝ) * (a + t * I) ^ 2) • f t - f t‖ ≤ ε := by
  have hlim : Tendsto (fun t : ℝ => ‖f t‖) (cocompact ℝ) (𝓝 0) := by
    simpa using (zero_at_infty f).norm
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 4)))
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_exp.continuousAt (x := 0)) (ε / (‖f‖ + 1)) (div_pos hε (by positivity))
  rw [Complex.exp_zero] at hη
  let B : ℝ := (|a| + R) ^ 2 + 1
  have hBpos : 0 < B := by positivity
  refine ⟨min (Real.log 2 / (2 * (a ^ 2 + 1))) (η / (2 * B)),
    lt_min (div_pos (Real.log_pos one_lt_two) (by positivity)) (div_pos hηpos (by positivity)),
    fun {δ} hδ hδlt t => ?_⟩
  by_cases ht : |t| ≤ R
  · have hsq : ‖(a + t * I : ℂ) ^ 2‖ < B :=
      ((norm_pow _ 2).trans_le (pow_le_pow_left₀ (norm_nonneg _)
        ((norm_add_le _ _).trans (by simpa using add_le_add_right ht |a|)) 2)).trans_lt
          (lt_add_one _)
    have hw : dist (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) 0 < η := by
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hδ' : 2 * δ < 2 * (η / (2 * B)) := by linarith [hδlt.trans_le (min_le_right _ _)]
      exact (mul_lt_mul'' hδ' hsq (by positivity) (norm_nonneg _)).trans_eq (by field_simp)
    have hexp_lt : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1‖ < ε / (‖f‖ + 1) := by
      simpa [dist_eq_norm] using hη hw
    rw [show exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t =
      (exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1) • f t by rw [sub_smul, one_smul], norm_smul]
    exact (mul_le_mul hexp_lt.le (f.norm_coe_le_norm t) (norm_nonneg _) (by positivity)).trans <| by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
  · have hft : ‖f t‖ < ε / 4 := hKc fun hm => not_le.2 (not_le.1 ht) (by simpa using hR t hm)
    have hexp_le : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2)‖ ≤ 2 := by
      rw [Complex.norm_exp, show (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2).re =
        2 * δ * (a ^ 2 - t ^ 2) by simp [sq]]
      refine (Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log zero_lt_two)
      have := (lt_div_iff₀ (by positivity : 0 < 2 * (a ^ 2 + 1))).1
        (hδlt.trans_le (min_le_left _ _))
      nlinarith [sq_nonneg t]
    exact (norm_sub_le _ _).trans <| by
      rw [norm_smul]; linarith [mul_le_mul_of_nonneg_right hexp_le (norm_nonneg (f t))]

private theorem natAbs_le_sq (k : ℤ) : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
  rw [show (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 by
    rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]]
  rcases Nat.eq_zero_or_pos k.natAbs with h0 | hpos
  · simp [h0]
  · nlinarith [show (1 : ℝ) ≤ (k.natAbs : ℝ) by exact_mod_cast hpos]

private theorem exp_damped_shift_le {δ T B x y : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hx : x ∈ Icc 0 1) (hy : |y| ≤ B) (k : ℤ) :
    ‖exp ((δ : ℂ) * ((x : ℂ) + (y + k * T : ℝ) * I) ^ 2)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [show ((δ : ℂ) * ((x : ℂ) + (y + k * T : ℝ) * I) ^ 2).re =
    δ * (x ^ 2 - (y + k * T) ^ 2) by simp [sq]]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hy2 : y ^ 2 ≤ B ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hB]
  have hk2 : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (natAbs_le_sq k) (sq_nonneg T)).trans_eq (by ring)
  nlinarith [sq_nonneg (2 * y + k * T)]

private theorem norm_damped_shift_le {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) {δ T B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (k : ℤ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (him : |z.im| ≤ B) :
    ‖exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  have hz' : z + k * T * I ∈ verticalClosedStrip 0 1 := by simpa using hz
  rw [norm_smul, mul_right_comm (Real.exp (δ * (1 + B ^ 2))) ‖g‖]
  refine mul_le_mul ?_ (hF.norm_le hz') (norm_nonneg _) (by positivity)
  have hzeq : z + k * T * I = (z.re : ℂ) + (z.im + k * T : ℝ) * I := by
    nth_rw 1 [← re_add_im z]; push_cast; ring
  rw [hzeq]
  exact exp_damped_shift_le hδ hB hz him k

private theorem norm_double_damped_shift_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ) (k : ℤ) (t : ℝ) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
      Real.exp (2 * δ) * ‖f‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [norm_smul, norm_smul, Complex.norm_exp, Complex.norm_exp, ← mul_assoc, ← Real.exp_add,
    mul_right_comm, ← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), ← Real.exp_add]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
  rw [show ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) by simp [sq],
    show ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2).re =
      δ * (a ^ 2 - (t + k * T) ^ 2) by simp [sq]]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hk2 : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (natAbs_le_sq k) (sq_nonneg T)).trans_eq (by ring)
  nlinarith [sq_nonneg (2 * t + k * T)]

/-- Continuity and periodicity of the vertical periodization of a Gaussian-damped `C₀` trace. -/
private theorem continuous_and_periodic_periodizeTrace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1)
    (hδ : 0 < δ) (hT : 0 < T) :
    Continuous (fun t : ℝ => ∑' k : ℤ, exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) •
      f (t + k * T)) ∧
    Function.Periodic (fun t : ℝ => ∑' k : ℤ, exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) •
      f (t + k * T)) T ∧
    (∀ t : ℝ, Summable fun k : ℤ => exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) •
      f (t + k * T)) := by
  set term : ℤ → ℝ → E := fun k t =>
    exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)
  set r : ℝ := Real.exp (-(δ * T ^ 2 / 2))
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  have hbound (B : ℝ) (hB : 0 ≤ B) (k : ℤ) (t : ℝ) (ht : |t| ≤ B) :
      ‖term k t‖ ≤ Real.exp (δ * (1 + B ^ 2)) * ‖f‖ * r ^ k.natAbs := by
    dsimp [term, r]; rw [norm_smul, mul_right_comm]
    exact mul_le_mul (exp_damped_shift_le hδ hB ha ht k) (f.norm_coe_le_norm _)
      (norm_nonneg _) (by positivity)
  have hsum (t : ℝ) : Summable fun k : ℤ => term k t :=
    .of_norm_bounded ((summable_pow_natAbs hr₀ hr₁).mul_left _) fun k =>
      hbound |t| (abs_nonneg t) k t le_rfl
  refine ⟨continuous_iff_continuousAt.2 fun t₀ => ?_, fun t => ?_, hsum⟩
  · set B := |t₀| + 1
    exact (continuousOn_tsum (fun k => by dsimp [term]; fun_prop)
      ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖f‖))
      fun k t ht => hbound B (by positivity) k t (le_of_lt ht)).continuousAt
        ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (lt_add_one |t₀|))
  · dsimp only; conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    congr 1 with k; simp only [Equiv.coe_addRight]
    rw [show t + T + (k : ℝ) * T = t + ((k + 1 : ℤ) : ℝ) * T by push_cast; ring]

/-- Holomorphy, boundary continuity, and vertical periodicity of `∑' k : ℤ, G (z + k T I)`. -/
private theorem diffContOnCl_and_periodic_periodizeStrip [CompleteSpace X₀] [CompleteSpace X₁]
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    let P : ℂ → C.SumSpace := fun z => ∑' k : ℤ,
      exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)
    DiffContOnCl ℂ P (verticalStrip 0 1) ∧
    (∀ z : ℂ, P (z + T * I) = P z) ∧
    (∀ t : ℝ, P (t * I) = C.fstToSum (∑' k : ℤ,
      exp ((δ : ℂ) * ((t + k * T : ℝ) * I) ^ 2) • g.1 (t + k * T))) ∧
    (∀ t : ℝ, P (1 + t * I) = C.sndToSum (∑' k : ℤ,
      exp ((δ : ℂ) * (1 + (t + k * T : ℝ) * I) ^ 2) • g.2 (t + k * T))) := by
  intro P
  set r : ℝ := Real.exp (-(δ * T ^ 2 / 2))
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  have hdiff : DifferentiableOn ℂ P (verticalStrip 0 1) := fun z₀ hz₀ => by
    set B := |z₀.im| + 1
    let U : Set ℂ := verticalStrip 0 1 ∩ {z : ℂ | |z.im| < B}
    have hUopen : IsOpen U :=
      (isOpen_verticalStrip 0 1).inter
        (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
    have hdU : DifferentiableOn ℂ P U :=
      differentiableOn_tsum_of_summable_norm
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
        (fun k => (by fun_prop : Differentiable ℂ fun z : ℂ =>
            exp ((δ : ℂ) * (z + k * T * I) ^ 2)).differentiableOn.smul
          (hF.diffContOnCl.differentiableOn.comp
            (by fun_prop : Differentiable ℂ fun z : ℂ => z + k * T * I).differentiableOn
            fun _ hz => by simpa using hz.1))
        hUopen fun k z hz => norm_damped_shift_le C hF hδ (by positivity) k
          (verticalStrip_subset_verticalClosedStrip 0 1 hz.1) (le_of_lt hz.2)
    exact (hdU.differentiableAt
      (hUopen.mem_nhds ⟨hz₀, show |z₀.im| < B from lt_add_one _⟩)).differentiableWithinAt
  have hcont : ContinuousOn P (closure (verticalStrip 0 1)) := by
    rw [closure_verticalStrip_zero_one]; intro z₀ hz₀
    set B := |z₀.im| + 1
    have hFc : ContinuousOn F (verticalClosedStrip 0 1) := by
      simpa [closure_verticalStrip_zero_one] using hF.diffContOnCl.continuousOn
    have hcontW : ContinuousOn P (verticalClosedStrip 0 1 ∩ {z : ℂ | |z.im| < B}) :=
      continuousOn_tsum
        (fun k => (by fun_prop : Continuous fun z : ℂ =>
            exp ((δ : ℂ) * (z + k * T * I) ^ 2)).continuousOn.smul
          (hFc.comp (by fun_prop : Continuous fun z : ℂ => z + k * T * I).continuousOn
            fun _ hz => by simpa using hz.1))
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
        fun k _ hz => norm_damped_shift_le C hF hδ (by positivity) k hz.1 (le_of_lt hz.2)
    exact (hcontW z₀ ⟨hz₀, show |z₀.im| < B from lt_add_one _⟩).mono_of_mem_nhdsWithin <|
      inter_mem_nhdsWithin _ <| (isOpen_lt (continuous_abs.comp continuous_im)
        continuous_const).mem_nhds (show |z₀.im| < B from lt_add_one _)
  refine ⟨⟨hdiff, hcont⟩, fun z => ?_, fun t => ?_, fun t => ?_⟩
  · dsimp only [P]; conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    congr 1 with k; simp only [Equiv.coe_addRight]
    rw [show z + T * I + k * T * I = z + ((k + 1 : ℤ) : ℂ) * T * I by push_cast; ring]
  · obtain ⟨-, -, hsum₀⟩ :=
      continuous_and_periodic_periodizeTrace g.1 (a := 0) ⟨le_rfl, zero_le_one⟩ hδ hT
    rw [C.fstToSum.map_tsum (by simpa using hsum₀ t)]; dsimp [P]; congr 1 with k
    rw [show (t : ℂ) * I + k * T * I = ((t + k * T : ℝ) : ℂ) * I by push_cast; ring,
      hF.apply_mul_I, map_smul]
  · obtain ⟨-, -, hsum₁⟩ :=
      continuous_and_periodic_periodizeTrace g.2 (a := 1) ⟨zero_le_one, le_rfl⟩ hδ hT
    rw [C.sndToSum.map_tsum (by simpa using hsum₁ t)]; dsimp [P]; congr 1 with k
    rw [show (1 : ℂ) + t * I + k * T * I = 1 + ((t + k * T : ℝ) : ℂ) * I by push_cast; ring,
      hF.apply_one_add_mul_I, map_smul]

/-- Cauchy–Goursat identity along `[0, 1] × [0, T]` for vertically `T * I`-periodic `P`. -/
private theorem integral_periodic_strip_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : ℝ} (hTpos : 0 < T) (P : ℂ → E) (hP : DiffContOnCl ℂ P (verticalStrip 0 1))
    (hper : ∀ z : ℂ, P (z + T * I) = P z) (m : ℤ) :
    (∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (y * I)) • P (y * I)) =
      (∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (1 + y * I)) • P (1 + y * I)) := by
  set ω : ℂ := -(2 * Real.pi * m / T : ℂ)
  let h : ℂ → E := fun z => exp (ω * z) • P z
  have hexp : Differentiable ℂ fun z : ℂ => exp (ω * z) := by fun_prop
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn h 0
    (1 + T * I)
    (hexp.continuous.continuousOn.smul <| hP.continuousOn.mono fun z ⟨hz₁, _⟩ => by
      rw [closure_verticalStrip_zero_one]; simpa [uIcc_of_le zero_le_one] using hz₁)
    (hexp.differentiableOn.smul <| hP.differentiableOn.mono fun z ⟨hz₁, _⟩ => by
      simpa [hTpos.le] using hz₁)
  simp only [zero_re, zero_im, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, one_im, mul_im, zero_add, ofReal_zero, zero_mul] at hrect
  have htop : (∫ x : ℝ in 0..1, h (x + T * I)) = ∫ x : ℝ in 0..1, h x :=
    intervalIntegral.integral_congr fun x _ => by
      have hωT : ω * (T * I) = ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
        have : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hTpos.ne'; simp only [ω]; push_cast; field_simp
      simp only [h, hper, mul_add, Complex.exp_add, hωT, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [htop, sub_self, zero_add, sub_eq_zero, smul_right_inj I_ne_zero] at hrect
  simpa [h] using hrect.symm

/-- For vertically `T * I`-periodic `P` with continuous `T`-periodic boundary traces `p₀, p₁`, the
Fourier coefficients `(fourierCoeff hp₀_per.lift m, exp (-2 π m / T) • fourierCoeff hp₁_per.lift m)`
belong to `C.inter`. -/
private theorem fourierCoeff_periodic_mem_inter [CompleteSpace X₀] [CompleteSpace X₁]
    {T : ℝ} [hT : Fact (0 < T)] {P : ℂ → C.SumSpace} (hP : DiffContOnCl ℂ P (verticalStrip 0 1))
    (hper : ∀ z : ℂ, P (z + T * I) = P z) {p₀ : ℝ → X₀} {p₁ : ℝ → X₁}
    (hp₀_cont : Continuous p₀) (hp₁_cont : Continuous p₁)
    (hp₀_per : Function.Periodic p₀ T) (hp₁_per : Function.Periodic p₁ T)
    (hP₀ : ∀ t : ℝ, P (t * I) = C.fstToSum (p₀ t))
    (hP₁ : ∀ t : ℝ, P (1 + t * I) = C.sndToSum (p₁ t)) (m : ℤ) :
    (fourierCoeff hp₀_per.lift m,
      exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff hp₁_per.lift m) ∈ C.inter := by
  rw [C.mem_inter_iff, ← C.sumSpaceEmbed_fstToSum, ← C.sumSpaceEmbed_sndToSum]
  congr 1
  rw [fourierCoeff_eq_intervalIntegral _ m 0, fourierCoeff_eq_intervalIntegral _ m 0, zero_add,
    C.fstToSum.map_smul_of_tower, map_smul, C.sndToSum.map_smul_of_tower,
    smul_comm (exp _) (1 / T : ℝ)]
  congr 1
  have hint₀ : IntervalIntegrable (fun y : ℝ => @fourier T (-m) y • hp₀_per.lift y) volume 0 T :=
    ((@fourier T (-m)).continuous.comp continuous_quotient_mk' |>.smul
      (hp₀_cont.congr fun _ => rfl)).intervalIntegrable 0 T
  have hint₁ : IntervalIntegrable (fun y : ℝ => @fourier T (-m) y • hp₁_per.lift y) volume 0 T :=
    ((@fourier T (-m)).continuous.comp continuous_quotient_mk' |>.smul
      (hp₁_cont.congr fun _ => rfl)).intervalIntegrable 0 T
  rw [← C.fstToSum.intervalIntegral_comp_comm hint₀, ← C.sndToSum.intervalIntegral_comp_comm hint₁,
    ← intervalIntegral.integral_smul]
  refine (intervalIntegral.integral_congr fun y _ => ?_).trans
    ((integral_periodic_strip_eq hT.out P hP hper m).trans
      (intervalIntegral.integral_congr fun y _ => ?_))
  · rw [Function.Periodic.lift_coe, map_smul, ← hP₀ y, fourier_coe_apply]; congr 2; push_cast; ring
  · rw [Function.Periodic.lift_coe, map_smul, ← hP₁ y, smul_smul, fourier_coe_apply,
      ← Complex.exp_add]
    congr 2; push_cast; ring

private theorem fourier_sub_apply {T : ℝ} (m : ℤ) (x v : AddCircle T) :
    fourier m (x - v) = fourier m x * fourier (-m) v := by
  rw [fourier_apply, zsmul_sub, sub_eq_add_neg, toCircle_add, Circle.coe_mul, ← fourier_apply,
    ← neg_zsmul, ← fourier_apply]

private theorem conv_fourier_eq {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (m : ℤ) (f : AddCircle T → E) (t : ℝ) :
    ∫ u : AddCircle T, fourier m u • f ((t : AddCircle T) - u) ∂haarAddCircle =
      fourier m (t : AddCircle T) • fourierCoeff f m := by
  let x : AddCircle T := t
  have hsub : (∫ u : AddCircle T, fourier m u • f (x - u) ∂haarAddCircle) =
      ∫ v : AddCircle T, fourier m (x - v) • f v ∂haarAddCircle := by
    simpa [sub_eq_add_neg] using
      integral_sub_left_eq_self (fun v : AddCircle T => fourier m (x - v) • f v) haarAddCircle x
  rw [hsub]; simp_rw [fourier_sub_apply, mul_smul, integral_smul]; rfl

private theorem integrable_smul_sub_haarAddCircle {T : ℝ} [Fact (0 < T)] {E : Type*}
    [NormedAddCommGroup E] [SMul ℂ E] [ContinuousSMul ℂ E] (R : C(AddCircle T, ℂ))
    {f : AddCircle T → E} (hf : Continuous f) (x : AddCircle T) :
    Integrable (fun u : AddCircle T => R u • f (x - u)) haarAddCircle :=
  (R.continuous.smul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    (.of_compactSpace _)

private theorem conv_approx_single {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : AddCircle T → E) (hf : Continuous f) {η M ε : ℝ}
    (hM : 0 < M) (hfb : ∀ x, ‖f x‖ ≤ M)
    (huc : ∀ a b, dist a b < η → dist (f a) (f b) < ε / 2)
    {K Q : C(AddCircle T, ℂ)} (hK_int : ∫ u : AddCircle T, K u ∂haarAddCircle = 1)
    (hK_norm : ∫ u : AddCircle T, ‖K u‖ ∂haarAddCircle = 1)
    (hK_supp : ∀ u : AddCircle T, η ≤ ‖u‖ → K u = 0)
    (hQK : ‖Q - K‖ < ε / (2 * M)) (x : AddCircle T) :
    ‖(∫ u : AddCircle T, Q u • f (x - u) ∂haarAddCircle) - f x‖ < ε := by
  have hintQ := integrable_smul_sub_haarAddCircle Q hf x
  have hintK := integrable_smul_sub_haarAddCircle K hf x
  have hintKx : Integrable (fun u : AddCircle T => K u • f x) haarAddCircle :=
    (K.continuous.smul continuous_const).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hconvK : ‖(∫ u : AddCircle T, K u • f (x - u) ∂haarAddCircle) - f x‖ ≤ ε / 2 := by
    conv_lhs => rw [show f x = ∫ u : AddCircle T, K u • f x ∂haarAddCircle by
      rw [integral_smul_const, hK_int, one_smul], ← integral_sub hintK hintKx]
    refine (norm_integral_le_integral_norm _).trans <|
      (integral_mono (hintK.sub hintKx).norm
        ((K.continuous.norm.mul_const (ε / 2)).integrable_of_hasCompactSupport (.of_compactSpace _))
        fun u => ?_).trans_eq (by rw [integral_mul_const, hK_norm, one_mul])
    simp only [Pi.sub_apply, ← smul_sub, norm_smul]
    by_cases hu : ‖u‖ < η
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← dist_eq_norm]
      exact (huc _ _ (by rwa [dist_eq_norm, sub_right_comm, sub_self, zero_sub, norm_neg])).le
    · simp [hK_supp u (not_lt.1 hu)]
  have hdiff : ‖(∫ u : AddCircle T, Q u • f (x - u) ∂haarAddCircle) -
      (∫ u : AddCircle T, K u • f (x - u) ∂haarAddCircle)‖ < ε / 2 := by
    rw [← integral_sub hintQ hintK]
    refine (norm_integral_le_of_norm_le_const (C := ‖Q - K‖ * M) (ae_of_all _ fun u => ?_)).trans_lt
      ?_
    · rw [← sub_smul, norm_smul]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm (Q - K) u) (hfb (x - u))
        (norm_nonneg _) (norm_nonneg _)
    · rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
      exact (mul_lt_mul_of_pos_right hQK hM).trans_eq (by field_simp)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (by linarith)

/-- Simultaneous uniform convolution approximation of two continuous maps on `AddCircle T` by a
single scalar trigonometric polynomial. -/
private theorem exists_fourier_span_conv_approx {T : ℝ} [Fact (0 < T)]
    [CompleteSpace X₀] [CompleteSpace X₁]
    (f₀ : AddCircle T → X₀) (f₁ : AddCircle T → X₁)
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q ∈ Submodule.span ℂ (Set.range (@fourier T)),
      (∀ x : AddCircle T, ‖(∫ u : AddCircle T, Q u • f₀ (x - u) ∂haarAddCircle) - f₀ x‖ < ε) ∧
      (∀ x : AddCircle T, ‖(∫ u : AddCircle T, Q u • f₁ (x - u) ∂haarAddCircle) - f₁ x‖ < ε) := by
  obtain ⟨η₀, hη₀, huc₀⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hf₀) (ε / 2) (half_pos hε)
  obtain ⟨η₁, hη₁, huc₁⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hf₁) (ε / 2) (half_pos hε)
  set η := min η₀ η₁
  have hη : 0 < η := lt_min hη₀ hη₁
  let tent : AddCircle T → ℝ := fun u => max 0 (1 - ‖u‖ / η)
  have htent_cont : Continuous tent := by fun_prop
  have htent_nonneg (u : AddCircle T) : 0 ≤ tent u := le_max_left _ _
  have htent_pos : 0 < ∫ u : AddCircle T, tent u ∂haarAddCircle :=
    integral_pos_of_integrable_nonneg_ne_zero htent_cont
      (htent_cont.integrable_of_hasCompactSupport (.of_compactSpace _)) htent_nonneg
      (by simp [tent] : tent 0 ≠ 0)
  let c : ℝ := ∫ u : AddCircle T, tent u ∂haarAddCircle
  let K : C(AddCircle T, ℂ) := ⟨fun u => ((c⁻¹ * tent u : ℝ) : ℂ), by fun_prop⟩
  have hK_int : ∫ u : AddCircle T, K u ∂haarAddCircle = 1 := by
    rw [show (fun u : AddCircle T => K u) = fun u => ((c⁻¹ : ℝ) : ℂ) * (tent u : ℂ) by
      ext u; simp [K], integral_const_mul, integral_complex_ofReal, ← ofReal_mul,
      inv_mul_cancel₀ htent_pos.ne', Complex.ofReal_one]
  have hK_norm : ∫ u : AddCircle T, ‖K u‖ ∂haarAddCircle = 1 := by
    have hnorm (u : AddCircle T) : ‖K u‖ = c⁻¹ * tent u := by
      dsimp [K]
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 htent_pos.le)
        (htent_nonneg u))]
    simp_rw [hnorm]; rw [integral_const_mul, inv_mul_cancel₀ htent_pos.ne']
  have hK_supp (u : AddCircle T) (hu : η ≤ ‖u‖) : K u = 0 := by
    simp [K, tent, max_eq_left (sub_nonpos.2 ((one_le_div hη).2 hu))]
  obtain ⟨M₀, hM₀pos, hM₀⟩ := (isCompact_univ.image hf₀).isBounded.exists_pos_norm_le
  obtain ⟨M₁, _, hM₁⟩ := (isCompact_univ.image hf₁).isBounded.exists_pos_norm_le
  set M := max M₀ M₁
  have hM : 0 < M := lt_of_lt_of_le hM₀pos (le_max_left _ _)
  have hdense : K ∈ (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  obtain ⟨Q, hQmem, hQK⟩ :=
    Metric.mem_closure_iff.1 hdense (ε / (2 * M)) (div_pos hε (by positivity))
  rw [dist_comm, dist_eq_norm] at hQK
  exact ⟨Q, hQmem,
    conv_approx_single f₀ hf₀ hM
      (fun _ => (hM₀ _ (mem_image_of_mem _ (mem_univ _))).trans (le_max_left _ _))
      (fun _ _ h => huc₀ (h.trans_le (min_le_left _ _))) hK_int hK_norm hK_supp hQK,
    conv_approx_single f₁ hf₁ hM
      (fun _ => (hM₁ _ (mem_image_of_mem _ (mem_univ _))).trans (le_max_right _ _))
      (fun _ _ h => huc₁ (h.trans_le (min_le_right _ _))) hK_int hK_norm hK_supp hQK⟩

/-- Damping the convolution of `(f₀, f₁)` against `Q ∈ span (range fourier)` produces an element of
`C.elementaryStripTraces` whenever the paired Fourier modes lie in `C.inter`. -/
private theorem exists_elementary_of_mem_span_fourier {T δ : ℝ} [hT : Fact (0 < T)] (hδ : 0 < δ)
    {f₀ : AddCircle T → X₀} {f₁ : AddCircle T → X₁} (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (hmem : ∀ m : ℤ,
      (fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m) ∈ C.inter)
    {Q : C(AddCircle T, ℂ)} (hQ : Q ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    ∃ h ∈ C.elementaryStripTraces,
      (∀ t : ℝ, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
        exp ((δ : ℂ) * (t * I) ^ 2) •
          ∫ u : AddCircle T, Q u • f₀ ((t : AddCircle T) - u) ∂haarAddCircle) ∧
      (∀ t : ℝ, (h : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
        exp ((δ : ℂ) * (1 + t * I) ^ 2) •
          ∫ u : AddCircle T, Q u • f₁ ((t : AddCircle T) - u) ∂haarAddCircle) := by
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
  refine Submodule.span_induction ?_
    ⟨0, C.elementaryStripTraces.zero_mem, fun _ => by simp, fun _ => by simp⟩ ?_ ?_ hQ
  · rintro _ ⟨m, rfl⟩
    let xm : C.inter :=
      ⟨(fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m), hmem m⟩
    refine ⟨C.expGaussianTrace hδ (2 * Real.pi * m / T) xm,
      C.expGaussianTrace_mem_elementaryStripTraces hδ _ xm, fun t => ?_, fun t => ?_⟩
    · rw [expGaussianTrace_apply_fst, C.interFst_apply, conv_fourier_eq, fourier_coe_apply,
        smul_smul, ← Complex.exp_add]; dsimp [xm]; congr 2; push_cast; ring
    · rw [expGaussianTrace_apply_snd, C.interSnd_apply, conv_fourier_eq, fourier_coe_apply]
      dsimp [xm]; rw [smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; field_simp; ring
  · rintro Q₁ Q₂ - - ⟨h₁, hh₁, h₁₀, h₁₁⟩ ⟨h₂, hh₂, h₂₀, h₂₁⟩
    refine ⟨h₁ + h₂, C.elementaryStripTraces.add_mem hh₁ hh₂, fun t => ?_, fun t => ?_⟩
    · simp only [Submodule.coe_add, Prod.fst_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₀ t, h₂₀ t, ← smul_add, ← integral_add (integrable_smul_sub_haarAddCircle Q₁ hf₀ t)
        (integrable_smul_sub_haarAddCircle Q₂ hf₀ t)]
      simp_rw [ContinuousMap.add_apply, add_smul]
    · simp only [Submodule.coe_add, Prod.snd_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₁ t, h₂₁ t, ← smul_add, ← integral_add (integrable_smul_sub_haarAddCircle Q₁ hf₁ t)
        (integrable_smul_sub_haarAddCircle Q₂ hf₁ t)]
      simp_rw [ContinuousMap.add_apply, add_smul]
  · rintro c Q₁ - ⟨h₁, hh₁, h₁₀, h₁₁⟩
    refine ⟨c • h₁, C.elementaryStripTraces.smul_mem c hh₁, fun t => ?_, fun t => ?_⟩
    · simp only [SetLike.val_smul, Prod.smul_fst, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₀ t, smul_comm c]; simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]
    · simp only [SetLike.val_smul, Prod.smul_snd, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₁ t, smul_comm c]; simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]

/-- Choosing `T` large enough makes the `k ≠ 0` tail of the doubly damped vertical periodization
strictly smaller than `ε`. -/
private theorem exists_period_tail_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (g : C.stripTraces) :
    ∃ T > 0,
      let r := Real.exp (-(δ * T ^ 2 / 2))
      r < 1 ∧ Real.exp (2 * δ) * ‖g‖ * (2 * (r * (1 - r)⁻¹)) < ε := by
  have hq : Tendsto (fun T : ℝ => -(δ * T ^ 2 / 2)) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (half_pos hδ))).congr fun _ => by dsimp; ring
  have hr : Tendsto (fun T : ℝ => Real.exp (-(δ * T ^ 2 / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hq
  have hlim : Tendsto (fun T : ℝ => Real.exp (2 * δ) * ‖g‖ *
      (2 * (Real.exp (-(δ * T ^ 2 / 2)) * (1 - Real.exp (-(δ * T ^ 2 / 2)))⁻¹))) atTop (𝓝 0) := by
    simpa using (((hr.mul ((tendsto_const_nhds.sub hr).inv₀ (by norm_num))).const_mul 2).const_mul
      (Real.exp (2 * δ) * ‖g‖))
  obtain ⟨T, hT, hr₁, hlt⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((hr.eventually (gt_mem_nhds zero_lt_one)).and (hlim.eventually (gt_mem_nhds hε)))).exists
  exact ⟨T, hT, hr₁, hlt⟩

/-- Pointwise three-step error bound (convolution + periodization tail + Gaussian damping) along
either boundary line `re z = a` (`a ∈ [0, 1]`). -/
private theorem norm_damped_conv_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : ℝ} [Fact (0 < T)] {a δ M ε : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ)
    (f : C₀(ℝ, E)) (hfM : ‖f‖ ≤ M)
    (hp_per : Function.Periodic (fun t : ℝ => ∑' k : ℤ,
      exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) T)
    (hsum : ∀ t : ℝ, Summable fun k : ℤ =>
      exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))
    (Q : C(AddCircle T, ℂ))
    (hQ : ∀ x : AddCircle T,
      ‖(∫ u : AddCircle T, Q u • hp_per.lift (x - u) ∂haarAddCircle) - hp_per.lift x‖ <
        (ε / 3) / Real.exp δ)
    (hr₁ : Real.exp (-(δ * T ^ 2 / 2)) < 1)
    (htail : Real.exp (2 * δ) * M *
      (2 * (Real.exp (-(δ * T ^ 2 / 2)) * (1 - Real.exp (-(δ * T ^ 2 / 2)))⁻¹)) < ε / 3)
    {t : ℝ} (hdamp : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t‖ ≤ ε / 4) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (∫ u : AddCircle T, Q u • hp_per.lift ((t : AddCircle T) - u) ∂haarAddCircle) - f t‖ ≤
      ε / 3 + ε / 3 + ε / 4 := by
  set r := Real.exp (-(δ * T ^ 2 / 2))
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  let d : E := exp ((δ : ℂ) * (a + t * I) ^ 2) • hp_per.lift t
  let m : E := exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t
  have hconv_err : ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (∫ u : AddCircle T, Q u • hp_per.lift ((t : AddCircle T) - u) ∂haarAddCircle) - d‖ ≤
        ε / 3 := by
    dsimp [d]; rw [← smul_sub, norm_smul, Complex.norm_exp]
    have hexp_le : Real.exp (((δ : ℂ) * (a + t * I) ^ 2).re) ≤ Real.exp δ := by
      refine Real.exp_le_exp.2 ?_
      rw [show ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) by simp [sq]]
      have : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
      nlinarith [sq_nonneg t]
    exact (mul_le_mul hexp_le (hQ t).le (norm_nonneg _) (Real.exp_pos δ).le).trans_eq
      (mul_div_cancel₀ _ (Real.exp_pos δ).ne')
  have htail_err : ‖d - m‖ ≤ ε / 3 := by
    have : 0 ≤ M := (norm_nonneg f).trans hfM
    let hcL : E →L[ℂ] E := ContinuousLinearMap.lsmul ℂ ℂ (exp ((δ : ℂ) * (a + t * I) ^ 2))
    have hd_sum : d = ∑' k : ℤ, exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) := by
      simpa only [d, Function.Periodic.lift_coe, hcL, ContinuousLinearMap.lsmul_apply] using
        hcL.map_tsum (hsum t)
    have hsmul_sum : Summable fun k : ℤ => exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) := by
      simpa only [Function.comp_def, hcL, ContinuousLinearMap.lsmul_apply] using
        (hsum t).mapL hcL
    have hk0 : exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + (0 : ℤ) * T : ℝ) * I) ^ 2) • f (t + (0 : ℤ) * T)) = m := by
      simp [m, smul_smul, ← Complex.exp_add, two_mul, add_mul]
    rw [hd_sum, hsmul_sum.tsum_eq_add_tsum_ite 0, hk0, add_sub_cancel_left]
    have hite_bound (k : ℤ) : ‖if k = 0 then (0 : E) else exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
        Real.exp (2 * δ) * M * (if k = 0 then 0 else r ^ k.natAbs) := by
      split_ifs
      · simp
      · exact (norm_double_damped_shift_le f ha hδ k t).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfM (by positivity))
            (by positivity))
    have hsum_ite : Summable fun k : ℤ =>
        Real.exp (2 * δ) * M * (if k = 0 then (0 : ℝ) else r ^ k.natAbs) :=
      (Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
        (fun _ => by split_ifs <;> [positivity; exact le_rfl])
        (summable_pow_natAbs hr₀ hr₁)).mul_left _
    have hsum_norm := hsum_ite.of_nonneg_of_le (fun _ => norm_nonneg _) hite_bound
    refine (norm_tsum_le_tsum_norm hsum_norm).trans
      ((Summable.tsum_le_tsum hite_bound hsum_norm hsum_ite).trans ?_)
    rw [tsum_mul_left, tsum_pow_natAbs_ite_eq hr₀ hr₁]; exact htail.le
  linarith [norm_sub_le_norm_sub_add_norm_sub (exp ((δ : ℂ) * (a + t * I) ^ 2) •
    (∫ u : AddCircle T, Q u • hp_per.lift ((t : AddCircle T) - u) ∂haarAddCircle)) d (f t),
    norm_sub_le_norm_sub_add_norm_sub d m (f t)]

/-- **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** When `X₀` and `X₁` are Banach
spaces, the `ℂ`-linear span of the elementary intersection-valued functions
`z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω ∈ ℝ`, `x ∈ X₀ ∩ X₁`) is dense in `C.stripTraces`. -/
theorem dense_elementaryStripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    Dense (C.elementaryStripTraces : Set C.stripTraces) := by
  refine Metric.dense_iff.2 fun g ε hε => ?_
  set g₀ : C₀(ℝ, X₀) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
  set g₁ : C₀(ℝ, X₁) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  obtain ⟨δ₀, hδ₀, hdamp₀⟩ := exists_gaussian_smul_approx_single 0 g₀ (by positivity : 0 < ε / 4)
  obtain ⟨δ₁, hδ₁, hdamp₁⟩ := exists_gaussian_smul_approx_single 1 g₁ (by positivity : 0 < ε / 4)
  set δ := min δ₀ δ₁ / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₀ hδ₁)
  obtain ⟨T, hTpos, hr₁, htail⟩ := exists_period_tail_lt C hδ (by positivity : 0 < ε / 3) g
  have : Fact (0 < T) := ⟨hTpos⟩
  obtain ⟨hp₀_cont, hp₀_per, hsum₀⟩ :=
    continuous_and_periodic_periodizeTrace g₀ (a := 0) ⟨le_rfl, zero_le_one⟩ hδ hTpos
  obtain ⟨hp₁_cont, hp₁_per, hsum₁⟩ :=
    continuous_and_periodic_periodizeTrace g₁ (a := 1) ⟨zero_le_one, le_rfl⟩ hδ hTpos
  obtain ⟨hP_diff, hP_per, hP₀, hP₁⟩ :=
    diffContOnCl_and_periodic_periodizeStrip C (C.isStripFunction_stripFunction g) hδ hTpos
  have hf₀ : Continuous hp₀_per.lift := continuous_coinduced_dom.2 hp₀_cont
  have hf₁ : Continuous hp₁_per.lift := continuous_coinduced_dom.2 hp₁_cont
  obtain ⟨Q, hQspan, hQ₀, hQ₁⟩ := exists_fourier_span_conv_approx hp₀_per.lift hp₁_per.lift hf₀ hf₁
    (div_pos (by positivity : 0 < ε / 3) (Real.exp_pos δ))
  obtain ⟨h, hhmem, hh₀, hh₁⟩ := exists_elementary_of_mem_span_fourier C hδ hf₀ hf₁
    (fourierCoeff_periodic_mem_inter C hP_diff hP_per hp₀_cont hp₁_cont hp₀_per hp₁_per
      (by simpa [zero_add] using hP₀) hP₁) hQspan
  refine ⟨h, ?_, hhmem⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
  refine lt_of_le_of_lt (norm_prod_le_iff.2 ⟨?_, ?_⟩) (by linarith : ε / 3 + ε / 3 + ε / 4 < ε)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.fst_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₀ t]
    simpa [zero_add] using norm_damped_conv_sub_le ⟨le_rfl, zero_le_one⟩ hδ g₀
      (norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))) hp₀_per hsum₀ Q hQ₀ hr₁ htail
      (hdamp₀ hδ ((half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_left _ _)) t)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.snd_sub, FunLike.coe_sub, Pi.sub_apply]; rw [norm_sub_rev, hh₁ t]
    simpa using norm_damped_conv_sub_le ⟨zero_le_one, le_rfl⟩ hδ g₁
      (norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))) hp₁_per hsum₁ Q hQ₁ hr₁ htail
      (hdamp₁ hδ ((half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_right _ _)) t)

end ElementaryTraces

namespace ComplexMethodSpace

variable {C}

/-- **Density of the intersection (Bergh–Löfström, Theorem 4.2.2 (a)).** When `X₀` and `X₁` are
Banach spaces, `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` for every `θ : ℝ`. -/
theorem denseRange_ofInter [CompleteSpace X₀] [CompleteSpace X₁] (θ : ℝ) :
    DenseRange (ofInter (C := C) θ) := by
  by_cases hθ : θ ∈ Icc 0 1
  · have himg : mk (C := C) θ '' (C.elementaryStripTraces : Set C.stripTraces) ⊆
        Set.range (ofInter (C := C) θ) := by
      rintro _ ⟨g, hg, rfl⟩
      -- Express range membership in terms of the underlying submodule to induct on `span`.
      change mk θ g ∈ LinearMap.range (ofInter (C := C) θ).toLinearMap
      refine Submodule.span_induction ?_ (by rw [map_zero]; exact Submodule.zero_mem _)
        (fun _ _ _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c _ _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hg
      rintro _ ⟨δ, hδ, ω, x, rfl⟩
      refine ⟨exp ((δ : ℂ) * (θ : ℂ) ^ 2 + (ω : ℂ) * (θ : ℂ)) • x, ?_⟩
      ext
      rw [ContinuousLinearMap.coe_coe, toSum_ofInter hθ, map_smul, map_smul, toSum_mk,
        stripEval_expGaussianTrace C hδ ω x (by simpa using hθ)]
    exact (mk_surjective.denseRange.dense_image (mk (C := C) θ).continuous
      C.dense_elementaryStripTraces).mono himg
  · exact Function.Surjective.denseRange fun u => ⟨0, by simp [eq_zero_of_notMem hθ u]⟩

end ComplexMethodSpace

end TauCeti.CompatibleCouple
