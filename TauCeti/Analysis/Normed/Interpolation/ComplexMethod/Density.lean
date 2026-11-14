/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Regular
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Bounded boundary traces, intersection density, and regularization in the complex method

Calderón's complex interpolation space `[X₀, X₁]_θ` is defined in
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic` using admissible functions on the closed
strip `0 ≤ re z ≤ 1` whose boundary traces lie in `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. This file establishes
the density and structural results of Bergh–Löfström §4.2:

1. **Bounded-boundary formulation (Bergh–Löfström, Lemma 4.2.1).** Dropping the condition that the
   boundary traces vanish at infinity yields `CompatibleCouple.IsBoundedStripFunction`, with traces
   in `(ℝ →ᵇ X₀) × (ℝ →ᵇ X₁)`. Damping by `exp (δ (z - θ)²)` and letting `δ → 0⁺` shows that
   bounded-boundary strip functions define the exact same space `[X₀, X₁]_θ` and the exact same
   quotient norm (`ComplexMethodSpace.exists_toSum_eq_iff_isBoundedStripFunction`,
   `ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction`), without completeness hypotheses.

2. **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** When `X₀` and `X₁` are Banach spaces,
   the `ℂ`-linear span `CompatibleCouple.elementaryStripTraces` of the scalar-multiplied
   intersection-valued functions `z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω ∈ ℝ`, `x ∈ X₀ ∩ X₁`) is
   dense in `CompatibleCouple.stripTraces` (`CompatibleCouple.dense_elementaryStripTraces`). The
   proof damps an admissible function by `exp (2 δ z²)`, periodizes `exp (δ z²) F z` vertically by
   `T * I`, identifies the Fourier coefficients of its two periodic boundary traces inside `X₀ ∩ X₁`
   via Cauchy's rectangle theorem, and approximates both traces simultaneously by convolving on
   `AddCircle T` with a scalar trigonometric polynomial.

3. **Intersection density and endpoint closures (Bergh–Löfström, Theorem 4.2.2 (a)–(b)).** When
   `X₀` and `X₁` are complete, `X₀ ∩ X₁` is dense in `[X₀, X₁]_θ` for every `θ : ℝ`
   (`ComplexMethodSpace.denseRange_ofInter`), every admissible trace takes values in the endpoint
   closures `(X₀°, X₁°) = (C.fstClosure, C.sndClosure)`, and the contractive endpoint inclusions
   `ComplexMethodSpace.toFst : [X₀, X₁]_0 →L[ℂ] X₀` and
   `ComplexMethodSpace.toSnd : [X₀, X₁]_1 →L[ℂ] X₁` map into `X₀°` and `X₁°`.

4. **Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)).** When `X₀` and `X₁` are
   complete, inclusion of `(X₀°, X₁°)` into `(X₀, X₁)` induces surjective linear isometries
   `CompatibleCouple.regularizeStripTracesEquiv : C.regularize.stripTraces ≃ₗᵢ[ℂ] C.stripTraces`
   and `ComplexMethodSpace.regularizeEquiv : [X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`, reducing complex
   interpolation of arbitrary Banach couples to regular couples (in particular enabling duality via
   `CompatibleCouple.dual`).

## Main declarations

* `TauCeti.CompatibleCouple.IsBoundedStripFunction`: strip functions with bounded continuous traces.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction`:
  equality of the bounded-boundary and vanishing-boundary norms on `[X₀, X₁]_θ`.
* `TauCeti.CompatibleCouple.expGaussianTrace`, `TauCeti.CompatibleCouple.elementaryStripTraces`,
  `TauCeti.CompatibleCouple.dense_elementaryStripTraces`: Calderón's density lemma in `stripTraces`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.denseRange_ofInter`: density of `X₀ ∩ X₁` in
  `[X₀, X₁]_θ`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.toFst`,
  `TauCeti.CompatibleCouple.ComplexMethodSpace.toSnd`: contractive endpoint maps at `θ = 0, 1`.
* `TauCeti.CompatibleCouple.regularizeStripTracesEquiv`,
  `TauCeti.CompatibleCouple.ComplexMethodSpace.regularizeEquiv`: isometric invariance under
  passing to `(X₀°, X₁°)`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§3–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.2 (Lemma 4.2.1, Theorem 4.2.2, Lemma 4.2.3).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Set Topology AddCircle
open scoped ZeroAtInfty BoundedContinuousFunction

namespace TauCeti.CompatibleCouple

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
    obtain ⟨M, hM⟩ := hF.exists_norm_le
    exact ⟨M, by rintro _ ⟨w, hw, rfl⟩; exact hM w hw⟩
  refine norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hF.diffContOnCl hB
    (fun w hw => ?_) (fun w hw => ?_)
  · rw [← re_add_im w, hw, ofReal_zero, zero_add, hF.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (g.1.norm_coe_le_norm _)
  · rw [← re_add_im w, hw, ofReal_one, hF.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (g.2.norm_coe_le_norm _)

/-- **Maximum principle** for bounded-boundary strip functions. -/
theorem norm_le (hF : C.IsBoundedStripFunction F g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F z‖ ≤ ‖g‖ := by
  refine (hF.norm_le_rpow_mul_rpow hz).trans ?_
  calc ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re ≤ ‖g‖ ^ (1 - z.re) * ‖g‖ ^ z.re := by
        gcongr
        · exact sub_nonneg.2 hz.2
        · exact norm_fst_le g
        · exact hz.1
        · exact norm_snd_le g
    _ = ‖g‖ := by
        rw [← Real.rpow_add' (norm_nonneg g) (by simp), sub_add_cancel, Real.rpow_one]

private theorem norm_exp_sub_sq (δ θ : ℝ) (z : ℂ) :
    ‖exp ((δ : ℂ) * (z - θ) ^ 2)‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq]

private theorem norm_exp_sub_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ} (hz : z.re ∈ Icc 0 1) :
    ‖exp ((δ : ℂ) * (z - θ) ^ 2)‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_exp_sub_sq]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

private theorem tendsto_norm_exp_sub_sq {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) :
    Tendsto (fun t : ℝ => ‖exp ((δ : ℂ) * (a + t * I - θ) ^ 2)‖) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have h : Tendsto (fun t : ℝ => δ * ((a - θ) ^ 2 - t ^ 2)) (cocompact ℝ) atBot :=
    ((tendsto_atBot_add_const_left _ ((a - θ) ^ 2)
      (tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot hδ).congr fun t => by
        simp [sub_eq_add_neg]
  have heq : (fun t : ℝ => ‖exp ((δ : ℂ) * (a + t * I - θ) ^ 2)‖) =
      Real.exp ∘ fun t => δ * ((a - θ) ^ 2 - t ^ 2) := by
    funext t
    simp [norm_exp_sub_sq]
  rw [heq]
  exact Real.tendsto_exp_atBot.comp h

/-- Damping a bounded-boundary strip function by `exp (δ (z - θ)²)` (`δ > 0`) yields an admissible
strip function with `C₀` boundary traces of norm at most `exp (δ (|θ| + 1)²) ‖g‖`. -/
theorem exists_isStripFunction_gaussianDamp (hF : C.IsBoundedStripFunction F g) {δ : ℝ}
    (hδ : 0 < δ) (θ : ℝ) :
    ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁),
      C.IsStripFunction (fun z => exp ((δ : ℂ) * (z - θ) ^ 2) • F z) g' ∧
        ‖g'‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖g‖ := by
  have hc : Differentiable ℂ (fun z : ℂ => exp ((δ : ℂ) * (z - θ) ^ 2)) := by fun_prop
  let g₀ : C₀(ℝ, X₀) :=
    ⟨⟨fun t => exp ((δ : ℂ) * (t * I - θ) ^ 2) • g.1 t,
      (hc.continuous.comp (by fun_prop)).smul g.1.continuous⟩,
      squeeze_zero_norm
        (fun t => (norm_smul _ _).trans_le
          (mul_le_mul_of_nonneg_left (g.1.norm_coe_le_norm t) (norm_nonneg _)))
        (by simpa using (tendsto_norm_exp_sub_sq hδ θ 0).mul_const ‖g.1‖)⟩
  let g₁ : C₀(ℝ, X₁) :=
    ⟨⟨fun t => exp ((δ : ℂ) * (1 + t * I - θ) ^ 2) • g.2 t,
      (hc.continuous.comp (by fun_prop)).smul g.2.continuous⟩,
      squeeze_zero_norm
        (fun t => (norm_smul _ _).trans_le
          (mul_le_mul_of_nonneg_left (g.2.norm_coe_le_norm t) (norm_nonneg _)))
        (by simpa using (tendsto_norm_exp_sub_sq hδ θ 1).mul_const ‖g.2‖)⟩
  refine ⟨(g₀, g₁), ⟨hc.diffContOnCl.smul hF.diffContOnCl, ?_,
    fun t => by simp [g₀, hF.apply_mul_I], fun t => by simp [g₁, hF.apply_one_add_mul_I]⟩, ?_⟩
  · obtain ⟨M, hM⟩ := hF.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ * (|θ| + 1) ^ 2) * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul (norm_exp_sub_sq_le hδ.le θ hz) (hM z hz) (norm_nonneg _) (by positivity)
  · refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_,
      (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_⟩
    · refine (norm_smul _ _).trans_le
        (mul_le_mul (norm_exp_sub_sq_le hδ.le θ (z := t * I) (by simp))
          ((g.1.norm_coe_le_norm t).trans (norm_fst_le g)) (norm_nonneg _) (by positivity))
    · refine (norm_smul _ _).trans_le
        (mul_le_mul (norm_exp_sub_sq_le hδ.le θ (z := 1 + t * I) (by simp))
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
  constructor
  · rintro ⟨F, g, hF, rfl⟩
    exact ⟨F, (g.1.toBCF, g.2.toBCF), hF.isBoundedStripFunction, rfl⟩
  · rintro ⟨F, g, hF, rfl⟩
    obtain ⟨g', hg', -⟩ := hF.exists_isStripFunction_gaussianDamp one_pos θ
    exact ⟨_, g', hg', by simp⟩

/-- **Bergh–Löfström, Lemma 4.2.1.** For `0 ≤ θ ≤ 1`, the quotient norm on `[X₀, X₁]_θ` coincides
with the infimum over bounded-boundary strip functions. -/
theorem norm_lt_iff_exists_isBoundedStripFunction (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {r : ℝ} :
    ‖u‖ < r ↔ ∃ F g, C.IsBoundedStripFunction F g ∧ toSum u = F θ ∧ ‖g‖ < r := by
  constructor
  · intro hr
    obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
    refine ⟨C.stripFunction g, ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.toBCF,
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.toBCF),
      (C.isStripFunction_stripFunction g).isBoundedStripFunction,
      by rw [toSum_mk, stripEval_apply], ?_⟩
    simpa [Prod.norm_def, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using hg
  · rintro ⟨F, g, hF, hu, hg⟩
    exact (norm_le_of_isBoundedStripFunction hθ hF hu).trans_lt hg

end ComplexMethodSpace

/-! ### Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3) -/

section ElementaryTraces

private def expGaussianScalar (δ ω : ℝ) (z : ℂ) : ℂ :=
  exp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z)

private theorem differentiable_expGaussianScalar (δ ω : ℝ) :
    Differentiable ℂ (expGaussianScalar δ ω) := by
  unfold expGaussianScalar
  fun_prop

private theorem norm_expGaussianScalar (δ ω : ℝ) (z : ℂ) :
    ‖expGaussianScalar δ ω z‖ = Real.exp (δ * (z.re ^ 2 - z.im ^ 2) + ω * z.re) := by
  rw [expGaussianScalar, Complex.norm_exp]
  congr 1
  simp [sq]

private theorem norm_expGaussianScalar_le {δ : ℝ} (hδ : 0 ≤ δ) (ω : ℝ) {z : ℂ}
    (hz : z.re ∈ Icc 0 1) :
    ‖expGaussianScalar δ ω z‖ ≤ Real.exp (δ + |ω|) := by
  rw [norm_expGaussianScalar]
  refine Real.exp_le_exp.2 ?_
  have hre : z.re ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hω : ω * z.re ≤ |ω| := by
    nlinarith [hz.1, hz.2, le_abs_self ω, neg_abs_le ω, abs_nonneg ω]
  nlinarith [sq_nonneg z.im]

private theorem tendsto_norm_expGaussianScalar {δ : ℝ} (hδ : 0 < δ) (ω a : ℝ) :
    Tendsto (fun t : ℝ => ‖expGaussianScalar δ ω (a + t * I)‖) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have hlin : Tendsto (fun t : ℝ => δ * (a ^ 2 - t ^ 2) + ω * a) (cocompact ℝ) atBot := by
    refine tendsto_atBot_add_const_right _ (ω * a) ?_
    exact ((tendsto_atBot_add_const_left _ (a ^ 2)
      (tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot hδ).congr fun t => by
        simp [sub_eq_add_neg]
  have heq : (fun t : ℝ => ‖expGaussianScalar δ ω (a + t * I)‖) =
      Real.exp ∘ fun t => δ * (a ^ 2 - t ^ 2) + ω * a := by
    funext t
    simp [norm_expGaussianScalar]
  rw [heq]
  exact Real.tendsto_exp_atBot.comp hlin

private def expGaussianTracePair {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C₀(ℝ, X₀) × C₀(ℝ, X₁) :=
  (⟨⟨fun t => expGaussianScalar δ ω (t * I) • C.interFst x,
      ((differentiable_expGaussianScalar δ ω).continuous.comp (by fun_prop)).smul continuous_const⟩,
      squeeze_zero_norm (fun t => (norm_smul _ _).le)
        (by simpa using (tendsto_norm_expGaussianScalar hδ ω 0).mul_const ‖C.interFst x‖)⟩,
    ⟨⟨fun t => expGaussianScalar δ ω (1 + t * I) • C.interSnd x,
      ((differentiable_expGaussianScalar δ ω).continuous.comp (by fun_prop)).smul continuous_const⟩,
      squeeze_zero_norm (fun t => (norm_smul _ _).le)
        (by simpa using (tendsto_norm_expGaussianScalar hδ ω 1).mul_const ‖C.interSnd x‖)⟩)

private theorem isStripFunction_expGaussian {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C.IsStripFunction (fun z => expGaussianScalar δ ω z • C.fstToSum (C.interFst x))
      (C.expGaussianTracePair hδ ω x) where
  diffContOnCl := ((differentiable_expGaussianScalar δ ω).smul_const _).diffContOnCl
  isBounded := by
    refine isBounded_iff_forall_norm_le.2
      ⟨Real.exp (δ + |ω|) * ‖C.fstToSum (C.interFst x)‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_expGaussianScalar_le hδ.le ω hz) (norm_nonneg _)
  apply_mul_I t := by simp [expGaussianTracePair]
  apply_one_add_mul_I t := by
    simpa [expGaussianTracePair] using
      congrArg (expGaussianScalar δ ω (1 + t * I) • ·) (C.fstToSum_interFst x)

/-- The admissible boundary trace of the elementary intersection-valued function
`z ↦ exp (δ z² + ω z) x` for `δ > 0`, `ω : ℝ`, and `x : C.inter`. -/
def expGaussianTrace {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) : C.stripTraces :=
  ⟨C.expGaussianTracePair hδ ω x,
    mem_stripTraces_iff.2 ⟨_, C.isStripFunction_expGaussian hδ ω x⟩⟩

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
  rw [stripEval_apply, stripFunction_eq (C.isStripFunction_expGaussian hδ ω x) hz]
  rfl

/-- The submodule of `C.stripTraces` spanned over `ℂ` by the elementary intersection-valued traces
`exp (δ z² + ω z) x` (`δ > 0`, `ω : ℝ`, `x : C.inter`). -/
def elementaryStripTraces : Submodule ℂ C.stripTraces :=
  Submodule.span ℂ
    {g | ∃ (δ : ℝ) (hδ : 0 < δ) (ω : ℝ) (x : C.inter), C.expGaussianTrace hδ ω x = g}

theorem expGaussianTrace_mem_elementaryStripTraces {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter) :
    C.expGaussianTrace hδ ω x ∈ C.elementaryStripTraces :=
  Submodule.subset_span ⟨δ, hδ, ω, x, rfl⟩

/-! #### Analytical helpers for `dense_elementaryStripTraces` -/

private theorem closure_verticalStrip_zero_one :
    closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
  rfl

private theorem summable_pow_natAbs {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable fun k : ℤ => r ^ k.natAbs := by
  refine Summable.of_nat_of_neg_add_one (summable_geometric_of_lt_one hr₀ hr₁) ?_
  have heq : (fun n : ℕ => r ^ (-(n + 1 : ℤ)).natAbs) = fun n : ℕ => r * r ^ n := by
    ext n
    have hn : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
    rw [hn, pow_succ']
  rw [heq]
  exact (summable_geometric_of_lt_one hr₀ hr₁).mul_left r

private theorem tsum_pow_natAbs_ite_eq {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    (∑' k : ℤ, if k = 0 then (0 : ℝ) else r ^ k.natAbs) = 2 * (r * (1 - r)⁻¹) := by
  have hsum := summable_pow_natAbs hr₀ hr₁
  have hite : (∑' k : ℤ, r ^ k.natAbs) =
      (1 : ℝ) + ∑' k : ℤ, if k = 0 then (0 : ℝ) else r ^ k.natAbs := by
    simpa using hsum.tsum_eq_add_tsum_ite (0 : ℤ)
  have h1 : (fun n : ℕ => r ^ (n : ℤ).natAbs) = fun n : ℕ => r ^ n := by ext n; simp
  have h2 : (fun n : ℕ => r ^ (-(n + 1 : ℤ)).natAbs) = fun n : ℕ => r * r ^ n := by
    ext n
    have hn : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
    rw [hn, pow_succ']
  have htot : (∑' k : ℤ, r ^ k.natAbs) = (1 - r)⁻¹ + r * (1 - r)⁻¹ := by
    rw [tsum_of_nat_of_neg_add_one (by rw [h1]; exact summable_geometric_of_lt_one hr₀ hr₁)
      (by rw [h2]; exact (summable_geometric_of_lt_one hr₀ hr₁).mul_left r), h1, h2,
      tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
  have hne : 1 - r ≠ 0 := sub_ne_zero.2 hr₁.ne'
  have halg : (1 - r)⁻¹ + r * (1 - r)⁻¹ = 1 + 2 * (r * (1 - r)⁻¹) := by field_simp; ring
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
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_exp.continuousAt (x := 0)) (ε / (‖f‖ + 1)) (div_pos hε (by positivity))
  rw [Complex.exp_zero] at hη
  let B : ℝ := (|a| + R) ^ 2 + 1
  have hBpos : 0 < B := by positivity
  let δ₀ : ℝ := min (Real.log 2 / (2 * (a ^ 2 + 1))) (η / (2 * B))
  refine ⟨δ₀, lt_min (div_pos (Real.log_pos one_lt_two) (by positivity))
    (div_pos hηpos (by positivity)), fun {δ} hδ hδlt t => ?_⟩
  by_cases ht : |t| ≤ R
  · have hsq : ‖(a + t * I : ℂ) ^ 2‖ < B := by
      have h1 : ‖(a + t * I : ℂ)‖ ≤ |a| + R :=
        (norm_add_le _ _).trans (by simpa using add_le_add_right ht |a|)
      exact ((norm_pow _ 2).trans_le (pow_le_pow_left₀ (norm_nonneg _) h1 2)).trans_lt
        (lt_add_one _)
    have hw : dist (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) 0 < η := by
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc 2 * δ * ‖(a + t * I : ℂ) ^ 2‖
          < 2 * (η / (2 * B)) * B := by
            have hδ' : 2 * δ < 2 * (η / (2 * B)) := by linarith [hδlt.trans_le (min_le_right _ _)]
            exact mul_lt_mul'' hδ' hsq (by positivity) (norm_nonneg _)
        _ = η := by field_simp
    have hexp_lt : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1‖ < ε / (‖f‖ + 1) := by
      simpa [dist_eq_norm] using hη hw
    have hsub : exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t =
        (exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1) • f t := by
      rw [sub_smul, one_smul]
    rw [hsub, norm_smul]
    calc ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) - 1‖ * ‖f t‖
        ≤ (ε / (‖f‖ + 1)) * ‖f‖ :=
          mul_le_mul hexp_lt.le (f.norm_coe_le_norm t) (norm_nonneg _) (by positivity)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith
  · have htK : t ∉ K := fun hmemK => not_le.2 (not_le.1 ht) (by simpa using hR t hmemK)
    have hft : ‖f t‖ < ε / 4 := hKc htK
    have hexp_le : ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2)‖ ≤ 2 := by
      rw [Complex.norm_exp]
      have hre : (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2).re = 2 * δ * (a ^ 2 - t ^ 2) := by
        simp [sq]
      rw [hre]
      refine (Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log zero_lt_two)
      have hδ1 : δ < Real.log 2 / (2 * (a ^ 2 + 1)) := hδlt.trans_le (min_le_left _ _)
      have h2δ : 2 * δ * (a ^ 2 + 1) < Real.log 2 := by
        have := (lt_div_iff₀ (by positivity : 0 < 2 * (a ^ 2 + 1))).1 hδ1
        linarith
      nlinarith [sq_nonneg t]
    calc ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t - f t‖
        ≤ ‖exp (((2 * δ : ℝ) : ℂ) * (a + t * I) ^ 2) • f t‖ + ‖f t‖ := norm_sub_le _ _
      _ ≤ 2 * ‖f t‖ + ‖f t‖ := by
          rw [norm_smul]
          gcongr
      _ ≤ ε := by linarith

private theorem natAbs_le_sq (k : ℤ) : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
  have hk : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
  rw [hk]
  rcases Nat.eq_zero_or_pos k.natAbs with h0 | hpos
  · simp [h0]
  · have h1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hpos
    nlinarith

/-- Uniform norm bound on `{z | |z.im| ≤ B}` for vertical translates of `exp (δ z²) • F z`. -/
private theorem norm_damped_shift_le {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) {δ T B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (k : ℤ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (him : |z.im| ≤ B) :
    ‖exp ((δ : ℂ) * (z + k * T * I) ^ 2) • F (z + k * T * I)‖ ≤
      Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  have hz' : z + k * T * I ∈ verticalClosedStrip 0 1 := by simpa using hz
  rw [norm_smul, Complex.norm_exp]
  have hre : ((δ : ℂ) * (z + k * T * I) ^ 2).re = δ * (z.re ^ 2 - (z.im + k * T) ^ 2) := by
    simp [sq]
  have hrhs :
      Real.exp (δ * (1 + B ^ 2)) * ‖g‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs =
        Real.exp (δ * (1 + B ^ 2) + -(δ * T ^ 2 / 2) * (k.natAbs : ℝ)) * ‖g‖ := by
    rw [← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), Real.exp_add]
    ring
  rw [hre, hrhs]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) (hF.norm_le hz') (norm_nonneg _) (Real.exp_pos _).le
  have hre1 : z.re ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have him2 : z.im ^ 2 ≤ B ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hB]
  have hquad : (k * T : ℝ) ^ 2 / 2 - z.im ^ 2 ≤ (z.im + k * T) ^ 2 := by
    nlinarith [sq_nonneg (2 * z.im + k * T)]
  have hk2 : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 := by
    calc T ^ 2 * (k.natAbs : ℝ) ≤ T ^ 2 * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (natAbs_le_sq k) (sq_nonneg T)
      _ = (k * T : ℝ) ^ 2 := by ring
  nlinarith

/-- Pointwise norm bound for `exp (δ (a + i t)²) • exp (δ (a + i (t + k T))²) • f (t + k T)`
holding uniformly in `t : ℝ`. -/
private theorem norm_double_damped_shift_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : C₀(ℝ, E)) {a δ T : ℝ} (ha : a ∈ Icc 0 1) (hδ : 0 < δ) (k : ℤ) (t : ℝ) :
    ‖exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
      Real.exp (2 * δ) * ‖f‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs := by
  rw [norm_smul, norm_smul, Complex.norm_exp, Complex.norm_exp, ← mul_assoc, ← Real.exp_add]
  have hrhs :
      Real.exp (2 * δ) * ‖f‖ * (Real.exp (-(δ * T ^ 2 / 2))) ^ k.natAbs =
        Real.exp (2 * δ + -(δ * T ^ 2 / 2) * (k.natAbs : ℝ)) * ‖f‖ := by
    rw [← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), Real.exp_add]
    ring
  rw [hrhs]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) (f.norm_coe_le_norm _) (norm_nonneg _)
    (Real.exp_pos _).le
  have hre1 : ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) := by simp [sq]
  have hre2 : ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2).re =
      δ * (a ^ 2 - (t + k * T) ^ 2) := by simp [sq]
  rw [hre1, hre2]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hquad : (k * T : ℝ) ^ 2 / 2 ≤ t ^ 2 + (t + k * T) ^ 2 := by
    nlinarith [sq_nonneg (2 * t + k * T)]
  have hk2 : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 := by
    calc T ^ 2 * (k.natAbs : ℝ) ≤ T ^ 2 * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (natAbs_le_sq k) (sq_nonneg T)
      _ = (k * T : ℝ) ^ 2 := by ring
  nlinarith

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
    have hrhs : Real.exp (δ * (1 + B ^ 2)) * ‖f‖ * r ^ k.natAbs =
        Real.exp (δ * (1 + B ^ 2) + -(δ * T ^ 2 / 2) * (k.natAbs : ℝ)) * ‖f‖ := by
      dsimp [r]
      rw [← Real.exp_nat_mul, mul_comm (k.natAbs : ℝ), Real.exp_add]
      ring
    dsimp [term]
    rw [norm_smul, Complex.norm_exp, hrhs]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) (f.norm_coe_le_norm _) (norm_nonneg _)
      (Real.exp_pos _).le
    have hre : ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2).re = δ * (a ^ 2 - (t + k * T) ^ 2) := by
      simp [sq]
    rw [hre]
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
    have ht2 : t ^ 2 ≤ B ^ 2 := by rwa [sq_le_sq, abs_of_nonneg hB]
    have hquad : (k * T : ℝ) ^ 2 / 2 - t ^ 2 ≤ (t + k * T) ^ 2 := by
      nlinarith [sq_nonneg (2 * t + k * T)]
    have hk2 : T ^ 2 * (k.natAbs : ℝ) ≤ (k * T : ℝ) ^ 2 := by
      calc T ^ 2 * (k.natAbs : ℝ) ≤ T ^ 2 * (k : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (natAbs_le_sq k) (sq_nonneg T)
        _ = (k * T : ℝ) ^ 2 := by ring
    nlinarith
  have hsum (t : ℝ) : Summable fun k : ℤ => term k t :=
    .of_norm_bounded ((summable_pow_natAbs hr₀ hr₁).mul_left _) fun k =>
      hbound |t| (abs_nonneg t) k t le_rfl
  refine ⟨continuous_iff_continuousAt.2 fun t₀ => ?_, fun t => ?_, hsum⟩
  · set B := |t₀| + 1
    have hB : 0 ≤ B := by positivity
    have hcont : ContinuousOn (fun t : ℝ => ∑' k : ℤ, term k t) {t : ℝ | |t| < B} :=
      continuousOn_tsum (fun k => by dsimp [term]; fun_prop)
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖f‖))
        fun k t ht => hbound B hB k t (le_of_lt ht)
    exact hcont.continuousAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds
      (by dsimp [B]; exact lt_add_one |t₀|))
  · dsimp only
    conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    congr 1 with k
    simp only [Equiv.coe_addRight]
    have harg : t + T + (k : ℝ) * T = t + ((k + 1 : ℤ) : ℝ) * T := by push_cast; ring
    rw [harg]

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
    have hz₀U : z₀ ∈ U := ⟨hz₀, by dsimp [B]; exact lt_add_one _⟩
    have hdU : DifferentiableOn ℂ P U :=
      differentiableOn_tsum_of_summable_norm
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
        (fun k => by
          have hexp : Differentiable ℂ (fun z : ℂ => exp ((δ : ℂ) * (z + k * T * I) ^ 2)) := by
            fun_prop
          have hshift : Differentiable ℂ (fun z : ℂ => z + k * T * I) := by fun_prop
          exact hexp.differentiableOn.smul
            (hF.diffContOnCl.differentiableOn.comp hshift.differentiableOn
              fun z hz => by simpa using hz.1))
        hUopen
        (fun k z hz => norm_damped_shift_le C hF hδ (by positivity) k
          (verticalStrip_subset_verticalClosedStrip 0 1 hz.1) (le_of_lt hz.2))
    exact (hdU.differentiableAt (hUopen.mem_nhds hz₀U)).differentiableWithinAt
  have hcont : ContinuousOn P (closure (verticalStrip 0 1)) := by
    rw [closure_verticalStrip_zero_one]
    intro z₀ hz₀
    set B := |z₀.im| + 1
    let W : Set ℂ := verticalClosedStrip 0 1 ∩ {z : ℂ | |z.im| < B}
    have hcontW : ContinuousOn P W :=
      continuousOn_tsum
        (fun k => by
          have hexp : Continuous (fun z : ℂ => exp ((δ : ℂ) * (z + k * T * I) ^ 2)) := by fun_prop
          have hshift : Continuous (fun z : ℂ => z + k * T * I) := by fun_prop
          have hFc : ContinuousOn F (verticalClosedStrip 0 1) := by
            simpa [closure_verticalStrip_zero_one] using hF.diffContOnCl.continuousOn
          exact hexp.continuousOn.smul
            (hFc.comp hshift.continuousOn fun z hz => by simpa using hz.1))
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (δ * (1 + B ^ 2)) * ‖g‖))
        fun k z hz => norm_damped_shift_le C hF hδ (by positivity) k hz.1 (le_of_lt hz.2)
    exact (hcontW z₀ ⟨hz₀, by dsimp [B]; exact lt_add_one _⟩).mono_of_mem_nhdsWithin <|
      inter_mem_nhdsWithin _ <|
        (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
          (by dsimp [B]; exact lt_add_one _)
  refine ⟨⟨hdiff, hcont⟩, fun z => ?_, fun t => ?_, fun t => ?_⟩
  · dsimp only [P]
    conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    congr 1 with k
    simp only [Equiv.coe_addRight]
    have harg : z + T * I + k * T * I = z + ((k + 1 : ℤ) : ℂ) * T * I := by push_cast; ring
    rw [harg]
  · obtain ⟨-, -, hsum₀⟩ :=
      continuous_and_periodic_periodizeTrace g.1 (a := 0) ⟨le_rfl, zero_le_one⟩ hδ hT
    rw [(C.fstToSum.map_tsum (by simpa using hsum₀ t))]
    dsimp [P]
    congr 1 with k
    have harg : (t : ℂ) * I + k * T * I = ((t + k * T : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg, hF.apply_mul_I, map_smul]
  · obtain ⟨-, -, hsum₁⟩ :=
      continuous_and_periodic_periodizeTrace g.2 (a := 1) ⟨zero_le_one, le_rfl⟩ hδ hT
    rw [(C.sndToSum.map_tsum (by simpa using hsum₁ t))]
    dsimp [P]
    congr 1 with k
    have harg : (1 : ℂ) + t * I + k * T * I = 1 + ((t + k * T : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg, hF.apply_one_add_mul_I, map_smul]

/-- Cauchy–Goursat identity along the rectangle `[0, 1] × [0, T]` for a vertically `T * I`-periodic
holomorphic function on the strip. -/
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
      rw [closure_verticalStrip_zero_one]
      simpa [uIcc_of_le zero_le_one] using hz₁)
    (hexp.differentiableOn.smul <| hP.differentiableOn.mono fun z ⟨hz₁, _⟩ => by
      simpa [hTpos.le] using hz₁)
  simp only [zero_re, zero_im, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, one_im, mul_im, zero_add, ofReal_zero, zero_mul] at hrect
  have htop : (∫ x : ℝ in 0..1, h (x + T * I)) = ∫ x : ℝ in 0..1, h x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hexp_per : exp (ω * (x + T * I)) = exp (ω * x) := by
      rw [mul_add, Complex.exp_add]
      have hωT : ω * (T * I) = ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
        have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hTpos.ne'
        simp only [ω]
        push_cast
        field_simp
      rw [hωT, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [h, hper, hexp_per]
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
  have hTpos : 0 < T := hT.out
  rw [C.mem_inter_iff, ← C.sumSpaceEmbed_fstToSum, ← C.sumSpaceEmbed_sndToSum]
  congr 1
  rw [fourierCoeff_eq_intervalIntegral _ m 0, fourierCoeff_eq_intervalIntegral _ m 0, zero_add,
    C.fstToSum.map_smul_of_tower, map_smul, C.sndToSum.map_smul_of_tower,
    smul_comm (exp _) (1 / T : ℝ)]
  congr 1
  have hint₀ : IntervalIntegrable (fun y : ℝ => @fourier T (-m) y • hp₀_per.lift y) volume 0 T :=
    ((@fourier T (-m)).continuous.comp continuous_quotient_mk' |>.smul
      (hp₀_cont.congr fun y => rfl)).intervalIntegrable 0 T
  have hint₁ : IntervalIntegrable (fun y : ℝ => @fourier T (-m) y • hp₁_per.lift y) volume 0 T :=
    ((@fourier T (-m)).continuous.comp continuous_quotient_mk' |>.smul
      (hp₁_cont.congr fun y => rfl)).intervalIntegrable 0 T
  rw [← C.fstToSum.intervalIntegral_comp_comm hint₀, ← C.sndToSum.intervalIntegral_comp_comm hint₁,
    ← intervalIntegral.integral_smul]
  refine (intervalIntegral.integral_congr fun y _ => ?_).trans
    ((integral_periodic_strip_eq hTpos P hP hper m).trans
      (intervalIntegral.integral_congr fun y _ => ?_))
  · rw [Function.Periodic.lift_coe, map_smul, ← hP₀ y, fourier_coe_apply]
    congr 2
    push_cast
    ring
  · rw [Function.Periodic.lift_coe, map_smul, ← hP₁ y, smul_smul, fourier_coe_apply,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring

private theorem fourier_sub_apply {T : ℝ} (m : ℤ) (x v : AddCircle T) :
    fourier m (x - v) = fourier m x * fourier (-m) v := by
  rw [fourier_apply, zsmul_sub, sub_eq_add_neg, toCircle_add, Circle.coe_mul, ← fourier_apply,
    ← neg_zsmul, ← fourier_apply]

private theorem conv_fourier_eq {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (m : ℤ) (f : AddCircle T → E) (t : ℝ) :
    ∫ u : AddCircle T, fourier m u • f ((t : AddCircle T) - u) ∂haarAddCircle =
      fourier m (t : AddCircle T) • fourierCoeff f m := by
  let x : AddCircle T := t
  have hsub :
      (∫ u : AddCircle T, fourier m u • f (x - u) ∂haarAddCircle) =
        ∫ v : AddCircle T, fourier m (x - v) • f v ∂haarAddCircle := by
    simpa [sub_eq_add_neg] using
      integral_sub_left_eq_self (fun v : AddCircle T => fourier m (x - v) • f v) haarAddCircle x
  rw [hsub]
  simp_rw [fourier_sub_apply, mul_smul, integral_smul]
  rfl

private theorem conv_approx_single {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : AddCircle T → E) (hf : Continuous f) {η M ε : ℝ}
    (hM : 0 < M) (hfb : ∀ x, ‖f x‖ ≤ M)
    (huc : ∀ a b, dist a b < η → dist (f a) (f b) < ε / 2)
    {K Q : C(AddCircle T, ℂ)} (hK_int : ∫ u : AddCircle T, K u ∂haarAddCircle = 1)
    (hK_norm : ∫ u : AddCircle T, ‖K u‖ ∂haarAddCircle = 1)
    (hK_supp : ∀ u : AddCircle T, η ≤ ‖u‖ → K u = 0)
    (hQK : ‖Q - K‖ < ε / (2 * M)) (x : AddCircle T) :
    ‖(∫ u : AddCircle T, Q u • f (x - u) ∂haarAddCircle) - f x‖ < ε := by
  have hintQ : Integrable (fun u : AddCircle T => Q u • f (x - u)) haarAddCircle :=
    (Q.continuous.smul
      (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (.of_compactSpace _)
  have hintK : Integrable (fun u : AddCircle T => K u • f (x - u)) haarAddCircle :=
    (K.continuous.smul
      (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (.of_compactSpace _)
  have hintKx : Integrable (fun u : AddCircle T => K u • f x) haarAddCircle :=
    (K.continuous.smul continuous_const).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hconvK : ‖(∫ u : AddCircle T, K u • f (x - u) ∂haarAddCircle) - f x‖ ≤ ε / 2 := by
    have hfx : f x = ∫ u : AddCircle T, K u • f x ∂haarAddCircle := by
      rw [integral_smul_const, hK_int, one_smul]
    conv_lhs => rw [hfx, ← integral_sub hintK hintKx]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt (u : AddCircle T) : ‖K u • f (x - u) - K u • f x‖ ≤ ‖K u‖ * (ε / 2) := by
      rw [← smul_sub, norm_smul]
      by_cases hu : ‖u‖ < η
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← dist_eq_norm]
        exact (huc _ _ (by rwa [dist_eq_norm, sub_right_comm, sub_self, zero_sub, norm_neg])).le
      · simp [hK_supp u (not_lt.1 hu)]
    exact (integral_mono (hintK.sub hintKx).norm
      ((K.continuous.norm.mul_const (ε / 2)).integrable_of_hasCompactSupport (.of_compactSpace _))
      hpt).trans_eq (by rw [integral_mul_const, hK_norm, one_mul])
  have hdiff :
      ‖(∫ u : AddCircle T, Q u • f (x - u) ∂haarAddCircle) -
        (∫ u : AddCircle T, K u • f (x - u) ∂haarAddCircle)‖ < ε / 2 := by
    rw [← integral_sub hintQ hintK]
    refine (norm_integral_le_of_norm_le_const (C := ‖Q - K‖ * M) ?_).trans_lt ?_
    · refine ae_of_all _ fun u => ?_
      rw [← sub_smul, norm_smul]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm (Q - K) u) (hfb (x - u))
        (norm_nonneg _) (norm_nonneg _)
    · rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
      calc ‖Q - K‖ * M < (ε / (2 * M)) * M := mul_lt_mul_of_pos_right hQK hM
        _ = ε / 2 := by field_simp
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
    have hcoe : (fun u : AddCircle T => K u) =
        fun u => ((c⁻¹ : ℝ) : ℂ) * (tent u : ℂ) := by
      ext u; simp [K]
    rw [hcoe, integral_const_mul, integral_complex_ofReal, ← ofReal_mul,
      inv_mul_cancel₀ htent_pos.ne', Complex.ofReal_one]
  have hK_norm : ∫ u : AddCircle T, ‖K u‖ ∂haarAddCircle = 1 := by
    have hnorm (u : AddCircle T) : ‖K u‖ = c⁻¹ * tent u := by
      have hnn : 0 ≤ c⁻¹ * tent u := mul_nonneg (inv_nonneg.2 htent_pos.le) (htent_nonneg u)
      dsimp [K]
      rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    simp_rw [hnorm]
    rw [integral_const_mul, inv_mul_cancel₀ htent_pos.ne']
  have hK_supp (u : AddCircle T) (hu : η ≤ ‖u‖) : K u = 0 := by
    have hle : 1 - ‖u‖ / η ≤ 0 := sub_nonpos.2 ((one_le_div hη).2 hu)
    simp [K, tent, max_eq_left hle]
  obtain ⟨M₀, hM₀pos, hM₀⟩ := (isCompact_univ.image hf₀).isBounded.exists_pos_norm_le
  obtain ⟨M₁, _, hM₁⟩ := (isCompact_univ.image hf₁).isBounded.exists_pos_norm_le
  set M := max M₀ M₁
  have hM : 0 < M := lt_of_lt_of_le hM₀pos (le_max_left _ _)
  have hdense : K ∈ (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨Q, hQmem, hQK⟩ :=
    Metric.mem_closure_iff.1 hdense (ε / (2 * M)) (div_pos hε (by positivity))
  rw [dist_comm, dist_eq_norm] at hQK
  exact ⟨Q, hQmem,
    conv_approx_single f₀ hf₀ hM
      (fun x => (hM₀ _ (mem_image_of_mem _ (mem_univ _))).trans (le_max_left _ _))
      (fun a b h => huc₀ (h.trans_le (min_le_left _ _))) hK_int hK_norm hK_supp hQK,
    conv_approx_single f₁ hf₁ hM
      (fun x => (hM₁ _ (mem_image_of_mem _ (mem_univ _))).trans (le_max_right _ _))
      (fun a b h => huc₁ (h.trans_le (min_le_right _ _))) hK_int hK_norm hK_supp hQK⟩

/-- Damping the convolution of `(f₀, f₁)` against any `Q ∈ span (range fourier)` produces an
element of `C.elementaryStripTraces` whenever `(fourierCoeff f₀ m, exp (-2 π m / T) •
fourierCoeff f₁ m) ∈ C.inter` for every `m : ℤ`. -/
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
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hQ
  · rintro _ ⟨m, rfl⟩
    let xm : C.inter :=
      ⟨(fourierCoeff f₀ m, exp (-(2 * Real.pi * m / T : ℂ)) • fourierCoeff f₁ m), hmem m⟩
    refine ⟨C.expGaussianTrace hδ (2 * Real.pi * m / T) xm,
      C.expGaussianTrace_mem_elementaryStripTraces hδ _ xm, fun t => ?_, fun t => ?_⟩
    · rw [expGaussianTrace_apply_fst, C.interFst_apply, conv_fourier_eq, fourier_coe_apply,
        smul_smul, ← Complex.exp_add]
      dsimp [xm]
      congr 2
      push_cast
      ring
    · rw [expGaussianTrace_apply_snd, C.interSnd_apply, conv_fourier_eq, fourier_coe_apply]
      dsimp [xm]
      rw [smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
  · exact ⟨0, C.elementaryStripTraces.zero_mem, fun t => by simp, fun t => by simp⟩
  · rintro Q₁ Q₂ - - ⟨h₁, hh₁, h₁₀, h₁₁⟩ ⟨h₂, hh₂, h₂₀, h₂₁⟩
    refine ⟨h₁ + h₂, C.elementaryStripTraces.add_mem hh₁ hh₂, fun t => ?_, fun t => ?_⟩
    · have hint₁ : Integrable (fun u : AddCircle T => Q₁ u • f₀ ((t : AddCircle T) - u))
          haarAddCircle :=
        (Q₁.continuous.smul
          (hf₀.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
            (.of_compactSpace _)
      have hint₂ : Integrable (fun u : AddCircle T => Q₂ u • f₀ ((t : AddCircle T) - u))
          haarAddCircle :=
        (Q₂.continuous.smul
          (hf₀.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
            (.of_compactSpace _)
      simp only [Submodule.coe_add, Prod.fst_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₀ t, h₂₀ t, ← smul_add, ← integral_add hint₁ hint₂]
      simp_rw [ContinuousMap.add_apply, add_smul]
    · have hint₁ : Integrable (fun u : AddCircle T => Q₁ u • f₁ ((t : AddCircle T) - u))
          haarAddCircle :=
        (Q₁.continuous.smul
          (hf₁.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
            (.of_compactSpace _)
      have hint₂ : Integrable (fun u : AddCircle T => Q₂ u • f₁ ((t : AddCircle T) - u))
          haarAddCircle :=
        (Q₂.continuous.smul
          (hf₁.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
            (.of_compactSpace _)
      simp only [Submodule.coe_add, Prod.snd_add, FunLike.coe_add, Pi.add_apply]
      rw [h₁₁ t, h₂₁ t, ← smul_add, ← integral_add hint₁ hint₂]
      simp_rw [ContinuousMap.add_apply, add_smul]
  · rintro c Q₁ - ⟨h₁, hh₁, h₁₀, h₁₁⟩
    refine ⟨c • h₁, C.elementaryStripTraces.smul_mem c hh₁, fun t => ?_, fun t => ?_⟩
    · simp only [SetLike.val_smul, Prod.smul_fst, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₀ t, smul_comm c]
      simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]
    · simp only [SetLike.val_smul, Prod.smul_snd, FunLike.coe_smul, Pi.smul_apply]
      rw [h₁₁ t, smul_comm c]
      simp_rw [ContinuousMap.smul_apply, smul_assoc, integral_smul]

/-- Choosing `T` large enough makes the `k ≠ 0` tail of the doubly damped vertical periodization
strictly smaller than `ε` in `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. -/
private theorem exists_period_tail_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (g : C.stripTraces) :
    ∃ T > 0,
      let r := Real.exp (-(δ * T ^ 2 / 2))
      r < 1 ∧ Real.exp (2 * δ) * ‖g‖ * (2 * (r * (1 - r)⁻¹)) < ε := by
  set C₀ := Real.exp (2 * δ) * ‖g‖ + 1
  have hC₀ : 0 < C₀ := by positivity
  set r₀ := min (1 / 2) (ε / (4 * C₀))
  have hr₀pos : 0 < r₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  set T := max 1 (Real.sqrt (2 * |Real.log r₀| / δ) + 1)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨T, hTpos, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  · set r := Real.exp (-(δ * T ^ 2 / 2))
    have hTgt : Real.sqrt (2 * |Real.log r₀| / δ) < T :=
      lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    have hTsq : 2 * |Real.log r₀| / δ < T ^ 2 := by
      calc 2 * |Real.log r₀| / δ
          = (Real.sqrt (2 * |Real.log r₀| / δ)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ < T ^ 2 := pow_lt_pow_left₀ hTgt (Real.sqrt_nonneg _) two_ne_zero
    have hexp_lt : -(δ * T ^ 2 / 2) < Real.log r₀ := by
      have h1 : |Real.log r₀| < δ * T ^ 2 / 2 := by
        have := (div_lt_iff₀ hδ).1 hTsq
        linarith
      linarith [neg_abs_le (Real.log r₀)]
    have hr_lt : r < r₀ := by
      rw [← Real.exp_log hr₀pos]
      exact Real.exp_lt_exp.2 hexp_lt
    have hr_half : r < 1 / 2 := hr_lt.trans_le (min_le_left _ _)
    have hr_eps : r < ε / (4 * C₀) := hr_lt.trans_le (min_le_right _ _)
    have h1r : 0 < 1 - r := by linarith
    have hinv : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ h1r zero_lt_two]
      linarith
    have h2r : 2 * (r * (1 - r)⁻¹) < ε / C₀ := by
      have hle : 2 * (r * (1 - r)⁻¹) ≤ 4 * r := by
        nlinarith [Real.exp_pos (-(δ * T ^ 2 / 2))]
      have hlt : 4 * r < ε / C₀ := by
        calc 4 * r < 4 * (ε / (4 * C₀)) := by linarith
          _ = ε / C₀ := by field_simp
      exact hle.trans_lt hlt
    calc Real.exp (2 * δ) * ‖g‖ * (2 * (r * (1 - r)⁻¹))
        ≤ C₀ * (2 * (r * (1 - r)⁻¹)) :=
          mul_le_mul_of_nonneg_right (by dsimp [C₀]; linarith) (by positivity)
      _ < C₀ * (ε / C₀) := mul_lt_mul_of_pos_left h2r hC₀
      _ = ε := mul_div_cancel₀ ε hC₀.ne'

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
    dsimp [d]
    rw [← smul_sub, norm_smul, Complex.norm_exp]
    have hexp_le : Real.exp (((δ : ℂ) * (a + t * I) ^ 2).re) ≤ Real.exp δ := by
      refine Real.exp_le_exp.2 ?_
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
      have hre : ((δ : ℂ) * (a + t * I) ^ 2).re = δ * (a ^ 2 - t ^ 2) := by simp [sq]
      rw [hre]
      nlinarith [sq_nonneg t]
    exact (mul_le_mul hexp_le (hQ t).le (norm_nonneg _) (Real.exp_pos δ).le).trans_eq
      (mul_div_cancel₀ _ (Real.exp_pos δ).ne')
  have htail_err : ‖d - m‖ ≤ ε / 3 := by
    have : 0 ≤ M := (norm_nonneg f).trans hfM
    let hcL : E →L[ℂ] E :=
      ContinuousLinearMap.lsmul ℂ ℂ (exp ((δ : ℂ) * (a + t * I) ^ 2))
    have hd_sum : d = ∑' k : ℤ,
        exp ((δ : ℂ) * (a + t * I) ^ 2) •
          (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) := by
      simpa only [d, Function.Periodic.lift_coe, hcL, ContinuousLinearMap.lsmul_apply] using
        hcL.map_tsum (hsum t)
    have hsmul_sum : Summable fun k : ℤ =>
        exp ((δ : ℂ) * (a + t * I) ^ 2) •
          (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T)) := by
      simpa only [Function.comp_def, hcL, ContinuousLinearMap.lsmul_apply] using
        (hsum t).mapL hcL
    have hk0 : exp ((δ : ℂ) * (a + t * I) ^ 2) •
        (exp ((δ : ℂ) * (a + (t + (0 : ℤ) * T : ℝ) * I) ^ 2) • f (t + (0 : ℤ) * T)) = m := by
      simp [m, smul_smul, ← Complex.exp_add, two_mul, add_mul]
    rw [hd_sum, hsmul_sum.tsum_eq_add_tsum_ite 0, hk0, add_sub_cancel_left]
    have hite_bound (k : ℤ) :
        ‖if k = 0 then (0 : E) else exp ((δ : ℂ) * (a + t * I) ^ 2) •
          (exp ((δ : ℂ) * (a + (t + k * T : ℝ) * I) ^ 2) • f (t + k * T))‖ ≤
        if k = 0 then 0 else Real.exp (2 * δ) * M * r ^ k.natAbs := by
      split_ifs with hk
      · simp
      · exact (norm_double_damped_shift_le f ha hδ k t).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfM (Real.exp_pos _).le) (by positivity))
    have hsum_ite : Summable fun k : ℤ =>
        if k = 0 then (0 : ℝ) else Real.exp (2 * δ) * M * r ^ k.natAbs :=
      .of_nonneg_of_le (fun k => by split_ifs <;> positivity)
        (fun k => by split_ifs <;> [positivity; exact le_rfl])
        ((summable_pow_natAbs hr₀ hr₁).mul_left (Real.exp (2 * δ) * M))
    have hsum_norm := hsum_ite.of_nonneg_of_le (fun _ => norm_nonneg _) hite_bound
    refine (norm_tsum_le_tsum_norm hsum_norm).trans
      ((Summable.tsum_le_tsum hite_bound hsum_norm hsum_ite).trans ?_)
    have hfactor : (fun k : ℤ => if k = 0 then (0 : ℝ)
        else Real.exp (2 * δ) * M * r ^ k.natAbs) =
        fun k : ℤ => Real.exp (2 * δ) * M * (if k = 0 then 0 else r ^ k.natAbs) := by
      ext k; split_ifs <;> simp
    rw [hfactor, tsum_mul_left, tsum_pow_natAbs_ite_eq hr₀ hr₁]
    exact htail.le
  have htri₁ := norm_sub_le_norm_sub_add_norm_sub
    (exp ((δ : ℂ) * (a + t * I) ^ 2) •
      (∫ u : AddCircle T, Q u • hp_per.lift ((t : AddCircle T) - u) ∂haarAddCircle)) d (f t)
  have htri₂ := norm_sub_le_norm_sub_add_norm_sub d m (f t)
  linarith

/-- **Calderón's density lemma (Bergh–Löfström, Lemma 4.2.3).** When `X₀` and `X₁` are Banach
spaces, the `ℂ`-linear span of the elementary intersection-valued functions
`z ↦ exp (δ z² + ω z) x` (`δ > 0`, `ω ∈ ℝ`, `x ∈ X₀ ∩ X₁`) is dense in `C.stripTraces`. -/
theorem dense_elementaryStripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    Dense (C.elementaryStripTraces : Set C.stripTraces) := by
  refine Metric.dense_iff.2 fun g ε hε => ?_
  set g₀ : C₀(ℝ, X₀) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1
  set g₁ : C₀(ℝ, X₁) := (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2
  obtain ⟨δ₀, hδ₀, hdamp₀⟩ :=
    exists_gaussian_smul_approx_single 0 g₀ (by positivity : 0 < ε / 4)
  obtain ⟨δ₁, hδ₁, hdamp₁⟩ :=
    exists_gaussian_smul_approx_single 1 g₁ (by positivity : 0 < ε / 4)
  set δ := min δ₀ δ₁ / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₀ hδ₁)
  have hδlt₀ : δ < δ₀ := (half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_left _ _)
  have hδlt₁ : δ < δ₁ := (half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_right _ _)
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
  have hmem := fourierCoeff_periodic_mem_inter C hP_diff hP_per hp₀_cont hp₁_cont hp₀_per hp₁_per
    (by simpa [zero_add] using hP₀) hP₁
  obtain ⟨Q, hQspan, hQ₀, hQ₁⟩ :=
    exists_fourier_span_conv_approx hp₀_per.lift hp₁_per.lift hf₀ hf₁
      (div_pos (by positivity : 0 < ε / 3) (Real.exp_pos δ))
  obtain ⟨h, hhmem, hh₀, hh₁⟩ :=
    exists_elementary_of_mem_span_fourier C hδ hf₀ hf₁ hmem hQspan
  refine ⟨h, ?_, hhmem⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
  refine lt_of_le_of_lt (norm_prod_le_iff.2 ⟨?_, ?_⟩) (by linarith : ε / 3 + ε / 3 + ε / 4 < ε)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.fst_sub, FunLike.coe_sub, Pi.sub_apply]
    rw [norm_sub_rev, hh₀ t]
    simpa [zero_add] using norm_damped_conv_sub_le ⟨le_rfl, zero_le_one⟩ hδ g₀
      (norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))) hp₀_per hsum₀ Q hQ₀ hr₁ htail
      (hdamp₀ hδ hδlt₀ t)
  · refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
    simp only [Prod.snd_sub, FunLike.coe_sub, Pi.sub_apply]
    rw [norm_sub_rev, hh₁ t]
    simpa using norm_damped_conv_sub_le ⟨zero_le_one, le_rfl⟩ hδ g₁
      (norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))) hp₁_per hsum₁ Q hQ₁ hr₁ htail
      (hdamp₁ hδ hδlt₁ t)

end ElementaryTraces

/-! ### Density of the intersection and endpoint inclusions (Bergh–Löfström, Theorem 4.2.2) -/

section InterDensity

/-- Every admissible boundary trace takes values in the closure `C.fstClosure` (`X₀°`) on the left
boundary line when `X₀` and `X₁` are complete. -/
theorem stripTraces_fst_apply_mem_fstClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t ∈ C.fstClosure := by
  let ev : C.stripTraces →L[ℂ] X₀ :=
    (ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
      ((ContinuousLinearMap.fst ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL)
  have hev (q : C.stripTraces) : ev q = (q : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t := by
    simp [ev, ZeroAtInftyContinuousMap.evalCLM_apply]
  have hsub : C.elementaryStripTraces ≤ C.fstClosure.comap ev.toLinearMap :=
    Submodule.span_le.2 <| by
      rintro _ ⟨δ, hδ, ω, x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hev,
        expGaussianTrace_apply_fst]
      exact C.fstClosure.smul_mem _ (C.interFst_mem_fstClosure x)
  have hcl : IsClosed (C.fstClosure.comap ev.toLinearMap : Set C.stripTraces) :=
    (inferInstance : IsClosed (C.fstClosure : Set X₀)).preimage ev.continuous
  have hmem := Submodule.mem_comap.1
    (hcl.closure_subset_iff.2 hsub (C.dense_elementaryStripTraces g))
  rwa [ContinuousLinearMap.coe_coe, hev] at hmem

/-- Every admissible boundary trace takes values in the closure `C.sndClosure` (`X₁°`) on the right
boundary line when `X₀` and `X₁` are complete. -/
theorem stripTraces_snd_apply_mem_sndClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t ∈ C.sndClosure := by
  let ev : C.stripTraces →L[ℂ] X₁ :=
    (ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
      ((ContinuousLinearMap.snd ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL)
  have hev (q : C.stripTraces) : ev q = (q : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t := by
    simp [ev, ZeroAtInftyContinuousMap.evalCLM_apply]
  have hsub : C.elementaryStripTraces ≤ C.sndClosure.comap ev.toLinearMap :=
    Submodule.span_le.2 <| by
      rintro _ ⟨δ, hδ, ω, x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hev,
        expGaussianTrace_apply_snd]
      exact C.sndClosure.smul_mem _ (C.interSnd_mem_sndClosure x)
  have hcl : IsClosed (C.sndClosure.comap ev.toLinearMap : Set C.stripTraces) :=
    (inferInstance : IsClosed (C.sndClosure : Set X₁)).preimage ev.continuous
  have hmem := Submodule.mem_comap.1
    (hcl.closure_subset_iff.2 hsub (C.dense_elementaryStripTraces g))
  rwa [ContinuousLinearMap.coe_coe, hev] at hmem

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

/-- The canonical contractive injection `[X₀, X₁]_0 →L[ℂ] X₀`, sending the class of `g` to
`g₀ 0`. -/
def toFst : C.ComplexMethodSpace 0 →L[ℂ] X₀ :=
  lift ((ZeroAtInftyContinuousMap.evalCLM ℂ 0).comp
      ((ContinuousLinearMap.fst ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    fun g hg => C.fstToSum_injective <| by
      have h0 : C.stripEval (0 : ℂ) g = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) := by
        simpa using C.stripFunction_mul_I g 0
      simpa [h0] using hg

@[simp]
theorem toFst_mk (g : C.stripTraces) :
    toFst (mk 0 g) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0 := by
  simp [toFst, ZeroAtInftyContinuousMap.evalCLM_apply]

@[simp]
theorem fstToSum_toFst (u : C.ComplexMethodSpace 0) :
    C.fstToSum (toFst u) = toSum u := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa [toSum_mk] using (C.stripFunction_mul_I g 0).symm

theorem toFst_injective : Function.Injective (toFst (C := C)) := fun u v huv =>
  toSum_injective <| by rw [← fstToSum_toFst, ← fstToSum_toFst, huv]

theorem norm_toFst_le (u : C.ComplexMethodSpace 0) : ‖toFst u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [toFst_mk]
  exact (((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.norm_coe_le_norm 0).trans
    (norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)))).trans_lt hg

@[simp]
theorem toFst_ofInter (x : C.inter) : toFst (ofInter 0 x) = C.interFst x :=
  C.fstToSum_injective <| by rw [fstToSum_toFst, toSum_ofInter ⟨le_rfl, zero_le_one⟩]

theorem toFst_mem_fstClosure [CompleteSpace X₀] [CompleteSpace X₁] (u : C.ComplexMethodSpace 0) :
    toFst u ∈ C.fstClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [toFst_mk]
  exact C.stripTraces_fst_apply_mem_fstClosure g 0

/-- The canonical contractive injection `[X₀, X₁]_1 →L[ℂ] X₁`, sending the class of `g` to
`g₁ 0`. -/
def toSnd : C.ComplexMethodSpace 1 →L[ℂ] X₁ :=
  lift ((ZeroAtInftyContinuousMap.evalCLM ℂ 0).comp
      ((ContinuousLinearMap.snd ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    fun g hg => C.sndToSum_injective <| by
      have h1 : C.stripEval (1 : ℂ) g = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0) := by
        simpa using C.stripFunction_one_add_mul_I g 0
      simpa [h1] using hg

@[simp]
theorem toSnd_mk (g : C.stripTraces) :
    toSnd (mk 1 g) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0 := by
  simp [toSnd, ZeroAtInftyContinuousMap.evalCLM_apply]

@[simp]
theorem sndToSum_toSnd (u : C.ComplexMethodSpace 1) :
    C.sndToSum (toSnd u) = toSum u := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa [toSum_mk] using (C.stripFunction_one_add_mul_I g 0).symm

theorem toSnd_injective : Function.Injective (toSnd (C := C)) := fun u v huv =>
  toSum_injective <| by rw [← sndToSum_toSnd, ← sndToSum_toSnd, huv]

theorem norm_toSnd_le (u : C.ComplexMethodSpace 1) : ‖toSnd u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [toSnd_mk]
  exact (((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.norm_coe_le_norm 0).trans
    (norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)))).trans_lt hg

@[simp]
theorem toSnd_ofInter (x : C.inter) : toSnd (ofInter 1 x) = C.interSnd x :=
  C.sndToSum_injective <| by
    rw [sndToSum_toSnd, toSum_ofInter ⟨zero_le_one, le_rfl⟩, C.fstToSum_interFst]

theorem toSnd_mem_sndClosure [CompleteSpace X₀] [CompleteSpace X₁] (u : C.ComplexMethodSpace 1) :
    toSnd u ∈ C.sndClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [toSnd_mk]
  exact C.stripTraces_snd_apply_mem_sndClosure g 0

end ComplexMethodSpace

end InterDensity

/-! ### Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)) -/

section Regularize

omit [T1Space V] in
private theorem regularize_compat (y : C.regularize.inter) :
    C.fstToSum (C.fstClosure.subtypeL (C.regularize.interFst y)) =
      C.sndToSum (C.sndClosure.subtypeL (C.regularize.interSnd y)) := by
  rw [Submodule.subtypeL_apply, Submodule.subtypeL_apply, ← C.interFst_regularizeInterEquiv,
    ← C.interSnd_regularizeInterEquiv]
  exact C.fstToSum_interFst (C.regularizeInterEquiv y)

omit [T1Space V] in
private theorem sumLift_regularize_eq :
    C.regularize.sumLift (C.fstToSum.comp C.fstClosure.subtypeL)
      (C.sndToSum.comp C.sndClosure.subtypeL) (regularize_compat C) = C.regularizeSumMap :=
  (C.regularize.sumLift_unique _ _ (regularize_compat C)
    (ContinuousLinearMap.ext fun x => by simp)
    (ContinuousLinearMap.ext fun x => by simp)).symm

/-- Inclusion of `(X₀°, X₁°)` into `(X₀, X₁)` embeds `C.regularize.stripTraces` isometrically
into `C.stripTraces`. -/
def regularizeStripTracesIsometry : C.regularize.stripTraces →ₗᵢ[ℂ] C.stripTraces where
  toLinearMap :=
    (stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
      (regularize_compat C)).toLinearMap
  norm_map' g := by
    rw [ContinuousLinearMap.coe_coe, ← Submodule.norm_coe, ← Submodule.norm_coe,
      Prod.norm_def, Prod.norm_def]
    congr 1
    · rw [ZeroAtInftyContinuousMap.norm_eq_iSup_norm, ZeroAtInftyContinuousMap.norm_eq_iSup_norm]
      simp only [stripTracesMap_apply_fst, Submodule.subtypeL_apply, Submodule.norm_coe]
    · rw [ZeroAtInftyContinuousMap.norm_eq_iSup_norm, ZeroAtInftyContinuousMap.norm_eq_iSup_norm]
      simp only [stripTracesMap_apply_snd, Submodule.subtypeL_apply, Submodule.norm_coe]

@[simp]
theorem regularizeStripTracesIsometry_apply_fst (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).1 t : X₀) :=
  stripTracesMap_apply_fst C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g t

@[simp]
theorem regularizeStripTracesIsometry_apply_snd (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).2 t : X₁) :=
  stripTracesMap_apply_snd C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g t

theorem stripEval_regularizeStripTracesIsometry (z : ℂ) (g : C.regularize.stripTraces) :
    C.stripEval z (C.regularizeStripTracesIsometry g) =
      C.regularizeSumMap (C.regularize.stripEval z g) := by
  -- Unfold `regularizeStripTracesIsometry` to `stripTracesMap` on `g`.
  change C.stripEval z
    (stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g) =
      _
  rw [stripEval_stripTracesMap, sumLift_regularize_eq]

private theorem surjective_regularizeStripTracesIsometry [CompleteSpace X₀] [CompleteSpace X₁] :
    Function.Surjective C.regularizeStripTracesIsometry := by
  have : CompleteSpace C.fstClosure :=
    (inferInstance : IsClosed (C.fstClosure : Set X₀)).completeSpace_coe
  have : CompleteSpace C.sndClosure :=
    (inferInstance : IsClosed (C.sndClosure : Set X₁)).completeSpace_coe
  have hcl : IsClosed (Set.range C.regularizeStripTracesIsometry) :=
    C.regularizeStripTracesIsometry.isometry.isUniformInducing.isComplete_range.isClosed
  have hsub : (C.elementaryStripTraces : Set C.stripTraces) ⊆
      Set.range C.regularizeStripTracesIsometry := by
    -- Express subset inclusion as a submodule inequality to induct over `span`.
    change C.elementaryStripTraces ≤ LinearMap.range C.regularizeStripTracesIsometry.toLinearMap
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, hδ, ω, x, rfl⟩
    refine ⟨C.regularize.expGaussianTrace hδ ω (C.regularizeInterEquiv.symm x), ?_⟩
    apply Subtype.ext
    refine Prod.ext (ZeroAtInftyContinuousMap.ext fun t => ?_)
      (ZeroAtInftyContinuousMap.ext fun t => ?_)
    · rw [LinearIsometry.coe_toLinearMap,
        regularizeStripTracesIsometry_apply_fst, expGaussianTrace_apply_fst,
        expGaussianTrace_apply_fst, SetLike.val_smul, coe_interFst_regularizeInterEquiv_symm]
    · rw [LinearIsometry.coe_toLinearMap,
        regularizeStripTracesIsometry_apply_snd, expGaussianTrace_apply_snd,
        expGaussianTrace_apply_snd, SetLike.val_smul, coe_interSnd_regularizeInterEquiv_symm]
  exact Set.range_eq_univ.1 <| hcl.closure_eq ▸ (C.dense_elementaryStripTraces.mono hsub).closure_eq

/-- **Regularization invariance of admissible traces.** When `X₀` and `X₁` are Banach spaces,
every admissible function for `(X₀, X₁)` arises from a unique admissible function for `(X₀°, X₁°)`
of equal trace norm. -/
def regularizeStripTracesEquiv [CompleteSpace X₀] [CompleteSpace X₁] :
    C.regularize.stripTraces ≃ₗᵢ[ℂ] C.stripTraces :=
  LinearIsometryEquiv.ofSurjective C.regularizeStripTracesIsometry
    (surjective_regularizeStripTracesIsometry C)

@[simp]
theorem regularizeStripTracesEquiv_apply [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.regularize.stripTraces) :
    C.regularizeStripTracesEquiv g = C.regularizeStripTracesIsometry g := (rfl)

namespace ComplexMethodSpace

variable {C} [CompleteSpace X₀] [CompleteSpace X₁]

private def regularizeInvMap (θ : ℝ) :
    C.ComplexMethodSpace θ →L[ℂ] C.regularize.ComplexMethodSpace θ :=
  lift ((mk θ).comp (C.regularizeStripTracesEquiv.symm.toContinuousLinearEquiv
      : C.stripTraces →L[ℂ] C.regularize.stripTraces))
    fun g hg => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [← map_zero (mk (C := C.regularize) θ), mk_eq_mk_iff, map_zero]
      apply C.regularizeSumMap_injective
      rw [map_zero, ← stripEval_regularizeStripTracesIsometry,
        ← regularizeStripTracesEquiv_apply, C.regularizeStripTracesEquiv.apply_symm_apply, hg]

@[simp]
private theorem regularizeInvMap_mk (θ : ℝ) (g : C.stripTraces) :
    regularizeInvMap θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) :=
  lift_mk _ _ g

private theorem regularizeInvMap_norm_le (θ : ℝ) (u : C.ComplexMethodSpace θ) :
    ‖regularizeInvMap θ u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [regularizeInvMap_mk]
  exact (norm_mk_le _).trans_lt ((C.regularizeStripTracesEquiv.symm.norm_map g).trans_lt hg)

/-- **Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)).** For any Banach couple
`(X₀, X₁)` and any `θ : ℝ`, passing to the endpoint closures `(X₀°, X₁°)` preserves the complex
interpolation space isometrically: `[X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`. -/
def regularizeEquiv (C : CompatibleCouple ℂ X₀ X₁ V) (θ : ℝ) :
    C.regularize.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.ComplexMethodSpace θ :=
  LinearIsometryEquiv.ofBounds
    { toFun := map θ C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C)
      invFun := regularizeInvMap θ
      left_inv u := by
        obtain ⟨g, rfl⟩ := mk_surjective u
        have hmap : stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
            (regularize_compat C) g = C.regularizeStripTracesEquiv g := rfl
        rw [map_mk, hmap, regularizeInvMap_mk, C.regularizeStripTracesEquiv.symm_apply_apply]
      right_inv u := by
        obtain ⟨g, rfl⟩ := mk_surjective u
        have hmap : stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
            (regularize_compat C) (C.regularizeStripTracesEquiv.symm g) = g :=
          C.regularizeStripTracesEquiv.apply_symm_apply g
        rw [regularizeInvMap_mk, map_mk, hmap]
      map_add' := map_add _
      map_smul' := map_smul _ }
    (norm_map_le_of_norm_le _ _ (regularize_compat C)
      (fun x => (Submodule.norm_coe x).le) (fun x => (Submodule.norm_coe x).le))
    (regularizeInvMap_norm_le θ)

@[simp]
theorem regularizeEquiv_mk (θ : ℝ) (g : C.regularize.stripTraces) :
    regularizeEquiv C θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv g) := by
  -- Unfold `regularizeEquiv` to its underlying `ComplexMethodSpace.map`.
  change map θ C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) (mk θ g) = _
  rw [map_mk]
  rfl

@[simp]
theorem regularizeEquiv_symm_mk (θ : ℝ) (g : C.stripTraces) :
    (regularizeEquiv C θ).symm (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) :=
  regularizeInvMap_mk θ g

/-- `regularizeEquiv` lies over `C.regularizeSumMap : X₀° + X₁° → X₀ + X₁`. -/
@[simp]
theorem toSum_regularizeEquiv (θ : ℝ) (u : C.regularize.ComplexMethodSpace θ) :
    toSum (regularizeEquiv C θ u) = C.regularizeSumMap (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [regularizeEquiv_mk, toSum_mk, toSum_mk, regularizeStripTracesEquiv_apply,
    stripEval_regularizeStripTracesIsometry]

/-- `regularizeEquiv` intertwines the inclusions of the intersections `X₀° ∩ X₁°` and `X₀ ∩ X₁`. -/
@[simp]
theorem regularizeEquiv_ofInter {θ : ℝ} (hθ : θ ∈ Icc 0 1) (y : C.regularize.inter) :
    regularizeEquiv C θ (ofInter θ y) = ofInter θ (C.regularizeInterEquiv y) := by
  ext
  rw [toSum_regularizeEquiv, toSum_ofInter hθ, toSum_ofInter hθ, regularizeSumMap_fstToSum,
    interFst_regularizeInterEquiv]

end ComplexMethodSpace

end Regularize

end TauCeti.CompatibleCouple
