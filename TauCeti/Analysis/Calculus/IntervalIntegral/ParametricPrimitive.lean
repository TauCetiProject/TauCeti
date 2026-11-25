/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Smoothness and derivatives of parametric primitives

If `f : H → ℝ → E` is jointly `C^n`, then so is its parametric primitive
`(x, b) ↦ ∫ t in a₀..b, f x t` (`intervalIntegral.contDiff_parametric_primitive_of_contDiff`).
This is the smooth counterpart of Mathlib's
`intervalIntegral.continuous_parametric_primitive_of_continuous`. Composing with a `C^n` map
`x ↦ (x, c x)` gives the smoothness of integrals `∫ t in a₀..c x, f x t` whose upper limit
depends on the parameter.

Smoothness also holds up to the boundary: if `f` is `C^n` on a product `s × t` of convex sets,
with `a₀ ∈ t` and `s` having unique derivatives, then the primitive is `C^n` on `s × t`
(`Convex.contDiffOn_parametric_primitive`). Neither set need be open. The proof rescales the
variable interval `[a₀, b]` to the fixed interval `[0, 1]`. The global statement is its case
`s = t = univ`.

Without a parameter one derivative is gained: the primitive `b ↦ ∫ t in a₀..b, f t` of a `C^n`
function `f : ℝ → E` is `C^{n+1}` (`intervalIntegral.contDiff_primitive_of_contDiff`), by the
fundamental theorem of calculus.

The file also differentiates parametric primitives when the integrand is only continuous, with a
jointly continuous derivative in the parameter
(`intervalIntegral.hasStrictFDerivAt_parametric_primitive`).
This is the **Leibniz integral rule** with a variable upper limit
(`intervalIntegral.hasFDerivAt_parametric_primitive_comp`, and
`intervalIntegral.hasDerivAt_parametric_primitive_comp` for a real parameter):

`d/dx ∫ t in a₀..c x, f x t = c'(x) f(x, c x) + ∫ t in a₀..c x, ∂ₓf(x, t)`.

The partial derivative in the parameter passes under the integral by Mathlib's
`intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv`, the partial derivative in the upper
limit is the fundamental theorem of calculus, and both are jointly continuous, so Mathlib's
criterion `hasStrictFDerivAt_uncurry_coprod` gives joint differentiability.
-/

public section

open MeasureTheory Set

namespace intervalIntegral

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- **Smoothness of a parametric primitive up to the boundary.** If `f` is `C^n` on `s × t`, where
`s` is convex with unique derivatives, `t` is convex and `a ∈ t`, then the primitive
`(x, y) ↦ ∫ r in a..y, f (x, r)` is `C^n` on `s × t`. Neither set need be open. -/
theorem _root_.Convex.contDiffOn_parametric_primitive {n : ℕ∞} {s : Set H} {t : Set ℝ} {a : ℝ}
    {f : H × ℝ → E} (hs : Convex ℝ s) (ht : Convex ℝ t) (hsu : UniqueDiffOn ℝ s) (ha : a ∈ t)
    (hf : ContDiffOn ℝ n f (s ×ˢ t)) :
    ContDiffOn ℝ n (fun p : H × ℝ ↦ ∫ r in a..p.2, f (p.1, r)) (s ×ˢ t) := by
  rcases t.subsingleton_or_nontrivial with htriv | hnt
  · exact contDiffOn_const.congr fun p hp ↦ by rw [htriv hp.2 ha, integral_same]
  have htu : UniqueDiffOn ℝ t := uniqueDiffOn_convex ht (ht.nontrivial_iff_nonempty_interior.1 hnt)
  have hW : UniqueDiffOn ℝ ((s ×ˢ t) ×ˢ Icc (0 : ℝ) 1) :=
    (hsu.prod htu).prod (uniqueDiffOn_Icc zero_lt_one)
  have hmaps : MapsTo (fun q : (H × ℝ) × ℝ ↦ (q.1.1, a + q.2 • (q.1.2 - a)))
      ((s ×ˢ t) ×ˢ Icc (0 : ℝ) 1) (s ×ˢ t) :=
    fun q hq ↦ ⟨hq.1.1, ht.add_smul_sub_mem ha hq.1.2 hq.2⟩
  have hF : ContDiffOn ℝ n (fun q : (H × ℝ) × ℝ ↦ (q.1.2 - a) • f (q.1.1, a + q.2 • (q.1.2 - a)))
      ((s ×ˢ t) ×ˢ Icc (0 : ℝ) 1) :=
    (contDiff_fst.snd.sub contDiff_const).contDiffOn.smul (hf.comp (by fun_prop) hmaps)
  refine ((hs.prod ht).contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure unitInterval))
    (g := fun _ ↦ (1 : ℝ)) (integrable_const 1) continuous_subtypeVal (hsu.prod htu) hW hF
    fun p hp τ ↦ ⟨hp, τ.property⟩).congr fun p _ ↦ ?_
  have h := smul_integral_comp_add_mul (fun r ↦ f (p.1, r)) (a := 0) (b := 1) (p.2 - a) a
  rw [mul_zero, add_zero, mul_one, add_sub_cancel] at h
  rw [← h, ← integral_smul, TauCeti.intervalIntegral_eq_integral_unitInterval]
  simp only [one_smul, smul_eq_mul, mul_comm]

/-- **Smoothness of a parametric primitive.** If `f : H → ℝ → E` is jointly `C^n`, then the
parametric primitive `(x, b) ↦ ∫ t in a₀..b, f x t` is `C^n`. -/
theorem contDiff_parametric_primitive_of_contDiff {f : H → ℝ → E} {n : ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (a₀ : ℝ) :
    ContDiff ℝ n fun p : H × ℝ ↦ ∫ t in a₀..p.2, f p.1 t :=
  contDiffOn_univ.1 <| by
    simpa only [univ_prod_univ, Function.uncurry_apply_pair] using
      Convex.contDiffOn_parametric_primitive convex_univ convex_univ uniqueDiffOn_univ
        (mem_univ a₀) (f := Function.uncurry f) (by simpa only [univ_prod_univ] using hf.contDiffOn)

/-- **Smoothness of a primitive.** If `f : ℝ → E` is `C^n`, then its primitive
`b ↦ ∫ t in a₀..b, f t` is `C^{n+1}`. -/
theorem contDiff_primitive_of_contDiff [CompleteSpace E] {f : ℝ → E} {n : ℕ∞}
    (hf : ContDiff ℝ n f) (a₀ : ℝ) : ContDiff ℝ (n + 1) fun b ↦ ∫ t in a₀..b, f t := by
  have hd : deriv (fun b ↦ ∫ t in a₀..b, f t) = f :=
    funext (hf.continuous.deriv_integral f a₀)
  exact contDiff_succ_iff_deriv.2
    ⟨differentiable_integral_of_continuous hf.continuous, by simp, by rwa [hd]⟩

/-- **Differentiation of a parametric primitive.** Let `f : H → ℝ → E` be jointly continuous and
differentiable in its first variable, with derivative `f' x t` jointly continuous in `(x, t)`. Then
the parametric primitive `(x, b) ↦ ∫ t in a₀..b, f x t` is strictly differentiable, with partial
derivative `∫ t in a₀..b, f' x t` in `x` and `f x b` in `b`. No differentiability in `t` is
needed. -/
theorem hasStrictFDerivAt_parametric_primitive [CompleteSpace E] {f : H → ℝ → E}
    {f' : H → ℝ → H →L[ℝ] E} (a₀ : ℝ) (hf : Continuous (Function.uncurry f))
    (hf' : ∀ x t, HasFDerivAt (f · t) (f' x t) x) (hf'c : Continuous (Function.uncurry f'))
    (p : H × ℝ) :
    HasStrictFDerivAt (fun p : H × ℝ ↦ ∫ t in a₀..p.2, f p.1 t)
      ((∫ t in a₀..p.2, f' p.1 t).coprod (ContinuousLinearMap.toSpanSingleton ℝ (f p.1 p.2)))
      p := by
  have hfx (x : H) : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
  have hfd : ∀ x t, fderiv ℝ (f · t) x = f' x t := fun x t ↦ (hf' x t).fderiv
  have h₁ (q : H × ℝ) :
      HasFDerivAt (fun x ↦ ∫ t in a₀..q.2, f x t) (∫ t in a₀..q.2, f' q.1 t) q.1 := by
    have h := hasFDerivAt_integral_of_continuousOn_fderiv (μ := volume) (f := f) (x₀ := q.1)
      (u := Set.univ) Filter.univ_mem (a := a₀) (b := q.2) hf.continuousOn
      (fun t _ x _ ↦ (hf' x t).differentiableAt.differentiableWithinAt)
      (by simp only [hfd]; exact hf'c.continuousOn)
    simpa only [hfd] using h
  have h₂ (q : H × ℝ) : HasFDerivAt (fun b ↦ ∫ t in a₀..b, f q.1 t)
      (ContinuousLinearMap.toSpanSingleton ℝ (f q.1 q.2)) q.2 :=
    ((hfx q.1).integral_hasStrictDerivAt a₀ q.2).hasDerivAt.hasFDerivAt
  have hc₂ : Continuous fun q : H × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ (f q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp hf
  exact hasStrictFDerivAt_uncurry_coprod (f := fun x b ↦ ∫ t in a₀..b, f x t)
    (f₁ := fun x b ↦ ∫ t in a₀..b, f' x t)
    (f₂ := fun x b ↦ ContinuousLinearMap.toSpanSingleton ℝ (f x b))
    (Filter.Eventually.of_forall h₁) (Filter.Eventually.of_forall h₂)
    (continuous_parametric_primitive_of_continuous hf'c).continuousAt hc₂.continuousAt

/-- **The Leibniz integral rule with a variable upper limit.** Let `f : H → ℝ → E` be jointly
continuous and differentiable in its first variable, with derivative `f' x t` jointly continuous in
`(x, t)`, and let the upper limit `c` have derivative `c'` at `x₀`. Then
`x ↦ ∫ t in a₀..c x, f x t` has derivative `(∫ t in a₀..c x₀, f' x₀ t) + c'.smulRight (f x₀ (c x₀))`
at `x₀`. -/
theorem hasFDerivAt_parametric_primitive_comp [CompleteSpace E] {f : H → ℝ → E}
    {f' : H → ℝ → H →L[ℝ] E} {c : H → ℝ} {c' : H →L[ℝ] ℝ} {x₀ : H} (a₀ : ℝ)
    (hf : Continuous (Function.uncurry f)) (hf' : ∀ x t, HasFDerivAt (f · t) (f' x t) x)
    (hf'c : Continuous (Function.uncurry f')) (hc : HasFDerivAt c c' x₀) :
    HasFDerivAt (fun x ↦ ∫ t in a₀..c x, f x t)
      ((∫ t in a₀..c x₀, f' x₀ t) + c'.smulRight (f x₀ (c x₀))) x₀ := by
  have h := (hasStrictFDerivAt_parametric_primitive a₀ hf hf' hf'c (x₀, c x₀)).hasFDerivAt.comp x₀
    ((hasFDerivAt_id x₀).prodMk hc)
  exact h.congr_fderiv (by ext v; simp)

/-- **The Leibniz integral rule with a variable upper limit**, for a real parameter. Let
`f : ℝ → ℝ → E` be jointly continuous and differentiable in its first variable, with derivative
`f' x t` jointly continuous in `(x, t)`, and let the upper limit `c` have derivative `c'` at `x₀`.
Then `d/dx ∫ t in a₀..c x, f x t = c' • f x₀ (c x₀) + ∫ t in a₀..c x₀, f' x₀ t` at `x₀`. -/
theorem hasDerivAt_parametric_primitive_comp [CompleteSpace E] {f f' : ℝ → ℝ → E} {c : ℝ → ℝ}
    {c' x₀ : ℝ} (a₀ : ℝ) (hf : Continuous (Function.uncurry f))
    (hf' : ∀ x t, HasDerivAt (f · t) (f' x t) x) (hf'c : Continuous (Function.uncurry f'))
    (hc : HasDerivAt c c' x₀) :
    HasDerivAt (fun x ↦ ∫ t in a₀..c x, f x t) (c' • f x₀ (c x₀) + ∫ t in a₀..c x₀, f' x₀ t)
      x₀ := by
  have hL : Continuous fun q : ℝ × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ (f' q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp hf'c
  have h := (hasFDerivAt_parametric_primitive_comp a₀ hf (fun x t ↦ (hf' x t).hasFDerivAt) hL
    hc.hasFDerivAt).hasDerivAt
  have hint : IntervalIntegrable (fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (f' x₀ t)) volume
      a₀ (c x₀) :=
    (hL.comp (Continuous.prodMk_right x₀)).intervalIntegrable _ _
  rw [add_apply, ContinuousLinearMap.intervalIntegral_apply hint] at h
  exact h.congr_deriv (by simp [add_comm])

end intervalIntegral
