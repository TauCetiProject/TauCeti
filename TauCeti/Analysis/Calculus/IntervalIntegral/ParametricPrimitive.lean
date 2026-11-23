/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Smoothness of parametric primitives

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

end intervalIntegral
