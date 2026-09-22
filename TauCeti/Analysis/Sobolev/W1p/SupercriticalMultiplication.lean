/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.HolderEmbedding

import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.L1Convergence

/-!
# Multiplication in supercritical first-order Sobolev spaces

Let `E` have real dimension `n` and let `p > n`. Morrey's embedding gives every element of
`W^{1,p}(ℝⁿ)` a canonical bounded continuous representative. Consequently the pointwise
product of two Sobolev functions is again Sobolev, with the weak Leibniz rule

`grad (u * v) = u * grad v + v * grad u`.

This file packages that product on the whole-space Sobolev type, together with its representative-
and gradient-level characterizations and its basic algebraic laws.

In dimension two this is the Sobolev multiplication input used for nonlinear Cauchy--Riemann
operators on strips and surfaces. The dimension restriction is load-bearing: without an
`L^∞` bound on either factor, two `L^p` gradients cannot in general be multiplied by the other
factor and remain in `L^p`.

## Main declarations

* `TauCeti.W1p.hasWeakFDerivOn_mul_morreyRepresentative`: the weak Leibniz rule for the canonical
  Morrey representatives.
* `TauCeti.W1p.mul`: multiplication in `W^{1,p}(ℝⁿ)` for `p > n`.
* `TauCeti.W1p.value_mul_ae` and `TauCeti.W1p.gradient_mul_ae`: the characteristic formulas for
  the product.
* `TauCeti.W1p.norm_mul_le`: the multiplication estimate `‖u v‖ ≤ C ‖u‖ ‖v‖`, with `C` three times
  the operator norm of Morrey's embedding.
* `TauCeti.W1p.mulL`: the product as a bounded bilinear map on `W^{1,p}(ℝⁿ)`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.39.
* L. C. Evans, *Partial Differential Equations*, §5.6.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

private theorem W1p.norm_morreyRepresentative_le_embedding
    (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) (x : E) :
    ‖W1p.morreyRepresentative u hp x‖ ≤ ‖W1p.morreyEmbedding hp u‖ := by
  rw [← W1p.morreyEmbedding_apply_apply, ← HolderSpace.toBoundedContinuousFunction_apply]
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (W1p.morreyEmbedding hp u).toBoundedContinuousFunction x).trans
      (HolderSpace.norm_toBoundedContinuousFunction_le (W1p.morreyEmbedding hp u))

private theorem W1p.enorm_morreyRepresentative_le_embedding
    (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) (x : E) :
    ‖W1p.morreyRepresentative u hp x‖ₑ ≤ ‖W1p.morreyEmbedding hp u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (W1p.norm_morreyRepresentative_le_embedding hp u x)

private theorem W1p.enorm_morreyRepresentative_sub_le_embedding_sub
    (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) (x : E) :
    ‖W1p.morreyRepresentative u hp x - W1p.morreyRepresentative v hp x‖ₑ ≤
      ‖W1p.morreyEmbedding hp u - W1p.morreyEmbedding hp v‖ₑ := by
  calc
    _ = ‖(W1p.morreyEmbedding hp u - W1p.morreyEmbedding hp v) x‖ₑ := by
      rw [← W1p.morreyEmbedding_apply_apply hp u x,
        ← W1p.morreyEmbedding_apply_apply hp v x]
      rfl
    _ = ‖W1p.morreyRepresentative (u - v) hp x‖ₑ := by
      rw [← map_sub, W1p.morreyEmbedding_apply_apply]
    _ ≤ ‖W1p.morreyEmbedding hp (u - v)‖ₑ :=
      W1p.enorm_morreyRepresentative_le_embedding hp (u - v) x
    _ = ‖W1p.morreyEmbedding hp u - W1p.morreyEmbedding hp v‖ₑ := by rw [map_sub]

private theorem W1p.memLp_top_morreyRepresentative (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    MemLp (W1p.morreyRepresentative u hp) ∞ (mu.restrict (⊤ : Opens E)) := by
  refine ((W1p.morreyEmbedding hp u).toBoundedContinuousFunction.memLp_top
    (μ := mu.restrict (⊤ : Opens E))).ae_eq ?_
  filter_upwards with x
  rw [HolderSpace.toBoundedContinuousFunction_apply,
    W1p.morreyEmbedding_apply_apply]

private theorem W1p.memLp_mul_morreyRepresentative (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    MemLp (fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x)
      (p : ℝ≥0∞) (mu.restrict (⊤ : Opens E)) := by
  have h := MemLp.mul' (p := ∞) (q := (p : ℝ≥0∞)) (r := (p : ℝ≥0∞))
    (Lp.memLp (W1p.value v)) (W1p.memLp_top_morreyRepresentative hp u)
  refine h.ae_eq ?_
  have hv : W1p.value v =ᵐ[mu.restrict (⊤ : Opens E)]
      W1p.morreyRepresentative v hp := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      W1p.value_ae_eq_morreyRepresentative v hp
  filter_upwards [hv] with x hx
  rw [hx]

private theorem W1p.memLp_mulGradient_morreyRepresentative
    (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    MemLp (fun x => W1p.morreyRepresentative u hp x • W1p.gradient v x +
      W1p.morreyRepresentative v hp x • W1p.gradient u x) (p : ℝ≥0∞)
        (mu.restrict (⊤ : Opens E)) := by
  exact (MemLp.smul (p := ∞) (q := (p : ℝ≥0∞)) (r := (p : ℝ≥0∞))
    (Lp.memLp (W1p.gradient v)) (W1p.memLp_top_morreyRepresentative hp u)).add
      (MemLp.smul (p := ∞) (q := (p : ℝ≥0∞)) (r := (p : ℝ≥0∞))
        (Lp.memLp (W1p.gradient u)) (W1p.memLp_top_morreyRepresentative hp v))

private theorem W1p.morreyRepresentative_ofTestFunction
    (hp : (finrank ℝ E : ℝ≥0) < p) (phi : TestFunction (⊤ : Opens E) ℝ ⊤) :
    W1p.morreyRepresentative (W1p.ofTestFunctionₗ mu ⊤ (p : ℝ≥0∞) phi) hp = phi := by
  let _ : (mu.restrict ((⊤ : Opens E) : Set E)).IsOpenPosMeasure := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (inferInstance : mu.IsOpenPosMeasure)
  apply (Continuous.ae_eq_iff_eq (mu.restrict (⊤ : Opens E))
    (W1p.continuous_morreyRepresentative (W1p.ofTestFunctionₗ mu ⊤ (p : ℝ≥0∞) phi) hp)
    phi.contDiff.continuous).1
  refine ((W1p.value_ae_eq_morreyRepresentative
    (W1p.ofTestFunctionₗ mu ⊤ (p : ℝ≥0∞) phi) hp).symm.filter_mono
      (ae_mono Measure.restrict_le_self)).trans ?_
  rw [W1p.value_ofTestFunctionₗ]
  exact testFunctionLp_apply_ae (mu := mu) (p : ℝ≥0∞) phi

/-- **Weak Leibniz rule in the supercritical range.** If `p > dim E`, the product of the
canonical Morrey representatives of `u` and `v` has weak gradient
`u • ∇v + v • ∇u`.

The statement uses the canonical continuous representatives because multiplication is not
well-defined on arbitrary pointwise representatives of `L^p` classes. -/
theorem W1p.hasWeakFDerivOn_mul_morreyRepresentative
    (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    HasWeakFDerivOn mu ⊤
      (fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x)
      (fun x => innerSL ℝ (W1p.morreyRepresentative u hp x • W1p.gradient v x +
        W1p.morreyRepresentative v hp x • W1p.gradient u x)) := by
  have hpTop : (p : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  apply hasWeakFDerivOn_iff_forall_isCompact_closure.2
  intro V hVc hVtop
  have hVle : V ≤ (⊤ : Opens E) := le_top
  have hfin : IsFiniteMeasure (mu.restrict (V : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top⟩
  let _ := hfin
  -- Approximation setup: pick test functions `phi n` whose Sobolev classes `a n` converge to `u`.
  obtain ⟨a, ha_mem, ha_tendsto⟩ := mem_closure_iff_seq_limit.mp
    (W1p.denseRange_ofTestFunctionₗ_top (mu := mu) hpTop u)
  choose phi hphi using ha_mem
  -- Morrey's embedding is continuous, so the representatives converge uniformly: `ha_uniform`
  -- is the vanishing sup-norm error, the only control available on the factor `u`.
  have ha_morrey : Tendsto (fun n => W1p.morreyEmbedding hp (a n)) atTop
      (𝓝 (W1p.morreyEmbedding hp u)) :=
    ((W1p.morreyEmbedding (mu := mu) hp).continuous.tendsto u).comp ha_tendsto
  have ha_uniform : Tendsto (fun n => ‖W1p.morreyEmbedding hp (a n) -
      W1p.morreyEmbedding hp u‖ₑ) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => W1p.morreyEmbedding hp (a n) -
        W1p.morreyEmbedding hp u) atTop (𝓝 0) := by
      simpa only [sub_self] using ha_morrey.sub_const (W1p.morreyEmbedding hp u)
    simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hsub
  -- On the relatively compact `V` the gradients converge in `L¹`, by restriction and the
  -- finiteness of `mu` there.
  have hgrad : Tendsto (fun n => W1p.gradient (W1p.restrictL hVle (a n))) atTop
      (𝓝 (W1p.gradient (W1p.restrictL hVle u))) := by
    simpa only [Function.comp_def, W1p.gradientL_apply] using
      ((W1p.gradientL (mu := mu) (Omega := V) (p := (p : ℝ≥0∞))).continuous.tendsto
        (W1p.restrictL hVle u)).comp
          ((W1p.restrictL hVle).continuous.tendsto u |>.comp ha_tendsto)
  have hgrad1 : Tendsto (fun n => ∫⁻ x in (V : Set E),
      ‖W1p.gradient (a n) x - W1p.gradient u x‖ₑ ∂mu) atTop (𝓝 0) := by
    refine (tendsto_lintegral_enorm_sub_of_tendsto_Lp hgrad).congr fun n => ?_
    apply lintegral_congr_ae
    filter_upwards [W1p.gradient_restrictL_ae hVle (a n),
      W1p.gradient_restrictL_ae hVle u] with x han hu
    rw [han, hu]
  -- Local integrability bounds: `v` and its gradient have finite `L¹` norms on `V`, and the
  -- representative of `v` is bounded; these are the constants in the two error estimates.
  have hvVal : ∫⁻ x in (V : Set E), ‖W1p.value v x‖ₑ ∂mu ≠ ∞ := by
    have hm : MemLp (W1p.value v) 1 (mu.restrict (V : Set E)) :=
      ((Lp.memLp (W1p.value v)).mono_measure
        (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hVle))).mono_exponent Fact.out
    simpa only [eLpNorm_one_eq_lintegral_enorm, lt_top_iff_ne_top] using hm.2
  have hvGrad : ∫⁻ x in (V : Set E), ‖W1p.gradient v x‖ₑ ∂mu ≠ ∞ := by
    have hm : MemLp (W1p.gradient v) 1 (mu.restrict (V : Set E)) :=
      ((Lp.memLp (W1p.gradient v)).mono_measure
        (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hVle))).mono_exponent Fact.out
    simpa only [eLpNorm_one_eq_lintegral_enorm, lt_top_iff_ne_top] using hm.2
  have hvBound : ∀ x, ‖W1p.morreyRepresentative v hp x‖ₑ ≤
      ‖W1p.morreyEmbedding hp v‖ₑ := W1p.enorm_morreyRepresentative_le_embedding hp v
  -- The Leibniz rule is already available for the smooth factors `phi n`.
  have hchain : ∀ n, HasWeakFDerivOn mu V
      (fun x => (phi n : E → ℝ) x * W1p.value v x)
      (fun x => innerSL ℝ ((phi n : E → ℝ) x • W1p.gradient v x +
        W1p.value v x • ∇ (phi n : E → ℝ) x)) := by
    intro n
    exact ((W1p.hasWeakFDerivOn v).contDiff_smul_gradient (phi n).contDiff).mono hVle
  -- Value convergence: the error is `(phi n - u) v`, bounded by the uniform error times the
  -- finite `∫ ‖v‖` on `V`.
  have hvalueConv : Tendsto (fun n => ∫⁻ x in (V : Set E),
      ‖(phi n : E → ℝ) x * W1p.value v x -
        W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x‖ₑ ∂mu)
      atTop (𝓝 0) := by
    have hb : ∀ n, ∫⁻ x in (V : Set E),
        ‖(phi n : E → ℝ) x * W1p.value v x -
          W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x‖ₑ ∂mu ≤
        ‖W1p.morreyEmbedding hp (a n) - W1p.morreyEmbedding hp u‖ₑ *
          ∫⁻ x in (V : Set E), ‖W1p.value v x‖ₑ ∂mu := by
      intro n
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      refine lintegral_mono_ae ?_
      filter_upwards [(W1p.value_ae_eq_morreyRepresentative v hp).filter_mono
        (ae_mono Measure.restrict_le_self)] with x hv
      rw [← hv, ← sub_mul, enorm_mul]
      gcongr
      rw [← W1p.morreyRepresentative_ofTestFunction (mu := mu) hp (phi n), hphi n]
      exact W1p.enorm_morreyRepresentative_sub_le_embedding_sub hp (a n) u x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hb
    simpa using ENNReal.Tendsto.mul_const ha_uniform (Or.inr hvVal)
  -- Gradient convergence: the error splits into `(phi n - u) ∇v`, handled by the uniform error,
  -- and `v (∇(phi n) - ∇u)`, handled by the `L¹` gradient convergence on `V`.
  have hgradientConv : Tendsto (fun n => ∫⁻ x in (V : Set E),
      ‖innerSL ℝ ((phi n : E → ℝ) x • W1p.gradient v x +
          W1p.value v x • ∇ (phi n : E → ℝ) x) -
        innerSL ℝ (W1p.morreyRepresentative u hp x • W1p.gradient v x +
          W1p.morreyRepresentative v hp x • W1p.gradient u x)‖ₑ ∂mu)
      atTop (𝓝 0) := by
    have hb : ∀ n, ∫⁻ x in (V : Set E),
        ‖innerSL ℝ ((phi n : E → ℝ) x • W1p.gradient v x +
            W1p.value v x • ∇ (phi n : E → ℝ) x) -
          innerSL ℝ (W1p.morreyRepresentative u hp x • W1p.gradient v x +
            W1p.morreyRepresentative v hp x • W1p.gradient u x)‖ₑ ∂mu ≤
        ‖W1p.morreyEmbedding hp (a n) - W1p.morreyEmbedding hp u‖ₑ *
            ∫⁻ x in (V : Set E), ‖W1p.gradient v x‖ₑ ∂mu +
          ‖W1p.morreyEmbedding hp v‖ₑ * ∫⁻ x in (V : Set E),
            ‖W1p.gradient (a n) x - W1p.gradient u x‖ₑ ∂mu := by
      intro n
      have hres : mu.restrict (V : Set E) ≤ mu.restrict ((⊤ : Opens E) : Set E) :=
        Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hVle)
      have hmeas : AEMeasurable (fun x =>
          ‖W1p.morreyEmbedding hp (a n) - W1p.morreyEmbedding hp u‖ₑ *
            ‖W1p.gradient v x‖ₑ) (mu.restrict (V : Set E)) :=
        ((Lp.aestronglyMeasurable (W1p.gradient v)).mono_measure hres).enorm.const_mul _
      rw [← lintegral_const_mul' _ _ (by finiteness),
        ← lintegral_const_mul' _ _ (by finiteness), ← lintegral_add_left' hmeas]
      refine lintegral_mono_ae ?_
      filter_upwards [(W1p.value_ae_eq_morreyRepresentative v hp).filter_mono
          (ae_mono Measure.restrict_le_self),
        (gradientTestFunctionLp_apply_ae (mu := mu) (p : ℝ≥0∞) (phi n)).filter_mono
          (ae_mono hres)] with x hv hgradphi
      have hphiGrad : ∇ (phi n : E → ℝ) x = W1p.gradient (a n) x := by
        rw [← hphi n, W1p.gradient_ofTestFunctionₗ, hgradphi]
      rw [hv, hphiGrad, ← map_sub, ← ofReal_norm, innerSL_apply_norm, ofReal_norm]
      have hsplit :
          (phi n : E → ℝ) x • W1p.gradient v x +
              W1p.morreyRepresentative v hp x • W1p.gradient (a n) x -
            (W1p.morreyRepresentative u hp x • W1p.gradient v x +
              W1p.morreyRepresentative v hp x • W1p.gradient u x) =
            ((phi n : E → ℝ) x - W1p.morreyRepresentative u hp x) •
                W1p.gradient v x +
              W1p.morreyRepresentative v hp x •
                (W1p.gradient (a n) x - W1p.gradient u x) := by
        rw [sub_smul, smul_sub]
        abel
      rw [hsplit]
      refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [enorm_smul]
        gcongr
        rw [← W1p.morreyRepresentative_ofTestFunction (mu := mu) hp (phi n), hphi n]
        exact W1p.enorm_morreyRepresentative_sub_le_embedding_sub hp (a n) u x
      · rw [enorm_smul]
        gcongr
        exact hvBound x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hb
    have hleft := ENNReal.Tendsto.mul_const ha_uniform (Or.inr hvGrad)
    have hright := ENNReal.Tendsto.const_mul hgrad1
      (Or.inr (by finiteness : ‖W1p.morreyEmbedding hp v‖ₑ ≠ ∞))
    simpa using hleft.add hright
  -- The limiting value and gradient candidates are locally integrable, as required by the
  -- weak-derivative limit theorem.
  have hvalLoc : LocallyIntegrableOn
      (fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x)
      (⊤ : Opens E) mu := locallyIntegrableOn_of_locallyIntegrable_restrict
        ((W1p.memLp_mul_morreyRepresentative hp u v).locallyIntegrable Fact.out)
  have hgradLoc : ∀ w, LocallyIntegrableOn
      (fun x => innerSL ℝ (W1p.morreyRepresentative u hp x • W1p.gradient v x +
        W1p.morreyRepresentative v hp x • W1p.gradient u x) w) (⊤ : Opens E) mu := by
    intro w
    refine (locallyIntegrableOn_of_locallyIntegrable_restrict
      (((W1p.memLp_mulGradient_morreyRepresentative hp u v).const_inner
        (𝕜 := ℝ) w).locallyIntegrable Fact.out)).congr ?_
    filter_upwards with x
    simp only [innerSL_apply_apply, real_inner_comm]
  -- Final limit step: local `L¹` convergence of values and derivatives transfers the Leibniz
  -- rule from the approximations to the limit.
  exact hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (hvalLoc.mono_set hVle)
    (fun w => (hgradLoc w).mono_set hVle) hchain hvalueConv hgradientConv

/-- Multiplication of two whole-space `W^{1,p}` functions in the supercritical range `p > dim E`.
The value is the pointwise product of their canonical Morrey representatives. -/
def W1p.mul (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p mu ⊤ (p : ℝ≥0∞) :=
  W1p.mk ((W1p.memLp_mul_morreyRepresentative hp u v).toLp _)
    ((W1p.memLp_mulGradient_morreyRepresentative hp u v).toLp _)
    (((W1p.hasWeakFDerivOn_mul_morreyRepresentative hp u v).congr_ae
      (MemLp.coeFn_toLp _).symm).congr_ae_deriv (by
        filter_upwards [MemLp.coeFn_toLp
          (W1p.memLp_mulGradient_morreyRepresentative hp u v)] with x hx
        rw [hx]))

/-- The value of the supercritical Sobolev product is the pointwise product of the canonical
Morrey representatives. -/
theorem W1p.value_mul_ae (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.value (W1p.mul hp u v) =ᵐ[mu]
      fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x := by
  rw [W1p.mul, W1p.value_mk]
  simpa only [Opens.coe_top, Measure.restrict_univ] using MemLp.coeFn_toLp
    (W1p.memLp_mul_morreyRepresentative hp u v)

/-- The canonical Morrey representative of a supercritical Sobolev product is the pointwise
product of the representatives. -/
@[simp]
theorem W1p.morreyRepresentative_mul (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.morreyRepresentative (W1p.mul hp u v) hp =
      W1p.morreyRepresentative u hp * W1p.morreyRepresentative v hp := by
  apply (Continuous.ae_eq_iff_eq mu
    (W1p.continuous_morreyRepresentative (W1p.mul hp u v) hp)
    ((W1p.continuous_morreyRepresentative u hp).mul
      (W1p.continuous_morreyRepresentative v hp))).1
  refine (W1p.value_ae_eq_morreyRepresentative (W1p.mul hp u v) hp).symm.trans ?_
  filter_upwards [W1p.value_mul_ae hp u v] with x hx
  simpa only [Pi.mul_apply] using hx

/-- The weak gradient of the supercritical Sobolev product satisfies the Leibniz rule. -/
theorem W1p.gradient_mul_ae (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.gradient (W1p.mul hp u v) =ᵐ[mu]
      fun x => W1p.morreyRepresentative u hp x • W1p.gradient v x +
        W1p.morreyRepresentative v hp x • W1p.gradient u x := by
  rw [W1p.mul, W1p.gradient_mk]
  simpa only [Opens.coe_top, Measure.restrict_univ] using MemLp.coeFn_toLp
    (W1p.memLp_mulGradient_morreyRepresentative hp u v)

/-- Supercritical Sobolev multiplication is commutative. -/
theorem W1p.mul_comm (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) : W1p.mul hp u v = W1p.mul hp v u := by
  apply W1p.ext_value
  apply Lp.ext
  have hae : W1p.value (W1p.mul hp u v) =ᵐ[mu] W1p.value (W1p.mul hp v u) := by
    filter_upwards [W1p.value_mul_ae hp u v, W1p.value_mul_ae hp v u] with x huv hvu
    rw [huv, hvu, _root_.mul_comm]
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

/-- Supercritical Sobolev multiplication distributes over addition in the second factor. -/
theorem W1p.mul_add (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v w : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp u (v + w) = W1p.mul hp u v + W1p.mul hp u w := by
  apply W1p.ext_value
  rw [← W1p.valueL_apply (W1p.mul hp u v + W1p.mul hp u w), map_add,
    W1p.valueL_apply, W1p.valueL_apply]
  apply Lp.ext
  have h₀ : W1p.value (W1p.mul hp u (v + w)) =ᵐ[mu.restrict (⊤ : Opens E)]
      fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative (v + w) hp x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.value_mul_ae hp u (v + w)
  have h₁ : W1p.value (W1p.mul hp u v) =ᵐ[mu.restrict (⊤ : Opens E)]
      fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.value_mul_ae hp u v
  have h₂ : W1p.value (W1p.mul hp u w) =ᵐ[mu.restrict (⊤ : Opens E)]
      fun x => W1p.morreyRepresentative u hp x * W1p.morreyRepresentative w hp x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.value_mul_ae hp u w
  filter_upwards [h₀, h₁, h₂, Lp.coeFn_add (W1p.value (W1p.mul hp u v))
    (W1p.value (W1p.mul hp u w))] with x huv hv hw hadd
  rw [huv, hadd, Pi.add_apply, hv, hw, W1p.morreyRepresentative_add, Pi.add_apply,
    _root_.mul_add]

/-- Supercritical Sobolev multiplication distributes over addition in the first factor. -/
theorem W1p.add_mul (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v w : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp (u + v) w = W1p.mul hp u w + W1p.mul hp v w := by
  rw [W1p.mul_comm hp (u + v), W1p.mul_add, W1p.mul_comm hp w u, W1p.mul_comm hp w v]

/-- Supercritical Sobolev multiplication is associative. -/
theorem W1p.mul_assoc (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v w : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp (W1p.mul hp u v) w = W1p.mul hp u (W1p.mul hp v w) := by
  apply W1p.morreyEmbedding_injective hp
  ext x
  simp only [W1p.morreyEmbedding_apply_apply, W1p.morreyRepresentative_mul, Pi.mul_apply,
    _root_.mul_assoc]

/-- Multiplication by zero on the right is zero. -/
@[simp]
theorem W1p.mul_zero (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp u 0 = 0 := by
  apply W1p.morreyEmbedding_injective hp
  ext x
  rw [W1p.morreyEmbedding_apply_apply, W1p.morreyEmbedding_apply_apply,
    W1p.morreyRepresentative_mul, W1p.morreyRepresentative_zero]
  simp only [Pi.mul_apply, Pi.zero_apply]
  ring

/-- Multiplication by zero on the left is zero. -/
@[simp]
theorem W1p.zero_mul (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp 0 u = 0 := by
  rw [W1p.mul_comm, W1p.mul_zero]

/-- Scalar multiplication can be pulled out of the right factor. -/
theorem W1p.mul_smul_comm (hp : (finrank ℝ E : ℝ≥0) < p) (c : ℝ)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp u (c • v) = c • W1p.mul hp u v := by
  apply W1p.morreyEmbedding_injective hp
  ext x
  simp only [W1p.morreyEmbedding_apply_apply, W1p.morreyRepresentative_mul,
    W1p.morreyRepresentative_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scalar multiplication can be pulled out of the left factor. -/
theorem W1p.smul_mul_assoc (hp : (finrank ℝ E : ℝ≥0) < p) (c : ℝ)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mul hp (c • u) v = c • W1p.mul hp u v := by
  rw [W1p.mul_comm hp (c • u), W1p.mul_smul_comm, W1p.mul_comm hp v u]

/-! ### The multiplication estimate -/

/-- The norm of an `Lᵖ` function dominated pointwise by a two-term combination of two other `Lᵖ`
functions obeys the same bound in norm.

Kept `private`: the natural home for this generic `Lp` fact is the root `MeasureTheory.Lp`
namespace, which is unreachable from inside `namespace TauCeti`, and its only use is the
multiplication estimate below. -/
private theorem norm_le_add_of_ae_norm_le {alpha F G H : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H] {m : Measure alpha}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp F q m} {g : Lp G q m} {h : Lp H q m} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hle : ∀ᵐ z ∂m, ‖f z‖ ≤ a * ‖g z‖ + b * ‖h z‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  obtain ⟨A, hAnorm, hAcoe⟩ : ∃ A : Lp ℝ q m, ‖A‖ = ‖g‖ ∧ ∀ᵐ z ∂m, A z = ‖g z‖ :=
    ⟨(Lp.memLp g).norm.toLp _, by rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def],
      (Lp.memLp g).norm.coeFn_toLp⟩
  obtain ⟨B, hBnorm, hBcoe⟩ : ∃ B : Lp ℝ q m, ‖B‖ = ‖h‖ ∧ ∀ᵐ z ∂m, B z = ‖h z‖ :=
    ⟨(Lp.memLp h).norm.toLp _, by rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def],
      (Lp.memLp h).norm.coeFn_toLp⟩
  calc ‖f‖ ≤ ‖a • A + b • B‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [hle, hAcoe, hBcoe, Lp.coeFn_add (a • A) (b • B), Lp.coeFn_smul a A,
          Lp.coeFn_smul b B] with z hz hA hB hadd hsA hsB
        rw [hadd, Pi.add_apply, hsA, hsB, Pi.smul_apply, Pi.smul_apply, hA, hB, smul_eq_mul,
          smul_eq_mul, Real.norm_of_nonneg (add_nonneg (mul_nonneg ha (norm_nonneg _))
            (mul_nonneg hb (norm_nonneg _)))]
        exact hz
    _ ≤ ‖a • A‖ + ‖b • B‖ := norm_add_le _ _
    _ = a * ‖g‖ + b * ‖h‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hAnorm, hBnorm]

/-- The pointwise bound behind the multiplication estimate: the value-gradient jet of a product is
dominated by the supremum norms of the Morrey representatives against the jets of the factors. -/
private theorem W1p.norm_coe_mul_le_ae (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    ∀ᵐ x ∂mu.restrict ((⊤ : Opens E) : Set E),
      ‖(W1p.mul hp u v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ ≤
        2 * ‖W1p.morreyEmbedding hp u‖ * ‖(v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ +
          ‖W1p.morreyEmbedding hp v‖ * ‖(u : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ := by
  filter_upwards [W1p.value_apply_ae (W1p.mul hp u v),
      W1p.gradient_apply_ae (W1p.mul hp u v), W1p.value_apply_ae v, W1p.gradient_apply_ae v,
      W1p.gradient_apply_ae u,
      (W1p.value_mul_ae hp u v).filter_mono (ae_mono Measure.restrict_le_self),
      (W1p.gradient_mul_ae hp u v).filter_mono (ae_mono Measure.restrict_le_self),
      (W1p.value_ae_eq_morreyRepresentative v hp).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hfst hsnd hvfst hvsnd husnd hvalue hgradient hvrep
  have hu0 : ‖W1p.morreyRepresentative u hp x‖ ≤ ‖W1p.morreyEmbedding hp u‖ :=
    W1p.norm_morreyRepresentative_le_embedding hp u x
  have hv0 : ‖W1p.morreyRepresentative v hp x‖ ≤ ‖W1p.morreyEmbedding hp v‖ :=
    W1p.norm_morreyRepresentative_le_embedding hp v x
  have hvvalue : ‖W1p.morreyRepresentative v hp x‖ ≤
      ‖(v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ := by
    rw [← hvrep, hvfst]
    exact WithLp.norm_fst_le (x := (v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x)
  have hvgrad : ‖W1p.gradient v x‖ ≤ ‖(v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ := by
    rw [hvsnd]
    exact WithLp.norm_snd_le (x := (v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x)
  have hugrad : ‖W1p.gradient u x‖ ≤ ‖(u : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ := by
    rw [husnd]
    exact WithLp.norm_snd_le (x := (u : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x)
  calc ‖(W1p.mul hp u v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖
      ≤ ‖WithLp.fst ((W1p.mul hp u v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x)‖ +
        ‖WithLp.snd ((W1p.mul hp u v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x)‖ :=
      WithLp.prod_norm_le_norm_fst_add_norm_snd _
    _ = ‖W1p.morreyRepresentative u hp x * W1p.morreyRepresentative v hp x‖ +
        ‖W1p.morreyRepresentative u hp x • W1p.gradient v x +
          W1p.morreyRepresentative v hp x • W1p.gradient u x‖ := by
      rw [← hfst, ← hsnd, hvalue, hgradient]
    _ ≤ ‖W1p.morreyEmbedding hp u‖ * ‖(v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ +
        (‖W1p.morreyEmbedding hp u‖ * ‖(v : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖ +
          ‖W1p.morreyEmbedding hp v‖ * ‖(u : Sobolev1JetLp mu ⊤ (p : ℝ≥0∞)) x‖) := by
      refine add_le_add ?_ ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      · rw [norm_mul]
        exact mul_le_mul hu0 hvvalue (norm_nonneg _) (norm_nonneg _)
      · rw [norm_smul]
        exact mul_le_mul hu0 hvgrad (norm_nonneg _) (norm_nonneg _)
      · rw [norm_smul]
        exact mul_le_mul hv0 hugrad (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- **The supercritical Sobolev multiplication estimate.** The `W^{1,p}` norm of a product is at
most three times the operator norm of Morrey's embedding times the product of the norms of the
factors. The embedding norm is what enters because the only control on a factor outside `L^p` is
the supremum norm of its Morrey representative. -/
theorem W1p.norm_mul_le (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    ‖W1p.mul hp u v‖ ≤ 3 * ‖W1p.morreyEmbedding (mu := mu) hp‖ * ‖u‖ * ‖v‖ := by
  calc ‖W1p.mul hp u v‖
      ≤ 2 * ‖W1p.morreyEmbedding hp u‖ * ‖v‖ + ‖W1p.morreyEmbedding hp v‖ * ‖u‖ :=
        norm_le_add_of_ae_norm_le (by positivity) (norm_nonneg _)
          (W1p.norm_coe_mul_le_ae hp u v)
    _ ≤ 2 * (‖W1p.morreyEmbedding (mu := mu) hp‖ * ‖u‖) * ‖v‖ +
        ‖W1p.morreyEmbedding (mu := mu) hp‖ * ‖v‖ * ‖u‖ := by
      gcongr <;> exact (W1p.morreyEmbedding hp).le_opNorm _
    _ = 3 * ‖W1p.morreyEmbedding (mu := mu) hp‖ * ‖u‖ * ‖v‖ := by ring

/-- **Supercritical Sobolev multiplication as a bounded bilinear map** on `W^{1,p}(ℝⁿ)`. Its
bound is `TauCeti.W1p.norm_mul_le`, and multiplication by a fixed factor is a bounded operator by
`TauCeti.W1p.norm_mulL_apply_le`. This is the form the nonlinear estimates use, where a product
must be differentiated and estimated in the Sobolev norm at once. -/
def W1p.mulL (hp : (finrank ℝ E : ℝ≥0) < p) :
    W1p mu ⊤ (p : ℝ≥0∞) →L[ℝ] W1p mu ⊤ (p : ℝ≥0∞) →L[ℝ] W1p mu ⊤ (p : ℝ≥0∞) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (W1p.mul hp) (W1p.add_mul hp) (W1p.smul_mul_assoc hp) (W1p.mul_add hp)
      (W1p.mul_smul_comm hp))
    (3 * ‖W1p.morreyEmbedding (mu := mu) hp‖) (W1p.norm_mul_le hp)

-- Deliberately not a `@[simp]` lemma: the carrier of `W1p mu ⊤ p` mentions `mu.restrict ↑⊤`, which
-- `simp` normalizes to `mu.restrict Set.univ` inside the coercion's implicit arguments, so this
-- left-hand side is not in simp-normal form and the rewrite never fires in a full `simp` run.
-- Use it through `simp only`/`rw`, as `TauCeti.W1p.norm_mulL_apply_le` does.
theorem W1p.mulL_apply (hp : (finrank ℝ E : ℝ≥0) < p) (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.mulL hp u v = W1p.mul hp u v :=
  (rfl)

/-- Multiplication by a fixed `u` is a bounded operator on `W^{1,p}(ℝⁿ)`, of norm at most three
times the operator norm of Morrey's embedding times `‖u‖`. -/
theorem W1p.norm_mulL_apply_le (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    ‖W1p.mulL hp u‖ ≤ 3 * ‖W1p.morreyEmbedding (mu := mu) hp‖ * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
    simpa only [W1p.mulL_apply] using W1p.norm_mul_le hp u v

end TauCeti
