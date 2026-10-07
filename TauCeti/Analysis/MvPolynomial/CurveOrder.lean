/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.DirectionalOrder
public import TauCeti.Analysis.Analytic.Order

/-!
# Ambient polynomial order along analytic curves

An analytic curve through a point cannot lower the ambient order of a polynomial.
Together with a line detecting that order, this compares ambient orders under analytic
coordinate substitutions and multiplication by an analytic function. These comparisons allow
polynomial order to be transported through local coordinate changes, even when the coordinate
change itself is not polynomial.
-/

public section

open Filter Topology

namespace MvPolynomial

variable {𝕜 σ τ : Type*} [NontriviallyNormedField 𝕜]

/-- Evaluation along a coordinatewise analytic curve does not decrease ambient order.
The index type need not be finite: each polynomial uses only finitely many coordinates. -/
theorem orderAt_le_analyticOrderAt_eval (p : MvPolynomial σ 𝕜)
    {γ : 𝕜 → σ → 𝕜} {t₀ : 𝕜} (hγ : ∀ i, AnalyticAt 𝕜 (fun t ↦ γ t i) t₀) :
    p.orderAt (γ t₀) ≤ analyticOrderAt (fun t ↦ eval (γ t) p) t₀ := by
  classical
  let q := taylor (γ t₀) p
  let δ : σ → 𝕜 → 𝕜 := fun i t ↦ γ t i - γ t₀ i
  have hδ (i : σ) : AnalyticAt 𝕜 (δ i) t₀ := (hγ i).sub analyticAt_const
  have hδorder (i : σ) : 1 ≤ analyticOrderAt (δ i) t₀ := by
    apply Order.one_le_iff_ne_zero.2
    exact (hδ i).analyticOrderAt_ne_zero.2 (sub_self _)
  have heq : (fun t ↦ eval (γ t) p) = fun t ↦ eval (fun i ↦ δ i t) q := by
    funext t
    rw [eval_taylor]
    have hpoint : (fun i ↦ δ i t) + γ t₀ = γ t := by
      ext i
      simp [δ]
    rw [hpoint]
  rw [heq]
  -- Each nonzero Taylor monomial has at least the ambient order along the curve.
  conv_rhs =>
    arg 1
    ext t
    rw [q.as_sum, map_sum]
  rw [← Finset.sum_fn]
  refine Finset.sum_induction _
    (fun f : 𝕜 → 𝕜 ↦ p.orderAt (γ t₀) ≤ analyticOrderAt f t₀)
    (fun f g hf hg ↦ (le_min hf hg).trans le_analyticOrderAt_add) (by simp)
    fun d hd ↦ ?_
  have hdegree : p.orderAt (γ t₀) ≤ d.degree :=
    p.orderAt_le (mem_support_iff.1 hd)
  simp only [eval_monomial, Finsupp.prod]
  have hprod : AnalyticAt 𝕜 (fun t ↦ ∏ i ∈ d.support, δ i t ^ d i) t₀ := by
    simpa only [Finset.prod_fn, Pi.pow_apply] using
      Finset.analyticAt_prod d.support (fun i _ ↦ (hδ i).pow (d i))
  rw [← Pi.mul_def, analyticOrderAt_mul analyticAt_const hprod]
  refine hdegree.trans (le_trans ?_ le_add_self)
  rw [← Finset.prod_fn, TauCeti.analyticOrderAt_prod (F := fun i t ↦ δ i t ^ d i)
    (fun i _ ↦ (hδ i).pow (d i)),
    Finsupp.degree_apply, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← Pi.pow_def, analyticOrderAt_pow (hδ i)]
  simpa only [nsmul_one] using nsmul_le_nsmul_right (hδorder i) (d i)

/-- An analytic substitution and multiplication by an analytic function cannot lower ambient
polynomial order. The identity is required only near the comparison point. -/
theorem orderAt_le_of_analyticAt_mul_eq [Fintype σ]
    (p : MvPolynomial τ 𝕜) (q : MvPolynomial σ 𝕜) (a : σ → 𝕜)
    {g : (σ → 𝕜) → τ → 𝕜} {u : (σ → 𝕜) → 𝕜}
    (hg : ∀ i, AnalyticAt 𝕜 (fun x ↦ g x i) a) (hu : AnalyticAt 𝕜 u a)
    (heq : ∀ᶠ x in 𝓝 a, eval (g x) p * u x = eval x q) :
    p.orderAt (g a) ≤ q.orderAt a := by
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ((orderAt_eq_top_iff (p := q) (a := a)).not.2 hq)
  obtain ⟨v, hv⟩ := q.exists_eventually_analyticOrderAt_eval_add_smul_eq
    (φ := fun _ : 𝕜 ↦ a) (x₀ := 0) continuousAt_const (.of_forall fun _ ↦ hm.symm)
  -- Detect the order of `q` by a line, then pull that line through the substitution.
  have hline : AnalyticAt 𝕜 (fun t : 𝕜 ↦ a + t • v) 0 := by fun_prop
  have hga (i : τ) : AnalyticAt 𝕜 (fun t : 𝕜 ↦ g (a + t • v) i) 0 := by
    simpa only [Function.comp_def] using (hg i).comp_of_eq hline (by simp)
  have hua : AnalyticAt 𝕜 (fun t : 𝕜 ↦ u (a + t • v)) 0 := by
    simpa only [Function.comp_def] using hu.comp_of_eq hline (by simp)
  have hidentity := hline.continuousAt.tendsto.eventually (by simpa using heq)
  have horder := analyticOrderAt_congr hidentity
  rw [← Pi.mul_def, analyticOrderAt_mul
    (by simpa only [aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hga p) hua,
    hv.self_of_nhds] at horder
  have hbound := p.orderAt_le_analyticOrderAt_eval hga
  simp only [zero_smul, add_zero] at hbound
  exact (hbound.trans le_self_add).trans_eq (horder.trans hm)

end MvPolynomial
