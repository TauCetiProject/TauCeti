/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
public import TauCeti.Probability.Concentration.EfronStein
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Gaussian Poincaré inequality

This file proves the Poincaré inequality `Var f(G) ≤ E ‖∇f(G)‖²` for the standard Gaussian law,
on `ℝ` and on `Fin n → ℝ` with the product law, for continuously differentiable functions with
bounded values and bounded (partial) derivatives.

The one-dimensional proof is Gaussian interpolation. For two independent standard Gaussians `X, Z`
and `Y_θ = cos θ • X + sin θ • Z` the function `ψ θ = E f(X) f(Y_θ)` runs from `E f²` at `θ = 0` to
`(E f)²` at `θ = π / 2`, and `ψ' θ = -sin θ • E f'(X) f'(Y_θ)`, by Gaussian integration by parts
after the rotation `(X, Z) ↦ (Y_θ, sin θ • X - cos θ • Z)`, which preserves the Gaussian product
law. Since `E f'(X) f'(Y_θ) ≤ E f'²`, the function `ψ θ + E f'² (1 - cos θ)` is monotone on
`[0, π / 2]`, which gives `Var f ≤ E f'²`. The `n`-dimensional inequality follows by tensorization
from the Efron–Stein inequality `efronStein`.

## Main results

* `TauCeti.Probability.variance_le_integral_deriv_sq_gaussianReal`: the Poincaré inequality for
  `gaussianReal 0 1`;
* `TauCeti.Probability.variance_le_sum_integral_fderiv_sq_pi`: the Poincaré inequality for the
  product of `n` standard Gaussian laws;
* `TauCeti.Probability.measurePreserving_orthogonal_gaussianReal`: invariance of the Gaussian
  product law on `ℝ × ℝ` under orthogonal maps;
* `TauCeti.Probability.integral_integral_update_pi`: resampling one coordinate preserves
  expectations under `Measure.pi`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- The characteristic function of the standard Gaussian law at a continuous linear functional. -/
theorem charFunDual_gaussianReal_zero_one (ℓ : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) ℓ = Complex.exp (-((ℓ 1 : ℝ) : ℂ) ^ 2 / 2) := by
  have h : ∀ x : ℝ, ℓ x = ℓ 1 * x := fun x => by
    simpa [mul_comm] using ℓ.map_smul x 1
  have key := charFun_gaussianReal (μ := 0) (v := 1) (ℓ 1)
  rw [charFun_apply_real] at key
  rw [charFunDual_apply]
  convert key using 1
  · congr 1
    funext x
    rw [h x]
    push_cast
    ring_nf
  · simp [neg_div]

/-- The standard Gaussian product law on `ℝ × ℝ` is invariant under the orthogonal map
`(x, z) ↦ (c x + s z, s x - c z)` when `c ^ 2 + s ^ 2 = 1`. -/
theorem measurePreserving_orthogonal_gaussianReal {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    MeasurePreserving (fun p : ℝ × ℝ => (c * p.1 + s * p.2, s * p.1 - c * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let M : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((c • ContinuousLinearMap.fst ℝ ℝ ℝ + s • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (s • ContinuousLinearMap.fst ℝ ℝ ℝ - c • ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hM : (fun p : ℝ × ℝ => (c * p.1 + s * p.2, s * p.1 - c * p.2)) = M := by
    ext p <;> simp [M]
  rw [hM]
  refine ⟨M.continuous.measurable, ?_⟩
  refine ((charFunDual_eq_prod_iff (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (ξ := ((gaussianReal 0 1).prod (gaussianReal 0 1)).map M)).1 fun L => ?_)
  rw [charFunDual_map, charFunDual_prod]
  simp only [charFunDual_gaussianReal_zero_one, ← Complex.exp_add]
  congr 1
  have h1 : L (c, s) = c * L (1, 0) + s * L (0, 1) := by
    have : ((c, s) : ℝ × ℝ) = c • ((1, 0) : ℝ × ℝ) + s • ((0, 1) : ℝ × ℝ) := by simp
    rw [this, map_add, map_smul, map_smul]
    simp
  have h2 : L (s, -c) = s * L (1, 0) - c * L (0, 1) := by
    have : ((s, -c) : ℝ × ℝ) = s • ((1, 0) : ℝ × ℝ) - c • ((0, 1) : ℝ × ℝ) := by simp
    rw [this, map_sub, map_smul, map_smul]
    simp
  have h3 : ((L.comp M).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) : StrongDual ℝ ℝ) 1 =
      c * L (1, 0) + s * L (0, 1) := by
    rw [← h1]; simp [M]
  have h4 : ((L.comp M).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) : StrongDual ℝ ℝ) 1 =
      s * L (1, 0) - c * L (0, 1) := by
    rw [← h2]; simp [M]
  have h5 : (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ) : StrongDual ℝ ℝ) 1 = L (1, 0) := by simp
  have h6 : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) : StrongDual ℝ ℝ) 1 = L (0, 1) := by simp
  rw [h3, h4, h5, h6]
  have hC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  push_cast
  linear_combination (-((L (1, 0) : ℂ) ^ 2 + (L (0, 1) : ℂ) ^ 2) / 2) * hC

local notation "γ" => gaussianReal 0 1

section Interpolation

variable {f : ℝ → ℝ} {A B : ℝ}

private theorem integrable_abs_gaussianReal : Integrable (fun x : ℝ => |x|) γ := by
  have := ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable le_rfl).norm
  simpa using this

private theorem integrable_abs_add_abs :
    Integrable (fun p : ℝ × ℝ => |p.1| + |p.2|) (Measure.prod γ γ) := by
  have h1 : Integrable (fun p : ℝ × ℝ => |p.1|) (Measure.prod γ γ) :=
    (measurePreserving_fst (μ := γ) (ν := γ)).integrable_comp
      integrable_abs_gaussianReal.aestronglyMeasurable |>.2 integrable_abs_gaussianReal
  have h2 : Integrable (fun p : ℝ × ℝ => |p.2|) (Measure.prod γ γ) :=
    (measurePreserving_snd (μ := γ) (ν := γ)).integrable_comp
      integrable_abs_gaussianReal.aestronglyMeasurable |>.2 integrable_abs_gaussianReal
  exact h1.add h2

/-- Gaussian integration by parts for `x * f (a + s * x)`. -/
private theorem integral_mul_comp_affine (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (a s : ℝ) :
    ∫ v, v * f (a + s * v) ∂γ = s * ∫ v, deriv f (a + s * v) ∂γ := by
  have hc : Continuous f := hf.continuous
  have hc' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hd : ∀ v, HasDerivAt (fun v => f (a + s * v)) (deriv f (a + s * v) * s) v := fun v => by
    have h1 : HasDerivAt (fun v : ℝ => a + s * v) s v := by
      simpa using ((hasDerivAt_id v).const_mul s).const_add a
    exact (hf.differentiable one_ne_zero (a + s * v)).hasDerivAt.comp v h1
  have hder : deriv (fun v => f (a + s * v)) = fun v => deriv f (a + s * v) * s :=
    funext fun v => (hd v).deriv
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have key := integral_mul_eq_integral_deriv_gaussianReal (fun v => f (a + s * v))
    (fun v => (hd v).differentiableAt)
    (by
      refine (integrable_abs_gaussianReal.const_mul A).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _) |>.trans_eq (mul_comm _ _))
    (by
      rw [hder]
      refine (integrable_const (B * |s|)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _))
  rw [key, hder]
  simp_rw [mul_comm (deriv f _) s]
  exact integral_const_mul s _

private theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (h : ∀ x, |g x| ≤ C) : Integrable g μ :=
  (integrable_const C).mono' hg (ae_of_all _ fun x => by simpa using h x)

private theorem integral_comp_of_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {T : α → β}
    (hT : MeasurePreserving T μ ν) {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    ∫ a, g (T a) ∂μ = ∫ b, g b ∂ν := by
  rw [← hT.map_eq]
  exact (integral_map hT.measurable.aemeasurable (hT.map_eq ▸ hg)).symm

private theorem hasDerivAt_interp (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (θ : ℝ) :
    HasDerivAt (fun θ => ∫ p, f p.1 * f (cos θ * p.1 + sin θ * p.2) ∂(Measure.prod γ γ))
      (∫ p, f p.1 * (deriv f (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ)) θ := by
  have hc : Continuous f := hf.continuous
  have hc' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun θ (p : ℝ × ℝ) => f p.1 * f (cos θ * p.1 + sin θ * p.2))
    (F' := fun θ (p : ℝ × ℝ) =>
      f p.1 * (deriv f (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2)))
    (x₀ := θ) (bound := fun p => A * B * (|p.1| + |p.2|)) (s := Set.univ) Filter.univ_mem
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun t => (by fun_prop : Continuous _).aestronglyMeasurable
  · refine integrable_of_abs_le (C := A * A) (by fun_prop : Continuous _).aestronglyMeasurable
      fun p => ?_
    rw [abs_mul]
    exact mul_le_mul (hA _) (hA _) (abs_nonneg _) hA0
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine ae_of_all _ fun p t _ => ?_
    have hw : |-sin t * p.1 + cos t * p.2| ≤ |p.1| + |p.2| := by
      calc |-sin t * p.1 + cos t * p.2| ≤ |-sin t * p.1| + |cos t * p.2| := abs_add_le _ _
        _ = |sin t| * |p.1| + |cos t| * |p.2| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ 1 * |p.1| + 1 * |p.2| := by
          gcongr
          · exact abs_sin_le_one t
          · exact abs_cos_le_one t
        _ = |p.1| + |p.2| := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |f p.1| * (|deriv f (cos t * p.1 + sin t * p.2)| * |-sin t * p.1 + cos t * p.2|)
        ≤ A * (B * (|p.1| + |p.2|)) := by gcongr <;> first | exact hA _ | exact hB _
      _ = A * B * (|p.1| + |p.2|) := by ring
  · exact integrable_abs_add_abs.const_mul (A * B)
  · refine ae_of_all _ fun p t _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => cos t * p.1 + sin t * p.2)
        (-sin t * p.1 + cos t * p.2) t :=
      ((hasDerivAt_cos t).mul_const p.1).add ((hasDerivAt_sin t).mul_const p.2)
    exact ((hf.differentiable one_ne_zero _).hasDerivAt.comp t h1).const_mul (f p.1)

private theorem integral_interp_deriv (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (θ : ℝ) :
    ∫ p, f p.1 * (deriv f (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ) =
      -sin θ * ∫ p, deriv f p.1 * deriv f (cos θ * p.1 + sin θ * p.2) ∂(Measure.prod γ γ) := by
  have hc : Continuous f := hf.continuous
  have hc' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨c, hcdef⟩ : ∃ c, c = cos θ := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = sin θ := ⟨_, rfl⟩
  rw [← hcdef, ← hsdef]
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hcdef, hsdef]; exact cos_sq_add_sin_sq θ
  have hmp := measurePreserving_orthogonal_gaussianReal hcs
  let H : ℝ × ℝ → ℝ := fun q => f (c * q.1 + s * q.2) * (deriv f q.1 * (-q.2))
  have hHc : Continuous H := by fun_prop
  have hHint : Integrable H (Measure.prod γ γ) := by
    refine (integrable_abs_add_abs.const_mul (A * B)).mono' hHc.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs]
    simp only [H, abs_mul, abs_neg]
    calc |f (c * q.1 + s * q.2)| * (|deriv f q.1| * |q.2|)
        ≤ A * (B * (|q.1| + |q.2|)) := by
          gcongr
          · exact hA _
          · exact hB _
          · exact le_add_of_nonneg_left (abs_nonneg _)
      _ = A * B * (|q.1| + |q.2|) := by ring
  have e1 : (fun p : ℝ × ℝ =>
      f p.1 * (deriv f (c * p.1 + s * p.2) * (-s * p.1 + c * p.2))) =
      fun p => H (c * p.1 + s * p.2, s * p.1 - c * p.2) := by
    funext p
    simp only [H]
    rw [show c * (c * p.1 + s * p.2) + s * (s * p.1 - c * p.2) = p.1 by
      linear_combination p.1 * hcs]
    ring
  rw [e1, integral_comp_of_measurePreserving hmp hHc.aestronglyMeasurable,
    integral_prod _ hHint]
  have hinner : ∀ u : ℝ, ∫ v, H (u, v) ∂γ = -s * (deriv f u * ∫ v, deriv f (c * u + s * v) ∂γ) := by
    intro u
    have : ∀ v : ℝ, H (u, v) = -(deriv f u) * (v * f (c * u + s * v)) := fun v => by
      simp only [H]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_mul_comp_affine hf hA hB]
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  congr 1
  have hint : Integrable (fun p : ℝ × ℝ => deriv f p.1 * deriv f (c * p.1 + s * p.2))
      (Measure.prod γ γ) :=
    integrable_of_abs_le (C := B * B) (by fun_prop : Continuous _).aestronglyMeasurable
      fun p => by
        rw [abs_mul]
        exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
  rw [integral_prod _ hint]
  congr 1
  funext u
  exact (integral_const_mul _ _).symm

end Interpolation

/-- **The Gaussian Poincaré inequality on `ℝ`.** For a continuously differentiable function `f`
with bounded values and bounded derivative, the variance of `f` under the standard Gaussian law is
at most the expectation of `(f')²`. The constant `1` is optimal, as `f = id` shows. -/
theorem variance_le_integral_deriv_sq_gaussianReal {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfb : ∃ A, ∀ x, |f x| ≤ A) (hdb : ∃ B, ∀ x, |deriv f x| ≤ B) :
    variance f γ ≤ ∫ x, deriv f x ^ 2 ∂γ := by
  obtain ⟨A, hA⟩ := hfb
  obtain ⟨B, hB⟩ := hdb
  have hc : Continuous f := hf.continuous
  have hc' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨D, hD⟩ : ∃ D, D = ∫ x, deriv f x ^ 2 ∂γ := ⟨_, rfl⟩
  rw [← hD]
  let ψ : ℝ → ℝ := fun θ =>
    ∫ p, f p.1 * f (cos θ * p.1 + sin θ * p.2) ∂(Measure.prod γ γ)
  let J : ℝ → ℝ := fun θ =>
    ∫ p, deriv f p.1 * deriv f (cos θ * p.1 + sin θ * p.2) ∂(Measure.prod γ γ)
  have hψ : ∀ θ, HasDerivAt ψ (-sin θ * J θ) θ := fun θ => by
    have := hasDerivAt_interp hf hA hB θ
    rwa [integral_interp_deriv hf hA hB θ] at this
  have hJ : ∀ θ, J θ ≤ D := fun θ => by
    have hcs : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
    have hmp := measurePreserving_orthogonal_gaussianReal hcs
    have hg : Continuous fun x => deriv f x ^ 2 := by fun_prop
    have e1 : ∫ p, deriv f p.1 ^ 2 ∂(Measure.prod γ γ) = D := by
      rw [hD]
      exact integral_comp_of_measurePreserving (T := Prod.fst) (measurePreserving_fst)
        (g := fun x => deriv f x ^ 2) hg.aestronglyMeasurable
    have e2 : ∫ p, deriv f (cos θ * p.1 + sin θ * p.2) ^ 2 ∂(Measure.prod γ γ) = D := by
      rw [hD]
      exact integral_comp_of_measurePreserving
        (T := fun p : ℝ × ℝ => cos θ * p.1 + sin θ * p.2)
        ((measurePreserving_fst (μ := γ) (ν := γ)).comp hmp)
        (g := fun x => deriv f x ^ 2) hg.aestronglyMeasurable
    have i1 : Integrable (fun p : ℝ × ℝ => deriv f p.1 ^ 2) (Measure.prod γ γ) :=
      integrable_of_abs_le (C := B ^ 2) (by fun_prop : Continuous _).aestronglyMeasurable
        fun p => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    have i2 : Integrable (fun p : ℝ × ℝ => deriv f (cos θ * p.1 + sin θ * p.2) ^ 2)
        (Measure.prod γ γ) :=
      integrable_of_abs_le (C := B ^ 2) (by fun_prop : Continuous _).aestronglyMeasurable
        fun p => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    have hle : J θ ≤ ∫ p, (deriv f p.1 ^ 2 + deriv f (cos θ * p.1 + sin θ * p.2) ^ 2) / 2
        ∂(Measure.prod γ γ) := by
      refine integral_mono (integrable_of_abs_le (C := B * B)
        (by fun_prop : Continuous _).aestronglyMeasurable fun p => ?_) ((i1.add i2).div_const 2)
        fun p => ?_
      · rw [abs_mul]
        exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
      · simp only
        nlinarith [sq_nonneg (deriv f p.1 - deriv f (cos θ * p.1 + sin θ * p.2))]
    rw [integral_div, integral_add i1 i2, e1, e2] at hle
    linarith
  have hφ : MonotoneOn (fun θ => ψ θ + D * (1 - cos θ)) (Set.Icc 0 (π / 2)) := by
    have hd : ∀ θ, HasDerivAt (fun θ => ψ θ + D * (1 - cos θ))
        (sin θ * (D - J θ)) θ := fun θ => by
      have h2 : HasDerivAt (fun θ => D * (1 - cos θ)) (D * sin θ) θ := by
        simpa using ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cos θ)).const_mul D
      exact ((hψ θ).add h2).congr_deriv (by ring)
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun θ _ => (hd θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hd θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
    rw [(hd θ).deriv]
    rw [interior_Icc] at hθ
    exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos]))
      (sub_nonneg.2 (hJ θ))
  have h0 : ψ 0 = ∫ x, f x * f x ∂γ := by
    simp only [ψ, cos_zero, sin_zero, one_mul, zero_mul, add_zero]
    exact integral_comp_of_measurePreserving (T := Prod.fst) (measurePreserving_fst)
      (g := fun x => f x * f x) (by fun_prop : Continuous _).aestronglyMeasurable
  have h1 : ψ (π / 2) = (∫ x, f x ∂γ) * ∫ x, f x ∂γ := by
    simp only [ψ, cos_pi_div_two, sin_pi_div_two, zero_mul, one_mul, zero_add]
    exact integral_prod_mul (μ := γ) (ν := γ) (fun x => f x) (fun x => f x)
  have hmem : MemLp f 2 γ :=
    MemLp.of_bound hc.aestronglyMeasurable A (ae_of_all _ fun x => by simpa using hA x)
  have hmono := hφ ⟨le_rfl, by linarith [pi_pos]⟩ ⟨by linarith [pi_pos], le_rfl⟩
    (by linarith [pi_pos])
  simp only [cos_zero, cos_pi_div_two, h0, h1] at hmono
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, sq]
  linarith

section Pi

/-- Resampling one coordinate of a `Measure.pi` sample from an independent draw of that
coordinate's law does not change the law of the sample. -/
theorem map_update_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) :
    ((Measure.pi μ).prod (μ i)).map (fun q => Function.update q.1 i q.2) = Measure.pi μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (∀ j, α j) × α i => Function.update q.1 i q.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (Function.update s i Set.univ j))
      (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, μ j (Function.update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, μ j (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1]
  simp [mul_comm]

/-- Averaging a bounded measurable function over a freshly resampled coordinate preserves its
expectation under `Measure.pi`. -/
theorem integral_integral_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {h : (∀ j, α j) → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ∫ x, ∫ y, h (Function.update x i y) ∂μ i ∂Measure.pi μ = ∫ x, h x ∂Measure.pi μ := by
  have hu : Measurable fun q : (∀ j, α j) × α i => h (Function.update q.1 i q.2) :=
    hh.comp measurable_update'
  have hint : Integrable (fun q : (∀ j, α j) × α i => h (Function.update q.1 i q.2))
      ((Measure.pi μ).prod (μ i)) :=
    integrable_of_abs_le hu.aestronglyMeasurable fun q => hC _
  refine (integral_prod _ hint).symm.trans ?_
  exact integral_comp_of_measurePreserving
    (T := fun q : (∀ j, α j) × α i => Function.update q.1 i q.2)
    ⟨measurable_update', map_update_prod_pi μ i⟩ hh.aestronglyMeasurable

/-- **The Gaussian Poincaré inequality on `ℝⁿ`.** For a continuously differentiable function `f`
on `Fin n → ℝ` with bounded values and bounded partial derivatives, the variance of `f` under
the product of `n` standard Gaussian laws is at most the expectation of the squared Euclidean norm
of its gradient, `∑ i, (∂ᵢ f)²`. -/
theorem variance_le_sum_integral_fderiv_sq_pi {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (hfb : ∃ A, ∀ x, |f x| ≤ A)
    (hdb : ∃ B, ∀ x i, |fderiv ℝ f x (Pi.single i 1)| ≤ B) :
    variance f (Measure.pi fun _ : Fin n => γ) ≤
      ∑ i, ∫ x, fderiv ℝ f x (Pi.single i 1) ^ 2 ∂(Measure.pi fun _ : Fin n => γ) := by
  obtain ⟨A, hA⟩ := hfb
  obtain ⟨B, hB⟩ := hdb
  have hc : Continuous f := hf.continuous
  have hmem : MemLp f 2 (Measure.pi fun _ : Fin n => γ) :=
    MemLp.of_bound hc.aestronglyMeasurable A (ae_of_all _ fun x => by simpa using hA x)
  have hES := efronStein (fun _ : Fin n => γ) hc.measurable hmem
  rw [← hmem.ofReal_variance_eq] at hES
  have hcoord : ∀ i : Fin n,
      ∫⁻ x, evariance (fun y => f (Function.update x i y)) γ ∂(Measure.pi fun _ : Fin n => γ) ≤
        ENNReal.ofReal
          (∫ x, fderiv ℝ f x (Pi.single i 1) ^ 2 ∂(Measure.pi fun _ : Fin n => γ)) := by
    intro i
    let h : (Fin n → ℝ) → ℝ := fun z => fderiv ℝ f z (Pi.single i 1) ^ 2
    have hcont : Continuous h :=
      (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2)
    have hbd : ∀ z, |h z| ≤ B ^ 2 := fun z => by
      simp only [h]
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB _ _) 2
    have hslice : ∀ x : Fin n → ℝ, evariance (fun y => f (Function.update x i y)) γ ≤
        ENNReal.ofReal (∫ y, h (Function.update x i y) ∂γ) := by
      intro x
      have hg : ContDiff ℝ 1 (fun y => f (Function.update x i y)) :=
        hf.comp (contDiff_update 1 x i)
      have hd : ∀ y, deriv (fun y => f (Function.update x i y)) y =
          fderiv ℝ f (Function.update x i y) (Pi.single i 1) := fun y =>
        ((hf.differentiable one_ne_zero (Function.update x i y)).hasFDerivAt.comp_hasDerivAt y
          (hasDerivAt_update x i y)).deriv
      have hmemx : MemLp (fun y => f (Function.update x i y)) 2 γ :=
        MemLp.of_bound hg.continuous.aestronglyMeasurable A
          (ae_of_all _ fun y => by simpa using hA _)
      rw [← hmemx.ofReal_variance_eq]
      refine ENNReal.ofReal_le_ofReal ?_
      have := variance_le_integral_deriv_sq_gaussianReal hg ⟨A, fun y => hA _⟩
        ⟨B, fun y => by rw [hd]; exact hB _ _⟩
      simpa [hd, h] using this
    have hu : Measurable fun q : (Fin n → ℝ) × ℝ => h (Function.update q.1 i q.2) :=
      hcont.measurable.comp measurable_update'
    have hGm : StronglyMeasurable fun x : Fin n → ℝ => ∫ y, h (Function.update x i y) ∂γ :=
      hu.stronglyMeasurable.integral_prod_right'
    have hGint : Integrable (fun x : Fin n → ℝ => ∫ y, h (Function.update x i y) ∂γ)
        (Measure.pi fun _ : Fin n => γ) :=
      integrable_of_abs_le (C := B ^ 2) hGm.aestronglyMeasurable fun x => by
        have := norm_integral_le_of_norm_le_const (μ := γ)
          (f := fun y => h (Function.update x i y)) (C := B ^ 2)
          (ae_of_all _ fun y => by simpa using hbd _)
        simpa using this
    calc ∫⁻ x, evariance (fun y => f (Function.update x i y)) γ ∂(Measure.pi fun _ : Fin n => γ)
        ≤ ∫⁻ x, ENNReal.ofReal (∫ y, h (Function.update x i y) ∂γ)
          ∂(Measure.pi fun _ : Fin n => γ) := lintegral_mono hslice
      _ = ENNReal.ofReal (∫ x, ∫ y, h (Function.update x i y) ∂γ
          ∂(Measure.pi fun _ : Fin n => γ)) :=
        (ofReal_integral_eq_lintegral_ofReal hGint
          (ae_of_all _ fun x => integral_nonneg fun y => sq_nonneg _)).symm
      _ = ENNReal.ofReal (∫ x, h x ∂(Measure.pi fun _ : Fin n => γ)) := by
        rw [integral_integral_update_pi (fun _ : Fin n => γ) i hcont.measurable hbd]
  have hsum := hES.trans (Finset.sum_le_sum fun i _ => hcoord i)
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ∫ x, fderiv ℝ f x (Pi.single i 1) ^ 2 ∂(Measure.pi fun _ : Fin n => γ) :=
    fun i _ => integral_nonneg fun x => sq_nonneg _
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).1 hsum

end Pi

end TauCeti.Probability
