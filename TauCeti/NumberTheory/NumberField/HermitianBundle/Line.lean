/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

/-!
# Hermitian metrics on a line are determined by one norm at each place

Let `E` be an `𝓞 K`-module whose scalar extension to `K` is identified with `K` by
`ι : E → K` (`IsBaseChange K ι`), for instance a nonzero fractional ideal. Each complex fibre
`E ⊗_σ ℂ` is then a complex line, so a hermitian form on it is determined by its value at one
nonzero vector. Consequently every hermitian metric `h` on `E` is one of the metrics
`HermitianMetric.ofIsBaseChange hι w`, `‖x‖_σ = e^{-λ_v} |σ(ι x)|`: for any `x₀` with `ι x₀ ≠ 0`
the weights are `λ_v = log |ι x₀|_v - log ‖x₀‖_v`
(`TauCeti.HermitianMetric.eq_ofIsBaseChange`). For a nonzero fractional ideal this says that every
hermitian metric is `HermitianMetric.fractionalIdeal` for some weights
(`TauCeti.HermitianMetric.eq_fractionalIdeal`).

## Main results

* `TauCeti.HermitianMetric.form_eq_mul_form_fiberEquiv_symm_one`: on a line, the form at `σ` is
  `h_σ(u, v) = conj (u₀) v₀ h_σ(g, g)`, in the coordinate `u ↦ u₀` of `fiberEquiv` and its
  basis vector `g`.
* `TauCeti.HermitianMetric.ext_of_norm_eq`: two hermitian metrics on a line with the same norm
  at one vector `x₀`, `ι x₀ ≠ 0`, at every embedding are equal.
* `TauCeti.HermitianMetric.eq_ofIsBaseChange`, `TauCeti.HermitianMetric.eq_fractionalIdeal`.
-/

public section

open scoped TensorProduct ComplexConjugate nonZeroDivisors

namespace TauCeti.HermitianMetric

open NumberField NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
variable {ι : E →ₗ[𝓞 K] K} (hι : IsBaseChange K ι)

/-- **On a line, a hermitian form is determined by one value.** With `g` the vector of the complex
fibre at `σ` with coordinate `1` under `fiberEquiv hι σ`, `h_σ(u, v) = conj (u₀) v₀ h_σ(g, g)`,
where `u₀, v₀` are the coordinates of `u, v`. -/
theorem form_eq_mul_form_fiberEquiv_symm_one (h : HermitianMetric K E) (σ : K →+* ℂ)
    (u v : Codomain σ ⊗[𝓞 K] E) :
    h.form σ u v = conj (fiberEquiv hι σ u) * fiberEquiv hι σ v *
      h.form σ ((fiberEquiv hι σ).symm 1) ((fiberEquiv hι σ).symm 1) := by
  have hc (w : Codomain σ ⊗[𝓞 K] E) :
      w = fiberEquiv hι σ w • (fiberEquiv hι σ).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hc u, hc v]
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

include hι in
/-- **Hermitian metrics on a line agree when one norm does.** If `h` and `h'` give the vector
`x₀`, with `ι x₀ ≠ 0`, the same norm at every complex embedding, they are equal. -/
theorem ext_of_norm_eq {h h' : HermitianMetric K E} {x₀ : E} (hx₀ : ι x₀ ≠ 0)
    (hn : ∀ σ, h.norm σ (1 ⊗ₜ x₀) = h'.norm σ (1 ⊗ₜ x₀)) : h = h' := by
  refine ext_tmul _ fun σ x y ↦ ?_
  have hF := fiberEquiv_one_tmul_ne_zero hι hx₀ σ
  have hgg : h.form σ ((fiberEquiv hι σ).symm 1) ((fiberEquiv hι σ).symm 1) =
      h'.form σ ((fiberEquiv hι σ).symm 1) ((fiberEquiv hι σ).symm 1) := by
    have he := congrArg (fun r : ℝ ↦ ((r ^ 2 : ℝ) : ℂ)) (hn σ)
    simp only [← form_self_eq_norm_sq] at he
    rw [form_eq_mul_form_fiberEquiv_symm_one hι h, form_eq_mul_form_fiberEquiv_symm_one hι h'] at he
    exact mul_left_cancel₀ (mul_ne_zero ((map_ne_zero _).mpr hF) hF) he
  rw [form_eq_mul_form_fiberEquiv_symm_one hι h, form_eq_mul_form_fiberEquiv_symm_one hι h', hgg]

/-- **Every hermitian metric on a line is of the form `‖x‖_σ = e^{-λ_v} |σ(ι x)|`**, with weights
`λ_v = log |ι x₀|_v - log ‖x₀‖_v` read off at any `x₀` with `ι x₀ ≠ 0`. -/
theorem eq_ofIsBaseChange (h : HermitianMetric K E) {x₀ : E} (hx₀ : ι x₀ ≠ 0) :
    h = ofIsBaseChange hι
      (fun v ↦ Real.log (v (ι x₀)) - Real.log (h.placeNorm v x₀)) := by
  refine ext_of_norm_eq hι hx₀ fun σ ↦ ?_
  have h1 : (1 : Codomain σ) ⊗ₜ[𝓞 K] x₀ ≠ 0 :=
    (fiberEquiv hι σ).map_ne_zero_iff.mp (fiberEquiv_one_tmul_ne_zero hι hx₀ σ)
  have hpos : 0 < h.norm σ (1 ⊗ₜ x₀) := h.norm_pos h1
  have hv : 0 < ‖σ (ι x₀)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hx₀)
  rw [norm_ofIsBaseChange_tmul, placeNorm_mk]
  simp [Real.exp_sub, Real.exp_log hpos, Real.exp_log hv, hv.ne']

variable [NumberField K]

/-- **Every hermitian metric on a nonzero fractional ideal `I` is `fractionalIdeal I w`** for the
weights `w_v = log |x₀|_v - log ‖x₀‖_v`, at any nonzero `x₀ ∈ I`. -/
theorem eq_fractionalIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (h : HermitianMetric K I)
    {x₀ : I} (hx₀ : (x₀ : K) ≠ 0) :
    h = fractionalIdeal I hI (fun v ↦ Real.log (v x₀) - Real.log (h.placeNorm v x₀)) := by
  rw [fractionalIdeal_def]
  exact eq_ofIsBaseChange (FractionalIdeal.isBaseChange_subtype hI) h hx₀

end TauCeti.HermitianMetric
