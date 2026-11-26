/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Analytic.ZeroCount
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Complex.Wirtinger.Green
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
import TauCeti.Analysis.Complex.ZeroMultiplicity
import TauCeti.Analysis.Calculus.FDeriv.CircleMap
import TauCeti.Analysis.Contour.Argument.PowerSum
import TauCeti.MeasureTheory.Integral.Circle.IntegrationByParts
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The weighted argument principle for `bar∂α = a α`

Let `α` be a real-differentiable function on an open set `Ω ⊆ ℂ` solving the scalar
Cauchy–Riemann equation `bar∂α = a α`, with a `C¹` coefficient `a`, and let the closed disc
`|z - c| ≤ R` lie in `Ω`, with `α` nowhere zero on its boundary circle. Such an `α` is in general
not holomorphic, but by the similarity principle it is `exp g` times a holomorphic function, for
any solution `g` of `bar∂g = a`
(`TauCeti.differentiableAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul`, with `g` from the
Dolbeault lemma `IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`). So its zeros in the
open disc are finitely many, and near each zero `z` it factors as
`α w = (w - z) ^ n v w` with `v` continuous and nonzero at `z`; a multiset `D` of points of the
disc whose multiplicities are these exponents exists
(`TauCeti.exists_multiset_eventually_eq_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul`), and it is
determined by `α`, since the exponent of such a factorization is unique
(`TauCeti.multiset_eq_of_eventually_eq_pow_mul`, in
`TauCeti.Analysis.Complex.ZeroMultiplicity`).

This file proves the **weighted argument principle** for such `α`: for every `φ` holomorphic on
`Ω`, with `γ = circleMap c R`,

`∑_{V ∈ D} φ(V) = (2πi)⁻¹ ∫₀^{2π} φ(γ θ) (α ∘ γ)'(θ) / α(γ θ) dθ + π⁻¹ ∫_{B} φ'(z) a(z) dA`,

where `B` is the open disc
(`TauCeti.sum_map_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul`).
The boundary term only involves `α` along the circle; the interior term is the correction coming
from the coefficient `a`, and it vanishes when `α` is holomorphic. For `φ(z) = zᵏ` this expresses
the power sums of the zeros of `α`, which determine its divisor through Newton's identities, by a
boundary integral and the moment `k / π ∫ zᵏ⁻¹ a` of the coefficient
(`TauCeti.sum_map_pow_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul`).

The motivating case is a section `α` of a Hermitian line with a unitary connection `d + A` on a
disc, holomorphic for it: `bar∂_A α = bar∂α + A^{0,1} α = 0` is `bar∂α = a α` with
`a = -A^{0,1}`. In Taubes's analysis of the large-parameter Seiberg–Witten equations near a
pseudoholomorphic curve, such identities relate the positions of the zeros of `α` on a normal disc
to the boundary framing and to integrals of the connection.

The proof applies the argument principle for holomorphic functions,
`TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`, to `f = exp (-g) α`. Along the circle
the logarithmic derivative of `f` is that of `α` minus the derivative of `g`, and integrating by
parts on the closed curve (`TauCeti.intervalIntegral_smul_deriv_comp_circleMap`) and applying
Green's formula on the disc turns `∫ φ(γ θ) (g ∘ γ)'(θ) dθ` into `-2i ∫ φ' a`.

## Main results

* `TauCeti.exists_contDiffOn_differentiableOn_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul`:
  an integrating factor `exp (-g)` making `α` holomorphic on all of `Ω`.
* `TauCeti.exists_multiset_eventually_eq_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul`: the
  zeros of `α` in the disc, with the exponents of its local factorizations as multiplicities.
* `TauCeti.sum_map_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul`: the
  weighted argument principle.
* `TauCeti.sum_map_pow_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul`: its
  form for the power sums of the zeros.

## References

* I. N. Vekua, *Generalized Analytic Functions*, Pergamon, 1962, Chapter III.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public noncomputable section

open Complex Filter Metric MeasureTheory Set Topology intervalIntegral
open scoped Real

namespace TauCeti

variable {α a φ : ℂ → ℂ} {Ω : Set ℂ} {c : ℂ} {R : ℝ}

/-! ### The integrating factor -/

/-- **A global integrating factor.** A real-differentiable solution of `bar∂α = a α` on an open set
`Ω`, with `C¹` coefficient `a`, has an integrating factor on all of `Ω`: a `C¹` solution `g` of
`bar∂g = a` on `Ω` for which `exp (-g) α` is holomorphic on `Ω`. -/
theorem exists_contDiffOn_differentiableOn_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
    (hΩ : IsOpen Ω) (hα : DifferentiableOn ℝ α Ω)
    (ha : ContDiffOn ℝ 1 a Ω) (heq : ∀ z ∈ Ω, conjWirtingerDeriv α z 1 = a z * α z) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ 1 g Ω ∧ (∀ z ∈ Ω, conjWirtingerDeriv g z 1 = a z) ∧
      DifferentiableOn ℂ (fun w ↦ exp (-g w) * α w) Ω := by
  obtain ⟨g, hg, hga⟩ := hΩ.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (n := 1) le_rfl ha
  refine ⟨g, hg, hga, fun z hz ↦ ?_⟩
  exact (differentiableAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
    ((hg.differentiableOn one_ne_zero z hz).differentiableAt (hΩ.mem_nhds hz))
    ((hα z hz).differentiableAt (hΩ.mem_nhds hz)) (hga z hz) (heq z hz)).differentiableWithinAt

/-! ### The boundary term -/

/-- Along the circle, the logarithmic derivative of `exp (-g) α` is that of `α` minus the
derivative of `g`. -/
private lemma deriv_circleMap_mul_logDeriv_exp_neg_mul {g : ℂ → ℂ} {θ : ℝ}
    (hg : DifferentiableAt ℝ g (circleMap c R θ)) (hα : DifferentiableAt ℝ α (circleMap c R θ))
    (hf : DifferentiableAt ℂ (fun w ↦ exp (-g w) * α w) (circleMap c R θ))
    (hα₀ : α (circleMap c R θ) ≠ 0) :
    deriv (circleMap c R) θ * logDeriv (fun w ↦ exp (-g w) * α w) (circleMap c R θ) =
      logDeriv (fun t ↦ α (circleMap c R t)) θ - deriv (fun t ↦ g (circleMap c R t)) θ := by
  have hγ := hasDerivAt_circleMap c R θ
  have hgγ := hg.hasFDerivAt.comp_hasDerivAt θ hγ
  have hαγ := hα.hasFDerivAt.comp_hasDerivAt θ hγ
  simp only [Function.comp_def] at hgγ hαγ
  -- The derivative of `f ∘ γ` computed by the chain rule and by the product rule.
  have heq := (hf.hasDerivAt.comp θ hγ).unique (hgγ.neg.cexp.mul hαγ)
  rw [logDeriv_apply, logDeriv_apply, hγ.deriv, hαγ.deriv, hgγ.deriv]
  have hE := exp_ne_zero (-g (circleMap c R θ))
  field_simp
  linear_combination heq

/-- **Green's formula for the derivative of a holomorphic function.** If `bar∂g = a` on a
neighbourhood `Ω` of the closed disc and `φ` is holomorphic on `Ω`, then
`∮ φ' g dz = 2i ∫_{|z - c| < R} φ' a dA`. This is Green's formula
`TauCeti.integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral` for the product `φ' g`, in
which `bar∂φ' = 0` and `bar∂g = a`. -/
private lemma circleIntegral_deriv_mul_eq {g : ℂ → ℂ} (hR : 0 ≤ R) (hΩ : IsOpen Ω)
    (hsub : closedBall c R ⊆ Ω) (hg : ContDiffOn ℝ 1 g Ω)
    (hga : ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = a z) (hφ : DifferentiableOn ℂ φ Ω) :
    ∮ z in C(c, R), deriv φ z * g z = 2 * I * ∫ z in ball c R, deriv φ z * a z := by
  have hφ' : DifferentiableOn ℂ (deriv φ) Ω := hφ.deriv hΩ
  have h := integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral hR (g := deriv φ) (ξ := g)
    (fun z hz ↦ ((hφ'.contDiffOn (n := 1) hΩ).contDiffAt
      (hΩ.mem_nhds (hsub hz))).restrict_scalars ℝ)
    fun z hz ↦ hg.contDiffAt (hΩ.mem_nhds (hsub hz))
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by
    have hz' := hsub (ball_subset_closedBall hz)
    rw [hga z hz', (hφ'.differentiableAt (hΩ.mem_nhds hz')).conjWirtingerDeriv_eq_zero]] at h
  simp only [smul_eq_mul, zero_apply, zero_mul, add_zero] at h
  rw [h]
  field_simp

/-! ### The weighted argument principle -/

/-- On a closed disc in `Ω` on whose boundary circle `α` does not vanish, the global integrating
factor `exp (-g)` makes `exp (-g) α` analytic on the closed disc and nonvanishing on its boundary
circle. -/
private lemma exists_analyticOnNhd_exp_neg_mul (hΩ : IsOpen Ω) (hsub : closedBall c R ⊆ Ω)
    (hα : DifferentiableOn ℝ α Ω) (ha : ContDiffOn ℝ 1 a Ω)
    (heq : ∀ z ∈ Ω, conjWirtingerDeriv α z 1 = a z * α z)
    (hsphere : ∀ z ∈ sphere c R, α z ≠ 0) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ 1 g Ω ∧ (∀ z ∈ Ω, conjWirtingerDeriv g z 1 = a z) ∧
      DifferentiableOn ℂ (fun w ↦ exp (-g w) * α w) Ω ∧
      (∀ z ∈ ball c R, ContinuousAt g z) ∧
      AnalyticOnNhd ℂ (fun w ↦ exp (-g w) * α w) (closedBall c R) ∧
      ∀ z ∈ sphere c R, exp (-g z) * α z ≠ 0 := by
  obtain ⟨g, hg, hga, hf⟩ :=
    exists_contDiffOn_differentiableOn_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul hΩ hα ha
      heq
  exact ⟨g, hg, hga, hf, fun z hz ↦ hg.continuousOn.continuousAt
      (hΩ.mem_nhds (hsub (ball_subset_closedBall hz))),
    fun z hz ↦ hf.analyticAt (hΩ.mem_nhds (hsub hz)),
    fun z hz ↦ mul_ne_zero (exp_ne_zero _) (hsphere z hz)⟩

/-- Near every point `z` of the open disc, `α w = (w - z) ^ n * v w` with `v` continuous and
nonzero at `z`, where `n` is the multiplicity of `z` in the multiset of zeros of the holomorphic
function `exp (-g) α`. -/
private lemma exists_eventually_eq_pow_count_zeroMultiset_mul {g : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ (fun w ↦ exp (-g w) * α w) (closedBall c R))
    (hfs : ∀ z ∈ sphere c R, exp (-g z) * α z ≠ 0) (hgc : ∀ z ∈ ball c R, ContinuousAt g z) :
    ∀ z ∈ ball c R, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, α w =
      (w - z) ^ (AnalyticOnNhd.zeroMultiset (fun w ↦ exp (-g w) * α w) (ball c R)).count z *
        v w := by
  classical
  intro z hz
  have hzc := ball_subset_closedBall hz
  have hord := hfa.analyticOrderAt_eq_count_zeroMultiset hfs hzc
  obtain ⟨h, hh, hh₀, hfh⟩ := (hfa z hzc).analyticOrderAt_ne_top.1 (by simp [hord])
  have hN : analyticOrderNatAt (fun w ↦ exp (-g w) * α w) z =
      (AnalyticOnNhd.zeroMultiset (fun w ↦ exp (-g w) * α w) (ball c R)).count z := by
    rw [AnalyticOnNhd.count_zeroMultiset hfa, indicator_of_mem hz]
  refine ⟨fun w ↦ exp (g w) * h w, (hgc z hz).cexp.mul hh.continuousAt,
    mul_ne_zero (exp_ne_zero _) hh₀, ?_⟩
  filter_upwards [hfh] with w hw
  simp only [smul_eq_mul] at hw
  have he : exp (g w) * exp (-g w) = 1 := by simp [← exp_add]
  rw [← hN]
  linear_combination exp (g w) * hw - α w * he

/-- **The zeros of a solution of `bar∂α = a α` in a disc.** Let `α` be real-differentiable on an
open set `Ω` containing the closed disc `|z - c| ≤ R`, with `bar∂α = a α` on `Ω` for a `C¹`
coefficient `a`, and nowhere zero on the boundary circle. Then there is a multiset `D` of points of
the open disc such that near every point `z` of the disc, `α w = (w - z) ^ D.count z * v w` with
`v` continuous at `z` and `v z ≠ 0`. -/
theorem exists_multiset_eventually_eq_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul (hΩ : IsOpen Ω)
    (hsub : closedBall c R ⊆ Ω) (hα : DifferentiableOn ℝ α Ω) (ha : ContDiffOn ℝ 1 a Ω)
    (heq : ∀ z ∈ Ω, conjWirtingerDeriv α z 1 = a z * α z)
    (hsphere : ∀ z ∈ sphere c R, α z ≠ 0) :
    ∃ D : Multiset ℂ, (∀ z ∈ D, z ∈ ball c R) ∧ ∀ z ∈ ball c R, ∃ v : ℂ → ℂ,
      ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, α w = (w - z) ^ D.count z * v w := by
  obtain ⟨g, -, -, -, hgc, hfa, hfs⟩ :=
    exists_analyticOnNhd_exp_neg_mul hΩ hsub hα ha heq hsphere
  exact ⟨_, fun z hz ↦ AnalyticOnNhd.mem_of_mem_zeroMultiset hz,
    exists_eventually_eq_pow_count_zeroMultiset_mul hfa hfs hgc⟩

/-- The weighted logarithmic integral of the holomorphic function `exp (-g) α` along the circle is
the boundary term of `α` plus `2i ∫ φ' a`. -/
private lemma circleIntegral_mul_logDeriv_exp_neg_mul {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hR : 0 ≤ R)
    (hsub : closedBall c R ⊆ Ω) (hα : DifferentiableOn ℝ α Ω) (hg : ContDiffOn ℝ 1 g Ω)
    (hga : ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = a z)
    (hf : DifferentiableOn ℂ (fun w ↦ exp (-g w) * α w) Ω)
    (hsphere : ∀ z ∈ sphere c R, α z ≠ 0) (hφ : DifferentiableOn ℂ φ Ω) :
    ∮ z in C(c, R), φ z * logDeriv (fun w ↦ exp (-g w) * α w) z =
      (∫ θ in 0..2 * π, φ (circleMap c R θ) * logDeriv (fun t ↦ α (circleMap c R t)) θ) +
        2 * I * ∫ z in ball c R, deriv φ z * a z := by
  set f : ℂ → ℂ := fun w ↦ exp (-g w) * α w
  have hmem (θ : ℝ) : circleMap c R θ ∈ Ω := hsub (circleMap_mem_closedBall c hR θ)
  have hsph : sphere c R ⊆ Ω := sphere_subset_closedBall.trans hsub
  have hsph' : sphere c |R| ⊆ Ω := by rwa [abs_of_nonneg hR]
  set I₁ : ℝ → ℂ := fun θ ↦ φ (circleMap c R θ) * logDeriv (fun t ↦ α (circleMap c R t)) θ
  set I₂ : ℝ → ℂ := fun θ ↦ φ (circleMap c R θ) * deriv (fun t ↦ g (circleMap c R t)) θ
  -- Along the circle the logarithmic derivative of `f` splits into those of `α` and `exp (-g)`.
  have hpt (θ : ℝ) :
      deriv (circleMap c R) θ • (φ (circleMap c R θ) * logDeriv f (circleMap c R θ)) =
        I₁ θ - I₂ θ := by
    have hθ : deriv (circleMap c R) θ * logDeriv f (circleMap c R θ) =
        logDeriv (fun t ↦ α (circleMap c R t)) θ - deriv (fun t ↦ g (circleMap c R t)) θ :=
      deriv_circleMap_mul_logDeriv_exp_neg_mul
      ((hg.differentiableOn one_ne_zero _ (hmem θ)).differentiableAt (hΩ.mem_nhds (hmem θ)))
      ((hα _ (hmem θ)).differentiableAt (hΩ.mem_nhds (hmem θ)))
      (hf.differentiableAt (hΩ.mem_nhds (hmem θ)))
      (hsphere _ (circleMap_mem_sphere c hR θ))
    simp only [I₁, I₂, smul_eq_mul]
    linear_combination φ (circleMap c R θ) * hθ
  have hI₂ : IntervalIntegrable I₂ volume 0 (2 * π) :=
    ((((hφ.continuousOn).comp_continuous (continuous_circleMap c R) hmem).mul
      (continuous_deriv_comp_circleMap hΩ hsph' hg)).intervalIntegrable _ _)
  have hcont : ContinuousOn (fun z ↦ φ z * logDeriv f z) (sphere c R) := by
    refine (hφ.continuousOn.mono hsph).mul ?_
    simp only [logDeriv]
    exact (((hf.deriv hΩ).continuousOn.mono hsph).div (hf.continuousOn.mono hsph)
      fun z hz ↦ mul_ne_zero (exp_ne_zero _) (hsphere z hz))
  have hI₁ : IntervalIntegrable I₁ volume 0 (2 * π) := by
    have hdiff : IntervalIntegrable (fun θ ↦ I₁ θ - I₂ θ) volume 0 (2 * π) :=
      (hcont.circleIntegrable hR).out.congr fun θ _ ↦ by
        rw [← hpt θ, deriv_circleMap, smul_eq_mul]
    simpa using hdiff.add hI₂
  have hparts := intervalIntegral_smul_deriv_comp_circleMap hΩ hsph' hg hφ
  simp only [smul_eq_mul] at hparts
  rw [circleIntegral, integral_congr fun θ _ ↦ hpt θ, integral_sub hI₁ hI₂, hparts,
    circleIntegral_deriv_mul_eq hR hΩ hsub hg hga hφ]
  ring

/-- **The weighted argument principle for `bar∂α = a α`.** Let `α` be real-differentiable on an
open set `Ω` containing the closed disc `|z - c| ≤ R`, `R ≥ 0`, with `bar∂α = a α` on `Ω` for a
`C¹` coefficient `a`, and nowhere zero on the boundary circle `γ = circleMap c R`. Let `D` be the
multiset of zeros of `α` in the open disc, counted with the exponents of the local factorizations
`α w = (w - z) ^ D.count z * v w`, `v` continuous and nonzero at `z`. Then for every `φ`
holomorphic on `Ω`,

`∑_{V ∈ D} φ(V) = (2πi)⁻¹ ∫₀^{2π} φ(γ θ) (log α ∘ γ)'(θ) dθ + π⁻¹ ∫_{|z - c| < R} φ'(z) a(z) dA`.

For holomorphic `α`, `a = 0` and this is the classical argument principle. -/
theorem sum_map_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul
    (hΩ : IsOpen Ω) (hR : 0 ≤ R) (hsub : closedBall c R ⊆ Ω) (hα : DifferentiableOn ℝ α Ω)
    (ha : ContDiffOn ℝ 1 a Ω) (heq : ∀ z ∈ Ω, conjWirtingerDeriv α z 1 = a z * α z)
    (hsphere : ∀ z ∈ sphere c R, α z ≠ 0) (hφ : DifferentiableOn ℂ φ Ω) {D : Multiset ℂ}
    (hD : ∀ z ∈ D, z ∈ ball c R)
    (hDα : ∀ z ∈ ball c R, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, α w = (w - z) ^ D.count z * v w) :
    (D.map φ).sum = (2 * π * I)⁻¹ * (∫ θ in 0..2 * π,
        φ (circleMap c R θ) * logDeriv (fun t ↦ α (circleMap c R t)) θ) +
      (π : ℂ)⁻¹ * ∫ z in ball c R, deriv φ z * a z := by
  obtain ⟨g, hg, hga, hf, hgc, hfa, hfs⟩ :=
    exists_analyticOnNhd_exp_neg_mul hΩ hsub hα ha heq hsphere
  -- `D` is the multiset of zeros of the holomorphic function `exp (-g) α`, so the holomorphic
  -- argument principle applies.
  rw [multiset_eq_of_eventually_eq_pow_mul hD (fun _ ↦ AnalyticOnNhd.mem_of_mem_zeroMultiset) hDα
      (exists_eventually_eq_pow_count_zeroMultiset_mul hfa hfs hgc),
    Contour.sum_map_zeroMultiset_eq_circleIntegral hR hfa hfs
      fun z hz ↦ hφ.analyticAt (hΩ.mem_nhds (hsub hz)),
    circleIntegral_mul_logDeriv_exp_neg_mul hΩ hR hsub hα hg hga hf hsphere hφ]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- **Power sums of the zeros of a solution of `bar∂α = a α`.** Under the hypotheses of
`TauCeti.sum_map_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul`, the
`k`-th power sum of the zeros of `α` in the disc is

`∑_{V ∈ D} Vᵏ = (2πi)⁻¹ ∫₀^{2π} (γ θ)ᵏ (log α ∘ γ)'(θ) dθ + k / π ∫_{|z - c| < R} zᵏ⁻¹ a(z) dA`.

For `k = 0` it is the number of zeros, the winding number of `α` along the circle. -/
theorem sum_map_pow_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul
    (hΩ : IsOpen Ω) (hR : 0 ≤ R) (hsub : closedBall c R ⊆ Ω) (hα : DifferentiableOn ℝ α Ω)
    (ha : ContDiffOn ℝ 1 a Ω) (heq : ∀ z ∈ Ω, conjWirtingerDeriv α z 1 = a z * α z)
    (hsphere : ∀ z ∈ sphere c R, α z ≠ 0) {D : Multiset ℂ} (hD : ∀ z ∈ D, z ∈ ball c R)
    (hDα : ∀ z ∈ ball c R, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, α w = (w - z) ^ D.count z * v w) (k : ℕ) :
    (D.map (· ^ k)).sum = (2 * π * I)⁻¹ * (∫ θ in 0..2 * π,
        circleMap c R θ ^ k * logDeriv (fun t ↦ α (circleMap c R t)) θ) +
      k / π * ∫ z in ball c R, z ^ (k - 1) * a z := by
  rw [sum_map_eq_intervalIntegral_add_integral_of_conjWirtingerDeriv_apply_one_eq_mul hΩ hR hsub hα
    ha heq hsphere (differentiable_pow k).differentiableOn hD hDα]
  simp only [deriv_pow_field, mul_assoc, MeasureTheory.integral_const_mul]
  ring

end TauCeti
