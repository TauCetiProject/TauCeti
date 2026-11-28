/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.MeanOscillation
public import TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.Ellipticity.Contraction
import TauCeti.Analysis.Sobolev.W1p.TangentialDerivative
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average.Oscillation
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace

/-!
# Mean oscillation of the Hessian at a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, let `z` lie on its boundary
hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `u ∈ W^{2,2}(H)` have zero boundary values, in the
sense that its first-order part lies in `H¹₀(H)`, and solve the non-divergence-form equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`,

with a measurable coefficient matrix `a`, neither continuous nor symmetric in general. Fix a
constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, write `θ(x) = ‖a(x) - A‖`
in the operator norm of the attached bilinear forms `TauCeti.PDE.matrixBilinearForm`, and assume
`θ ≤ K` on `B_r⁺` for a constant `K`. This file proves the boundary counterparts of the mean
oscillation estimates for the Hessian on balls (in the `TauCeti.PDE` namespace,
`setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`
in the interior) for the columns `D²u τ` of the weak Hessian in the tangential directions,
`⟪τ, ν⟫ = 0`. There is `C`, depending only on `n`, `λ` and `Λ`, such that for `0 < ρ ≤ r` and every
real `t`

`∫_{B_ρ⁺} ‖D²u τ - p_ρ‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u τ - t ν‖²`
`  + C ‖τ‖² (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`,

where `p_ρ` is the multiple of `ν` closest to `D²u τ` in `L²(B_ρ⁺)`. This is
`exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_inner_setAverage_div_smul_sq_le_add`,
whose case `a = A`, `K = 0` covers constant coefficients.
If moreover `D²u ∈ L^{2q}(B_r⁺)` for Hölder conjugate exponents `q, q'`, the
coefficient term becomes a mean deviation of `a`, and the estimate takes the scale-invariant form

`⨍_{B_ρ⁺} ‖D²u τ - p_ρ‖² ≤ C (ρ / r)² ⨍_{B_r⁺} ‖D²u τ - t ν‖²`
`  + C ‖τ‖² (r / ρ)^(n + 1) (⨍_{B_r⁺} f² + E)`

with `E = (K^(2q' - 1) ⨍_{B_r⁺} θ)^(1/q') (⨍_{B_r⁺} ‖D²u‖^(2q))^(1/q)`
(`exists_setAverage_ball_inter_norm_iteratedGradient_apply_sub_inner_setAverage_div_smul_sq_le`).
The frozen matrix `A` is arbitrary: nothing requires the coefficients near the boundary to be
close to a matrix invariant under the reflection in the hyperplane, which coefficients of vanishing
mean oscillation need not be.

These are the estimates on half-balls that Krylov's sharp function method needs for the `W^{2,p}`
estimate up to a flat boundary. Only the tangential columns are compared with constants: their
entries are all the second derivatives but `∂_ν∂_ν u`, which the equation expresses pointwise
through them and `f` when `a` is uniformly elliptic.

Recovering that entry gives the estimate for the whole Hessian,
`exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add`: there is
`C = C(n, λ, Λ)` such that for `0 < ρ ≤ r`

`∫_{B_ρ⁺} ‖D²u - (D²u)_{B_ρ⁺}‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u‖²`
`  + C (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`.

## The argument

The tangential derivative `d = ∂_τ u` lies in `H¹₀(H)`, because the translations along `τ` preserve
`H` (`TauCeti.Wkp.exists_hasWeakLineDerivOn_value_of_firstOrder_mem_w1p0Submodule`), and its
gradient is the column `D²u τ`. Differentiating the frozen equation shows that `d` solves the
divergence-form equation `-div(A ∇d) = -div(g τ)` weakly in `H`, with `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`
(`TauCeti.PDE.gradient_ae_eq_iteratedGradient_apply_and_energyFormH1_eq_of_hasWeakLineDerivOn`).
Extended by zero, `d` vanishes off `H`, so Krylov's mean oscillation estimate for the gradient at a
flat boundary
(`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add`)
applies to it with the constant coefficient `A` and the datum `g τ`. Finally
`g = f + ∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu` on `B_r⁺`, which gives
`∫_{B_r⁺} g² ≤ 2 (∫_{B_r⁺} f² + (n + 1)² ∫_{B_r⁺} θ² ‖D²u‖²)`
(`TauCeti.PDE.setIntegral_contraction_sq_le`).

For the whole Hessian, let `w = ν / ‖ν‖` and `τⱼ = eⱼ - ⟪eⱼ, w⟫ w`. A symmetric endomorphism `S`
is controlled by the `S τⱼ` up to its component `⟪S w, w⟫`, and since `⟪A w, w⟫ ≥ λ` that
component is recovered from the contraction `∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫`
(`TauCeti.PDE.norm_sq_le_sum_norm_apply_sq_add_contraction_sq`). Applied to
`S = D²u - (D²u)_{B_ρ⁺}`, the contraction is `g - g_{B_ρ⁺}`, whose `L²` norm is bounded by that of
`g` (`TauCeti.setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sq_of_subset`).

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475 (mean oscillation estimates for equations with
  coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics **96**, AMS, 2008 (mean oscillation estimates for the second derivatives, and
  estimates near a flat boundary through the tangential derivatives).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The tangential derivative `∂_τ u` of `u ∈ W^{2,2}(H)` with zero boundary values, extended by
zero to the whole space: it vanishes off `H`, its gradient is `D²u τ` on `H`, and it solves
`-div(A ∇(∂_τ u)) = -div(g τ)` weakly in `H` for every constant `A`, with `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem exists_extension_tangential_derivative {H : Opens E} {ν τ : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hτ : ⟪τ, ν⟫_ℝ = 0) {u : Wkp volume H 2 2}
    (hu0 : Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2) :
    ∃ W : W1p volume (⊤ : Opens E) 2,
      (∀ᵐ x ∂volume.restrict (⊤ : Opens E), x ∉ H → W1p.value W x = 0) ∧
      (W1p.gradient W : E → E) =ᵐ[volume.restrict H] (fun x => Wkp.iteratedGradient 1 u x τ) ∧
      ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (φ : 𝓓((⊤ : Opens E) ⊓ H, ℝ)),
        energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left W)
            (W1p.ofTestFunctionₗ volume ((⊤ : Opens E) ⊓ H) 2 φ) =
          ∫ x in (⊤ : Opens E) ⊓ H, ⟪(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
            (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • τ,
              ∇ (φ : E → ℝ) x⟫_ℝ := by
  -- `∂_τ u ∈ H¹₀(H)`, with gradient `D²u τ`, solves the differentiated equation in `H`.
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value_of_firstOrder_mem_w1p0Submodule (by simp)
    (convex_of_halfSpace hH) (mapsTo_add_smul_of_halfSpace hH hτ) hu0
  obtain ⟨hgrad, heqn⟩ :=
    gradient_ae_eq_iteratedGradient_apply_and_energyFormH1_eq_of_hasWeakLineDerivOn u hd
  refine ⟨W1p0.extendByZeroL (le_top : H ≤ ⊤) d, ?_, ?_, ?_⟩
  · filter_upwards [W1p0.value_extendByZeroL_ae (le_top : H ≤ ⊤) d] with x hx hxH
    rw [hx, indicator_of_notMem hxH]
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 le_top)
        (W1p0.gradient_extendByZeroL_ae (le_top : H ≤ ⊤) d), hgrad,
      ae_restrict_mem H.isOpen.measurableSet] with x h1 h2 hx
    rw [h1, indicator_of_mem hx, h2]
  · -- On `⊤ ⊓ H = H` the restriction of the zero extension is `∂_τ u` itself.
    have key : ∀ V : Opens E, V = H → ∀ (hV : V ≤ ⊤) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (φ : 𝓓(V, ℝ)), energyFormH1 (fun _ => A) 0 0
          (W1p.restrictL hV (W1p0.extendByZeroL (le_top : H ≤ ⊤) d : W1p volume ⊤ 2))
          (W1p.ofTestFunctionₗ volume V 2 φ) =
        ∫ x in V, ⟪(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
          (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • τ,
            ∇ (φ : E → ℝ) x⟫_ℝ := by
      rintro V rfl hV A φ
      rw [W1p0.restrictL_extendByZeroL]
      exact heqn A φ
    exact key _ (top_inf_eq H) inf_le_left

/-- **Mean oscillation of the tangential columns of the Hessian at a flat boundary, constant
coefficients.** Let `0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the
following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary
hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with
constants `λ`, `Λ`, and let `u ∈ W^{2,2}(H)`, with first-order part in `H¹₀(H)`, solve
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`. Then for every tangential direction `τ`,
`⟪τ, ν⟫ = 0`, every `0 < ρ ≤ r` and every real `t`,

`∫_{B_ρ⁺} ‖D²u τ - p_ρ‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u τ - t ν‖² + C ‖τ‖² ∫_{B_r⁺} f²`,

where `p_ρ = (⟪(D²u τ)_{B_ρ⁺}, ν⟫ / ‖ν‖²) ν` is the multiple of `ν` closest to `D²u τ` in
`L²(B_ρ⁺)`. Here `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, and
`∂ᵢ∂ⱼu = ⟪D²u eᵢ, eⱼ⟫`. -/
private theorem
    exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_sq_le_add_of_sum_mul_inner_eq
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Opens E} {u : Wkp volume H 2 2}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {f : E → ℝ} {ν z τ : E} {c₀ r ρ : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ⟪τ, ν⟫_ℝ = 0 →
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2 →
      (∀ᵐ x ∂volume.restrict (ball z r ∩ H), ∑ i, ∑ j, A i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      0 < ρ → ρ ≤ r → ∀ t : ℝ,
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          (⟪⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 3) *
            (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ - t • ν‖ ^ 2) +
          C * ‖τ‖ ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 := by
  obtain ⟨C, hC, hest⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add
      (n := n) (Lam := Lam) hlam
  refine ⟨C, hC, ?_⟩
  intro H u A f ν z τ c₀ r ρ hA hν hH hzc hτ hu0 heq hρ hρr t
  obtain ⟨W, hW0, hWg, hWeq⟩ := exists_extension_tangential_derivative hH hτ hu0
  -- The frozen right-hand side `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is square integrable on `H`.
  set g : E → ℝ := fun x => ∑ i, ∑ j, A i j *
    ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ
  have hg : MemLp g 2 (volume.restrict (ball z r ∩ H)) :=
    (((Matrix.contraction A).comp_memLp' (Lp.memLp (Wkp.iteratedGradient 1 u))).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)).ae_eq
      (ae_of_all _ fun x => Matrix.contraction_apply A _)
  have hGc : MemLp (fun x => g x • τ - 0) 2 (volume.restrict (ball z r ∩ H)) := by
    simpa only [sub_zero, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using
      (ContinuousLinearMap.toSpanSingleton ℝ τ).comp_memLp' hg
  -- The coefficient `A` deviates from itself by zero.
  have hAA : matrixBilinearForm A - matrixBilinearForm A = 0 := sub_self (matrixBilinearForm A)
  have hθ0 : ‖matrixBilinearForm A - matrixBilinearForm A‖ = 0 := by
    rw [hAA, ContinuousLinearMap.opNorm_zero]
  have key := hest (U := ⊤) (a := fun _ => A) (G := fun x => g x • τ) (c := 0) (K := 0) hA
    aestronglyMeasurable_const (fun _ _ => hθ0.le) hν hH hzc (by simp) hW0 (hWeq A) hGc hρ hρr t
  -- On the half-balls the gradient of the extension is the column `D²u τ`, and `g = f`.
  have hWt : ∀ s : ℝ, (W1p.gradient W : E → E) =ᵐ[volume.restrict (ball z s ∩ H)]
      fun x => Wkp.iteratedGradient 1 u x τ := fun s =>
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hWg
  have hgf : ∫ x in ball z r ∩ H, ‖g x • τ - 0‖ ^ 2 = ‖τ‖ ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [heq] with x hx
    rw [sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← hx, mul_comm]
  rw [average_congr (hWt ρ), integral_congr_ae ((hWt ρ).mono fun x hx => by rw [hx]),
    integral_congr_ae ((hWt r).mono fun x hx => by rw [hx]), hgf] at key
  simpa [hθ0, mul_assoc] using key

/-- **Mean oscillation of the tangential columns of the Hessian at a flat boundary.** Let
`0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the following property. Let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with constants `λ`, `Λ`, and
let `a` be measurable on `B_r⁺` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the operator norm of the
attached bilinear forms. Let `u ∈ W^{2,2}(H)`, with first-order part in `H¹₀(H)`, solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`. Then for every tangential direction `τ`,
`⟪τ, ν⟫ = 0`, every `0 < ρ ≤ r` and every real `t`,

`∫_{B_ρ⁺} ‖D²u τ - p_ρ‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u τ - t ν‖²`
`  + C ‖τ‖² (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`,

where `p_ρ` is the multiple of `ν` closest to `D²u τ` in `L²(B_ρ⁺)`. Neither continuity nor
symmetry of `a` is assumed. -/
theorem
  exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_inner_setAverage_div_smul_sq_le_add
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Opens E} {u : Wkp volume H 2 2}
      {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : E → ℝ} {ν z τ : E} {c₀ r ρ K : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ⟪τ, ν⟫_ℝ = 0 →
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2 →
      (∀ᵐ x ∂volume.restrict (ball z r ∩ H), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      0 < ρ → ρ ≤ r → ∀ t : ℝ,
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          (⟪⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 3) *
            (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ - t • ν‖ ^ 2) +
          C * ‖τ‖ ^ 2 * ((∫ x in ball z r ∩ H, f x ^ 2) +
            ∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
              ‖Wkp.iteratedGradient 1 u x‖ ^ 2) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_sq_le_add_of_sum_mul_inner_eq
      (n := n) (Lam := Lam) hlam
  refine ⟨2 * (n + 1) ^ 2 * C, by positivity, ?_⟩
  intro H u a A f ν z τ c₀ r ρ K hA ha haK hν hH hzc hτ hu0 heq hρ hρr t
  -- Freeze the coefficients at `A`: the right-hand side becomes `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`.
  have key := hest (f := fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x)) hA hν hH hzc
    hτ hu0 (ae_of_all _ fun x => (Matrix.contraction_apply A _).symm) hρ hρr t
  have hcon := setIntegral_contraction_sq_le (measurableSet_ball.inter H.isOpen.measurableSet) ha
    haK u inter_subset_right heq
  have hS : MeasurableSet (ball z r ∩ (H : Set E)) :=
    measurableSet_ball.inter H.isOpen.measurableSet
  set X := ∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ - t • ν‖ ^ 2
  set F := ∫ x in ball z r ∩ H, f x ^ 2
  set T := ∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
    ‖Wkp.iteratedGradient 1 u x‖ ^ 2
  have hP : 0 ≤ C * (ρ / r) ^ (n + 3) * X :=
    mul_nonneg (mul_nonneg hC.le (pow_nonneg (div_nonneg hρ.le (hρ.le.trans hρr)) _))
      (setIntegral_nonneg hS fun _ _ => by positivity)
  have hF : 0 ≤ F := setIntegral_nonneg hS fun _ _ => by positivity
  have hQ : 0 ≤ C * ‖τ‖ ^ 2 := mul_nonneg hC.le (sq_nonneg _)
  have hm : (1 : ℝ) ≤ (n + 1) ^ 2 := one_le_pow₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  -- Collect the constants: `C ≤ 2 (n + 1)² C`.
  calc _ ≤ C * (ρ / r) ^ (n + 3) * X + C * ‖τ‖ ^ 2 * (2 * (F + (n + 1) ^ 2 * T)) :=
        key.trans (by gcongr)
    _ ≤ _ := by
        nlinarith [mul_nonneg hP (sub_nonneg.2 hm), mul_nonneg (mul_nonneg hQ hF) (sub_nonneg.2 hm)]

/-- **Mean oscillation of the tangential columns of the Hessian at a flat boundary, averaged
form.** Let `0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the following
property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary hyperplane, and
write `B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with constants `λ`,
`Λ`, and let `a` be measurable on `B_r⁺` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the operator norm
of the attached bilinear forms. Let `u ∈ W^{2,2}(H)`, with first-order part in `H¹₀(H)`, solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`, and let `D²u ∈ L^{2q}(B_r⁺)` for a pair of Hölder
conjugate exponents `q, q'`. Then for every tangential direction `τ`, `⟪τ, ν⟫ = 0`, every
`0 < ρ ≤ r` and every real `t`,

`⨍_{B_ρ⁺} ‖D²u τ - p_ρ‖² ≤ C (ρ / r)² ⨍_{B_r⁺} ‖D²u τ - t ν‖²`
`  + C ‖τ‖² (r / ρ)^(n + 1) (⨍_{B_r⁺} f² + E)`

with `E = (K^(2q' - 1) ⨍_{B_r⁺} θ)^(1/q') (⨍_{B_r⁺} ‖D²u‖^(2q))^(1/q)`, where `p_ρ` is the
multiple of `ν` closest to `D²u τ` in `L²(B_ρ⁺)`. Every average is invariant under dilations about
`z`, and the coefficients enter only through the mean deviation `⨍_{B_r⁺} θ`. -/
theorem exists_setAverage_ball_inter_norm_iteratedGradient_apply_sub_inner_setAverage_div_smul_sq_le
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Opens E} {u : Wkp volume H 2 2}
      {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : E → ℝ} {ν z τ : E} {c₀ r ρ K q q' : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ⟪τ, ν⟫_ℝ = 0 →
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2 →
      (∀ᵐ x ∂volume.restrict (ball z r ∩ H), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      q.HolderConjugate q' →
      MemLp (Wkp.iteratedGradient 1 u : E → E →L[ℝ] E) (ENNReal.ofReal (2 * q))
        (volume.restrict (ball z r ∩ H)) →
      0 < ρ → ρ ≤ r → ∀ t : ℝ,
      ⨍ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          (⟪⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ 2 * (⨍ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ - t • ν‖ ^ 2) +
          C * ‖τ‖ ^ 2 * (r / ρ) ^ (n + 1) * ((⨍ x in ball z r ∩ H, f x ^ 2) +
            (K ^ (2 * q' - 1) *
                ⨍ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖) ^ q'⁻¹ *
              (⨍ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x‖ ^ (2 * q)) ^ q⁻¹) := by
  obtain ⟨C, hC, hest⟩ :=
  exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_inner_setAverage_div_smul_sq_le_add
      (n := n) (Lam := Lam) hlam
  refine ⟨C, hC, ?_⟩
  intro H u a A f ν z τ c₀ r ρ K q q' hA ha haK hν hH hzc hτ hu0 heq hq hHq hρ hρr t
  have hr : 0 < r := hρ.trans_le hρr
  -- The half-balls have positive measure and scale like the balls.
  have hHs (s : ℝ) : {y | c₀ < ⟪y, ν⟫_ℝ} ∩ ball z s = ball z s ∩ H := by ext; simp [hH, and_comm]
  have hV := volume.addHaar_real_setOf_lt_inner_inter_ball_pos hν hzc hr
  have hVρ := volume.addHaar_real_setOf_lt_inner_inter_ball_eq_div_pow_mul hν hzc hρ.le hr
  simp only [hHs, finrank_euclideanSpace_fin] at hV hVρ
  set S := ball z r ∩ (H : Set E)
  set θ : E → ℝ := fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖
  have hθm : AEStronglyMeasurable θ (volume.restrict S) :=
    aestronglyMeasurable_norm_matrixBilinearForm_sub ha A
  have hθ : ∀ᵐ x ∂volume.restrict S, 0 ≤ θ x ∧ θ x ≤ K :=
    (ae_restrict_mem (measurableSet_ball.inter H.isOpen.measurableSet)).mono fun x hx =>
      ⟨norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A), haK x hx⟩
  have key : ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
        (⟪⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
      C * (ρ / r) ^ (n + 1 + 2) * (∫ x in S, ‖Wkp.iteratedGradient 1 u x τ - t • ν‖ ^ 2) +
        C * ‖τ‖ ^ 2 * (1 * (∫ x in S, θ x ^ 2 * ‖Wkp.iteratedGradient 1 u x‖ ^ 2) +
          ∫ x in S, f x ^ 2) :=
    (hest hA ha haK hν hH hzc hτ hu0 heq hρ hρr t).trans_eq (by ring)
  -- Pass to averages, using `|B_ρ⁺| = (ρ / r)^(n + 1) |B_r⁺|` and Hölder's inequality.
  refine (setAverage_le_of_setIntegral_le_add_sq_mul_norm_sq hV (div_pos hρ hr) hVρ
    (mul_nonneg hC.le (sq_nonneg _)) zero_le_one hq hθm hθ hHq key).trans_eq ?_
  rw [inv_div]
  ring

/-- **Mean oscillation of a tangential column of the Hessian about its average.** With the
notation of
`exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_sq_le_add_of_sum_mul_inner_eq`, the
square mean oscillation of the column `D²u τ` on `B_ρ⁺ = B(z, ρ) ∩ H` about its average decays
like that of a solution of the homogeneous equation, up to the `L²` norm of `g τ`,
`g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. No equation for `u` is assumed. -/
private theorem exists_setIntegral_ball_inter_norm_apply_sub_setAverage_sq_le {lam Lam : ℝ}
    (hlam : 0 < lam) :
    ∃ D : ℝ, 0 < D ∧ ∀ {H : Opens E} {u : Wkp volume H 2 2}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ν z τ : E} {c₀ r ρ : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ⟪τ, ν⟫_ℝ = 0 →
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2 → 0 < ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ‖ ^ 2 ≤
        D * (ρ / r) ^ (n + 3) * (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ‖ ^ 2) +
          D * ‖τ‖ ^ 2 *
            ∫ x in ball z r ∩ H, Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2 := by
  obtain ⟨D, hD, hest⟩ :=
    exists_setIntegral_ball_inter_norm_iteratedGradient_apply_sub_sq_le_add_of_sum_mul_inner_eq
      (n := n) (Lam := Lam) hlam
  refine ⟨D, hD, fun {H u A ν z τ c₀ r ρ} hA hν hH hzc hτ hu0 hρ hρr => ?_⟩
  -- `u` solves the constant-coefficient equation with right-hand side `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`.
  have key := hest (f := fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x)) hA hν hH hzc
    hτ hu0 (ae_of_all _ fun x => (Matrix.contraction_apply A _).symm) hρ hρr 0
  simp only [zero_smul, sub_zero] at key
  have htH : ball z ρ ∩ (H : Set E) ⊆ H := inter_subset_right
  have hht : volume (ball z ρ ∩ (H : Set E)) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have : IsFiniteMeasure (volume.restrict (ball z ρ ∩ (H : Set E))) :=
    isFiniteMeasure_restrict.2 hht
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2 (volume.restrict (H : Set E)) :=
    Lp.memLp _
  have hTτ : MemLp (fun x => Wkp.iteratedGradient 1 u x τ) 2 (volume.restrict (H : Set E)) :=
    (ContinuousLinearMap.apply ℝ E τ).comp_memLp' hT
  -- The average is the best constant, in particular better than the multiple `p_ρ` of `ν`.
  exact (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hht
    ((hTτ.mono_measure (Measure.restrict_mono htH le_rfl)).integrable one_le_two)
    (hTτ.integrableOn_norm_sub_sq_of_subset htH hht _)).trans key

/-- **The Hessian is controlled by its tangential columns and the equation.** Let `w` be a unit
vector, `τⱼ = eⱼ - ⟪eⱼ, w⟫ w`, and let `A` be a matrix with `λ ≤ ⟪A w, w⟫` and `‖A‖ ≤ Λ`. Almost
everywhere on a set `t ⊆ Ω` of finite measure, the deviation of the Hessian of `u ∈ W^{2,2}(Ω)` from
its average over `t` is controlled by the deviations of its columns `D²u τⱼ` and of
`g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` from their averages. -/
private theorem ae_norm_iteratedGradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hΛ : ‖matrixBilinearForm A‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    {t : Set (EuclideanSpace ℝ (Fin (n + 1)))} (htΩ : t ⊆ Omega) (ht : volume t ≠ ⊤) :
    ∀ᵐ x ∂volume.restrict t, ‖Wkp.iteratedGradient 1 u x -
        ⨍ y in t, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2 *
          ∑ j, ‖Wkp.iteratedGradient 1 u x (τ j) - ⨍ y in t, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2 +
        2 / lam ^ 2 * (Matrix.contraction A (Wkp.iteratedGradient 1 u x) -
          ⨍ y in t, Matrix.contraction A (Wkp.iteratedGradient 1 u y)) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict t) := isFiniteMeasure_restrict.2 ht
  have hT : Integrable (fun x => Wkp.iteratedGradient 1 u x) (volume.restrict t) :=
    ((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono htΩ le_rfl)).integrable one_le_two
  -- Averages commute with continuous linear functionals of the Hessian.
  have havg : ∀ L : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ,
      L (⨍ y in t, Wkp.iteratedGradient 1 u y) =
        ⨍ y in t, L (Wkp.iteratedGradient 1 u y) := fun L => by
    rw [setAverage_eq, setAverage_eq, map_smul, L.integral_comp_comm hT]
  have hsym := ae_restrict_of_ae_restrict_of_subset htΩ (ae_all_iff.2 fun j =>
    Wkp.inner_iteratedGradient_one_apply_ae_eq u w (τ j))
  -- The average of the Hessian is symmetric between `w` and each `τⱼ`.
  have hMsym : ∀ j, ⟪(⨍ y in t, Wkp.iteratedGradient 1 u y) w, τ j⟫_ℝ =
      ⟪(⨍ y in t, Wkp.iteratedGradient 1 u y) (τ j), w⟫_ℝ := fun j => by
    set M := ⨍ y in t, Wkp.iteratedGradient 1 u y
    have h1 := havg ((innerSL ℝ (τ j)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) w))
    have h2 := havg ((innerSL ℝ w).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) (τ j)))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply] at h1 h2
    rw [← real_inner_comm (M w) (τ j), ← real_inner_comm (M (τ j)) w, h1, h2]
    exact average_congr (hsym.mono fun y hy => by
      beta_reduce
      rw [real_inner_comm (Wkp.iteratedGradient 1 u y w) (τ j)]
      exact (hy j).trans (real_inner_comm _ _))
  filter_upwards [hsym] with x hx
  have key := norm_sq_le_sum_norm_apply_sq_add_contraction_sq hlam hΛ hw hAw hτ
    (Wkp.iteratedGradient 1 u x - ⨍ y in t, Wkp.iteratedGradient 1 u y) fun j => by
      rw [sub_apply, sub_apply, inner_sub_left, inner_sub_left, hx j, hMsym j]
  rw [map_sub, havg] at key
  simpa only [sub_apply, ContinuousLinearMap.average_apply hT, Nat.cast_add, Nat.cast_one]
    using key

/-- **The integrated pointwise bound.** With `w`, `A` and `t` as in
`ae_norm_iteratedGradient_sub_setAverage_sq_le`, the square mean oscillation of the Hessian over
`t` is controlled by those of its columns `D²u τⱼ` and of `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem setIntegral_norm_iteratedGradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hΛ : ‖matrixBilinearForm A‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    {t : Set (EuclideanSpace ℝ (Fin (n + 1)))} (htΩ : t ⊆ Omega) (htf : volume t ≠ ⊤) :
    ∫ x in t, ‖Wkp.iteratedGradient 1 u x - ⨍ y in t, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2 * (∑ j, ∫ x in t,
        ‖Wkp.iteratedGradient 1 u x (τ j) - ⨍ y in t, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2) +
      2 / lam ^ 2 * ∫ x in t, (Matrix.contraction A (Wkp.iteratedGradient 1 u x) -
        ⨍ y in t, Matrix.contraction A (Wkp.iteratedGradient 1 u y)) ^ 2 := by
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := Lp.memLp _
  have hTτ : ∀ v, MemLp (fun x => Wkp.iteratedGradient 1 u x v) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := fun v =>
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) v).comp_memLp' hT
  have hg : MemLp (fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x)) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Matrix.contraction A).comp_memLp' hT
  have hgsq : ∀ c : ℝ, IntegrableOn (fun x =>
      (Matrix.contraction A (Wkp.iteratedGradient 1 u x) - c) ^ 2) t := fun c =>
    (hg.integrableOn_norm_sub_sq_of_subset htΩ htf c).congr
      (ae_of_all _ fun x => by simp only [Real.norm_eq_abs, sq_abs])
  have hint := integral_mono_ae (hT.integrableOn_norm_sub_sq_of_subset htΩ htf _)
    (((integrable_finsetSum _ fun j _ => (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf
      _).const_mul _).add ((hgsq _).const_mul _))
    (ae_norm_iteratedGradient_sub_setAverage_sq_le u hlam hΛ hw hAw hτ htΩ htf)
  refine hint.trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (((integrable_finsetSum _ fun j _ =>
      (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf _).const_mul _))
      ((hgsq _).const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun j _ => (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf _]

/-- For `w = ‖ν‖⁻¹ ν` the tangential parts `eⱼ - ⟪eⱼ, w⟫ w` of the coordinate vectors are
orthogonal to `ν`. -/
private theorem inner_single_sub_inner_smul_eq_zero {ν : EuclideanSpace ℝ (Fin (n + 1))}
    (hν : ν ≠ 0) (j : Fin (n + 1)) :
    ⟪EuclideanSpace.single j (1 : ℝ) - ⟪EuclideanSpace.single j (1 : ℝ), ‖ν‖⁻¹ • ν⟫_ℝ •
      (‖ν‖⁻¹ • ν), ν⟫_ℝ = 0 := by
  have hν0 : ‖ν‖ ≠ 0 := norm_ne_zero_iff.2 hν
  simp only [inner_sub_left, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real]
  field_simp
  ring

/-- For a unit vector `w`, the tangential parts `eⱼ - ⟪eⱼ, w⟫ w` have norm at most `2`. -/
private theorem norm_single_sub_inner_smul_le_two {w : EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ‖w‖ = 1) (j : Fin (n + 1)) :
    ‖EuclideanSpace.single j (1 : ℝ) - ⟪EuclideanSpace.single j (1 : ℝ), w⟫_ℝ • w‖ ≤ 2 := by
  have h1 := abs_real_inner_le_norm (EuclideanSpace.single j (1 : ℝ)) w
  rw [PiLp.norm_single, norm_one, hw, mul_one] at h1
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, hw, mul_one, Real.norm_eq_abs, PiLp.norm_single, norm_one]
  linarith

/-- A column `D²u τ` with `‖τ‖ ≤ 2` has at most four times the `L²` mass of `D²u` on a set
`s ⊆ Ω` of finite measure. -/
private theorem setIntegral_norm_iteratedGradient_apply_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {τ : EuclideanSpace ℝ (Fin (n + 1))} (hτ : ‖τ‖ ≤ 2) {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hsΩ : s ⊆ Omega) (hsm : MeasurableSet s) (hsf : volume s ≠ ⊤) :
    ∫ x in s, ‖Wkp.iteratedGradient 1 u x τ‖ ^ 2 ≤
      4 * ∫ x in s, ‖Wkp.iteratedGradient 1 u x‖ ^ 2 := by
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := Lp.memLp _
  have hTs := hT.integrableOn_norm_sub_sq_of_subset hsΩ hsf 0
  have hTτs := ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) τ).comp_memLp'
    hT).integrableOn_norm_sub_sq_of_subset hsΩ hsf 0
  simp only [sub_zero] at hTs hTτs
  rw [← integral_const_mul]
  refine setIntegral_mono_on hTτs (hTs.const_mul 4) hsm fun x _ => ?_
  have h1 := (Wkp.iteratedGradient 1 u x).le_opNorm τ
  have h2 := mul_le_mul_of_nonneg_left hτ (norm_nonneg (Wkp.iteratedGradient 1 u x))
  nlinarith [norm_nonneg (Wkp.iteratedGradient 1 u x τ)]

/-- The arithmetic that collects the constants in
`exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add`. -/
private theorem final_bound {C₁ D lam q I F Θ G Gt X Ψ : ℝ} (hC₁0 : 0 ≤ C₁) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hI : 0 ≤ I) (hF : 0 ≤ F) (hΘ : 0 ≤ Θ)
    (hX : X ≤ C₁ * Ψ + 2 / lam ^ 2 * Gt) (hsum : Ψ ≤ (n + 1) * (D * q * (4 * I) + D * (4 * G)))
    (hGt : Gt ≤ G) (hG : G ≤ 2 * (F + (n + 1) ^ 2 * Θ)) :
    X ≤ (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
        q * I +
      (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
        (F + Θ) := by
  have hn : (1 : ℝ) ≤ (n + 1) ^ 2 := one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])
  refine hX.trans ?_
  have hG' : G ≤ 2 * (n + 1) ^ 2 * (F + Θ) := hG.trans (by nlinarith)
  have hP : 0 ≤ 4 * C₁ * (n + 1) * D := by positivity
  have hR : 0 ≤ 4 * C₁ * (n + 1) * D + 2 / lam ^ 2 := by positivity
  have hR' : 0 ≤ 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) := by positivity
  calc C₁ * Ψ + 2 / lam ^ 2 * Gt
      ≤ C₁ * ((n + 1) * (D * q * (4 * I) + D * (4 * G))) + 2 / lam ^ 2 * G :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hC₁0)
          (mul_le_mul_of_nonneg_left hGt (by positivity))
    _ = 4 * C₁ * (n + 1) * D * (q * I) + (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * G := by ring
    _ ≤ (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
          (q * I) + (2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2)) * (F + Θ) := by
        refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq hI)) ?_
        calc (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * G
            ≤ (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * (2 * (n + 1) ^ 2 * (F + Θ)) :=
              mul_le_mul_of_nonneg_left hG' hR
          _ = _ := by ring
    _ ≤ _ := by
        rw [← mul_assoc _ q I]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hF hΘ))

/-- **Mean oscillation of the Hessian at a flat boundary.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `z` lie on its boundary hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let
`u ∈ W^{2,2}(H)` have zero boundary values, with first-order part in `H¹₀(H)`, and solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`. Let `A` be a constant matrix, uniformly elliptic
with constants `0 < λ ≤ Λ`, and suppose that `a` is measurable on `B_r⁺` and that
`θ(x) = ‖a(x) - A‖`, in the operator norm of the attached bilinear forms, is bounded there. Then
there is `C`, depending only on `n`, `λ` and `Λ`, such that for `0 < ρ ≤ r`

`∫_{B_ρ⁺} ‖D²u - (D²u)_{B_ρ⁺}‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u‖²`
`  + C (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`.

Neither continuity nor symmetry of `a` is assumed. This is the boundary counterpart of the
interior estimate
`setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`.
-/
theorem exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) H 2 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ K : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume H 2 →
      (∀ᵐ x ∂volume.restrict (ball z r ∩ H), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      0 < ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x -
          ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 3) * (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x‖ ^ 2) +
          C * ((∫ x in ball z r ∩ H, f x ^ 2) +
            ∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
              ‖Wkp.iteratedGradient 1 u x‖ ^ 2) := by
  obtain ⟨D, hD, hcol⟩ := exists_setIntegral_ball_inter_norm_apply_sub_setAverage_sq_le
    (n := n) (Lam := Lam) hlam
  set C₁ : ℝ := 2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1,
    by positivity, fun {H u a A f ν z c₀ r ρ K} hA ha haK hν hH hzc hu0 heq hρ hρr => ?_⟩
  have hz : z ∈ ball z r := mem_ball_self (hρ.trans_le hρr)
  have hΛ := matrixBilinearForm_opNorm_le_of_upper_bound A (hA.pos.le.trans hA.le)
    (hA.upper_bound hz)
  -- The unit normal `w` and the tangential parts `τⱼ = eⱼ - ⟪eⱼ, w⟫ w` of the coordinate vectors.
  set w := ‖ν‖⁻¹ • ν
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hν
  have hAw : lam ≤ matrixBilinearForm A w w := by
    have := hA.lower_bound hz w
    rwa [← matrixBilinearForm_self, hw, one_pow, mul_one] at this
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)), ∀ j,
      τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w := ⟨_, fun _ => rfl⟩
  have hτν : ∀ j, ⟪τ j, ν⟫_ℝ = 0 := fun j => hτ j ▸ inner_single_sub_inner_smul_eq_zero hν j
  have hτ2 : ∀ j, ‖τ j‖ ≤ 2 := fun j => hτ j ▸ norm_single_sub_inner_smul_le_two hw j
  have hts : ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z r ∩ H :=
    inter_subset_inter_left _ (ball_subset_ball hρr)
  have hsm : MeasurableSet (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    measurableSet_ball.inter H.isOpen.measurableSet
  have hsf : volume (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have htf : volume (ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    ((measure_mono hts).trans_lt hsf.lt_top).ne
  have hint' := setIntegral_norm_iteratedGradient_sub_setAverage_sq_le u hlam hΛ hw hAw hτ
    inter_subset_right htf
  have hq : 0 ≤ (ρ / r) ^ (n + 3) := pow_nonneg (div_nonneg hρ.le (hρ.trans_le hρr).le) _
  -- Each tangential column decays, up to the `L²` norm of `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`.
  have hcolj : ∀ j, ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x (τ j) -
      ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2 ≤
      D * (ρ / r) ^ (n + 3) * (4 * ∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x‖ ^ 2) +
        D * (4 * ∫ x in ball z r ∩ H, Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2) :=
      fun j => by
    have h1 := setIntegral_norm_iteratedGradient_apply_sq_le u (hτ2 j) inter_subset_right hsm hsf
    have h2 : ‖τ j‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (τ j), hτ2 j]
    have hG0 : 0 ≤ ∫ x in ball z r ∩ H, Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2 :=
      setIntegral_nonneg hsm fun _ _ => sq_nonneg _
    refine (hcol hA hν hH hzc (hτν j) hu0 hρ hρr).trans (add_le_add
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg hD.le hq)) ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hG0) hD.le
  -- The oscillation of `g` is at most its `L²` norm, which the equation controls.
  have hGt := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sq_of_subset
    (((Matrix.contraction A).comp_memLp' (Lp.memLp (Wkp.iteratedGradient 1 u))).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)) hts htf
  simp only [Real.norm_eq_abs, sq_abs] at hGt
  have hG := setIntegral_contraction_sq_le hsm ha haK u inter_subset_right heq
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcolj j
  push_cast [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine final_bound hC₁0 hD.le hq ?_ ?_ ?_ hint' hsum hGt hG <;>
    exact setIntegral_nonneg hsm fun _ _ => by positivity

end PDE

end TauCeti
