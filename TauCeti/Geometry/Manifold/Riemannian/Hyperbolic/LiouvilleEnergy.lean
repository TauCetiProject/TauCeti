/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.Poincare
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# The Liouville energy of the curvature equation

Let `M` be a closed surface with a Riemannian metric `g`, volume `dV` and Gaussian curvature
`K = Scal^g / 2`. The metric `e^(2u) g` is hyperbolic exactly when `u` solves the curvature
equation `Δ⁺u + K + e^(2u) = 0`, where `Δ⁺ = -div grad` is the nonnegative Laplacian
(`Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`). This equation is
the Euler–Lagrange equation of the **Liouville energy**

`J(u) = ∫ (|∇u|² / 2 + K u + e^(2u) / 2) dV`

(`TauCeti.Manifold.liouvilleEnergy`), and this file sets up the variational treatment of the
equation through `J`. The function `K` is arbitrary here; nothing below uses the dimension.

The first variation of `J` at `u` in the direction `v` is
`∫ (⟪∇v, ∇u⟫ + K v + e^(2u) v) dV`, which Green's identity turns into `∫ v (Δ⁺u + K + e^(2u)) dV`
on a closed manifold. Hence a `C²` function is a critical point of `J` exactly when it solves the
equation. The integrand of `J` is convex in `(u, ∇u)`, so `J` lies above its tangent lines at a `C²`
function, and a solution is a global minimizer of `J`; conversely a `C²` minimizer is a solution.

For existence by minimization, the decisive property is coercivity. Suppose `M` is connected and
`∫ K dV < 0`; when `K` is the Gaussian curvature of a closed surface, Gauss–Bonnet identifies
`∫ K dV` with `2π χ(M)`, so this says that `M` has negative Euler characteristic. Writing
`u = ū + w` with `ū = ⨍ u` the mean, Jensen's inequality bounds `∫ e^(2u) dV` below by
`Vol(M) e^(2ū)`, and the Poincaré–Wirtinger inequality bounds `∫ K w dV` by the Dirichlet
energy. This gives a constant `C` with

`(∫ |∇u|² dV) / 4 + (-∫ K dV) |ū| ≤ J(u) + C`

for every `C¹` function `u`. In particular `J` is bounded below, and a sequence on which `J` is
bounded has bounded Dirichlet energy and bounded means, hence is bounded in `H¹`.

## Main results

* `TauCeti.Manifold.liouvilleEnergy`: the Liouville energy `J`.
* `TauCeti.Manifold.hasDerivAt_liouvilleEnergy_add_smul`: the first variation of `J`, and
  `TauCeti.Manifold.hasDerivAt_liouvilleEnergy_add_smul_eq_integral`: its form
  `∫ v (Δ⁺u + K + e^(2u)) dV` on a closed manifold.
* `TauCeti.Manifold.forall_hasDerivAt_liouvilleEnergy_add_smul_iff`: the critical points of `J`
  are the solutions of `Δ⁺u + K + e^(2u) = 0`.
* `TauCeti.Manifold.liouvilleEnergy_add_integral_mul_le`: the convexity inequality for `J`.
* `TauCeti.Manifold.liouvilleEnergy_le_of_neg_laplaceBeltrami_add_add_exp_eq_zero`: a solution
  minimizes `J`, and `TauCeti.Manifold.forall_liouvilleEnergy_le_iff`: the `C²` minimizers of `J`
  are exactly the solutions.
* `TauCeti.Manifold.exists_le_liouvilleEnergy_add`: the coercivity estimate, and
  `TauCeti.Manifold.bddBelow_liouvilleEnergy_image`: `J` is bounded below.

## References

* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47, §3.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 6.
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]

section Definition

variable [IsManifold I 1 M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The **Liouville energy** `J(u) = ∫ (|∇u|² / 2 + K u + e^(2u) / 2) dV` of a function `u`, for a
function `K` on a Riemannian manifold. Its Euler–Lagrange equation is `Δ⁺u + K + e^(2u) = 0`, with
`Δ⁺ = -div grad`; when `K` is the Gaussian curvature of a surface, this says that `e^(2u) g` has
curvature `-1`. Its classical meaning is for differentiable `u`. -/
def liouvilleEnergy (K u : M → ℝ) : ℝ :=
  ∫ x, (‖mgradient I u x‖ ^ 2 / 2 + K x * u x + Real.exp (2 * u x) / 2) ∂riemannianVolume I M

/-- Unfolding lemma for `TauCeti.Manifold.liouvilleEnergy`. -/
theorem liouvilleEnergy_def (K u : M → ℝ) :
    liouvilleEnergy I K u =
      ∫ x, (‖mgradient I u x‖ ^ 2 / 2 + K x * u x + Real.exp (2 * u x) / 2)
        ∂riemannianVolume I M :=
  (rfl)

end Definition

section Compact

variable [IsManifold I 1 M] [CompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A continuous function on a compact Riemannian manifold is integrable. -/
private theorem integrable_of_continuous {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolume I M) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The product of an integrable function with a continuous function on a compact Riemannian
manifold is integrable. -/
private theorem integrable_mul_of_continuous {K f : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hf : Continuous f) :
    Integrable (fun x ↦ K x * f x) (riemannianVolume I M) :=
  hK.mul_of_top_left (hf.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace f) _)

/-- On a compact manifold, the Liouville energy of a `C¹` function `u` is
`(∫ |∇u|² dV) / 2 + ∫ K u dV + (∫ e^(2u) dV) / 2`, for an integrable `K`. -/
theorem liouvilleEnergy_eq_add {K u : M → ℝ} (hK : Integrable K (riemannianVolume I M))
    (hu : ContMDiff I 𝓘(ℝ) 1 u) :
    liouvilleEnergy I K u =
      (∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M) / 2 +
        ∫ x, K x * u x ∂riemannianVolume I M +
          (∫ x, Real.exp (2 * u x) ∂riemannianVolume I M) / 2 := by
  have hexp : Continuous fun x ↦ Real.exp (2 * u x) :=
    Real.continuous_exp.comp (continuous_const.mul hu.continuous)
  have hG : Integrable (fun x ↦ ‖mgradient I u x‖ ^ 2 / 2) (riemannianVolume I M) :=
    (integrable_of_continuous (continuous_norm_sq_mgradient hu)).div_const 2
  rw [liouvilleEnergy_def, integral_add (f := fun x ↦ ‖mgradient I u x‖ ^ 2 / 2 + K x * u x)
      (hG.add (integrable_mul_of_continuous hK hu.continuous))
      ((integrable_of_continuous hexp).div_const 2),
    integral_add hG (integrable_mul_of_continuous hK hu.continuous), integral_div, integral_div]

/-- The derivative of `t ↦ ∫ e^(2 (u + t v)) dV` at `t = 0` is `∫ 2 v e^(2u) dV`, for continuous
`u` and `v` on a compact manifold. -/
private theorem hasDerivAt_integral_exp_add_mul {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, Real.exp (2 * (u x + t * v x)) ∂riemannianVolume I M)
      (∫ x, 2 * v x * Real.exp (2 * u x) ∂riemannianVolume I M) 0 := by
  have hF (t : ℝ) : Continuous fun x ↦ Real.exp (2 * (u x + t * v x)) := by fun_prop
  -- On `|t| < 1` the `t`-derivative `2 v e^(2 (u + t v))` is at most `2 |v| e^(2 (|u| + |v|))`.
  have hbound (x : M) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) :
      ‖2 * v x * Real.exp (2 * (u x + t * v x))‖ ≤
        2 * |v x| * Real.exp (2 * (|u x| + |v x|)) := by
    have ht' : |t| ≤ 1 := (mem_ball_zero_iff.1 ht).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, Real.abs_exp]
    gcongr
    · exact le_abs_self _
    · calc t * v x ≤ |t| * |v x| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |v x| := mul_le_of_le_one_left (abs_nonneg _) ht'
  have hderiv (x : M) (t : ℝ) :
      HasDerivAt (fun t ↦ Real.exp (2 * (u x + t * v x)))
        (2 * v x * Real.exp (2 * (u x + t * v x))) t := by
    have := (((hasDerivAt_id' t).mul_const (v x)).const_add (u x)).const_mul 2 |>.exp
    convert this using 1
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := riemannianVolume I M)
    (F' := fun t x ↦ 2 * v x * Real.exp (2 * (u x + t * v x)))
    (bound := fun x ↦ 2 * |v x| * Real.exp (2 * (|u x| + |v x|)))
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t ↦ (hF t).aestronglyMeasurable)
    (integrable_of_continuous (hF 0)) (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun x t ht ↦ hbound x t ht) (integrable_of_continuous (by fun_prop))
    (ae_of_all _ fun x t _ ↦ hderiv x t)
  simpa only [zero_mul, add_zero] using h.2

/-- Along the line `u + t v`, the Dirichlet and linear parts of the Liouville energy are polynomials
in `t`. -/
private theorem liouvilleEnergy_add_smul_eq {K u v : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hu : ContMDiff I 𝓘(ℝ) 1 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) (t : ℝ) :
    liouvilleEnergy I K (u + t • v) =
      ((∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M) +
          2 * t * (∫ x, inner ℝ (mgradient I v x) (mgradient I u x) ∂riemannianVolume I M) +
          t ^ 2 * ∫ x, ‖mgradient I v x‖ ^ 2 ∂riemannianVolume I M) / 2 +
        ((∫ x, K x * u x ∂riemannianVolume I M) + t * ∫ x, K x * v x ∂riemannianVolume I M) +
        (∫ x, Real.exp (2 * (u x + t * v x)) ∂riemannianVolume I M) / 2 := by
  have hB : Integrable (fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x))
      (riemannianVolume I M) := integrable_of_continuous (continuous_inner_mgradient hv hu)
  have hGu := integrable_of_continuous (I := I) (continuous_norm_sq_mgradient hu)
  have hGv := integrable_of_continuous (I := I) (continuous_norm_sq_mgradient hv)
  have hpt := norm_sq_mgradient_add_smul (hu.mdifferentiable one_ne_zero)
    (hv.mdifferentiable one_ne_zero) t
  have hK' (x : M) : K x * (u x + t * v x) = K x * u x + t * (K x * v x) := by ring
  rw [liouvilleEnergy_eq_add (u := u + t • v) hK
    (hu.add ((contDiff_const_smul t).contMDiff.comp hv))]
  simp only [hpt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hK']
  rw [integral_add (f := fun x ↦ ‖mgradient I u x‖ ^ 2 +
      2 * t * inner ℝ (mgradient I v x) (mgradient I u x)) (hGu.add (hB.const_mul _))
      (hGv.const_mul _), integral_add hGu (hB.const_mul _), integral_const_mul,
    integral_const_mul, integral_add (f := fun x ↦ K x * u x)
      (integrable_mul_of_continuous hK hu.continuous)
      ((integrable_mul_of_continuous hK hv.continuous).const_mul _), integral_const_mul]

/-- **The first variation of the Liouville energy.** On a compact manifold with a continuous metric,
let `K` be integrable and `u`, `v` be `C¹`. Then `t ↦ J(u + t v)` has derivative
`∫ (⟪∇v, ∇u⟫ + K v + e^(2u) v) dV` at `t = 0`. -/
theorem hasDerivAt_liouvilleEnergy_add_smul {K u v : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hu : ContMDiff I 𝓘(ℝ) 1 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    HasDerivAt (fun t : ℝ ↦ liouvilleEnergy I K (u + t • v))
      (∫ x, (inner ℝ (mgradient I v x) (mgradient I u x) + K x * v x +
        Real.exp (2 * u x) * v x) ∂riemannianVolume I M) 0 := by
  simp only [liouvilleEnergy_add_smul_eq hK hu hv]
  set μ := riemannianVolume I M
  set B := ∫ x, inner ℝ (mgradient I v x) (mgradient I u x) ∂μ
  -- Differentiate the quadratic polynomial, the linear term and the exponential term separately.
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * B)).const_add
      (∫ x, ‖mgradient I u x‖ ^ 2 ∂μ)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (∫ x, ‖mgradient I v x‖ ^ 2 ∂μ))).div_const 2 |>.add
    (((hasDerivAt_id (0 : ℝ)).const_mul (∫ x, K x * v x ∂μ)).const_add (∫ x, K x * u x ∂μ))
    |>.add ((hasDerivAt_integral_exp_add_mul (I := I) hu.continuous hv.continuous).div_const 2)
  convert h using 1
  · funext t
    simp only [Pi.add_apply, id]
    ring
  · have hB : Integrable (fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x)) μ :=
      integrable_of_continuous (continuous_inner_mgradient hv hu)
    have hev : Integrable (fun x ↦ Real.exp (2 * u x) * v x) μ := by
      have := hu.continuous; have := hv.continuous
      exact integrable_of_continuous (by fun_prop)
    rw [integral_add (f := fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x) + K x * v x)
      (hB.add (integrable_mul_of_continuous hK hv.continuous)) hev,
      integral_add hB (integrable_mul_of_continuous hK hv.continuous)]
    simp only [mul_one, Nat.cast_ofNat]
    rw [show (fun x ↦ 2 * v x * Real.exp (2 * u x)) = fun x ↦ 2 * (Real.exp (2 * u x) * v x) by
      funext x; ring, integral_const_mul]
    ring

/-- Real numbers `S`, `t` and `V > 0` satisfy `t S + V e^(2t) / 2 ≥ -S |t| - S² / V`. This bounds
the part of the Liouville energy carried by the mean `t` of a function. -/
private theorem neg_mul_abs_sub_le_mul_add_exp {S V t : ℝ} (hV : 0 < V) :
    -S * |t| - S ^ 2 / V ≤ t * S + V * Real.exp (2 * t) / 2 := by
  have hq : 0 ≤ S ^ 2 / V := by positivity
  have hVq : V * (S ^ 2 / V) = S ^ 2 := mul_div_cancel₀ _ hV.ne'
  rcases le_total t 0 with ht | ht
  · rw [abs_of_nonpos ht]
    nlinarith [Real.exp_pos (2 * t)]
  · rw [abs_of_nonneg ht]
    have hexp := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * t)
    -- `V t² + 2 t S + S² / V = (V t + S)² / V ≥ 0`.
    have hsq : 0 ≤ V * (V * t ^ 2 + 2 * t * S + S ^ 2 / V) := by
      nlinarith [sq_nonneg (V * t + S)]
    have := (mul_nonneg_iff_of_pos_left hV).1 hsq
    nlinarith [mul_le_mul_of_nonneg_left hexp hV.le]

variable [PreconnectedSpace M]

/-- **Coercivity of the Liouville energy.** On a compact connected manifold without boundary with a
continuous metric, let `K` be square integrable with `∫ K dV < 0`. There is a constant `C` such that
every `C¹` function `u`, with mean `ū = ⨍ u`, satisfies
`(∫ |∇u|² dV) / 4 + (-∫ K dV) |ū| ≤ J(u) + C`. -/
theorem exists_le_liouvilleEnergy_add [I.Boundaryless] {K : M → ℝ}
    (hK : MemLp K 2 (riemannianVolume I M)) (hKneg : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃ C : ℝ, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      (∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M) / 4 +
          (-∫ x, K x ∂riemannianVolume I M) * |⨍ x, u x ∂riemannianVolume I M| ≤
        liouvilleEnergy I K u + C := by
  -- Split `u = ū + w` with `ū` the mean. The Dirichlet term is kept; `∫ K w` is bounded by Young's
  -- and the Poincaré–Wirtinger inequalities, and by Jensen's inequality the mean contributes at
  -- least `ū S + V e^(2ū) / 2 ≥ -S |ū| - S² / V`, where `S = ∫ K` and `V` is the volume.
  set μ := riemannianVolume I M
  set S := ∫ x, K x ∂μ
  set V := μ.real univ
  have hK1 : Integrable K μ := hK.integrable one_le_two
  -- The volume is positive, as the zero measure has `∫ K dV = 0`.
  have hμ : μ ≠ 0 := fun h ↦ hKneg.ne (by simp only [S, h, integral_zero_measure])
  have hV : 0 < V :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top μ univ)
  obtain ⟨P, hP⟩ := exists_integral_sq_sub_average_le_mul_integral_norm_sq_mgradient
    (I := I) (M := M)
  -- Young's inequality with weight `Q = P + 1`: `K w ≥ -w² / (4 Q) - Q K²`.
  set Q : ℝ := P + 1
  have hQ : 0 < Q := by positivity
  refine ⟨S ^ 2 / V + Q * ∫ x, K x ^ 2 ∂μ, fun u hu ↦ ?_⟩
  set ū := ⨍ x, u x ∂μ
  set G := ∫ x, ‖mgradient I u x‖ ^ 2 ∂μ
  have hw : Continuous fun x ↦ u x - ū := hu.continuous.sub continuous_const
  have hW : Integrable (fun x ↦ (u x - ū) ^ 2) μ := integrable_of_continuous (hw.pow 2)
  have hK2 : Integrable (fun x ↦ K x ^ 2) μ := hK.integrable_sq
  have hKw := integrable_mul_of_continuous hK1 hw
  -- The linear term: `∫ K u = ∫ K w + ū S` and `∫ K w ≥ -(∫ w²) / (4 Q) - Q ∫ K²`.
  have hlin : ∫ x, K x * u x ∂μ =
      ∫ x, K x * (u x - ū) ∂μ + ū * S := by
    rw [← integral_const_mul, ← integral_add hKw (hK1.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  have hyoung : -((∫ x, (u x - ū) ^ 2 ∂μ) / (4 * Q)) - Q * ∫ x, K x ^ 2 ∂μ ≤
      ∫ x, K x * (u x - ū) ∂μ := by
    rw [← integral_div, ← integral_const_mul, ← integral_neg,
      ← integral_sub (f := fun x ↦ -((u x - ū) ^ 2 / (4 * Q))) (g := fun x ↦ Q * K x ^ 2)
        (hW.div_const _).neg (hK2.const_mul _)]
    refine integral_mono ((hW.div_const _).neg.sub (hK2.const_mul _)) hKw fun x ↦ ?_
    have h4 : 0 ≤ (u x - ū + 2 * Q * K x) ^ 2 / (4 * Q) := by positivity
    have hexpand : (u x - ū + 2 * Q * K x) ^ 2 / (4 * Q) =
        (u x - ū) ^ 2 / (4 * Q) + K x * (u x - ū) + Q * K x ^ 2 := by
      field_simp
      ring
    dsimp only [Pi.sub_apply, Pi.neg_apply]
    linarith
  have hPw : ∫ x, (u x - ū) ^ 2 ∂μ ≤ Q * G := (hP u hu).trans (by gcongr; linarith)
  -- The exponential term: `∫ e^(2u) ≥ V e^(2ū)`, by Jensen's inequality.
  have hexp : V * Real.exp (2 * ū) ≤ ∫ x, Real.exp (2 * u x) ∂μ := by
    have : NeZero μ := ⟨hμ⟩
    have h2u : Continuous fun x ↦ 2 * u x := continuous_const.mul hu.continuous
    have hJ := convexOn_exp.map_average_le (μ := μ) Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ ↦ mem_univ _) (integrable_of_continuous h2u)
      (integrable_of_continuous (Real.continuous_exp.comp h2u))
    have hav : ⨍ x, 2 * u x ∂μ = 2 * ū := by
      simp only [ū, average_eq, smul_eq_mul, integral_const_mul]
      ring
    rwa [hav, average_eq, smul_eq_mul, le_inv_mul_iff₀ hV] at hJ
  have hmeanS := neg_mul_abs_sub_le_mul_add_exp (S := S) (t := ū) hV
  have hG : 0 ≤ G := integral_nonneg fun x ↦ by positivity
  have hdiv : (∫ x, (u x - ū) ^ 2 ∂μ) / (4 * Q) ≤ G / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [liouvilleEnergy_eq_add hK1 hu, hlin]
  nlinarith

/-- **The Liouville energy is bounded below.** On a compact connected manifold without boundary
with a continuous metric, if `K` is square integrable with `∫ K dV < 0`, then the Liouville energy
is bounded below on `C¹` functions. -/
theorem bddBelow_liouvilleEnergy_image [I.Boundaryless] {K : M → ℝ}
    (hK : MemLp K 2 (riemannianVolume I M)) (hKneg : ∫ x, K x ∂riemannianVolume I M < 0) :
    BddBelow (liouvilleEnergy I K '' {u | ContMDiff I 𝓘(ℝ) 1 u}) := by
  obtain ⟨C, hC⟩ := exists_le_liouvilleEnergy_add hK hKneg
  refine ⟨-C, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h := hC u hu
  have hG : 0 ≤ ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M :=
    integral_nonneg fun x ↦ by positivity
  have hm : 0 ≤ (-∫ x, K x ∂riemannianVolume I M) * |⨍ x, u x ∂riemannianVolume I M| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  linarith

end Compact

/-! ### The Euler–Lagrange equation on a closed manifold -/

section EulerLagrange

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a closed manifold, Green's identity turns `∫ (⟪∇v, ∇u⟫ + K v + e^(2u) v) dV` into
`∫ v (Δ⁺u + K + e^(2u)) dV`, for `u` of class `C²` and `v` of class `C¹`. -/
private theorem integral_mul_neg_laplaceBeltrami_add_add_exp {K u v : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    ∫ x, v x * (-laplaceBeltrami I u x + K x + Real.exp (2 * u x)) ∂riemannianVolume I M =
      ∫ x, (inner ℝ (mgradient I v x) (mgradient I u x) + K x * v x +
        Real.exp (2 * u x) * v x) ∂riemannianVolume I M := by
  have hΔ : Continuous (laplaceBeltrami I u) := continuous_laplaceBeltrami hu
  have hexp : Continuous fun x ↦ Real.exp (2 * u x) * v x := by
    have := hu.continuous; have := hv.continuous; fun_prop
  have hKv := integrable_mul_of_continuous hK hv.continuous
  have hpt (x : M) : v x * (-laplaceBeltrami I u x + K x + Real.exp (2 * u x)) =
      -(v x * laplaceBeltrami I u x) + K x * v x + Real.exp (2 * u x) * v x := by ring
  have hB : Continuous fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x) :=
    continuous_inner_mgradient hv (hu.of_le one_le_two)
  have hvΔ : Integrable (fun x ↦ -(v x * laplaceBeltrami I u x)) (riemannianVolume I M) :=
    (integrable_of_continuous (hv.continuous.mul hΔ)).neg
  have hB' : Integrable (fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x))
      (riemannianVolume I M) := integrable_of_continuous hB
  simp only [hpt]
  rw [integral_add (f := fun x ↦ -(v x * laplaceBeltrami I u x) + K x * v x) (hvΔ.add hKv)
      (integrable_of_continuous hexp), integral_add hvΔ hKv, integral_neg,
    integral_mul_laplaceBeltrami hv (HasCompactSupport.of_compactSpace v) hu, neg_neg,
    integral_add (f := fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x) + K x * v x)
      (hB'.add hKv) (integrable_of_continuous hexp), integral_add hB' hKv]

/-- **The first variation of the Liouville energy on a closed manifold.** For integrable `K`, a
`C²` function `u` and a `C¹` function `v`, `t ↦ J(u + t v)` has derivative
`∫ v (Δ⁺u + K + e^(2u)) dV` at `t = 0`, where `Δ⁺ = -div grad`. -/
theorem hasDerivAt_liouvilleEnergy_add_smul_eq_integral {K u v : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    HasDerivAt (fun t : ℝ ↦ liouvilleEnergy I K (u + t • v))
      (∫ x, v x * (-laplaceBeltrami I u x + K x + Real.exp (2 * u x)) ∂riemannianVolume I M) 0 := by
  rw [integral_mul_neg_laplaceBeltrami_add_add_exp hK hu hv]
  exact hasDerivAt_liouvilleEnergy_add_smul hK (hu.of_le one_le_two) hv

/-- **The Euler–Lagrange equation of the Liouville energy.** On a closed manifold, let `K` be
continuous. A `C²` function `u` is a critical point of the Liouville energy, in the sense that
`t ↦ J(u + t v)` has derivative `0` at `t = 0` for every smooth `v`, exactly when it solves the
curvature equation `Δ⁺u + K + e^(2u) = 0`. -/
theorem forall_hasDerivAt_liouvilleEnergy_add_smul_iff {K u : M → ℝ} (hK : Continuous K)
    (hu : ContMDiff I 𝓘(ℝ) 2 u) :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
        HasDerivAt (fun t : ℝ ↦ liouvilleEnergy I K (u + t • v)) 0 0) ↔
      ∀ x, -laplaceBeltrami I u x + K x + Real.exp (2 * u x) = 0 := by
  have hK1 : Integrable K (riemannianVolume I M) := integrable_of_continuous hK
  constructor
  · intro hcrit
    have hcont : Continuous fun x ↦ -laplaceBeltrami I u x + K x + Real.exp (2 * u x) :=
      ((continuous_laplaceBeltrami hu).neg.add hK).add
        (Real.continuous_exp.comp (continuous_const.mul hu.continuous))
    -- The defect of the equation integrates to zero against every smooth function.
    have hae : ∀ᵐ x ∂riemannianVolume I M,
        -laplaceBeltrami I u x + K x + Real.exp (2 * u x) = 0 := by
      refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
        fun v hv _ ↦ ?_
      exact (hasDerivAt_liouvilleEnergy_add_smul_eq_integral hK1 hu (hv.of_le (by simp))).unique
        (hcrit v hv)
    exact congrFun ((hcont.ae_eq_iff_eq _ continuous_zero).1 hae)
  · intro h v hv
    convert hasDerivAt_liouvilleEnergy_add_smul_eq_integral hK1 hu (hv.of_le (by simp)) using 1
    simp [h]

/-- **The convexity inequality for the Liouville energy.** On a closed manifold, for integrable
`K`, a `C²` function `u` and a `C¹` function `v`,
`J(u) + ∫ v (Δ⁺u + K + e^(2u)) dV ≤ J(u + v)`. -/
theorem liouvilleEnergy_add_integral_mul_le {K u v : M → ℝ}
    (hK : Integrable K (riemannianVolume I M)) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    liouvilleEnergy I K u +
        ∫ x, v x * (-laplaceBeltrami I u x + K x + Real.exp (2 * u x)) ∂riemannianVolume I M ≤
      liouvilleEnergy I K (u + v) := by
  have hu1 : ContMDiff I 𝓘(ℝ) 1 u := hu.of_le one_le_two
  have hint {w : M → ℝ} (hw : ContMDiff I 𝓘(ℝ) 1 w) : Integrable (fun x ↦
      ‖mgradient I w x‖ ^ 2 / 2 + K x * w x + Real.exp (2 * w x) / 2) (riemannianVolume I M) :=
    ((integrable_of_continuous (continuous_norm_sq_mgradient hw)).div_const 2 |>.add
      (integrable_mul_of_continuous hK hw.continuous)).add
      (integrable_of_continuous (by have := hw.continuous; fun_prop))
  have hvar : Integrable (fun x ↦ inner ℝ (mgradient I v x) (mgradient I u x) + K x * v x +
      Real.exp (2 * u x) * v x) (riemannianVolume I M) :=
    ((integrable_of_continuous (continuous_inner_mgradient hv hu1)).add
      (integrable_mul_of_continuous hK hv.continuous)).add
      (integrable_of_continuous (by have := hu.continuous; have := hv.continuous; fun_prop))
  rw [integral_mul_neg_laplaceBeltrami_add_add_exp hK hu hv, liouvilleEnergy_def,
    liouvilleEnergy_def, ← integral_add (hint hu1) hvar]
  refine integral_mono ((hint hu1).add hvar) (hint (hu1.add hv)) fun x ↦ ?_
  -- Pointwise, `|a + b|² ≥ |a|² + 2 ⟪b, a⟫` and `e^(2 (u + v)) ≥ e^(2u) (1 + 2 v)`.
  have hgrad : mgradient I (u + v) x = mgradient I u x + mgradient I v x := by
    rw [mgradient_add (hu1.mdifferentiable one_ne_zero) (hv.mdifferentiable one_ne_zero),
      Pi.add_apply]
  have hexp : Real.exp (2 * u x) * (1 + 2 * v x) ≤ Real.exp (2 * (u x + v x)) := by
    rw [show 2 * (u x + v x) = 2 * u x + 2 * v x by ring, Real.exp_add]
    gcongr
    linarith [Real.add_one_le_exp (2 * v x)]
  simp only [Pi.add_apply, hgrad, norm_add_sq_real,
    real_inner_comm (mgradient I v x) (mgradient I u x)]
  nlinarith [sq_nonneg ‖mgradient I v x‖]

/-- **Solutions of the curvature equation minimize the Liouville energy.** On a closed manifold, if
a `C²` function `u` solves `Δ⁺u + K + e^(2u) = 0`, then `J(u) ≤ J(w)` for every `C¹` function
`w`. -/
theorem liouvilleEnergy_le_of_neg_laplaceBeltrami_add_add_exp_eq_zero {K u w : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (h : ∀ x, -laplaceBeltrami I u x + K x + Real.exp (2 * u x) = 0)
    (hw : ContMDiff I 𝓘(ℝ) 1 w) :
    liouvilleEnergy I K u ≤ liouvilleEnergy I K w := by
  -- The equation expresses `K = Δu - e^(2u)`, a continuous function.
  have hK : Continuous K := by
    have hKeq : K = fun x ↦ laplaceBeltrami I u x - Real.exp (2 * u x) := by
      funext x; linarith [h x]
    rw [hKeq]
    exact (continuous_laplaceBeltrami hu).sub
      (Real.continuous_exp.comp (continuous_const.mul hu.continuous))
  have hle := liouvilleEnergy_add_integral_mul_le (v := w - u)
    (integrable_of_continuous hK) hu (hw.sub (hu.of_le one_le_two))
  simpa [h] using hle

/-- **The minimizers of the Liouville energy.** On a closed manifold, let `K` be continuous. A `C²`
function `u` minimizes the Liouville energy among `C²` functions exactly when it solves the
curvature equation `Δ⁺u + K + e^(2u) = 0`. -/
theorem forall_liouvilleEnergy_le_iff {K u : M → ℝ} (hK : Continuous K)
    (hu : ContMDiff I 𝓘(ℝ) 2 u) :
    (∀ w : M → ℝ, ContMDiff I 𝓘(ℝ) 2 w → liouvilleEnergy I K u ≤ liouvilleEnergy I K w) ↔
      ∀ x, -laplaceBeltrami I u x + K x + Real.exp (2 * u x) = 0 := by
  refine ⟨fun hmin ↦ (forall_hasDerivAt_liouvilleEnergy_add_smul_iff hK hu).1 fun v hv ↦ ?_,
    fun h w hw ↦ liouvilleEnergy_le_of_neg_laplaceBeltrami_add_add_exp_eq_zero hu h
      (hw.of_le one_le_two)⟩
  -- `t ↦ J(u + t v)` has a minimum at `t = 0`, so its derivative there vanishes.
  have hd := hasDerivAt_liouvilleEnergy_add_smul_eq_integral
    (integrable_of_continuous hK : Integrable K (riemannianVolume I M)) hu (hv.of_le (by simp))
  have hloc : IsLocalMin (fun t : ℝ ↦ liouvilleEnergy I K (u + t • v)) 0 :=
    Filter.Eventually.of_forall fun t ↦ by
      simpa using hmin (u + t • v)
        (hu.add ((contDiff_const_smul t).contMDiff.comp (hv.of_le (by simp))))
  rwa [hloc.hasDerivAt_eq_zero hd] at hd

end EulerLagrange

end TauCeti.Manifold
