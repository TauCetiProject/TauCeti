/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Ball
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# Taubes's monotonicity inequality for the defect energy

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β`, and its **defect energy** on a ball
is `E(σ) = (r / 4) ∫_{B_σ} |1 - |χ|²|`. Taubes's monotonicity inequality

`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C r^(-1/2)) E'(σ) + C σ⁴`

is what turns the smallest-scale lower bound at a zero of `α` into the quadratic lower bound
`E(σ) ≥ c σ²` (`TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`), and gives the
quadratic upper bound at every centre (`TauCeti.exists_forall_measure_closedBall_le_of_ae_le`).
This file derives it in a flat chart, the four-dimensional real inner product space `E` with an
orthogonal complex structure `J` and a unitary frame `e` (`J e₀ = e₁`, `J e₂ = e₃`), whose Kähler
form is `ω = e⁰ ∧ e¹ + e² ∧ e³`, and then in a Darboux chart, where the geometry of the manifold
contributes the factor `1 + C σ`.

The argument is Stokes's theorem for a closed two-form `F`, in the application the curvature
`i F_a` of the connection on the twisting line. The Liouville form `λ = ι_{x - c} ω / 2` about the
centre `c` has `dλ = ω`, so `F ∧ ω = d(F ∧ λ)` and the Kähler component `⟨F, ω⟩` of `F` integrates
over a ball to the integral of `F ∧ λ` over its boundary sphere. In vector form `F ∧ λ` is the flux
of the field `V(x) = (⋆F)(·, J (x - c))♯ / 2`, whose divergence is `⟨F, ω⟩` because `F` is closed,
and at `x = c + y` the outward component of `V` is

`⟪V (c + y), y⟫ = F_{c+y}(w, J w) / 2`,

where `w` is a vector of length `‖y‖` spanning, with `J w`, the complex line orthogonal to `y` and
`J y`. Taubes's curvature estimates bound the Hermitian part `B(v, v) = F(v, J v)` of `F` above by
the defect density `δ = (r / 4) |1 - |χ|²|`, as `F(v, J v) ≤ ((1 + κ) δ + K) ‖v‖²` (with `κ = 0`
after his refined bound on the anti-self-dual part, and `κ = C r^(-1/2)` after the coarse one), and
his formula for the `ω`-component gives `δ ≤ ⟨F, ω⟩ + K`. With the divergence theorem on a ball
(`TauCeti.setIntegral_ball_trace_fderiv`) these two pointwise inequalities give

`∫_{B_σ} δ ≤ (σ / 2) (1 + κ) σ³ ∫_S δ (c + σ θ) dθ + K (|S| / 2 + |B₁|) σ⁴`

(`TauCeti.SeibergWitten.setIntegral_ball_le_mul_integral_toSphere_add`), whose sphere integral is
the derivative of the ball integrals (`ContinuousOn.hasDerivAt_setIntegral_ball`). For the defect
measure `δ dμ` this is the differential inequality hypothesis of the covering and density
arguments above with `C = 0` and `C r^(-1/2)` replaced by `κ`
(`TauCeti.SeibergWitten.measure_closedBall_le_mul_deriv_add`).

On a symplectic four-manifold, a Darboux chart about the centre makes the symplectic form the
constant form `ω`, while the compatible complex structure `J' x` and the metric
`g x = ω(·, J' x ·)` vary with the point; a linear symplectic change of coordinates makes them `J`
and the Euclidean metric at `c`. In such a chart the bound on the ball needs no correction. The
metric volume form is `ω² / 2`, the Lebesgue measure of the chart, and the Kähler component of
`g x` is `F(f₀, f₁) + F(f₂, f₃)` in a `g x`-unitary frame `f`, which equals
`F(e₀, e₁) + F(e₂, e₃)` because `ω` takes the standard values on both frames
(`ContinuousAlternatingMap.apply_add_apply_eq_of_cross_eq_zero`). Only the Hermitian bound on the
sphere sees the geometry. Replacing `J' x` by `J` changes `F(v, J' x v)` by at most
`‖F‖ ‖J' x - J‖ ‖v‖²`, and Taubes's curvature bound `‖F‖ ≤ A δ + K` makes this a multiple of `δ`.
If `J'` and `g` move by at most `L ‖x - c‖` from their values at the centre, the sphere of radius
`σ` therefore carries the factor `1 + (1 + A) L σ`, which is the factor `1 + C σ` of the
inequality (`TauCeti.SeibergWitten.measure_closedBall_le_mul_one_add_mul_deriv_add`). The balls
are those of the chart.

## Main results

* `TauCeti.SeibergWitten.setIntegral_ball_le_mul_integral_toSphere_add`: the monotonicity
  inequality, with the sphere integral.
* `TauCeti.SeibergWitten.measure_closedBall_le_mul_deriv_add`: the monotonicity inequality for the
  measure `δ dμ`, with the derivative of the radial function `σ ↦ ∫_{B_σ} δ`.
* `TauCeti.SeibergWitten.measure_closedBall_le_mul_one_add_mul_deriv_add`: the monotonicity
  inequality in a Darboux chart, for a complex structure and a metric that vary with the point.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open MeasureTheory Metric Set Filter Topology Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The flux field -/

/-- The product of the component `F(e_a, e_b)` of a two-form field and the coordinate
`⟪e_k, x - c⟫` about the centre `c`. -/
private def fluxTerm (e : OrthonormalBasis (Fin 4) ℝ E) (c : E) (F : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (a b k : Fin 4) (x : E) : ℝ :=
  F x ![e a, e b] * ⟪e k, x - c⟫

/-- The flux field `V(x) = (⋆F)(·, J (x - c))♯ / 2` of a two-form field `F` about `c`, written in
the frame `e`, for the complex structure `J` with `J e₀ = e₁` and `J e₂ = e₃`. Its divergence is
the Kähler component `F(e₀, e₁) + F(e₂, e₃)` of a closed `F` (`trace_fderiv_fluxField`). -/
private def fluxField (e : OrthonormalBasis (Fin 4) ℝ E) (c : E) (F : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (x : E) : E :=
  (2 : ℝ)⁻¹ •
    ((fluxTerm e c F 2 3 0 x + fluxTerm e c F 1 3 3 x + fluxTerm e c F 1 2 2 x) • e 0 +
      (fluxTerm e c F 2 3 1 x - fluxTerm e c F 0 3 3 x - fluxTerm e c F 0 2 2 x) • e 1 +
      (fluxTerm e c F 0 1 2 x - fluxTerm e c F 1 3 1 x - fluxTerm e c F 0 3 0 x) • e 2 +
      (fluxTerm e c F 1 2 1 x + fluxTerm e c F 0 2 0 x + fluxTerm e c F 0 1 3 x) • e 3)

variable {e : OrthonormalBasis (Fin 4) ℝ E} {c : E} {F : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x : E}

private lemma hasFDerivAt_fluxTerm (hF : DifferentiableAt ℝ F x) (a b k : Fin 4) :
    HasFDerivAt (fluxTerm e c F a b k)
      (F x ![e a, e b] • innerSL ℝ (e k) +
        ⟪e k, x - c⟫ • (fderiv ℝ F x).flipAlternating ![e a, e b]) x := by
  have h₁ := hF.hasFDerivAt.continuousAlternatingMap_apply_const ![e a, e b]
  have h₂ : HasFDerivAt (fun y : E ↦ ⟪e k, y - c⟫) (innerSL ℝ (e k)) x := by
    simpa [inner_sub_right] using ((innerSL ℝ (e k)).hasFDerivAt).sub_const ⟪e k, c⟫
  exact h₁.mul h₂

private lemma contDiffAt_fluxTerm (hF : ContDiffAt ℝ 1 F x) (a b k : Fin 4) :
    ContDiffAt ℝ 1 (fluxTerm e c F a b k) x :=
  ((ContinuousAlternatingMap.apply ℝ E ℝ ![e a, e b]).contDiff.contDiffAt.comp x hF).mul
    (contDiffAt_const.inner ℝ (contDiffAt_id.sub contDiffAt_const))

private lemma contDiffAt_fluxField (hF : ContDiffAt ℝ 1 F x) :
    ContDiffAt ℝ 1 (fluxField e c F) x := by
  have h := fun a b k ↦ contDiffAt_fluxTerm (e := e) (c := c) hF a b k
  unfold fluxField
  exact (((((h 2 3 0).add (h 1 3 3)).add (h 1 2 2)).smul contDiffAt_const).add
    ((((h 2 3 1).sub (h 0 3 3)).sub (h 0 2 2)).smul contDiffAt_const) |>.add
    ((((h 0 1 2).sub (h 1 3 1)).sub (h 0 3 0)).smul contDiffAt_const) |>.add
    ((((h 1 2 1).add (h 0 2 0)).add (h 0 1 3)).smul contDiffAt_const)).const_smul _

variable [FiniteDimensional ℝ E] in
/-- **The divergence of the flux field is the Kähler component of `F`.** If the two-form field `F`
is differentiable and closed at `x`, then `tr (DV(x)) = F_x(e₀, e₁) + F_x(e₂, e₃)`. -/
private lemma trace_fderiv_fluxField (hF : DifferentiableAt ℝ F x) (hdF : extDeriv F x = 0) :
    LinearMap.trace ℝ E (fderiv ℝ (fluxField e c F) x : E →ₗ[ℝ] E) =
      F x ![e 0, e 1] + F x ![e 2, e 3] := by
  have h := fun a b k ↦ hasFDerivAt_fluxTerm (e := e) (c := c) hF a b k
  have hV : HasFDerivAt (fluxField e c F) _ x :=
    (((((h 2 3 0).add (h 1 3 3)).add (h 1 2 2)).smul_const (e 0)).add
      ((((h 2 3 1).sub (h 0 3 3)).sub (h 0 2 2)).smul_const (e 1)) |>.add
      ((((h 0 1 2).sub (h 1 3 1)).sub (h 0 3 0)).smul_const (e 2)) |>.add
      ((((h 1 2 1).add (h 0 2 0)).add (h 0 1 3)).smul_const (e 3))).const_smul (2 : ℝ)⁻¹
  have hd : ∀ i j k, fderiv ℝ F x (e i) ![e j, e k] - fderiv ℝ F x (e j) ![e i, e k] +
      fderiv ℝ F x (e k) ![e i, e j] = 0 := fun i j k ↦ by
    rw [← extDeriv_apply_triple, hdF, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [hV.fderiv]
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_smulRight, map_smul, map_add,
    LinearMap.trace_smulRight]
  simp only [ContinuousLinearMap.toLinearMap_innerSL_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K,
    OrthonormalBasis.norm_eq_one, RCLike.ofReal_real_eq_id, id_eq, one_pow, smul_eq_mul, mul_one,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.flipAlternating_apply_apply, e.inner_eq_ite,
    Fin.reduceEq, ↓reduceIte, mul_zero, zero_add]
  linear_combination (⟪e 0, x - c⟫ / 2) * hd 0 2 3 + (⟪e 1, x - c⟫ / 2) * hd 1 2 3 +
    (⟪e 2, x - c⟫ / 2) * hd 0 1 2 + (⟪e 3, x - c⟫ / 2) * hd 0 1 3

/-! ### The boundary flux -/

/-- For `y ∈ E`, the vector `w = -y₂ e₀ + y₃ e₁ + y₀ e₂ - y₁ e₃`, of the same length as `y`. With
`J w` it spans the complex line orthogonal to `y` and `J y`. -/
private def tangentVector (e : OrthonormalBasis (Fin 4) ℝ E) (y : E) : E :=
  -(e.repr y 2 • e 0) + e.repr y 3 • e 1 + e.repr y 0 • e 2 - e.repr y 1 • e 3

private lemma repr_tangentVector (y : E) (i : Fin 4) :
    e.repr (tangentVector e y) i =
      ![-e.repr y 2, e.repr y 3, e.repr y 0, -e.repr y 1] i := by
  simp only [tangentVector, e.repr_apply_apply, inner_add_right, inner_sub_right, inner_neg_right,
    inner_smul_right, e.inner_eq_ite]
  fin_cases i <;> simp

private lemma norm_tangentVector (y : E) : ‖tangentVector e y‖ = ‖y‖ := by
  rw [← e.repr.norm_map, ← e.repr.norm_map y, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [repr_tangentVector, Real.norm_eq_abs, sq_abs, Fin.sum_univ_four, Matrix.cons_val_zero,
    even_two, Even.neg_pow, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The outward flux density of the flux field.** At `c + y`, the component of `V` along `y`
is half the value of `F` on the complex line orthogonal to `y`:
`⟪V (c + y), y⟫ = F_{c+y}(w, J w) / 2`. -/
private lemma inner_fluxField_add {J : AlmostComplexStructure E} (h₀ : J (e 0) = e 1)
    (h₂ : J (e 2) = e 3) (y : E) :
    ⟪fluxField e c F (c + y), y⟫ =
      F (c + y) ![tangentVector e y, J (tangentVector e y)] / 2 := by
  rw [ContinuousAlternatingMap.apply_vecCons_eq_sum_repr_fin_four e.toBasis]
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    AlmostComplexStructure.repr_apply h₀ h₂, repr_tangentVector, smul_eq_mul]
  simp only [fluxField, fluxTerm, add_sub_cancel_left, inner_smul_left, inner_add_left,
    ← e.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    RCLike.conj_to_real, Fin.isValue]
  ring

/-! ### The monotonicity inequality -/

/-- A space with an orthonormal frame indexed by `Fin 4` is four-dimensional. -/
private lemma finrank_eq_four (e : OrthonormalBasis (Fin 4) ℝ E) :
    finrank ℝ E = 4 := by
  simpa using finrank_eq_card_basis e.toBasis

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **Stokes's theorem for the Kähler component.** For a two-form field `F` that is `C¹` near
`closedBall c σ` and closed on `ball c σ`, the Kähler component `F(e₀, e₁) + F(e₂, e₃)` integrates
over the ball to the flux of `V` through the sphere. -/
private lemma setIntegral_ball_eq_integral_inner_fluxField {σ : ℝ} (hσ : 0 ≤ σ)
    (hF : ∀ x ∈ closedBall c σ, ContDiffAt ℝ 1 F x) (hdF : ∀ x ∈ ball c σ, extDeriv F x = 0) :
    ∫ x in ball c σ, (F x ![e 0, e 1] + F x ![e 2, e 3]) ∂μ =
      σ ^ 3 * ∫ θ : sphere (0 : E) 1, ⟪fluxField e c F (c + σ • (θ : E)), θ⟫ ∂μ.toSphere := by
  have hn := finrank_eq_four e
  have h := setIntegral_ball_trace_fderiv (μ := μ) (V := fluxField e c F) c hσ
    fun x hx ↦ contDiffAt_fluxField (hF x hx)
  rw [hn] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  exact (trace_fderiv_fluxField ((hF x (ball_subset_closedBall hx)).differentiableAt
    one_ne_zero) (hdF x hx)).symm

/-- **The flux bound.** If the Hermitian part of `F` is bounded by `δ` on the sphere of radius
`σ > 0` about `c`, `F(v, J v) ≤ ((1 + κ) δ + K) ‖v‖²`, then the flux of `V` through that sphere is
at most `(σ / 2) ((1 + κ) ∫ δ + K |S|)`. -/
private lemma integral_inner_fluxField_le {J : AlmostComplexStructure E}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {δ : E → ℝ} {σ κ K : ℝ} (hσ : 0 < σ)
    (hF : ∀ x ∈ closedBall c σ, ContDiffAt ℝ 1 F x) (hδ : ContinuousOn δ (closedBall c σ))
    (hB : ∀ x ∈ sphere c σ, ∀ v, F x ![v, J v] ≤ ((1 + κ) * δ x + K) * ‖v‖ ^ 2) :
    ∫ θ : sphere (0 : E) 1, ⟪fluxField e c F (c + σ • (θ : E)), θ⟫ ∂μ.toSphere ≤
      σ / 2 * (1 + κ) * ∫ θ : sphere (0 : E) 1, δ (c + σ • (θ : E)) ∂μ.toSphere +
        σ / 2 * K * μ.toSphere.real univ := by
  have hnorm : ∀ θ : sphere (0 : E) 1, ‖σ • (θ : E)‖ = σ := fun θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hσ.le]
  -- Pointwise, `σ ⟪V (c + σ θ), θ⟫ = F(w, J w) / 2` with `‖w‖ = σ`.
  have hbdry : ∀ θ : sphere (0 : E) 1, ⟪fluxField e c F (c + σ • (θ : E)), θ⟫ ≤
      σ / 2 * ((1 + κ) * δ (c + σ • (θ : E)) + K) := fun θ ↦ by
    have hmem : c + σ • (θ : E) ∈ sphere c σ := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, hnorm]
    have key := inner_fluxField_add (c := c) (F := F) h₀ h₂ (σ • (θ : E))
    rw [inner_smul_right] at key
    have hb := hB _ hmem (tangentVector e (σ • (θ : E)))
    rw [norm_tangentVector, hnorm] at hb
    refine le_of_mul_le_mul_left ?_ hσ
    rw [key]
    linear_combination hb / 2
  have hmemB : ∀ θ : sphere (0 : E) 1, c + σ • (θ : E) ∈ closedBall c σ := fun θ ↦ by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm]
  have hcont : Continuous fun θ : sphere (0 : E) 1 ↦ c + σ • (θ : E) :=
    continuous_const.add (continuous_const.smul continuous_subtypeVal)
  have hintV : Integrable (fun θ : sphere (0 : E) 1 ↦
      ⟪fluxField e c F (c + σ • (θ : E)), θ⟫) μ.toSphere :=
    ((ContinuousOn.comp_continuous (fun x hx ↦
      (contDiffAt_fluxField (hF x hx)).continuousAt.continuousWithinAt) hcont hmemB).inner
        continuous_subtypeVal).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hintδ : Integrable (fun θ : sphere (0 : E) 1 ↦ δ (c + σ • (θ : E))) μ.toSphere :=
    (hδ.comp_continuous hcont hmemB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫ θ : sphere (0 : E) 1, ⟪fluxField e c F (c + σ • (θ : E)), θ⟫ ∂μ.toSphere
      ≤ ∫ θ : sphere (0 : E) 1, σ / 2 * ((1 + κ) * δ (c + σ • (θ : E)) + K) ∂μ.toSphere :=
        integral_mono hintV ((hintδ.const_mul _).add (integrable_const K) |>.const_mul _) hbdry
    _ = _ := by
        rw [integral_const_mul, integral_add (hintδ.const_mul _) (integrable_const K),
          integral_const_mul, integral_const, smul_eq_mul]
        ring

/-- **Taubes's monotonicity inequality in a flat chart.** Let `J` be an orthogonal complex
structure with unitary frame `e` (`J e₀ = e₁`, `J e₂ = e₃`), let `F` be a two-form field that is
`C¹` at the points of the closed ball `closedBall c σ` and closed on the open ball, and let `δ` be
continuous on the closed ball. Suppose that `δ` is
bounded by the Kähler component of `F` on the ball, `δ ≤ F(e₀, e₁) + F(e₂, e₃) + K`, and that the
Hermitian part of `F` is bounded by `δ` on the boundary sphere,
`F(v, J v) ≤ ((1 + κ) δ + K) ‖v‖²`. Then

`∫_{B_σ} δ ≤ (σ / 2) (1 + κ) σ³ ∫_S δ (c + σ θ) dθ + K (|S| / 2 + |B₁|) σ⁴`,

where `S` is the unit sphere with its surface measure `μ.toSphere` and `B₁` the unit ball. -/
theorem setIntegral_ball_le_mul_integral_toSphere_add {J : AlmostComplexStructure E}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {δ : E → ℝ} {σ κ K : ℝ} (hσ : 0 ≤ σ)
    (hF : ∀ x ∈ closedBall c σ, ContDiffAt ℝ 1 F x) (hdF : ∀ x ∈ ball c σ, extDeriv F x = 0)
    (hδ : ContinuousOn δ (closedBall c σ))
    (hω : ∀ x ∈ ball c σ, δ x ≤ F x ![e 0, e 1] + F x ![e 2, e 3] + K)
    (hB : ∀ x ∈ sphere c σ, ∀ v, F x ![v, J v] ≤ ((1 + κ) * δ x + K) * ‖v‖ ^ 2) :
    ∫ x in ball c σ, δ x ∂μ ≤
      σ / 2 * (1 + κ) * (σ ^ 3 * ∫ θ : sphere (0 : E) 1, δ (c + σ • (θ : E)) ∂μ.toSphere) +
        K * (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)) * σ ^ 4 := by
  have hn := finrank_eq_four e
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hn
  rcases hσ.eq_or_lt with rfl | hσ
  · simp [Metric.ball_eq_empty.mpr le_rfl]
  -- The Kähler component bounds `δ` on the ball.
  have hFc : ContinuousOn (fun x ↦ F x ![e 0, e 1] + F x ![e 2, e 3]) (closedBall c σ) :=
    fun x hx ↦ ((((ContinuousAlternatingMap.apply ℝ E ℝ ![e 0, e 1]).continuous.continuousAt.comp
      (hF x hx).continuousAt).add
      ((ContinuousAlternatingMap.apply ℝ E ℝ ![e 2, e 3]).continuous.continuousAt.comp
        (hF x hx).continuousAt))).continuousWithinAt
  have hintδ : IntegrableOn δ (ball c σ) μ :=
    (hδ.integrableOn_compact (isCompact_closedBall c σ)).mono_set ball_subset_closedBall
  have hintω : IntegrableOn (fun x ↦ F x ![e 0, e 1] + F x ![e 2, e 3]) (ball c σ) μ :=
    (hFc.integrableOn_compact (isCompact_closedBall c σ)).mono_set ball_subset_closedBall
  have hintK : IntegrableOn (fun _ ↦ K) (ball c σ) μ := integrableOn_const measure_ball_lt_top.ne
  have hball : ∫ x in ball c σ, δ x ∂μ ≤
      ∫ x in ball c σ, (F x ![e 0, e 1] + F x ![e 2, e 3]) ∂μ + K * μ.real (ball c σ) := by
    calc ∫ x in ball c σ, δ x ∂μ
        ≤ ∫ x in ball c σ, (F x ![e 0, e 1] + F x ![e 2, e 3] + K) ∂μ :=
          setIntegral_mono_on hintδ (hintω.add hintK) measurableSet_ball hω
      _ = _ := by
          rw [integral_add hintω hintK, setIntegral_const, smul_eq_mul, mul_comm K]
  -- By Stokes, the Kähler component integrates to the flux, which `δ` bounds on the sphere.
  have hsphere := mul_le_mul_of_nonneg_left
    (integral_inner_fluxField_le (μ := μ) h₀ h₂ hσ hF hδ hB) (by positivity : 0 ≤ σ ^ 3)
  have hvol : μ.real (ball c σ) = σ ^ 4 * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ c hσ.le, hn, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), measureReal_def]
  rw [setIntegral_ball_eq_integral_inner_fluxField hσ.le hF hdF, hvol] at hball
  linear_combination hball + hsphere

/-- **Taubes's monotonicity inequality for the defect measure.** Let `J`, `e` and the closed
two-form field `F` be as in `setIntegral_ball_le_mul_integral_toSphere_add`, on the open ball
`ball c R`, and let `δ ≥ 0` be a continuous density on that ball bounded by the Kähler component of
`F`, `δ ≤ F(e₀, e₁) + F(e₂, e₃) + K`. Let `0 < σ < R` be a radius on whose sphere `δ` bounds the
Hermitian part of `F`, `F(v, J v) ≤ ((1 + κ) δ + K) ‖v‖²`. Then the measure `ν = δ dμ` satisfies,
at the radius `σ`, the differential inequality

`ν(B_σ) ≤ (σ / 2) (1 + κ) d/dσ ν(B_σ) + K (|S| / 2 + |B₁|) σ⁴`

for the closed balls `B_σ = closedBall c σ`. -/
theorem measure_closedBall_le_mul_deriv_add {J : AlmostComplexStructure E}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {δ : E → ℝ} {R κ K σ : ℝ}
    (hF : ∀ x ∈ ball c R, ContDiffAt ℝ 1 F x) (hdF : ∀ x ∈ ball c R, extDeriv F x = 0)
    (hδ : ContinuousOn δ (ball c R)) (hδ₀ : ∀ x ∈ ball c R, 0 ≤ δ x)
    (hω : ∀ x ∈ ball c R, δ x ≤ F x ![e 0, e 1] + F x ![e 2, e 3] + K)
    (hB : ∀ x ∈ sphere c σ, ∀ v, F x ![v, J v] ≤ ((1 + κ) * δ x + K) * ‖v‖ ^ 2)
    (hσ : σ ∈ Ioo 0 R) :
    ((μ.withDensity fun x ↦ ENNReal.ofReal (δ x)) (closedBall c σ)).toReal ≤
      σ / 2 * (1 + κ) * deriv (fun s ↦
        ((μ.withDensity fun x ↦ ENNReal.ofReal (δ x)) (closedBall c s)).toReal) σ +
        K * (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)) * σ ^ 4 := by
  have hn := finrank_eq_four e
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hn
  set ν := μ.withDensity fun x ↦ ENNReal.ofReal (δ x)
  -- Work inside the closed ball of an intermediate radius `σ < R' < R`.
  obtain ⟨R', hσR', hR'R⟩ := exists_between hσ.2
  have hσ' : σ ∈ Ioo 0 R' := ⟨hσ.1, hσR'⟩
  have hR' : closedBall c R' ⊆ ball c R := closedBall_subset_ball hR'R
  -- On radii in `[0, R']`, the measure of the closed ball is the integral of `δ` over the ball.
  have hνball : ∀ s ∈ Icc 0 R', (ν (closedBall c s)).toReal = ∫ x in ball c s, δ x ∂μ := by
    intro s hs
    have hsub : closedBall c s ⊆ ball c R := (closedBall_subset_closedBall hs.2).trans hR'
    rw [withDensity_apply _ measurableSet_closedBall, ← integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_closedBall).mpr (ae_of_all _ fun x hx ↦ hδ₀ x (hsub hx)))
      ((hδ.mono hsub).aestronglyMeasurable measurableSet_closedBall),
      setIntegral_congr_set (Measure.addHaar_closedBall_ae_eq_ball μ c s)]
  have hderiv := (hδ.mono hR').hasDerivAt_setIntegral_ball (μ := μ) hσ'
  rw [hn, smul_eq_mul] at hderiv
  have hderiv' : deriv (fun s ↦ (ν (closedBall c s)).toReal) σ =
      σ ^ 3 * ∫ θ : sphere (0 : E) 1, δ (c + σ • (θ : E)) ∂μ.toSphere := by
    refine (hderiv.congr_of_eventuallyEq ?_).deriv
    filter_upwards [isOpen_Ioo.mem_nhds hσ'] with s hs
    exact hνball s (Ioo_subset_Icc_self hs)
  rw [hderiv', hνball σ (Ioo_subset_Icc_self hσ')]
  have hsubo : closedBall c σ ⊆ ball c R := closedBall_subset_ball hσ.2
  exact setIntegral_ball_le_mul_integral_toSphere_add h₀ h₂ hσ.1.le (fun x hx ↦ hF x (hsubo hx))
    (fun x hx ↦ hdF x (hsubo (ball_subset_closedBall hx))) (hδ.mono hsubo)
    (fun x hx ↦ hω x (hsubo (ball_subset_closedBall hx))) hB

/-! ### The monotonicity inequality in a Darboux chart -/

/-- **Taubes's monotonicity inequality in a Darboux chart.** Let `J`, `e` and the closed two-form
field `F` be as in `measure_closedBall_le_mul_deriv_add`, on the open ball `ball c R`, and let
`δ ≥ 0` be a continuous density there bounded by the Kähler component of `F`,
`δ ≤ F(e₀, e₁) + F(e₂, e₃) + K`. Let `0 < σ < R` be a radius on whose sphere `δ` bounds the
Hermitian part of `F` only for a complex structure `J' x` and a quadratic form `g x` that vary with
the point: `F(v, J' x v) ≤ ((1 + κ) δ + K) g x v`, where `J' x` is within `L ‖x - c‖` of `J`,
`g x v` is at most `(1 + L ‖x - c‖) ‖v‖²`, and the norm of `F` is bounded by the density,
`‖F‖ ≤ A δ + K`. Then the measure `ν = δ dμ` satisfies, at the radius `σ`, the differential
inequality

`ν(B_σ) ≤ (σ / 2) (1 + (1 + A) L σ) (1 + κ) d/dσ ν(B_σ) + K (1 + 2 L R) (|S| / 2 + |B₁|) σ⁴`

for the closed balls `B_σ = closedBall c σ`. -/
theorem measure_closedBall_le_mul_one_add_mul_deriv_add {J : AlmostComplexStructure E}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {J' : E → E → E} {g : E → E → ℝ} {δ : E → ℝ}
    {R κ K A L σ : ℝ} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hF : ∀ x ∈ ball c R, ContDiffAt ℝ 1 F x) (hdF : ∀ x ∈ ball c R, extDeriv F x = 0)
    (hδ : ContinuousOn δ (ball c R)) (hδ₀ : ∀ x ∈ ball c R, 0 ≤ δ x)
    (hω : ∀ x ∈ ball c R, δ x ≤ F x ![e 0, e 1] + F x ![e 2, e 3] + K)
    (hB : ∀ x ∈ sphere c σ, ∀ v, F x ![v, J' x v] ≤ ((1 + κ) * δ x + K) * g x v)
    (hg : ∀ x ∈ sphere c σ, ∀ v, g x v ≤ (1 + L * ‖x - c‖) * ‖v‖ ^ 2)
    (hJ : ∀ x ∈ sphere c σ, ∀ v, ‖J' x v - J v‖ ≤ L * ‖x - c‖ * ‖v‖)
    (hFn : ∀ x ∈ sphere c σ, ‖F x‖ ≤ A * δ x + K) (hσ : σ ∈ Ioo 0 R) :
    ((μ.withDensity fun x ↦ ENNReal.ofReal (δ x)) (closedBall c σ)).toReal ≤
      σ / 2 * (1 + (1 + A) * L * σ) * (1 + κ) * deriv (fun s ↦
        ((μ.withDensity fun x ↦ ENNReal.ofReal (δ x)) (closedBall c s)).toReal) σ +
        K * (1 + 2 * L * R) * (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)) * σ ^ 4 := by
  have hσR : sphere c σ ⊆ ball c R := sphere_subset_closedBall.trans (closedBall_subset_ball hσ.2)
  have hKR : K ≤ K * (1 + 2 * L * R) := by
    nlinarith [mul_nonneg hK (mul_nonneg hL (hσ.1.trans hσ.2).le)]
  -- On the sphere, `δ` bounds the Hermitian part of `F` for the constant structure `J`, at the
  -- cost of the factor `1 + (1 + A) L σ`.
  have hB' : ∀ x ∈ sphere c σ, ∀ v, F x ![v, J v] ≤
      ((1 + ((1 + κ) * (1 + (1 + A) * L * σ) - 1)) * δ x + K * (1 + 2 * L * R)) * ‖v‖ ^ 2 := by
    intro x hx v
    have hxR := hσR hx
    have hxc : ‖x - c‖ = σ := by rwa [mem_sphere, dist_eq_norm] at hx
    have hδx := hδ₀ x hxR
    -- Exchanging `J' x v` for `J v` changes `F(v, ·)` by `F(v, J' x v - J v)`.
    have hsub : F x ![v, J v] = F x ![v, J' x v] - F x ![v, J' x v - J v] := by
      have h := (F x).map_vecCons_sub (J' x v) (J v) ![v]
      rw [(F x).apply_vecCons_swap v, (F x).apply_vecCons_swap v,
        (F x).apply_vecCons_swap v] at h
      linarith
    have hnorm : |F x ![v, J' x v - J v]| ≤ ‖F x‖ * (‖v‖ * ‖J' x v - J v‖) := by
      simpa [Fin.prod_univ_two, Real.norm_eq_abs] using (F x).le_opNorm ![v, J' x v - J v]
    have hg' := hg x hx v
    have hJ' := hJ x hx v
    rw [hxc] at hg' hJ'
    have h₁ : ((1 + κ) * δ x + K) * g x v ≤ ((1 + κ) * δ x + K) * ((1 + L * σ) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hg' (add_nonneg (mul_nonneg (by linarith) hδx) hK)
    have h₂ : ‖F x‖ * (‖v‖ * ‖J' x v - J v‖) ≤ (A * δ x + K) * (‖v‖ * (L * σ * ‖v‖)) :=
      mul_le_mul (hFn x hx) (mul_le_mul_of_nonneg_left hJ' (norm_nonneg v))
        (by positivity) (add_nonneg (mul_nonneg hA hδx) hK)
    calc F x ![v, J v]
        ≤ ((1 + κ) * δ x + K) * ((1 + L * σ) * ‖v‖ ^ 2) +
            (A * δ x + K) * (‖v‖ * (L * σ * ‖v‖)) := by
          linarith [hB x hx v, neg_abs_le (F x ![v, J' x v - J v])]
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ hA) hL) hσ.1.le)
            (mul_nonneg hδx (sq_nonneg ‖v‖)),
            mul_nonneg (mul_nonneg hK hL) (mul_nonneg (sub_nonneg.2 hσ.2.le) (sq_nonneg ‖v‖))]
  refine (measure_closedBall_le_mul_deriv_add (μ := μ) h₀ h₂ hF hdF hδ hδ₀
    (fun x hx ↦ (hω x hx).trans (by linarith)) hB' hσ).trans_eq ?_
  ring

end TauCeti.SeibergWitten
