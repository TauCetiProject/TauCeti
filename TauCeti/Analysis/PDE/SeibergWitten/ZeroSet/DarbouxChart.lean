/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.FlatChart
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.UpperDensity
import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
import TauCeti.MeasureTheory.Covering.ChartDensity

/-!
# Density of the defect energy for large-parameter solutions in a Darboux chart

On a symplectic four-manifold, a Darboux chart about a point `c` makes the symplectic form the
constant form `ω = e⁰ ∧ e¹ + e² ∧ e³` of a four-dimensional real inner product space `E` with an
orthogonal complex structure `J` and a positively oriented unitary frame `e` (`J e₀ = e₁`,
`J e₂ = e₃`). The compatible almost complex structure and its metric `g_x = ω(·, J_x ·)` still move
with the point. The Seiberg–Witten equations at `x` are written in a `g_x`-unitary frame, that is,
through a coframe `S x : E →L[ℝ] E` sending chart vectors to their frame coordinates. A unitary
frame for a metric compatible with `ω` is a symplectic frame, so `S x` preserves `ω`:
`⟪J (S x u), S x v⟫ = ⟪J u, v⟫`. After a linear symplectic change of chart, `S c` is the
identity, and a smooth frame then satisfies `‖S x - 1‖ ≤ L ‖x - c‖`.

The real curvature form `F = i F_a` of the connection on the twisting line is a closed two-form
on the chart. In the frame it is the two-form `G x` with `F x = G x ∘ S x`, and the curvature
equation of the large-parameter equations at `x` is the flat-chart equation
`G + ⋆G = (r / 4) ω - q(√r (φ + β)) - η` of
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.FlatChart`, with the spinors `φ` and `β` and the
forcing `η` read in the same frame. Taubes's coarse bounds are hypotheses, as there.

The chart inequality `TauCeti.SeibergWitten.measure_closedBall_le_mul_one_add_mul_deriv_add` of
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Monotonicity` takes a moving complex structure `J' x`
and quadratic form `g x`. The frame supplies them: the complex structure
`J' x = (S x)⁻¹ J S x = J S†S` that `S x` carries to `J`, and the metric `g x v = ‖S x v‖²`. The
inputs of that inequality transfer from `G` to `F` as follows.

* The Kähler component is the same in the chart and in the frame,
  `F(e₀, e₁) + F(e₂, e₃) = G(e₀, e₁) + G(e₂, e₃)`, because `S x` is symplectic
  (`TauCeti.AlmostComplexStructure.compContinuousLinearMap_apply_add_apply_eq`). So the defect
  density `δ = (r / 4) |1 - |φ|² - |β|²|` is bounded by the Kähler component of `F` exactly as in
  the flat chart (`TauCeti.SeibergWitten.div_mul_abs_one_sub_sub_le_apply_add_apply_add`).
* A symplectic `S` satisfies `S J S† = J`
  (`TauCeti.AlmostComplexStructure.apply_apply_adjoint_apply`), so the Hermitian part
  `F(v, J' v) = G(S v, J S v)` is bounded by the flat-chart bound on `G` against `g x v`, while
  `‖J' x - J‖ = ‖S†S - 1†1‖` (`ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le`)
  and `g x v / ‖v‖² - 1` are `O(‖S - 1‖)`.
* The whole curvature is bounded by the defect density, `‖G‖ ≤ (2 + C) δ + O(1)`
  (`TauCeti.SeibergWitten.norm_le_of_add_hodgeStar_eq_of_norm_smul_sub_hodgeStar_le`), hence so is
  `‖F‖ ≤ ‖G‖ ‖S‖²`. So on the sphere of radius `σ` the moving geometry costs a factor `1 + C' σ`.

Only the bounds on `G` use the equations. Given the Kähler-component bound for `F` and the
Hermitian and norm bounds for `G`, the transfer through a symplectic frame gives the monotonicity
inequality without them
(`TauCeti.SeibergWitten.measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame`, in
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Monotonicity`).

The result is Taubes's differential inequality in a Darboux chart, with the geometric factor
`1 + C' σ`:

`E_r(B_σ) ≤ (σ / 2) (1 + C' σ) (1 + C r^(-1/2)) E_r'(σ) + K' σ⁴`

(`TauCeti.SeibergWitten.exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame`), with
`C'` and `K'` depending only on the constants of the hypotheses and on the radius of the chart, not
on `r`, on the solution or on the centre. Integrating it as in the flat chart
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_withDensity_closedBall_of_eq_zero`) and as in
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.UpperDensity` gives

* the quadratic lower bound `E_r(B_σ) ≥ c σ²` at zeros of `α`, for `c₀ r^(-1/2) ≤ σ ≤ ρ₀`
  (`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame`);
* the quadratic upper bound `E_r(B_σ) ≤ C'' σ²` at every centre whose ball of radius `R / 2` has
  defect energy at most `M`, for `c₀ r^(-1/2) ≤ σ ≤ R / 2`
  (`TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_frame`).

The balls are those of the chart, and the measure `μ` is an additive Haar measure of the chart;
the Riemannian volume form `ω² / 2` is a multiple of it. The chart is centred at the centre of
the balls, so the covering argument of `TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.FlatChart`,
whose balls have many centres, needs a Darboux chart about each of them.

**On the manifold.** The manifold is a metric space `X`, with a measure `μX`, the defect energy
of the solution on `X`. About a point `z` a Darboux chart is a map `e : X → E` on a set `s`, and
the defect energy `ν` of the chart is compared with the pushforward of `μX`, through the sets
`s ∩ e ⁻¹' t` for `t ⊆ ball (e z) R`; they are equal when the Riemannian volume reads as `μ` in
the chart. The balls of `X` and of the chart are compared through Lipschitz bounds at the centre
(`TauCeti.ofReal_div_mul_pow_le_measure_closedBall_of_dist_le_mul_dist_apply`,
`TauCeti.measure_closedBall_le_ofReal_mul_mul_pow_of_dist_apply_le_mul_dist`). This gives

* the quadratic lower bound `μX (B_ρ(z)) ≥ c ρ²` for the balls of `X` at a zero of `α`, when the
  inverse of the chart is `Λ`-Lipschitz at `e z` and the defect energy of the chart is at most the
  restricted pushforward of `μX`
  (`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le`);
* the quadratic upper bound `μX (B_ρ(z)) ≤ C'' ρ²` for the balls of `X` at every centre `z` whose
  chart ball of radius `R / 2` has defect energy at most `M`, when the chart is `Λ`-Lipschitz at
  `z` on a ball `closedBall z R₁ ⊆ s` and the restricted pushforward of `μX` is at most the defect
  energy of the chart
  (`TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_frame_of_dist_apply_le`);
* Taubes's packing bound: a set `Z` of zeros of `α` with a Darboux chart about each of its points,
  with uniform constants, is covered by at most `4 μX(Z_{σ/2}) / (c σ²)` balls of `X` of radius
  `σ` centred in `Z`, for `σ ≤ 2 ρ₀`, `r ≥ max 1 (8 K)` and `r ≥ (2 c₀ / σ)²`
  (`TauCeti.SeibergWitten.exists_forall_coveringNumber_le_of_frame`). When `μX(Z_{σ/2})` is
  finite, the lower bound and `TauCeti.exists_finset_isCover_pairwiseDisjoint_closedBall` also
  give such a cover whose half-balls are pairwise disjoint.

## Main results

* `TauCeti.SeibergWitten.exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame`:
  Taubes's monotonicity inequality in a Darboux chart.
* `TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame`: the
  quadratic lower bound at a zero of `α`.
* `TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_frame`: the quadratic upper bound
  at every centre.
* `TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le`,
  `TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_frame_of_dist_apply_le`: the
  quadratic lower and upper bounds for the balls of a metric space, through a Darboux chart.
* `TauCeti.SeibergWitten.exists_forall_coveringNumber_le_of_frame`: the covering of the zeros of
  `α` in a metric space with a Darboux chart about each of them.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Propositions 3.1–3.2 and Lemma 3.6.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Metric MeasureTheory Set
open scoped RealInnerProductSpace InnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {J : AlmostComplexStructure E}

/-! ### The monotonicity inequality in a Darboux chart -/

variable [Fact (finrank ℝ E = 4)] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {Q : QuadraticForm ℝ E} {o : Orientation ℝ E (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {e : OrthonormalBasis (Fin 4) ℝ E}

attribute [local instance] finiteDimensional_of_finrank_four

variable (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ E) (he : e.toBasis.orientation = o)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)

include h₀ h₂₃ hQ he hρ h₂

/-- **Taubes's monotonicity inequality for large-parameter solutions in a Darboux chart.** Fix
constants `K, C, H, L ≥ 0` and a radius `R`. There are constants `C', K' ≥ 0` with the
following property. On the ball `ball c R` of the chart let `F` be a closed `C¹` two-form field,
let `S x` be a coframe preserving the Kähler form `ω(u, v) = ⟪J u, v⟫` with
`‖S x - 1‖ ≤ L ‖x - c‖`, and let `G x` be `F x` in the frame, `F x = G x ∘ S x`. Let `φ`, `β` be
continuous fields of positive half-spinors in the canonical line of `J` and in its complement, and
suppose that `G` satisfies the curvature equation `G + ⋆G = (r / 4) ω - q(√r (φ + β)) - η` with
`r ≥ 1`, Taubes's coarse bounds `‖φ‖² + ‖β‖² ≤ 1 + K / r`, `‖β‖² ≤ (K / r) w₊ + K / r²` and
`‖G⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where `w₊ = max (1 - ‖φ‖²) 0` and `G⁻ = (G - ⋆G) / 2`,
and the forcing bound `‖η‖ ≤ H`. Then the defect energy `ν = δ dμ`,
`δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|`, satisfies at every radius `0 < σ < R`

`ν(B_σ) ≤ (σ / 2) (1 + C' σ) (1 + C / √r) d/dσ ν(B_σ) + K' σ⁴`

for the closed balls `B_σ = closedBall c σ` of the chart, by
`TauCeti.SeibergWitten.measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame`. -/
theorem exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame {K C H L R : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    ∃ C' ≥ 0, ∃ K' ≥ 0, ∀ r, 1 ≤ r →
      ∀ (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ) (S : E → E →L[ℝ] E) (φ β : E → positiveHalfSpinors o ρ)
        (η : E → ⋀[ℝ]^2 E) (c : E),
      (∀ x ∈ ball c R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball c R, extDeriv F x = 0) →
      (∀ x ∈ ball c R, F x = (G x).compContinuousLinearMap (S x)) →
      (∀ x ∈ ball c R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) →
      (∀ x ∈ ball c R, ‖S x - 1‖ ≤ L * ‖x - c‖) →
      ContinuousOn φ (ball c R) → ContinuousOn β (ball c R) →
      (∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball c R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball c R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball c R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball c R, (alternatingFormEquiv E 2).symm (G x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball c R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      ∀ σ ∈ Ioo 0 R,
        ((μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|))
            (closedBall c σ)).toReal ≤
          σ / 2 * (1 + C' * σ) * (1 + C / √r) * deriv (fun s ↦ ((μ.withDensity fun x ↦
              ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|)) (closedBall c s)).toReal) σ +
            K' * σ ^ 4 := by
  -- The constants use `|R|` so that `C'` and `K'` are nonnegative with no sign hypothesis on `R`.
  set M := L * |R|
  set K₁ := (1 + C) * K + √2 * H / 2 + C with hK₁d
  set K₂ := (2 + C) * (K + 1) + H
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨(1 + (2 + C) * (1 + M) ^ 2) * ((2 + M) * L), by positivity,
    (K₁ + K₂) * (1 + M) ^ 2 * (1 + 2 * ((2 + M) * L) * |R|) *
      (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)), by positivity,
    fun r hr F G S φ β η c hF hdF hFG hSω hS hφc hβc hφ hβ hφβ hβK hη hGeq hGm σ hσ ↦ ?_⟩
  have hr0 : 0 < r := by linarith
  set δ : E → ℝ := fun x ↦ r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|
  have hδx (x : E) : r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| = δ x := rfl
  have hσR : sphere c σ ⊆ ball c R := sphere_subset_closedBall.trans (closedBall_subset_ball hσ.2)
  -- The defect density is bounded by the Kähler component, which is the same for `F` and `G`.
  have hω : ∀ x ∈ ball c R, δ x ≤ F x ![e 0, e 1] + F x ![e 2, e 3] + (K₁ + K₂) := by
    intro x hx
    have h := div_mul_abs_one_sub_sub_le_apply_add_apply_add h₀ h₂₃ hQ hkl he hr0 hK (hφ x hx)
      (hβ x hx) (hφβ x hx) (hGeq x hx)
    rw [hδx] at h
    rw [hFG x hx, AlmostComplexStructure.compContinuousLinearMap_apply_add_apply_eq Fact.out h₀ h₂₃
      (hSω x hx)]
    have hηx : √2 * ‖η x‖ / 2 ≤ √2 * H / 2 := by gcongr; exact hη x hx
    nlinarith [mul_nonneg hC hK, hK₁d]
  -- In the frame, the defect density bounds the Hermitian part of `G` and its norm.
  have hGB : ∀ x ∈ ball c R, ∀ u, G x ![u, J u] ≤ ((1 + C / √r) * δ x + (K₁ + K₂)) * ‖u‖ ^ 2 := by
    intro x hx u
    refine (apply_apply_le_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hr (hφ x hx) (hβ x hx)
      (hβK x hx) (hGeq x hx) hC (hGm x hx) u).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    have : √2 * ‖η x‖ / 2 ≤ √2 * H / 2 := by gcongr; exact hη x hx
    rw [hδx]
    linarith
  have hGn : ∀ x ∈ ball c R, ‖G x‖ ≤ (2 + C) * δ x + (K₁ + K₂) := by
    intro x hx
    have h := norm_le_of_add_hodgeStar_eq_of_norm_smul_sub_hodgeStar_le h₀ h₂₃ hQ hkl he (hφ x hx)
      (hβ x hx) hρ h₂ hr (hβK x hx) (hφβ x hx) (hGeq x hx) hC (hGm x hx)
    have hG : ‖G x‖ ≤ ‖(alternatingFormEquiv E 2).symm (G x)‖ := by
      simpa using norm_alternatingFormEquiv_le ((alternatingFormEquiv E 2).symm (G x))
    rw [hδx] at h
    linarith [hη x hx]
  have hδc : ContinuousOn δ (ball c R) :=
    continuousOn_const.mul ((continuousOn_const.sub (hφc.norm.pow 2)).sub (hβc.norm.pow 2)).abs
  have h := measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame (μ := μ) h₀ h₂₃
    (div_nonneg hC (Real.sqrt_nonneg r)) (add_nonneg hK₁ hK₂) (by positivity : (0 : ℝ) ≤ 2 + C) hL
    hF hdF hδc (fun x _ ↦ mul_nonneg (by linarith) (abs_nonneg _)) hω
    (fun x hx ↦ hFG x (hσR hx)) (fun x hx ↦ hSω x (hσR hx)) (fun x hx ↦ hS x (hσR hx))
    (fun x hx ↦ hGB x (hσR hx)) (fun x hx ↦ hGn x (hσR hx)) hσ
  -- `0 < σ < R` gives `R = |R|`, and `R` occurs in `h` only inside the constants.
  rwa [← abs_of_pos (hσ.1.trans hσ.2)] at h

/-! ### Quadratic bounds for the defect energy in a Darboux chart -/

/-- **Quadratic lower bound for the defect energy at a zero of `α`, in a Darboux chart.** Fix
constants `K, C, H, L ≥ 0` and a radius `R > 0`. There are constants `c₀, c, ρ₀ > 0` with the
following property. Let `r ≥ 1` with `r ≥ 8 K`, and let `x₀` be a zero of `α`. On the ball
`ball x₀ R` of a Darboux chart centred at `x₀`, let the fields `F`, `G`, `S`, `φ`, `β`, `η`
satisfy the hypotheses of
`TauCeti.SeibergWitten.exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame`, let `α`
be a differentiable function with `|α| = |φ|` (the coefficient of `φ = α u₀`), and let its
covariant derivative for the connection form `b` satisfy Taubes's gradient bound
`|∇_a α|² ≤ K r w₊ + K`, measured in the chart. Then the defect energy `ν = δ dμ`,
`δ = (r / 4) |1 - |φ|² - |β|²|`, satisfies `ν(B_σ) ≥ c σ²` for every `c₀ / √r ≤ σ ≤ ρ₀`. -/
theorem exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame {K C H L R : ℝ} (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ c₀ > 0, ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → 8 * K ≤ r →
      ∀ (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ) (S : E → E →L[ℝ] E) (φ β : E → positiveHalfSpinors o ρ)
        (α : E → ℂ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (η : E → ⋀[ℝ]^2 E) (x₀ : E),
      (∀ x ∈ ball x₀ R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball x₀ R, extDeriv F x = 0) →
      (∀ x ∈ ball x₀ R, F x = (G x).compContinuousLinearMap (S x)) →
      (∀ x ∈ ball x₀ R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) →
      (∀ x ∈ ball x₀ R, ‖S x - 1‖ ≤ L * ‖x - x₀‖) →
      ContinuousOn φ (ball x₀ R) → ContinuousOn β (ball x₀ R) →
      (∀ x ∈ ball x₀ R, DifferentiableAt ℝ α x) → (∀ x ∈ ball x₀ R, ‖φ x‖ = ‖α x‖) →
      (∀ x ∈ ball x₀ R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball x₀ R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball x₀ R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball x₀ R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball x₀ R, ‖covariantDeriv b α x‖ ^ 2 ≤ K * r * max (1 - ‖φ x‖ ^ 2) 0 + K) →
      (∀ x ∈ ball x₀ R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball x₀ R, (alternatingFormEquiv E 2).symm (G x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball x₀ R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      α x₀ = 0 →
      ∀ σ, c₀ / √r ≤ σ → σ ≤ ρ₀ →
        ENNReal.ofReal (c * σ ^ 2) ≤ (μ.withDensity fun x ↦
          ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|)) (closedBall x₀ σ) := by
  obtain ⟨C', hC', K', hK', hmono⟩ :=
    exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame (μ := μ) h₀ h₂₃ hQ hkl he hρ
      h₂ hK hC hH hL
  obtain ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_withDensity_closedBall_of_eq_zero (G := positiveHalfSpinors o ρ)
      (F := positiveHalfSpinors o ρ) (μ := μ) Fact.out hK hC' hC hK' hR
  refine ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, fun r hr hrK F G S φ β α b η x₀ hF hdF hFG hSω hS hφc hβc hα
    hφα hφ hβ hφβ hβK hgrad hη hGeq hGm hα₀ ↦ hdens r hr hrK φ β α b x₀ hφc hβc hα hφα hφβ hβK
      hgrad (hmono r hr F G S φ β η x₀ hF hdF hFG hSω hS hφc hβc hφ hβ hφβ hβK hη hGeq hGm) hα₀⟩

/-- **Quadratic upper bound for the defect energy in a Darboux chart.** Fix constants
`K, C, H, L, M ≥ 0`, a radius `R > 0` and a scale `c₀ > 0`. There is a constant `C'' > 0` with the
following property. Let `r ≥ 1` and let the fields `F`, `G`, `S`, `φ`, `β`, `η` satisfy the
hypotheses of
`TauCeti.SeibergWitten.exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame` on the
ball `ball c R` of a Darboux chart centred at `c`. If the defect energy `ν = δ dμ`,
`δ = (r / 4) |1 - |φ|² - |β|²|`, of the ball `B_{R/2}` is at most `M`, then
`ν(B_σ) ≤ C'' σ²` for every `c₀ / √r ≤ σ ≤ R / 2`. Unlike the lower bound
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame`), the centre
need not be a zero of `α`. -/
theorem exists_forall_measure_closedBall_le_of_frame {K C H L R M c₀ : ℝ} (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (hM : 0 ≤ M) (hc₀ : 0 < c₀) :
    ∃ C'' > 0, ∀ r, 1 ≤ r →
      ∀ (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ) (S : E → E →L[ℝ] E) (φ β : E → positiveHalfSpinors o ρ)
        (η : E → ⋀[ℝ]^2 E) (c : E),
      (∀ x ∈ ball c R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball c R, extDeriv F x = 0) →
      (∀ x ∈ ball c R, F x = (G x).compContinuousLinearMap (S x)) →
      (∀ x ∈ ball c R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) →
      (∀ x ∈ ball c R, ‖S x - 1‖ ≤ L * ‖x - c‖) →
      ContinuousOn φ (ball c R) → ContinuousOn β (ball c R) →
      (∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball c R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball c R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball c R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball c R, (alternatingFormEquiv E 2).symm (G x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball c R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|))
        (closedBall c (R / 2)) ≤ ENNReal.ofReal M →
      ∀ σ, c₀ / √r ≤ σ → σ ≤ R / 2 →
        (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|))
          (closedBall c σ) ≤ ENNReal.ofReal (C'' * σ ^ 2) := by
  obtain ⟨C', hC', K', hK', hmono⟩ :=
    exists_measure_closedBall_le_mul_one_add_mul_deriv_add_of_frame (μ := μ) h₀ h₂₃ hQ hkl he hρ
      h₂ hK hC hH hL
  obtain ⟨C'', hC'', hbound⟩ :=
    TauCeti.exists_forall_measure_closedBall_le_of_ae_le (X := E) hC' hC hK' hM hc₀ (half_pos hR)
  refine ⟨C'', hC'', fun r hr F G S φ β η c hF hdF hFG hSω hS hφc hβc hφ hβ hφβ hβK hη hGeq hGm
    hνM σ hσ hσR ↦ hbound r hr _ c hνM (Filter.Eventually.of_forall fun s hs ↦ ?_) σ hσ hσR⟩
  have hs0 : 0 < s := (by positivity : 0 ≤ c₀ / √r).trans_lt hs.1
  exact hmono r hr F G S φ β η c hF hdF hFG hSω hS hφc hβc hφ hβ hφβ hβK hη hGeq hGm s
    ⟨hs0, hs.2.trans (half_lt_self hR)⟩

/-! ### Quadratic bounds and the covering of the zeros on a metric space -/

/-- **Quadratic lower bound for the defect energy at a zero of `α`, on a metric space.** Fix
constants `K, C, H, L ≥ 0`, a radius `R > 0` and a constant `Λ > 0`. There are constants
`c₀, c, ρ₀ > 0` with the following property. Let `X` be a metric space with a measure `μX`, for
instance a symplectic four-manifold with a distance and its defect energy measure, and let `z` be a
point of `X`. Let `e : X → E` be a Darboux chart on a set `s`, whose inverse is `Λ`-Lipschitz at
`e z` on the ball `ball (e z) R`: `dist y z ≤ Λ ‖e y - e z‖` for `y ∈ s` with
`e y ∈ ball (e z) R`. Let the fields `F`, `G`, `S`, `φ`, `β`, `α`, `b`, `η` satisfy the
hypotheses of `TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame`
on `ball (e z) R`, with `α (e z) = 0`, and suppose that the defect energy `ν = δ dμ` of the chart,
`δ = (r / 4) |1 - |φ|² - |β|²|`, is at most the pushforward of `μX` restricted to `s` on
`ball (e z) R`: `ν t ≤ μX (s ∩ e ⁻¹' t)` for measurable `t ⊆ ball (e z) R`. Then
`μX (closedBall z ρ) ≥ c ρ²` for every `c₀ / √r ≤ ρ ≤ ρ₀`, for the balls of `X`. -/
theorem exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] {K C H L R Λ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (hΛ : 0 < Λ) :
    ∃ c₀ > 0, ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → 8 * K ≤ r →
      ∀ (μX : Measure X) (e : X → E) (s : Set X) (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ)
        (S : E → E →L[ℝ] E) (φ β : E → positiveHalfSpinors o ρ) (α : E → ℂ)
        (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (η : E → ⋀[ℝ]^2 E) (z : X),
      (∀ y ∈ s, e y ∈ ball (e z) R → dist y z ≤ Λ * dist (e y) (e z)) →
      (∀ t ⊆ ball (e z) R, MeasurableSet t →
        (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|)) t ≤
          μX (s ∩ e ⁻¹' t)) →
      (∀ x ∈ ball (e z) R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball (e z) R, extDeriv F x = 0) →
      (∀ x ∈ ball (e z) R, F x = (G x).compContinuousLinearMap (S x)) →
      (∀ x ∈ ball (e z) R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) →
      (∀ x ∈ ball (e z) R, ‖S x - 1‖ ≤ L * ‖x - e z‖) →
      ContinuousOn φ (ball (e z) R) → ContinuousOn β (ball (e z) R) →
      (∀ x ∈ ball (e z) R, DifferentiableAt ℝ α x) → (∀ x ∈ ball (e z) R, ‖φ x‖ = ‖α x‖) →
      (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball (e z) R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball (e z) R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball (e z) R,
        ‖covariantDeriv b α x‖ ^ 2 ≤ K * r * max (1 - ‖φ x‖ ^ 2) 0 + K) →
      (∀ x ∈ ball (e z) R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball (e z) R, (alternatingFormEquiv E 2).symm (G x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball (e z) R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      α (e z) = 0 →
      ∀ ρ, c₀ / √r ≤ ρ → ρ ≤ ρ₀ → ENNReal.ofReal (c * ρ ^ 2) ≤ μX (closedBall z ρ) := by
  obtain ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame (μ := μ) h₀ h₂₃ hQ hkl he hρ h₂ hK
      hC hH hL hR
  -- In the chart the lower bound holds up to the radius `min ρ₀ (R / 2) < R`; the inverse of
  -- the chart rescales the radii by `Λ` and the constant by `Λ⁻²`.
  refine ⟨Λ * c₀, by positivity, c / Λ ^ 2, by positivity, Λ * min ρ₀ (R / 2), by positivity,
    fun r hr hrK μX e s F G S φ β α b η z hdist hν hF hdF hFG hSω hS hφc hβc hα hφα hφ hβ hφβ hβK
      hgrad hη hGeq hGm hα₀ σ hσ hσρ₀ ↦ ?_⟩
  refine ofReal_div_mul_pow_le_measure_closedBall_of_dist_le_mul_dist_apply hdist hν hΛ
    ((min_le_right _ _).trans_lt (half_lt_self hR)) (fun τ hτ hτb ↦ hdens r hr hrK F G S φ β α b η
      (e z) hF hdF hFG hSω hS hφc hβc hα hφα hφ hβ hφβ hβK hgrad hη hGeq hGm hα₀ τ hτ
        (hτb.trans (min_le_left _ _))) ?_ hσρ₀
  rwa [← mul_div_assoc]

/-- **Quadratic upper bound for the defect energy, on a metric space.** Fix constants
`K, C, H, L, M ≥ 0`, radii `R > 0` and `R₁`, a scale `c₀ > 0` and a constant `Λ > 0`. There is a
constant `C'' > 0` with the following property. Let `X` be a metric space with a measure `μX` and
let `z` be a point of `X`. Let `e : X → E` be a Darboux chart on a set `s` containing the closed
ball of radius `R₁` about `z`, which is `Λ`-Lipschitz at `z` on that ball:
`‖e y - e z‖ ≤ Λ dist y z`. Let the fields `F`, `G`, `S`, `φ`, `β`, `η` satisfy the hypotheses of
`TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_frame` on `ball (e z) R`, including
the bound `M` on the defect energy `ν = δ dμ` of the chart ball of radius `R / 2`,
`δ = (r / 4) |1 - |φ|² - |β|²|`, and suppose that the pushforward of `μX` restricted to `s` is
at most `ν` on `ball (e z) R`: `μX (s ∩ e ⁻¹' t) ≤ ν t` for measurable `t ⊆ ball (e z) R`.
Then `μX (closedBall z ρ) ≤ C'' ρ²` for every `ρ ≤ R₁` with `c₀ / √r ≤ ρ` and `Λ ρ ≤ R / 2`, for
the balls of `X`. Unlike the lower bound
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le`),
the centre need not be a zero of `α`. -/
theorem exists_forall_measure_closedBall_le_of_frame_of_dist_apply_le {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] {K C H L R R₁ M c₀ Λ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (hM : 0 ≤ M) (hc₀ : 0 < c₀) (hΛ : 0 < Λ) :
    ∃ C'' > 0, ∀ r, 1 ≤ r →
      ∀ (μX : Measure X) (e : X → E) (s : Set X) (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ)
        (S : E → E →L[ℝ] E) (φ β : E → positiveHalfSpinors o ρ) (η : E → ⋀[ℝ]^2 E) (z : X),
      closedBall z R₁ ⊆ s → (∀ y ∈ closedBall z R₁, dist (e y) (e z) ≤ Λ * dist y z) →
      (∀ t ⊆ ball (e z) R, MeasurableSet t → μX (s ∩ e ⁻¹' t) ≤
        (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|)) t) →
      (∀ x ∈ ball (e z) R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball (e z) R, extDeriv F x = 0) →
      (∀ x ∈ ball (e z) R, F x = (G x).compContinuousLinearMap (S x)) →
      (∀ x ∈ ball (e z) R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) →
      (∀ x ∈ ball (e z) R, ‖S x - 1‖ ≤ L * ‖x - e z‖) →
      ContinuousOn φ (ball (e z) R) → ContinuousOn β (ball (e z) R) →
      (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball (e z) R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball (e z) R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball (e z) R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball (e z) R, (alternatingFormEquiv E 2).symm (G x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball (e z) R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|))
        (closedBall (e z) (R / 2)) ≤ ENNReal.ofReal M →
      ∀ ρ, ρ ≤ R₁ → c₀ / √r ≤ ρ → Λ * ρ ≤ R / 2 →
        μX (closedBall z ρ) ≤ ENNReal.ofReal (C'' * ρ ^ 2) := by
  -- In the chart the upper bound holds from the scale `Λ c₀`; the chart rescales the radii by `Λ`
  -- and the constant by `Λ²`.
  obtain ⟨C'', hC'', hbound⟩ :=
    exists_forall_measure_closedBall_le_of_frame (μ := μ) h₀ h₂₃ hQ hkl he hρ h₂ hK hC hH hL hR
      hM (mul_pos hΛ hc₀)
  refine ⟨C'' * Λ ^ 2, by positivity, fun r hr μX e s F G S φ β η z hs hdist hν hF hdF hFG hSω hS
    hφc hβc hφ hβ hφβ hβK hη hGeq hGm hνM σ hσR₁ hσ hσR ↦ ?_⟩
  refine measure_closedBall_le_ofReal_mul_mul_pow_of_dist_apply_le_mul_dist hs hdist hν hΛ.le
    (half_lt_self hR) (fun τ hτ hτR ↦ hbound r hr F G S φ β η (e z) hF hdF hFG hSω hS hφc hβc hφ
      hβ hφβ hβK hη hGeq hGm hνM τ hτ hτR) hσR₁ ?_ hσR
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hσ hΛ.le

/-- **Covering the zeros of `α` on a metric space.** Fix constants `K, C, H, L ≥ 0`, a radius
`R > 0` and a constant `Λ > 0`. There are constants `c₀, c, ρ₀ > 0` with the following property.
Let `X` be a metric space with a measure `μX`, for instance a symplectic four-manifold with a
distance and its defect energy measure, and let `Z ⊆ X` be a set of zeros: about each `z ∈ Z`
there is a Darboux chart `e` on a set `s` with the hypotheses of
`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le`,
its inverse `Λ`-Lipschitz at `e z` on `ball (e z) R`, the fields of the chart satisfying the
equations and Taubes's coarse bounds there, the defect energy of the chart at most the pushforward
of `μX` restricted to `s`, and `α (e z) = 0`. Then for every `σ > 0` with `σ ≤ 2 ρ₀`, as soon as
`r ≥ 1`, `r ≥ 8 K` and `r ≥ (2 c₀ / σ)²`, the set `Z` is covered by at most
`4 μX(Z_{σ/2}) / (c σ²)` closed balls of `X` of radius `σ` centred in `Z`, where `Z_{σ/2}` is the
closed `σ / 2`-thickening of `Z`. -/
theorem exists_forall_coveringNumber_le_of_frame {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {K C H L R Λ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (hΛ : 0 < Λ) :
    ∃ c₀ > 0, ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → 8 * K ≤ r → ∀ (μX : Measure X) (Z : Set X),
      (∀ z ∈ Z, ∃ (e : X → E) (s : Set X) (F G : E → E [⋀^Fin 2]→L[ℝ] ℝ) (S : E → E →L[ℝ] E)
          (φ β : E → positiveHalfSpinors o ρ) (α : E → ℂ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ)
          (η : E → ⋀[ℝ]^2 E),
        (∀ y ∈ s, e y ∈ ball (e z) R → dist y z ≤ Λ * dist (e y) (e z)) ∧
        (∀ t ⊆ ball (e z) R, MeasurableSet t →
          (μ.withDensity fun x ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|)) t ≤
            μX (s ∩ e ⁻¹' t)) ∧
        (∀ x ∈ ball (e z) R, ContDiffAt ℝ 1 F x) ∧ (∀ x ∈ ball (e z) R, extDeriv F x = 0) ∧
        (∀ x ∈ ball (e z) R, F x = (G x).compContinuousLinearMap (S x)) ∧
        (∀ x ∈ ball (e z) R, ∀ u v, ⟪J (S x u), S x v⟫ = ⟪J u, v⟫) ∧
        (∀ x ∈ ball (e z) R, ‖S x - 1‖ ≤ L * ‖x - e z‖) ∧
        ContinuousOn φ (ball (e z) R) ∧ ContinuousOn β (ball (e z) R) ∧
        (∀ x ∈ ball (e z) R, DifferentiableAt ℝ α x) ∧ (∀ x ∈ ball (e z) R, ‖φ x‖ = ‖α x‖) ∧
        (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) ∧
        (∀ x ∈ ball (e z) R, cliffordProjection o ρ J.kahlerForm (β x) = 0) ∧
        (∀ x ∈ ball (e z) R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) ∧
        (∀ x ∈ ball (e z) R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) ∧
        (∀ x ∈ ball (e z) R,
          ‖covariantDeriv b α x‖ ^ 2 ≤ K * r * max (1 - ‖φ x‖ ^ 2) 0 + K) ∧
        (∀ x ∈ ball (e z) R, ‖η x‖ ≤ H) ∧
        (∀ x ∈ ball (e z) R, (alternatingFormEquiv E 2).symm (G x) +
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)) = (r / 4) • J.kahlerForm -
            (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) ∧
        (∀ x ∈ ball (e z) R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (G x) -
            o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (G x)))‖ ≤
            r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) ∧
        α (e z) = 0) →
      ∀ σ : ℝ≥0, σ ≠ 0 → (σ : ℝ) ≤ 2 * ρ₀ → (2 * c₀ / σ) ^ 2 ≤ r →
        (coveringNumber σ Z : ℝ≥0∞) ≤
          ENNReal.ofReal (4 / (c * σ ^ 2)) * μX (cthickening (σ / 2) Z) := by
  obtain ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_measure_closedBall_of_frame_of_dist_le (μ := μ) (X := X) h₀ h₂₃
      hQ hkl he hρ h₂ hK hC hH hL hR hΛ
  refine ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, fun r hr hrK μX Z hZ σ hσ hσρ₀ hrσ ↦
    TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le hc (fun z hz ↦ ?_) hσ
      hσρ₀ hrσ⟩
  obtain ⟨e, s, F, G, S, φ, β, α, b, η, hdist, hν, hF, hdF, hFG, hSω, hS, hφc, hβc, hα, hφα, hφ,
    hβ, hφβ, hβK, hgrad, hη, hGeq, hGm, hα₀⟩ := hZ z hz
  exact hdens r hr hrK μX e s F G S φ β α b η z hdist hν hF hdF hFG hSω hS hφc hβc hα hφα hφ hβ
    hφβ hβK hgrad hη hGeq hGm hα₀

end TauCeti.SeibergWitten
