/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameter.Curvature
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Covering
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Defect.Energy
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Monotonicity

/-!
# Density of the defect energy for large-parameter solutions in a flat chart

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = φ + β`, with `φ = α u₀` in the canonical line
and `β` in its complement, and the real curvature form `F = i F_a` of the connection on the
twisting line satisfies

`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`

(see `TauCeti.Analysis.PDE.SeibergWitten.LargeParameter.Curvature`). Its defect energy is the
measure `E_r = δ dμ` with density `δ = (r / 4) |1 - |φ|² - |β|²|`
(`TauCeti.SeibergWitten.defectMeasure`). This file works in a flat chart: the four-dimensional
real inner product space `E` with an orthogonal complex structure `J` and a positively oriented
unitary frame `e` (`J e₀ = e₁`, `J e₂ = e₃`), whose Kähler form is `ω = e⁰ ∧ e¹ + e² ∧ e³`.
The curvature `F` is a closed two-form field, and the curvature equation is read through the
identification of two-forms with `⋀² E` (`TauCeti.alternatingFormEquiv`).

Taubes's monotonicity inequality in a flat chart
(`TauCeti.SeibergWitten.measure_closedBall_le_mul_deriv_add`) takes two pointwise inequalities as
hypotheses: the bound `δ ≤ F(e₀, e₁) + F(e₂, e₃) + K` of the defect density by the Kähler
component of `F`, and the bound `F(v, J v) ≤ ((1 + κ) δ + K) ‖v‖²` of the Hermitian part of `F`.
Both follow from the curvature equation together with Taubes's coarse bounds

`|φ|² + |β|² ≤ 1 + K / r`,  `|β|² ≤ (K / r) w₊ + K / r²`,
`|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`,

where `w₊ = max (1 - |φ|²) 0` and `F⁻ = (F - ⋆F) / 2`, and a bound `|η| ≤ H` on the forcing, with
`κ = C / √r` (`TauCeti.SeibergWitten.div_mul_abs_one_sub_sub_le_inner_add`,
`TauCeti.SeibergWitten.hermitianForm_apply_self_le_of_add_hodgeStar_eq`, read on two-forms as
`TauCeti.SeibergWitten.div_mul_abs_one_sub_sub_le_apply_add_apply_add` and
`TauCeti.SeibergWitten.apply_apply_le_of_add_hodgeStar_eq`). So the defect energy of a solution
satisfies the monotonicity inequality

`E_r(B_σ) ≤ (σ / 2) (1 + C r^(-1/2)) E_r'(σ) + K' (|S| / 2 + |B₁|) σ⁴`,
`K' = (1 + C) K + √2 H / 2 + C`

(`TauCeti.SeibergWitten.measure_closedBall_le_mul_deriv_add_of_add_hodgeStar_eq`), with `C` and
`K'` independent of `r` and of the solution.

At a zero of `α`, Taubes's gradient bound `|∇_a α|² ≤ K r w₊ + K` gives the smallest-scale lower
bound `E_r(B_{c₀ / √r}) ≥ c₁ / r`
(`TauCeti.SeibergWitten.ofReal_div_le_setLIntegral_of_eq_zero`), and integrating the monotonicity
inequality propagates it to Taubes's quadratic lower bound

`E_r(B_σ) ≥ c σ²`  for `c₀ / √r ≤ σ ≤ ρ₀`

(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_add_hodgeStar_eq`).
By the maximal disjoint half-ball argument a set `Z` of zeros of `α` in a region where the
equations hold is then covered by `N(σ) ≤ 4 E_r(Z_{σ/2}) / (c σ²)` balls of radius `σ` centred at
zeros, for `r ≥ (2 c₀ / σ)²`
(`TauCeti.SeibergWitten.exists_forall_coveringNumber_le_of_add_hodgeStar_eq`).
The constants `c₀`, `c` and `ρ₀` depend only on `K`, `C`, `H`, the radius `R` of the balls on which
the equations hold, and the volume of the unit ball; they depend neither on `r` nor on the
solution. The factor `1 + C r^(-1/2)` is absorbed into the constants, since it is integrated only
over the range `σ ≥ c₀ r^(-1/2)`
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_withDensity_closedBall_of_eq_zero`).

The curvature geometry of the manifold, which turns the factor `1` in front of `E_r'(σ)` into
`1 + C σ` in Darboux coordinates, is treated in
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.DarbouxChart`.

## Main results

* `TauCeti.SeibergWitten.measure_closedBall_le_mul_deriv_add_of_add_hodgeStar_eq`: Taubes's
  monotonicity inequality for the defect energy of a solution.
* `TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_add_hodgeStar_eq`:
  the quadratic lower bound for the defect energy of balls centred at zeros of `α`.
* `TauCeti.SeibergWitten.exists_forall_coveringNumber_le_of_add_hodgeStar_eq`: the covering
  bound `N(σ) ≤ 4 E_r(Z_{σ/2}) / (c σ²)` for a set `Z` of zeros of `α`, where `Z_{σ/2}` is the
  closed `σ / 2`-thickening of `Z`; it becomes `N(σ) ≤ C σ⁻²` once the defect energy is bounded.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Metric MeasureTheory Set
open scoped RealInnerProductSpace InnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 4)]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Q : QuadraticForm ℝ E} {o : Orientation ℝ E (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ E} {J : AlmostComplexStructure E}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ E) (he : e.toBasis.orientation = o)

attribute [local instance] finiteDimensional_of_finrank_four

include h₀ h₂₃ hQ he

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The defect density is bounded by the Kähler component of a two-form.** If the two-vector of
the two-form `G` satisfies the curvature equation `G + ⋆G = (r / 4) ω - q(√r (φ + β)) - η` with
`r > 0`, `K ≥ 0` and `‖φ‖² + ‖β‖² ≤ 1 + K / r`, then the defect density
`δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|` satisfies `δ ≤ G(e₀, e₁) + G(e₂, e₃) + K / 2 + √2 ‖η‖ / 2`
(`TauCeti.SeibergWitten.div_mul_abs_one_sub_sub_le_inner_add`). -/
theorem div_mul_abs_one_sub_sub_le_apply_add_apply_add {G : E [⋀^Fin 2]→L[ℝ] ℝ}
    {φ β : positiveHalfSpinors o ρ} {η : ⋀[ℝ]^2 E} {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0) (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hGeq : (alternatingFormEquiv E 2).symm G +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm G) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 E) - η) :
    r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| ≤ G ![e 0, e 1] + G ![e 2, e 3] + K / 2 + √2 * ‖η‖ / 2 := by
  have h := div_mul_abs_one_sub_sub_le_inner_add hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he)
    (AlmostComplexStructure.norm_kahlerForm_sq_eq_two
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)) hφ hβ hr hK hφβ hGeq
  rwa [real_inner_comm, AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃,
    inner_add_right, inner_alternatingFormEquiv_symm_ιMulti,
    inner_alternatingFormEquiv_symm_ιMulti] at h

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The Hermitian part of a two-form is bounded by the defect density.** If the two-vector of
the two-form `G` satisfies the curvature equation `G + ⋆G = (r / 4) ω - q(√r (φ + β)) - η` with
`r ≥ 1`, Taubes's coarse bounds `‖β‖² ≤ (K / r) w₊ + K / r²` and
`‖G⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C` with `C ≥ 0`, where `w₊ = max (1 - ‖φ‖²) 0` and
`G⁻ = (G - ⋆G) / 2`, then
`G(v, J v) ≤ ((1 + C / √r) δ + (1 + C) K + √2 ‖η‖ / 2 + C) ‖v‖²`,
`δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|`
(`TauCeti.SeibergWitten.hermitianForm_apply_self_le_of_add_hodgeStar_eq`). -/
theorem apply_apply_le_of_add_hodgeStar_eq {G : E [⋀^Fin 2]→L[ℝ] ℝ}
    {φ β : positiveHalfSpinors o ρ} {η : ⋀[ℝ]^2 E} {r K C : ℝ} (hr : 1 ≤ r)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0)
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hGeq : (alternatingFormEquiv E 2).symm G +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm G) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 E) - η) (hC : 0 ≤ C)
    (hGm : ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm G -
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm G))‖ ≤
        r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C) (v : E) :
    G ![v, J v] ≤
      ((1 + C / √r) * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) + (1 + C) * K + √2 * ‖η‖ / 2 + C) *
        ‖v‖ ^ 2 := by
  have h := hermitianForm_apply_self_le_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hφ hβ hr hβK hGeq hC
    hGm v
  rwa [AlmostComplexStructure.hermitianForm_apply_self, inner_alternatingFormEquiv_symm_ιMulti]
    at h

/-- **Taubes's monotonicity inequality for large-parameter solutions in a flat chart.** Let `F` be
a closed `C¹` two-form field on the ball `ball c R`, and let `φ`, `β` be continuous fields of
positive half-spinors in the canonical line of `J` and in its complement. Suppose that on the ball
the curvature equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` holds, with `r ≥ 1`, Taubes's
coarse bounds `‖φ‖² + ‖β‖² ≤ 1 + K / r`, `‖β‖² ≤ (K / r) w₊ + K / r²` and
`‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where `w₊ = max (1 - ‖φ‖²) 0` and `F⁻ = (F - ⋆F) / 2`,
and a forcing bound `‖η‖ ≤ H`, where `K, C ≥ 0`. Then the defect energy `ν = δ dμ`,
`δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|`, satisfies at every radius `0 < σ < R`

`ν(B_σ) ≤ (σ / 2) (1 + C / √r) d/dσ ν(B_σ) + ((1 + C) K + √2 H / 2 + C) (|S| / 2 + |B₁|) σ⁴`

for the closed balls `B_σ = closedBall c σ`. -/
theorem measure_closedBall_le_mul_deriv_add_of_add_hodgeStar_eq
    {F : E → E [⋀^Fin 2]→L[ℝ] ℝ} {φ β : E → positiveHalfSpinors o ρ} {η : E → ⋀[ℝ]^2 E}
    {c : E} {R r K C H σ : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K) (hC₀ : 0 ≤ C)
    (hF : ∀ x ∈ ball c R, ContDiffAt ℝ 1 F x) (hdF : ∀ x ∈ ball c R, extDeriv F x = 0)
    (hφc : ContinuousOn φ (ball c R)) (hβc : ContinuousOn β (ball c R))
    (hφ : ∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x)
    (hβ : ∀ x ∈ ball c R, cliffordProjection o ρ J.kahlerForm (β x) = 0)
    (hφβ : ∀ x ∈ ball c R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r)
    (hβK : ∀ x ∈ ball c R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2)
    (hη : ∀ x ∈ ball c R, ‖η x‖ ≤ H)
    (hFeq : ∀ x ∈ ball c R, (alternatingFormEquiv E 2).symm (F x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x)
    (hFm : ∀ x ∈ ball c R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (F x) -
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)))‖ ≤
        r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) (hσ : σ ∈ Ioo 0 R) :
    (defectMeasure μ r φ β (closedBall c σ)).toReal ≤
      σ / 2 * (1 + C / √r) * deriv (fun s ↦ (defectMeasure μ r φ β (closedBall c s)).toReal) σ +
        ((1 + C) * K + √2 * H / 2 + C) * (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)) *
          σ ^ 4 := by
  have hr0 : 0 < r := by linarith
  -- The bound of the defect density by the Kähler component.
  have hω : ∀ x ∈ ball c R, r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ≤
      F x ![e 0, e 1] + F x ![e 2, e 3] + ((1 + C) * K + √2 * H / 2 + C) := by
    intro x hx
    have h := div_mul_abs_one_sub_sub_le_apply_add_apply_add h₀ h₂₃ hQ hkl he hr0 hK (hφ x hx)
      (hβ x hx) (hφβ x hx) (hFeq x hx)
    have : √2 * ‖η x‖ / 2 ≤ √2 * H / 2 := by gcongr; exact hη x hx
    nlinarith [mul_nonneg hC₀ hK]
  -- The bound of the Hermitian part by the defect density.
  have hB : ∀ x ∈ ball c R, ∀ v, F x ![v, J v] ≤
      ((1 + C / √r) * (r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|) + ((1 + C) * K + √2 * H / 2 + C)) *
        ‖v‖ ^ 2 := by
    intro x hx v
    refine (apply_apply_le_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hr (hφ x hx) (hβ x hx) (hβK x hx)
      (hFeq x hx) hC₀ (hFm x hx) v).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    have : √2 * ‖η x‖ / 2 ≤ √2 * H / 2 := by gcongr; exact hη x hx
    linarith
  have hδ : ContinuousOn (fun x ↦ r / 4 * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2|) (ball c R) :=
    continuousOn_const.mul ((continuousOn_const.sub (hφc.norm.pow 2)).sub (hβc.norm.pow 2)).abs
  rw [defectMeasure_def]
  exact measure_closedBall_le_mul_deriv_add (μ := μ) h₀ h₂₃ hF hdF hδ
    (fun x _ ↦ by positivity) hω
    (fun x hx ↦ hB x (sphere_subset_closedBall.trans (closedBall_subset_ball hσ.2) hx)) hσ

/-- **Quadratic lower bound for the defect energy at zeros of `α`.** Fix constants
`K, C, H ≥ 0` and a radius `R > 0`. There are constants `c₀, c, ρ₀ > 0` with the following
property. Let `r ≥ 1` with `r ≥ 8 K`. On the ball `ball x₀ R` let `F` be a closed `C¹` two-form
field, let `φ`, `β` be continuous fields of positive half-spinors in the canonical line of `J` and
in its complement, and let `α` be a differentiable function with `|α| = |φ|` (the coefficient of
`φ = α u₀`), whose covariant derivative for the connection form `b` is `∇_a α`. Suppose that on
the ball the curvature equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` holds, with Taubes's
coarse bounds `|φ|² + |β|² ≤ 1 + K / r`, `|β|² ≤ (K / r) w₊ + K / r²`,
`|∇_a α|² ≤ K r w₊ + K` and `‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where
`w₊ = max (1 - |φ|²) 0` and `F⁻ = (F - ⋆F) / 2`, and the forcing bound `‖η‖ ≤ H`. If `α x₀ = 0`,
then the defect energy `ν = δ dμ`, `δ = (r / 4) |1 - |φ|² - |β|²|`, satisfies `ν(B_σ) ≥ c σ²` for
every `c₀ / √r ≤ σ ≤ ρ₀`. -/
theorem exists_forall_ofReal_mul_sq_le_measure_closedBall_of_add_hodgeStar_eq {K C H R : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H) (hR : 0 < R) :
    ∃ c₀ > 0, ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → 8 * K ≤ r →
      ∀ (F : E → E [⋀^Fin 2]→L[ℝ] ℝ) (φ β : E → positiveHalfSpinors o ρ) (α : E → ℂ)
        (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (η : E → ⋀[ℝ]^2 E) (x₀ : E),
      (∀ x ∈ ball x₀ R, ContDiffAt ℝ 1 F x) → (∀ x ∈ ball x₀ R, extDeriv F x = 0) →
      ContinuousOn φ (ball x₀ R) → ContinuousOn β (ball x₀ R) →
      (∀ x ∈ ball x₀ R, DifferentiableAt ℝ α x) → (∀ x ∈ ball x₀ R, ‖φ x‖ = ‖α x‖) →
      (∀ x ∈ ball x₀ R, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ ball x₀ R, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ ball x₀ R, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ ball x₀ R, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ ball x₀ R, ‖covariantDeriv b α x‖ ^ 2 ≤ K * r * max (1 - ‖φ x‖ ^ 2) 0 + K) →
      (∀ x ∈ ball x₀ R, ‖η x‖ ≤ H) →
      (∀ x ∈ ball x₀ R, (alternatingFormEquiv E 2).symm (F x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ ball x₀ R, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (F x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      α x₀ = 0 →
      ∀ σ, c₀ / √r ≤ σ → σ ≤ ρ₀ →
        ENNReal.ofReal (c * σ ^ 2) ≤ defectMeasure μ r φ β (closedBall x₀ σ) := by
  obtain ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_withDensity_closedBall_of_eq_zero (G := positiveHalfSpinors o ρ)
      (F := positiveHalfSpinors o ρ) (μ := μ) Fact.out hK le_rfl hC
      (K' := ((1 + C) * K + √2 * H / 2 + C) * (μ.toSphere.real univ / 2 + μ.real (ball (0 : E) 1)))
      (by positivity) hR
  refine ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, fun r hr hrK F φ β α b η x₀ hF hdF hφc hβc hα hφα hφ hβ
    hφβ hβK hgrad hη hFeq hFm hα₀ ↦ ?_⟩
  rw [defectMeasure_def]
  refine hdens r hr hrK φ β α b x₀ hφc hβc hα hφα hφβ hβK hgrad (fun s hs ↦ ?_) hα₀
  -- Taubes's monotonicity inequality holds at every radius below `R`.
  rw [← defectMeasure_def μ r φ β, zero_mul, add_zero, mul_one]
  exact (measure_closedBall_le_mul_deriv_add_of_add_hodgeStar_eq (μ := μ) h₀ h₂₃ hQ hkl he hr hK
    hC hF hdF hφc hβc hφ hβ hφβ hβK hη hFeq hFm hs).trans_eq (by ring)

/-- **Covering the zeros of `α`.** Fix constants `K, C, H ≥ 0` and a radius `R > 0`. There are
constants `c₀, c, ρ₀ > 0` with the following property. Let `r ≥ 1` with `r ≥ 8 K`, and let the
fields `F`, `φ`, `β`, `α`, `b`, `η` satisfy the hypotheses of
`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_add_hodgeStar_eq` on a
set `U`. Let `Z` be a set of zeros of `α` with `ball x R ⊆ U` for every `x ∈ Z`. Then for every
`σ > 0` with `σ ≤ 2 ρ₀`, as soon as `r ≥ (2 c₀ / σ)²`, the set `Z` is covered by at most
`4 ν(Z_{σ/2}) / (c σ²)` closed balls of radius `σ` centred in `Z`, where `ν = δ dμ` is the defect
energy, `δ = (r / 4) |1 - |φ|² - |β|²|`, and `Z_{σ/2}` is the closed `σ / 2`-thickening of `Z`. -/
theorem exists_forall_coveringNumber_le_of_add_hodgeStar_eq {K C H R : ℝ} (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hR : 0 < R) :
    ∃ c₀ > 0, ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → 8 * K ≤ r →
      ∀ (F : E → E [⋀^Fin 2]→L[ℝ] ℝ) (φ β : E → positiveHalfSpinors o ρ) (α : E → ℂ)
        (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (η : E → ⋀[ℝ]^2 E) (U Z : Set E),
      (∀ x ∈ U, ContDiffAt ℝ 1 F x) → (∀ x ∈ U, extDeriv F x = 0) →
      ContinuousOn φ U → ContinuousOn β U →
      (∀ x ∈ U, DifferentiableAt ℝ α x) → (∀ x ∈ U, ‖φ x‖ = ‖α x‖) →
      (∀ x ∈ U, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ U, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ U, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) →
      (∀ x ∈ U, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ U, ‖covariantDeriv b α x‖ ^ 2 ≤ K * r * max (1 - ‖φ x‖ ^ 2) 0 + K) →
      (∀ x ∈ U, ‖η x‖ ≤ H) →
      (∀ x ∈ U, (alternatingFormEquiv E 2).symm (F x) +
        o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)) = (r / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 E) - η x) →
      (∀ x ∈ U, ‖(2⁻¹ : ℝ) • ((alternatingFormEquiv E 2).symm (F x) -
          o.hodgeStar hkl ((alternatingFormEquiv E 2).symm (F x)))‖ ≤
          r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      (∀ x ∈ Z, α x = 0 ∧ ball x R ⊆ U) →
      ∀ σ : ℝ≥0, σ ≠ 0 → (σ : ℝ) ≤ 2 * ρ₀ → (2 * c₀ / σ) ^ 2 ≤ r →
        (coveringNumber σ Z : ℝ≥0∞) ≤ ENNReal.ofReal (4 / (c * σ ^ 2)) *
          defectMeasure μ r φ β (cthickening (σ / 2) Z) := by
  obtain ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_measure_closedBall_of_add_hodgeStar_eq (μ := μ) (ρ := ρ) h₀ h₂₃
      hQ hkl he hK hC hH hR
  refine ⟨c₀, hc₀, c, hc, ρ₀, hρ₀, fun r hr hrK F φ β α b η U Z hF hdF hφc hβc hα hφα hφ hβ hφβ
    hβK hgrad hη hFeq hFm hZ σ hσ hσρ₀ hrσ ↦ ?_⟩
  refine TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le hc
    (fun x hx ↦ ?_) hσ hσρ₀ hrσ
  obtain ⟨hα₀, hU⟩ := hZ x hx
  exact hdens r hr hrK F φ β α b η x (fun y hy ↦ hF y (hU hy)) (fun y hy ↦ hdF y (hU hy))
    (hφc.mono hU) (hβc.mono hU) (fun y hy ↦ hα y (hU hy)) (fun y hy ↦ hφα y (hU hy))
    (fun y hy ↦ hφ y (hU hy)) (fun y hy ↦ hβ y (hU hy)) (fun y hy ↦ hφβ y (hU hy))
    (fun y hy ↦ hβK y (hU hy)) (fun y hy ↦ hgrad y (hU hy)) (fun y hy ↦ hη y (hU hy))
    (fun y hy ↦ hFeq y (hU hy)) (fun y hy ↦ hFm y (hU hy)) hα₀

end TauCeti.SeibergWitten
