/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature
public import TauCeti.Geometry.Euclidean.Volume.Polar
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.KahlerFlux

/-!
# Taubes's monotonicity inequality for the defect energy

# Taubes's monotonicity inequality for the defect energy

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `ψ = φ + β`, with `φ` in the canonical line and `β`
in its complement, and curvature `F = i F_a` of the connection on the twisting line. Its **defect
energy** on a ball is

`E(σ) = μ(closedBall x σ)`,  `μ = (r / 4) |1 - |φ|² - |β|²| dvol`.

This file derives Taubes's differential inequality

`E(σ) ≤ (σ / 2) (1 + C r^(-1/2)) E'(σ) + K σ⁴`  for almost every `σ ∈ (0, R)`

in a flat chart, from the curvature equation `F + ⋆F = (r / 4) ω - q(√r ψ) - η` and the coarse
bounds `|φ|² + |β|² ≤ 1 + C / r`, `|β|² ≤ (C / r) w₊ + C / r²` and
`|F⁻| ≤ (r / (4 √2)) (1 + C r^(-1/2)) w₊ + C`, `w₊ = max (1 - |φ|²) 0`, taken as hypotheses on the
ball `ball x R`. The constant `K` depends only on `C`, the bound `N` on the forcing `η` and the
volume of the unit ball; it is independent of `r`, `R`, the centre and the solution
(`TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`). This is the hypothesis of
the quadratic lower bound `E(σ) ≥ c σ²` at a zero of `φ` and of the covering bound for the zero set
(`TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`,
`TauCeti.exists_forall_coveringNumber_le_of_ae_le`), with no curvature correction `C σ` since the
chart is flat.

The argument is Taubes's. The flux identity for the `ω`-component of the closed form `F`
(`TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`) expresses
`∫_{ball x σ} ⟪ω, F⟫` as `(σ / 2)` times the integral over the sphere of `B(w, w)`, the Hermitian
part of `F` on a unit vector `w` orthogonal to the radial direction and its `J`-image. Two pointwise
consequences of the curvature equation and the coarse bounds then compare both sides with the
defect density:

* in the interior, `(r / 4) |1 - |φ|² - |β|²| ≤ ⟪ω, F⟫ + (√2 N + C) / 2`, because
  `⟪ω, F⟫ = (r / 4) (1 - |φ|² + |β|²) - ⟪ω, η⟫ / 2`
  (`TauCeti.SeibergWitten.mul_abs_one_sub_sub_le_inner_kahlerForm_add`);
* on the sphere, `B(w, w) ≤ ⟪ω, F⟫ / 2 + |F⁻| / √2`, the largest value of the Hermitian part, is at
  most `(1 + C r^(-1/2))` times the defect density up to a bounded error
  (`TauCeti.SeibergWitten.mul_inner_kahlerForm_sub_hermitianForm_le`).

The sphere integral of the defect density is the derivative `E'(σ)` for almost every `σ`
(`TauCeti.ae_hasDerivAt_setIntegral_ball`), and the Hausdorff measure of the sphere is the
derivative `4 |B₁| σ³` of the volume of the ball.

The fields are global in the chart: the curvature is `F = -db` for a `C²` connection form `b` on the
whole space, as in `TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent`, and `φ`, `β` are continuous.
Deriving the coarse bounds from the equations, and the curvature corrections `(1 + C σ)` on a curved
four-manifold, are not done here.

## Main results

* `TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`: the monotonicity
  inequality for the defect energy.
* `TauCeti.SeibergWitten.mul_abs_one_sub_sub_le_inner_kahlerForm_add`,
  `TauCeti.SeibergWitten.mul_inner_kahlerForm_sub_hermitianForm_le`: the two pointwise comparisons
  with the defect density.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open CliffordAlgebra Module Metric MeasureTheory Filter Set exteriorPower
open scoped RealInnerProductSpace Topology

namespace TauCeti.SeibergWitten

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

attribute [local instance] finiteDimensional_of_finrank_four

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  {r C N : ℝ} {F η : ⋀[ℝ]^2 V} {φ β : positiveHalfSpinors o ρ}

include h₀ h₂₃ hQ he

/-- At a solution of the large-parameter curvature equation the defect density
`(r / 4) |1 - |φ|² - |β|²|` is at most the `ω`-component `⟪ω, F⟫` of the curvature, up to a
bounded error. -/
theorem mul_abs_one_sub_sub_le_inner_kahlerForm_add (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    (hη : ‖η‖ ≤ N) (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + C / r) :
    r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| ≤ ⟪J.kahlerForm, F⟫ + (√2 * N + C) / 2 := by
  have hr0 : 0 < r := by linarith
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  have hc := inner_div_two_eq_of_add_hodgeStar_eq hQ hkl hω hω₂ hφ hβ hr0.le hF
  have hωη : ⟪J.kahlerForm, η⟫ ≤ √2 * N := by
    have hω' : ‖J.kahlerForm‖ = √2 := by rw [← hω₂, Real.sqrt_sq (norm_nonneg _)]
    calc ⟪J.kahlerForm, η⟫ ≤ ‖J.kahlerForm‖ * ‖η‖ := real_inner_le_norm _ _
      _ ≤ √2 * N := by rw [hω']; gcongr
  -- `r |1 - |φ|² - |β|²| ≤ r (1 - |φ|² + |β|²) + 2 C`, by cases on the sign.
  have hdef : r * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| ≤ r * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) + 2 * C := by
    have hCr : r * (C / r) = C := mul_div_cancel₀ C hr0.ne'
    rcases le_total 0 (1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2) with h | h
    · rw [abs_of_nonneg h]
      nlinarith [mul_nonneg hr0.le (sq_nonneg ‖β‖)]
    · rw [abs_of_nonpos h]
      nlinarith [mul_nonneg hr0.le (sq_nonneg ‖β‖)]
  linarith

/-- At a solution of the large-parameter curvature equation satisfying the coarse bounds, the
radial integrand `‖v‖² ⟪ω, F⟫ - B(v, v)` of the ball-sphere identity
`TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq` is at most `‖v‖²` times
`(1 + C / √r)` times the defect density `(r / 4) |1 - |φ|² - |β|²|`, up to a bounded error. -/
theorem mul_inner_kahlerForm_sub_hermitianForm_le (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    (hη : ‖η‖ ≤ N)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C)
    (hβK : ‖β‖ ^ 2 ≤ C / r * max (1 - ‖φ‖ ^ 2) 0 + C / r ^ 2) (v : V) :
    ‖v‖ ^ 2 * ⟪J.kahlerForm, F⟫ - J.hermitianForm F v v ≤
      ‖v‖ ^ 2 * ((1 + C / √r) * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) +
        ((1 + C) * C / 2 + C / 4 + √2 * N / 4 + C / √2)) := by
  have hr0 : 0 < r := by linarith
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  have hc := inner_div_two_eq_of_add_hodgeStar_eq hQ hkl hω hω₂ hφ hβ hr0.le hF
  have hωη : -⟪J.kahlerForm, η⟫ ≤ √2 * N := by
    have hω' : ‖J.kahlerForm‖ = √2 := by rw [← hω₂, Real.sqrt_sq (norm_nonneg _)]
    calc -⟪J.kahlerForm, η⟫ ≤ ‖J.kahlerForm‖ * ‖η‖ := by
          rw [← inner_neg_right]
          exact (real_inner_le_norm _ _).trans_eq (by rw [norm_neg])
      _ ≤ √2 * N := by rw [hω']; gcongr
  have hB := AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le h₀ h₂₃ hkl he F v
  set m := ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖
  set a := ‖φ‖ ^ 2
  set bb := ‖β‖ ^ 2
  set w := max (1 - a) 0
  set δ := C / √r
  have ha : 0 ≤ a := sq_nonneg _
  have hb0 : 0 ≤ bb := sq_nonneg _
  have hw0 : 0 ≤ w := le_max_right _ _
  have hw1 : w ≤ 1 := max_le (by linarith) zero_le_one
  have h1a : 1 - a ≤ w := le_max_left _ _
  have hs1 : 1 ≤ √r := Real.one_le_sqrt.2 hr
  have hδ0 : 0 ≤ δ := by positivity
  have hδC : δ ≤ C := div_le_self hC hs1
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hs2p : 0 < √2 := by positivity
  -- The coarse bound on `β`: `r |β|² ≤ C w + C / r ≤ 2 C`.
  have hrb : r * bb ≤ 2 * C := by
    have h := mul_le_mul_of_nonneg_left hβK hr0.le
    have e1 : r * (C / r * w + C / r ^ 2) = C * w + C / r := by field_simp
    have hCr : C / r ≤ C := div_le_self hC hr
    nlinarith
  -- The vacuum defect `w` is controlled by the defect density and `|β|²`.
  have hwd : w ≤ |1 - a - bb| + bb := by
    rcases le_total (1 - a) 0 with h | h
    · have hw : w = 0 := max_eq_right h
      rw [hw]; positivity
    · have hw : w = 1 - a := max_eq_left h
      rw [hw]; linarith [le_abs_self (1 - a - bb)]
  -- The anti-self-dual bound divided by `√2`.
  have hm : m / √2 ≤ r / 8 * (1 + δ) * w + C / √2 := by
    rw [div_le_iff₀ hs2p]
    have : r / 8 * (1 + δ) * w * √2 = r / (4 * √2) * (1 + δ) * w := by
      field_simp
      rw [Real.sq_sqrt zero_le_two]
      ring
    rw [add_mul, this, div_mul_cancel₀ _ hs2p.ne']
    exact hFm
  have hmain : ⟪J.kahlerForm, F⟫ / 2 + m / √2 ≤
      (1 + δ) * (r / 4 * |1 - a - bb|) + ((1 + C) * C / 2 + C / 4 + √2 * N / 4 + C / √2) := by
    have hd : r / 4 * w ≤ r / 4 * |1 - a - bb| + C / 2 := by
      have := mul_le_mul_of_nonneg_left hwd (by positivity : (0 : ℝ) ≤ r / 4)
      linarith
    have hA : r / 8 * (1 - a + bb) ≤ r / 8 * w + C / 4 := by
      have := mul_le_mul_of_nonneg_left h1a (by positivity : (0 : ℝ) ≤ r / 8)
      linarith
    have hδw : 0 ≤ r / 8 * δ * w := by positivity
    have hδd : δ * (C / 2) ≤ C * (C / 2) := mul_le_mul_of_nonneg_right hδC (by positivity)
    have hdd : (1 + δ) * (r / 4 * w) ≤ (1 + δ) * (r / 4 * |1 - a - bb| + C / 2) :=
      mul_le_mul_of_nonneg_left hd (by linarith)
    have e1 : r / 8 * (1 + δ) * w = r / 8 * w + r / 8 * δ * w := by ring
    have e2 : (1 + δ) * (r / 4 * w) = 2 * (r / 8 * w) + 2 * (r / 8 * δ * w) := by ring
    have e3 : (1 + δ) * (r / 4 * |1 - a - bb| + C / 2) =
        (1 + δ) * (r / 4 * |1 - a - bb|) + C / 2 + δ * (C / 2) := by ring
    have e4 : (1 + C) * C / 2 = C / 2 + C * (C / 2) := by ring
    linarith
  have hv := sq_nonneg ‖v‖
  have hBle : ‖v‖ ^ 2 * ⟪J.kahlerForm, F⟫ - J.hermitianForm F v v ≤
      ‖v‖ ^ 2 * (⟪J.kahlerForm, F⟫ / 2 + m / √2) := by
    have h := (abs_le.1 hB).1
    have e : ‖v‖ ^ 2 * (⟪J.kahlerForm, F⟫ / 2 + m / √2) =
        ‖v‖ ^ 2 * ⟪J.kahlerForm, F⟫ - ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 + m / √2 * ‖v‖ ^ 2 := by ring
    rw [e]
    linarith
  exact hBle.trans (mul_le_mul_of_nonneg_left hmain hv)

end Pointwise

section Integrated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  [MeasurableSpace V] [BorelSpace V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

attribute [local instance] finiteDimensional_of_finrank_four

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

include h₀ h₂₃ hQ he

/-- **Taubes's monotonicity inequality for the defect energy**, in a flat chart. Work in an
oriented four-dimensional inner product space with a constant unitary frame `e`, `J e₀ = e₁`,
`J e₂ = e₃`, and Kähler two-vector `ω`. Fix constants `C, N ≥ 0`. There is `K ≥ 0` such that for
every `r ≥ 1`, every ball `ball x R` and every solution on it of the large-parameter curvature
equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`, with `φ` in the canonical line and `β` in its
complement, `|η| ≤ N` and the coarse bounds `|φ|² + |β|² ≤ 1 + C / r`,
`|β|² ≤ (C / r) w₊ + C / r²` and `|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where
`w₊ = max (1 - |φ|²) 0`, the defect energy `E(σ) = μ(closedBall x σ)` of
`μ = (r / 4) |1 - |φ|² - |β|²| dvol` satisfies

`E(σ) ≤ (σ / 2) (1 + C / √r) E'(σ) + K σ⁴`

for almost every `σ ∈ (0, R)`. Here `F` is the curvature `i F_a = -db` of a `C²` connection form
`b`, read as a two-vector, and `φ`, `β` are continuous. -/
theorem exists_ae_measure_closedBall_le_mul_deriv_add {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) :
    ∃ K, 0 ≤ K ∧ ∀ ⦃r : ℝ⦄ ⦃b : V → V [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃F η : V → ⋀[ℝ]^2 V⦄
      ⦃φ β : V → positiveHalfSpinors o ρ⦄ ⦃x : V⦄ ⦃R : ℝ⦄, 1 ≤ r → ContDiff ℝ 2 b →
      (∀ y, alternatingFormEquiv V 2 (F y) = -extDeriv b y) → Continuous φ → Continuous β →
      (∀ y ∈ ball x R, cliffordProjection o ρ J.kahlerForm (φ y) = φ y) →
      (∀ y ∈ ball x R, cliffordProjection o ρ J.kahlerForm (β y) = 0) →
      (∀ y ∈ ball x R, F y + o.hodgeStar hkl (F y) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ y + β y)) : ⋀[ℝ]^2 V) - η y) →
      (∀ y ∈ ball x R, ‖η y‖ ≤ N) →
      (∀ y ∈ ball x R, ‖(2⁻¹ : ℝ) • (F y - o.hodgeStar hkl (F y))‖ ≤
        r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ y‖ ^ 2) 0 + C) →
      (∀ y ∈ ball x R, ‖φ y‖ ^ 2 + ‖β y‖ ^ 2 ≤ 1 + C / r) →
      (∀ y ∈ ball x R, ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖φ y‖ ^ 2) 0 + C / r ^ 2) →
      ∀ᵐ σ, σ ∈ Ioo 0 R →
        ((volume : Measure V).withDensity (fun y ↦ ENNReal.ofReal
            (r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|)) (closedBall x σ)).toReal ≤
          σ / 2 * (1 + C / √r) * deriv (fun σ ↦ ((volume : Measure V).withDensity
            (fun y ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|))
              (closedBall x σ)).toReal) σ + K * σ ^ 4 := by
  set N₁ := (√2 * N + C) / 2
  set K₂ := (1 + C) * C / 2 + C / 4 + √2 * N / 4 + C / √2
  set V₁ := (volume : Measure V).real (ball 0 1)
  have hN₁ : 0 ≤ N₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨V₁ * (N₁ + 2 * K₂), by positivity, ?_⟩
  intro r b F η φ β x R hr hb hF hφc hβc hφ hβ hFeq hη hFm hφβ hβK
  -- Writing `E(σ) = ∫_{ball x σ} d` for the defect density `d`, the flux identity gives
  -- `∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} Q` for almost every `σ`. The interior bound
  -- `d ≤ ⟪ω, F⟫ + N₁` and the sphere bound `Q ≤ σ² ((1 + δ) d + K₂)` combine with
  -- `∫_{sphere x σ} d = E'(σ)` and `μH(sphere x σ) = 4 V₁ σ³` at almost every radius.
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  set δ := C / √r
  set d : V → ℝ := fun y ↦ r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2| with hddef
  have hdc : Continuous d :=
    continuous_const.mul ((continuous_const.sub (hφc.norm.pow 2)).sub (hβc.norm.pow 2)).abs
  have hd0 (y : V) : 0 ≤ d y := by positivity
  have hFc : Continuous F :=
    AlmostComplexStructure.continuous_of_alternatingFormEquiv_eq_neg_extDeriv hb hF
  set g : V → ℝ := fun y ↦ ⟪J.kahlerForm, F y⟫ with hgdef
  have hg : Continuous g := continuous_const.inner hFc
  set Qf : V → ℝ := fun y ↦ ‖y - x‖ ^ 2 * g y - J.hermitianForm (F y) (y - x) (y - x)
    with hQdef
  have hQc : Continuous Qf :=
    (((continuous_id.sub continuous_const).norm.pow 2).mul hg).sub
      (AlmostComplexStructure.continuous_hermitianForm_apply_sub_apply_sub hFc x)
  -- The defect energy of a ball is the integral of the density over the open ball.
  have hE : (fun s ↦ ((volume : Measure V).withDensity
      (fun y ↦ ENNReal.ofReal (d y)) (closedBall x s)).toReal) =
      fun s ↦ ∫ y in ball x s, d y := by
    funext s
    have hae : closedBall x s =ᵐ[volume] ball x s := by
      refine ae_eq_set.2 ⟨?_, by simp [sdiff_eq_empty.2 ball_subset_closedBall]⟩
      exact measure_mono_null (by rw [closedBall_sdiff_ball])
        (Measure.addHaar_sphere volume x s)
    have hdi : IntegrableOn d (ball x s) :=
      (hdc.continuousOn.integrableOn_compact (isCompact_closedBall x s)).mono_set
        ball_subset_closedBall
    rw [withDensity_apply _ measurableSet_closedBall, setLIntegral_congr hae,
      ← ofReal_integral_eq_lintegral_ofReal hdi (Eventually.of_forall hd0),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_ball fun y _ ↦ hd0 y)]
  -- The two pointwise bounds on the ball.
  have hint (y : V) (hy : y ∈ ball x R) : d y ≤ g y + N₁ :=
    mul_abs_one_sub_sub_le_inner_kahlerForm_add h₀ h₂₃ hQ hkl he hr hC (hφ y hy) (hβ y hy)
      (hFeq y hy) (hη y hy) (hφβ y hy)
  have hbd (y : V) (hy : y ∈ ball x R) : Qf y ≤ ‖y - x‖ ^ 2 * ((1 + δ) * d y + K₂) :=
    mul_inner_kahlerForm_sub_hermitianForm_le h₀ h₂₃ hQ hkl he hr hC (hφ y hy) (hβ y hy)
      (hFeq y hy) (hη y hy) (hFm y hy) (hβK y hy) (y - x)
  -- Integrability on almost every sphere.
  have hsph {f : V → ℝ} (hf : Continuous f) :
      ∀ᵐ σ, σ ∈ Ioo 0 R → IntegrableOn f (sphere x σ) μHE[finrank ℝ V - 1] := by
    have hfi : Integrable ((ball x R).indicator f) :=
      (integrable_indicator_iff measurableSet_ball).2
        ((hf.continuousOn.integrableOn_compact (isCompact_closedBall x R)).mono_set
          ball_subset_closedBall)
    have h := ae_integrableOn_sphere x hfi
    rw [ae_restrict_iff' measurableSet_Ioi] at h
    filter_upwards [h] with σ hσ hσR
    refine (hσ hσR.1).congr_fun (fun y hy ↦ indicator_of_mem ?_ f)
      isClosed_sphere.measurableSet
    rw [mem_sphere] at hy
    rw [mem_ball, hy]
    exact hσR.2
  have hvol (ρ : ℝ) (hρ : 0 ≤ ρ) : ∫ _ in ball x ρ, (1 : ℝ) = V₁ * ρ ^ 4 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.addHaar_ball _ _ hρ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      (Fact.out : finrank ℝ V = 4)]
    simp only [V₁, measureReal_def]
    ring
  filter_upwards [AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq h₀ h₂₃ hkl he
      hb hF x, ae_hasDerivAt_setIntegral_ball x hdc.locallyIntegrable,
    ae_hasDerivAt_setIntegral_ball x (f := fun _ : V ↦ (1 : ℝ)) (locallyIntegrable_const 1),
    hsph hQc, hsph hdc, hsph (continuous_const (y := (1 : ℝ)))] with σ h1 h2 h3 hQs hds h1s hσ
  obtain ⟨hσ0, hσR⟩ := hσ
  replace hQs := hQs ⟨hσ0, hσR⟩
  replace hds := hds ⟨hσ0, hσR⟩
  replace h1s := h1s ⟨hσ0, hσR⟩
  have h1' : ∫ y in ball x σ, g y =
      (2 * σ)⁻¹ * ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1] := h1 hσ0
  rw [hE, h2.deriv]
  have hS1 : ∫ _ in sphere x σ, (1 : ℝ) ∂μHE[finrank ℝ V - 1] = V₁ * (4 * σ ^ 3) := by
    have h' : HasDerivAt (fun ρ ↦ ∫ _ in ball x ρ, (1 : ℝ)) (V₁ * (4 * σ ^ 3)) σ := by
      have h4 : HasDerivAt (fun ρ ↦ V₁ * ρ ^ 4) (V₁ * (4 * σ ^ 3)) σ := by
        simpa using (hasDerivAt_pow 4 σ).const_mul V₁
      refine h4.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hσ0] with ρ hρ using hvol ρ hρ.le
    exact h3.unique h'
  have hsub : ball x σ ⊆ ball x R := ball_subset_ball hσR.le
  -- The defect energy of the ball is at most the `ω`-component of the curvature, plus an error.
  have hball : ∫ y in ball x σ, d y ≤ (∫ y in ball x σ, g y) + N₁ * (V₁ * σ ^ 4) := by
    have hdi : IntegrableOn d (ball x σ) :=
      (hdc.continuousOn.integrableOn_compact (isCompact_closedBall x σ)).mono_set
        ball_subset_closedBall
    have hgi : IntegrableOn g (ball x σ) :=
      (hg.continuousOn.integrableOn_compact (isCompact_closedBall x σ)).mono_set
        ball_subset_closedBall
    have h1i : IntegrableOn (fun _ ↦ (1 : ℝ)) (ball x σ) :=
      (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall x σ)).mono_set
        ball_subset_closedBall
    calc ∫ y in ball x σ, d y ≤ ∫ y in ball x σ, (g y + N₁ * 1) :=
          setIntegral_mono_on hdi (hgi.add (h1i.const_mul N₁)) measurableSet_ball
            fun y hy ↦ by simpa using hint y (hsub hy)
      _ = (∫ y in ball x σ, g y) + N₁ * (V₁ * σ ^ 4) := by
          rw [integral_add hgi (h1i.const_mul N₁), integral_const_mul, hvol σ hσ0.le]
  -- The flux through the sphere is controlled by the derivative of the defect energy.
  have hsphere : ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1] ≤
      σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
        K₂ * (V₁ * (4 * σ ^ 3))) := by
    have hki : IntegrableOn (fun y ↦ σ ^ 2 * ((1 + δ) * d y + K₂ * 1)) (sphere x σ)
        μHE[finrank ℝ V - 1] :=
      ((hds.const_mul (1 + δ)).add (h1s.const_mul K₂)).const_mul (σ ^ 2)
    calc ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1]
        ≤ ∫ y in sphere x σ, σ ^ 2 * ((1 + δ) * d y + K₂ * 1) ∂μHE[finrank ℝ V - 1] :=
          setIntegral_mono_on hQs hki isClosed_sphere.measurableSet fun y hy ↦ by
            have hyR : y ∈ ball x R := by
              rw [mem_sphere] at hy
              rw [mem_ball, hy]
              exact hσR
            have h := hbd y hyR
            rw [mem_sphere, dist_eq_norm] at hy
            rw [hy] at h
            simpa using h
      _ = σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
            K₂ * (V₁ * (4 * σ ^ 3))) := by
          rw [integral_const_mul, integral_add (hds.const_mul (1 + δ)) (h1s.const_mul K₂),
            integral_const_mul (1 + δ), integral_const_mul K₂, hS1]
  rw [h1'] at hball
  have hmul := mul_le_mul_of_nonneg_left hsphere (by positivity : (0 : ℝ) ≤ (2 * σ)⁻¹)
  have e1 : (2 * σ)⁻¹ * (σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
      K₂ * (V₁ * (4 * σ ^ 3)))) = σ / 2 * (1 + δ) *
        ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] + 2 * K₂ * V₁ * σ ^ 4 := by
    field_simp
    ring
  rw [e1] at hmul
  have hEσ : ((volume : Measure V).withDensity (fun y ↦ ENNReal.ofReal
      (r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|)) (closedBall x σ)).toReal =
      ∫ y in ball x σ, d y := congrFun hE σ
  rw [hEσ]
  linarith

end Integrated

end TauCeti.SeibergWitten
