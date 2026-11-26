/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Hamiltonian.RadialTwist
import TauCeti.Geometry.Symplectic.Capacity.Levels

/-!
# The `π₁`-sensitive capacity of a disc is at least its area

On the complex line with its standard area form (`TauCeti.stdComplexSymplecticForm`), the disc of
radius `r` has area `π r²`. This file proves the lower bound

`π r² ≤ c°_HZ(U; W)`

for every set `U` containing a disc of radius `r` and every set `W` in which contractibility is
tested (`TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`). In particular the disc `D` of radius
`r` has `π r² ≤ c°_HZ(D)`. The Hofer–Zehnder capacity of the disc is exactly `π r²`; the upper bound
rests on an existence theorem for periodic orbits and is not proved here.

The lower bound comes from the squared distance `F(w) = ‖w - p‖²`, the radial Hamiltonian
`-G(‖w - p‖²) / 2` of the profile `G(s) = -2 s` (`TauCeti.radialHamiltonian`). Its flow rotates
every circle about `p` at the angular speed `-2`, so a nonconstant orbit of period `T` needs
`2T ∈ 2πℤ`, and `T ≥ π` (`TauCeti.eq_of_periodic_radialHamiltonian`). This is independent of any
contractibility, so no level of `F` carries a closed characteristic of period less than `π`,
contractible in any `W`. The level-set lower bound
`TauCeti.SmoothTwoForm.IsNondegenerate.ofReal_mul_sub_le_contractibleHZCapacity` then gives
`τ (b - a) ≤ c°_HZ(U; W)` for every `τ < π` and `0 < a < b < r²`, and letting `τ → π`, `a → 0`
and `b → r²` gives `π r²`.

## Main results

* `TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`: a set containing a disc of radius `r` has
  `π₁`-sensitive capacity at least `π r²`, whatever set contractibility is tested in.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (radial Hamiltonians and the capacity of the ball).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 12.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1 and the remarks after it.
-/

public section

noncomputable section

open Complex Filter Function Metric Set Topology
open scoped ContDiff

namespace TauCeti

/-- On the complex line, the squared distance `‖w - p‖²` to `p` is the radial Hamiltonian of the
profile `s ↦ -2 s`, whose Hamiltonian flow turns every circle about `p` at the angular speed `-2`.
No level `‖w - p‖² = s` carries a closed characteristic of period at most `τ < π`, whatever set
contractibility is tested in: one period would turn the circle through an angle smaller than
`2π` in absolute value, so the orbit is constant. -/
private theorem not_hasContractibleClosedCharacteristicOfPeriodLE_radialHamiltonian (p : ℂ)
    (W : Set ℂ) (s : ℝ) {τ : ℝ} (hτ : τ < Real.pi) :
    ¬stdComplexSymplecticForm.constSmooth.HasContractibleClosedCharacteristicOfPeriodLE W
      (radialHamiltonian (fun s ↦ -2 * s) p) s τ := by
  have hG : Differentiable ℝ fun s : ℝ ↦ -2 * s := by fun_prop
  have hderiv (s : ℝ) : deriv (fun s : ℝ ↦ -2 * s) s = -2 := by simp
  -- The Hamiltonian vector field is the infinitesimal rotation `-2 i (w - p)`, which is Lipschitz.
  have hX : LipschitzWith 2
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian (fun s ↦ -2 * s) p)) :=
    LipschitzWith.of_dist_le_mul fun v w ↦ by
      rw [hamiltonianVectorField_radialHamiltonian (hG _),
        hamiltonianVectorField_radialHamiltonian (hG _), hderiv, hderiv, dist_eq_norm,
        dist_eq_norm, ← mul_sub, sub_sub_sub_cancel_right, norm_mul]
      simp
  rw [SmoothTwoForm.hasContractibleClosedCharacteristicOfPeriodLE_iff]
  rintro ⟨T, γ, hT, hTτ, hγ, hper, ⟨t, ht⟩, -⟩
  refine ht (eq_of_periodic_radialHamiltonian hX (fun s ↦ ?_) (hG _) hT.ne' hper ?_ t)
  · -- An integral curve of the Hamiltonian vector field solves Hamilton's equations.
    have h := hγ s
    rw [SymplecticForm.hamiltonianVectorField_constSmooth] at h
    exact hasDerivAt_iff_hasFDerivAt.2 (hasMFDerivAt_iff_hasFDerivAt.1 h)
  · rw [hderiv, abs_mul, abs_of_pos hT]
    norm_num
    linarith

/-- **The `π₁`-sensitive capacity of a disc is at least its area.** On the complex line with its
standard area form, a set `U` containing the disc of radius `r ≥ 0` about some point has
`c°_HZ(U; W) ≥ π r²`, whatever set `W` contractibility is tested in. In particular the disc `D` of
radius `r` has `c°_HZ(D) ≥ π r²`. -/
theorem ofReal_pi_mul_sq_le_contractibleHZCapacity {p : ℂ} {r : ℝ} (hr : 0 ≤ r) {W U : Set ℂ}
    (hU : ball p r ⊆ U) :
    ENNReal.ofReal (Real.pi * r ^ 2) ≤
      stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  set F := radialHamiltonian (fun s ↦ -2 * s) p
  have hF (w : ℂ) : F w = ‖w - p‖ ^ 2 := by
    simp only [F, radialHamiltonian_apply]
    ring
  have hFc : ContDiff ℝ ∞ F := contDiff_radialHamiltonian (by fun_prop) p
  have hball : ball p r ⊆ interior U := interior_maximal hU isOpen_ball
  -- For each `t ∈ (0, 1)`, the levels of `F` in `((1 - t) r² / 2, (1 + t) r² / 2)` carry no
  -- closed characteristic of period at most `π t`, giving the bound `π t · t r² = π t² r²`.
  have hle : ∀ᶠ t in 𝓝[<] (1 : ℝ), ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) ≤
      stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U := by
    filter_upwards [Ioo_mem_nhdsLT one_pos] with t ⟨ht₀, ht₁⟩
    have hR : 0 < r ^ 2 := by positivity
    have hb : (1 + t) * r ^ 2 / 2 < r ^ 2 := by nlinarith
    have hm : 0 ≤ ((1 + t) * r ^ 2 / 2 + r ^ 2) / 2 := by positivity
    convert (SymplecticForm.isNondegenerate_constSmooth stdComplexSymplecticForm)
      |>.ofReal_mul_sub_le_contractibleHZCapacity (τ := Real.pi * t) (W := W) hFc.contMDiff
        (a := (1 - t) * r ^ 2 / 2) (b := (1 + t) * r ^ 2 / 2) (by nlinarith)
        ((isCompact_closedBall p √((1 + t) * r ^ 2 / 2)).of_isClosed_subset
          (isClosed_le hFc.continuous continuous_const) fun w hw ↦ ?_)
        (fun w hw ↦ hball ?_) (by simp [ModelWithCorners.interior_eq_univ])
        ⟨p, by rw [hF, sub_self, norm_zero]; nlinarith⟩
        ⟨p + (√(((1 + t) * r ^ 2 / 2 + r ^ 2) / 2) : ℂ), hball ?_, ?_⟩
        fun s _ ↦ not_hasContractibleClosedCharacteristicOfPeriodLE_radialHamiltonian p W s
          (by nlinarith [Real.pi_pos]) using 2
    · ring
    · rw [mem_ofPred_eq, hF] at hw
      rw [mem_closedBall, dist_eq_norm]
      exact Real.le_sqrt_of_sq_le hw
    · rw [mem_ofPred_eq, hF] at hw
      rw [mem_ball, dist_eq_norm]
      nlinarith [norm_nonneg (w - p)]
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' hr]
      linarith
    · rw [hF, add_sub_cancel_left, norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hm]
      linarith
  refine le_of_tendsto ?_ hle
  have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds

end TauCeti
