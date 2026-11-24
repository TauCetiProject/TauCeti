/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
public import TauCeti.Geometry.Symplectic.Floer.Pregluing.EndChart

/-!
# Pre-gluing a Floer cylinder to the end of a PSS plane

Let `u` be a map on a PSS plane `ℂ`, in the real coordinates `ℝ × ℝ ≃ ℂ`. Its Floer end at `∞`
is read in the end lift `φ(s, t) = exp (2π (s + i t))` of the positive plane
(`TauCeti.Floer.PSSPlane.cylindricalEndLift`), in which the end is the half-cylinder `s > 0`. This
chart serves both planes: the end lift of the negative plane is `φ` composed with `z ↦ -z`
(`TauCeti.Floer.PSSPlane.cylindricalEndLift_negative`), and in `φ` the datum of the negative plane
for a Hamiltonian `H` is the datum of the positive plane for `-H(-t)`
(`TauCeti.Floer.PSSPlane.perturbation_negative`). The end coordinates of a point `w ≠ 0` in `φ`
are `(log ‖w‖ / 2π, arg w / 2π)`, the real and imaginary parts of the end coordinate
`TauCeti.Floer.PSSPlane.endCoord` of the positive plane, and `φ` recovers the point from them
(`TauCeti.Floer.PSSPlane.realChart_positive_endCoord`).

From `s = 2` on, a PSS plane solving the Floer equation is a Floer half-cylinder `U = u ∘ φ` for
the cylindrical datum `H(t) dt`
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive`),
converging to a one-periodic orbit `x` as `s → ∞`. The boundary of the one-dimensional moduli
spaces of PSS planes, such as those whose count is the unit of the pair-of-pants product, consists
of planes broken at their end: a plane `u` together with a Floer cylinder `v`, read in the same
coordinates, whose loops converge to `x` as `s → -∞`. For the negative plane, whose end is an
output, `(s, t) ↦ v(-s, -t)` is then a Floer cylinder for `H` whose input is the output of the
plane.

The first step of gluing such a pair is the *pre-glued plane*
(`TauCeti.Floer.PSSPlane.preglueEnd x u v R`), the pre-glued map
`TauCeti.Floer.preglueEndChart` of `TauCeti.Geometry.Symplectic.Floer.Pregluing.EndChart` for the
end chart `φ` (`TauCeti.Floer.PSSPlane.isEndChart_realChart_positive`). Up to the height `R - 1`
of the end it is `u`; further out it is the pre-glued map `TauCeti.Floer.preglue x U v R` of
`TauCeti.Geometry.Symplectic.Floer.Pregluing`, moved out along the end by `R`. It interpolates
through the orbit `x` on the neck `R - 1 ≤ s ≤ R + 1` and is the translate `v(s - 2R, t)` beyond
`R + 1`, so its end is the other end of the cylinder `v`.

* **Away from the neck it is `u`.** At a point of height at most `R - 1` the pre-glued plane is `u`
  (`TauCeti.Floer.PSSPlane.preglueEnd_of_le`), and near a point of height less than `R - 1`,
  including the pole `0` of the plane when `R > 1`, it agrees with `u`
  (`TauCeti.Floer.PSSPlane.preglueEnd_eventuallyEq_of_lt`). So it solves the Floer equation there
  if `u` does, the Morse incidence condition at the pole included.
* **In the end chart it is the translated pre-glued cylinder.** If `x` and `v` have period one in
  `t` and `R ≥ 1`, the pre-glued plane read in `φ` is `y ↦ preglue x U v R (y - (R, 0))`
  (`TauCeti.Floer.PSSPlane.preglueEnd_comp_realChart`); beyond the height `R + 1` it is
  `v(s - 2R, t)` (`TauCeti.Floer.PSSPlane.preglueEnd_realChart_of_add_one_le`).
* **It is smooth.** For `R ≥ 1` the pre-glued plane of `Cⁿ` data is `Cⁿ` on the whole plane, at
  the pole included (`TauCeti.Floer.PSSPlane.contDiff_preglueEnd`).
* **The pre-gluing error is exponentially small.** If `U` converges to `x` in `C¹` at an
  exponential rate `κ` and solves the cylindrical Floer equation beyond a height `T`, and `v`
  converges to `x` at the same rate at `-∞` and solves the Floer equation, then for every large
  `R` the Floer operator of the pre-glued plane in the end chart is at most `C' e^{-κ R}` beyond
  the height `T`
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEnd_comp_realChart_le`).
* **It converges to the broken plane.** As `R → ∞`, the pre-glued planes are eventually `u` on
  every compact subset of the plane (`TauCeti.Floer.PSSPlane.eventually_eqOn_preglueEnd`), and
  read in the end chart translated by `2R`, they are eventually `v` on every compact subset of the
  cylinder (`TauCeti.Floer.PSSPlane.eventually_preglueEnd_realChart_add_eq`).

The hypotheses on `U` are what the asymptotic analysis of the end supplies for a finite-energy PSS
plane with a nondegenerate asymptotic orbit and an almost complex structure cylindrical on its
end. The Sobolev setting, the right inverse of the linearized operator and the Newton iteration
that corrects the pre-glued plane to a solution are not treated here.

## Main definitions

* `TauCeti.Floer.PSSPlane.preglueEnd x u v R`: the pre-glued plane of `u` and of the Floer
  cylinder `v` at the end of a PSS plane, with gluing parameter `R`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  gluing of Floer cylinders to the ends of the PSS planes.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the pre-gluing construction and its error estimate.
-/

public section

open Filter Set Topology Function ContinuousLinearMap Real
open TauCeti.Complex (realChart contDiff_realChart)

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Floer.PSSPlane

/-! ### The pre-glued plane -/

/-- The end lift of the positive plane is a cylindrical end chart, with the end coordinates
`(log ‖w‖ / 2π, arg w / 2π)` of a point `w`. -/
theorem isEndChart_realChart_positive :
    IsEndChart (realChart positive.cylindricalEndLift) fun z ↦
      ((positive.endCoord (Complex.equivRealProdCLM.symm z)).re,
        (positive.endCoord (Complex.equivRealProdCLM.symm z)).im) where
  chart_endCoord _ h₀ := realChart_positive_endCoord fun h ↦ by simp [h] at h₀
  exists_endCoord_chart y := exists_endCoord_realChart_positive y.1 y.2
  chart_add_one := realChart_positive_add_one

/-- **The pre-glued plane** of a map `u` on a PSS plane and a map `v` on the cylinder, through the
loop `x`, with gluing parameter `R`: the pre-glued map `TauCeti.Floer.preglueEndChart` of the end
lift `φ` of the positive plane. At a point whose end coordinates `(s, t)` in `φ` have `s > 0` it is
the pre-glued map `preglue x (u ∘ φ) v R` at `(s - R, t)`; elsewhere it is `u`. It is `u` where
`s ≤ R - 1` (`TauCeti.Floer.PSSPlane.preglueEnd_of_le`), and `v(s - 2R, t)` where `s ≥ R + 1` when
`R ≥ 0` and `x` and `v` have period one in `t`
(`TauCeti.Floer.PSSPlane.preglueEnd_realChart_of_add_one_le`). -/
noncomputable def preglueEnd (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) : V :=
  preglueEndChart (realChart positive.cylindricalEndLift)
    (fun z ↦ ((positive.endCoord (Complex.equivRealProdCLM.symm z)).re,
      (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)) x u v R z

theorem preglueEnd_def (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) :
    preglueEnd x u v R z =
      if 0 < (positive.endCoord (Complex.equivRealProdCLM.symm z)).re then
        preglue x (u ∘ realChart positive.cylindricalEndLift) v R
          ((positive.endCoord (Complex.equivRealProdCLM.symm z)).re - R,
            (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
      else u z := by
  rw [preglueEnd, preglueEndChart_def]

variable {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ}

/-- **Away from the neck the pre-glued plane is `u`.** At a point of height at most `R - 1` in the
end lift, the pre-glued plane is `u`. -/
theorem preglueEnd_of_le (h : (positive.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ R - 1) :
    preglueEnd x u v R z = u z :=
  preglueEndChart_of_le isEndChart_realChart_positive h

/-- **Near the pole the pre-glued plane is `u`.** For `R ≥ 1` the pre-glued plane agrees with `u`
near the pole `0`, since the height `log ‖w‖ / 2π` is at most `0` on the unit disc; so it satisfies
whatever incidence condition `u` satisfies at the pole. -/
theorem preglueEnd_eventuallyEq_nhds_zero (hR : 1 ≤ R) : preglueEnd x u v R =ᶠ[𝓝 0] u := by
  have hc : ContinuousAt (fun w : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm w‖) 0 := by fun_prop
  have h₁ : ‖Complex.equivRealProdCLM.symm (0 : ℝ × ℝ)‖ < 1 := by simp
  filter_upwards [hc.eventually_lt continuousAt_const h₁] with w hw
  refine preglueEnd_of_le ?_
  rw [re_endCoord, endSign_positive]
  have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    (Real.log_nonpos (norm_nonneg (Complex.equivRealProdCLM.symm w)) hw.le)
  linarith

/-- Near a point of height less than `R - 1` in the end lift, the pre-glued plane agrees with `u`.
At the pole `0`, whose height is `0`, this needs `R > 1`. -/
theorem preglueEnd_eventuallyEq_of_lt
    (h : (positive.endCoord (Complex.equivRealProdCLM.symm z)).re < R - 1) :
    preglueEnd x u v R =ᶠ[𝓝 z] u := by
  by_cases hz : Complex.equivRealProdCLM.symm z = 0
  · obtain rfl : z = 0 := by simpa using hz
    rw [hz, endCoord_zero, Complex.zero_re] at h
    exact preglueEnd_eventuallyEq_nhds_zero (by linarith)
  · exact preglueEndChart_eventuallyEq_of_lt isEndChart_realChart_positive
      ((positive.contDiffAt_re_endCoord hz (n := 0)).continuousAt.comp
        Complex.equivRealProdCLM.symm.continuous.continuousAt) h

/-- **The pre-glued plane on the end.** At the image under the end lift of a point `(s, t)` with
`s > 0`, the pre-glued plane is the pre-glued map at `(s - R, t)`, when the loop `x` and the map
`v` have period one in `t`. -/
theorem preglueEnd_realChart (hx : Periodic x 1) (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    preglueEnd x u v R (realChart positive.cylindricalEndLift (s, t)) =
      preglue x (u ∘ realChart positive.cylindricalEndLift) v R (s - R, t) :=
  preglueEndChart_chart isEndChart_realChart_positive hx hv hs t

/-- **The pre-glued plane in the end chart.** If the loop `x` and the map `v` have period one in
`t` and `R ≥ 1`, the pre-glued plane read in the end lift `φ` of the positive plane is the
pre-glued map of `u ∘ φ` and `v`, translated by `R`. -/
theorem preglueEnd_comp_realChart (hx : Periodic x 1) (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hR : 1 ≤ R) :
    preglueEnd x u v R ∘ realChart positive.cylindricalEndLift =
      fun y ↦ preglue x (u ∘ realChart positive.cylindricalEndLift) v R (y - (R, 0)) :=
  preglueEndChart_comp_chart isEndChart_realChart_positive hx hv hR

/-- **Far out on the end the pre-glued plane is the cylinder.** If the loop `x` and the map `v`
have period one in `t` and `R ≥ 0`, then at the image under the end lift of a point `(s, t)` with
`s ≥ R + 1` the pre-glued plane is `v(s - 2R, t)`. -/
theorem preglueEnd_realChart_of_add_one_le (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 0 ≤ R) {s : ℝ} (hs : R + 1 ≤ s) (t : ℝ) :
    preglueEnd x u v R (realChart positive.cylindricalEndLift (s, t)) = v (s - 2 * R, t) :=
  preglueEndChart_chart_of_add_one_le isEndChart_realChart_positive hx hv hR hs t

/-- **The pre-glued plane is smooth.** If `u` is `Cⁿ` on the plane, the loop `x` and the map `v`
are `Cⁿ` and of period one in `t`, and `R ≥ 1`, the pre-glued plane is `Cⁿ` on the whole plane. -/
theorem contDiff_preglueEnd {n : ℕ∞} (hx : ContDiff ℝ n x) (hxper : Periodic x 1)
    (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hR : 1 ≤ R) : ContDiff ℝ n (preglueEnd x u v R) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : Complex.equivRealProdCLM.symm z = 0
  · obtain rfl : z = 0 := by simpa using hz
    exact hu.contDiffAt.congr_of_eventuallyEq (preglueEnd_eventuallyEq_nhds_zero hR)
  -- Away from the pole, every point is the image under the end lift of its end coordinates.
  obtain ⟨y, rfl⟩ : ∃ y, realChart positive.cylindricalEndLift y = z :=
    ⟨_, realChart_positive_endCoord hz⟩
  exact contDiffAt_preglueEndChart isEndChart_realChart_positive
    (contDiff_realChart positive.contDiff_cylindricalEndLift).contDiffAt
    (det_fderiv_realChart_cylindricalEndLift_pos positive y).ne' hx hxper
    (hu.comp (contDiff_realChart positive.contDiff_cylindricalEndLift)).contDiffAt hv.contDiffAt
    hvper hR

/-! ### Convergence to the broken plane -/

/-- **On compact sets the pre-glued planes are eventually `u`.** For every compact set `K` of the
plane, the pre-glued plane agrees with `u` on `K` for all large gluing parameters `R`: the height
`log ‖w‖ / 2π` is bounded above on `K`. -/
theorem eventually_eqOn_preglueEnd {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∀ᶠ R in atTop, EqOn (preglueEnd x u v R) u K := by
  obtain ⟨M, hM⟩ := (hK.image (Complex.equivRealProdCLM.symm.continuous.norm)).bddAbove
  filter_upwards [eventually_ge_atTop (1 / (2 * π) * M + 1)] with R hR z hz
  refine preglueEnd_of_le ?_
  rw [re_endCoord, endSign_positive]
  have h₁ : Real.log ‖Complex.equivRealProdCLM.symm z‖ ≤ M :=
    (Real.log_le_self (norm_nonneg _)).trans (hM (mem_image_of_mem _ hz))
  have h₂ := mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  linarith

/-- **On compact sets moving with the neck the pre-glued planes are eventually `v`.** If the loop
`x` and the map `v` have period one in `t`, then for every compact set `K` of the cylinder, the
pre-glued plane read in the end lift translated by `2R` agrees with `v` on `K` for all large
gluing parameters `R`. -/
theorem eventually_preglueEnd_realChart_add_eq (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∀ᶠ R in atTop, ∀ y ∈ K,
      preglueEnd x u v R (realChart positive.cylindricalEndLift (y + (2 * R, 0))) = v y := by
  obtain ⟨m, hm⟩ := (hK.image continuous_fst).bddBelow
  filter_upwards [eventually_ge_atTop (1 - m), eventually_ge_atTop 0] with R hR hR₀ y hy
  have hs : m ≤ y.1 := hm (mem_image_of_mem _ hy)
  obtain ⟨s, t⟩ := y
  rw [Prod.mk_add_mk, add_zero,
    preglueEnd_realChart_of_add_one_le hx hv hR₀ (by dsimp only at hs; linarith),
    add_sub_cancel_right]

end Floer.PSSPlane

namespace SymplecticForm

open Floer
open Floer.PSSPlane (positive)

variable [FiniteDimensional ℝ V]

/-- **The pre-gluing error at the end of a PSS plane is exponentially small.** Let `H` be a `C²`
Hamiltonian and `J_t(y)` a continuous family of endomorphisms, the cylindrical data of the end of
the plane in the end lift `φ` of the positive plane, and let `x` be an orbit of `X_{H_t}` of
period one. Suppose that `U = u ∘ φ` converges to `x` in `C¹` at the exponential rate `κ > 0` as
`s → ∞` and solves the Floer equation of the datum `H_t dt` beyond the height `T`, and that `v`, of
period one in `t`, converges to `x` in `C¹` at the rate `κ` as `s → -∞` and solves the Floer
equation on `ℝ × [0, 1]`. Then for every large gluing parameter `R`, the Floer operator of the
pre-glued plane, read in the end lift, is at most `C' e^{-κ R}` on `(T, ∞) × [0, 1]`.

For the positive plane given by a Hamiltonian `H`, `H` here is that Hamiltonian; for the negative
plane given by `H`, it is the reversed Hamiltonian `-H(-t)`. -/
theorem exists_eventually_norm_floerOperator_preglueEnd_comp_realChart_le (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {C κ T : ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ realChart positive.cylindricalEndLift) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (realChart positive.cylindricalEndLift (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) (s, t) -
          (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u ∘ realChart positive.cylindricalEndLift) z = 0)
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hvF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (PSSPlane.preglueEnd x u v R ∘ realChart positive.cylindricalEndLift) z‖ ≤
        C' * Real.exp (-(κ * R)) :=
  ω.exists_eventually_norm_floerOperator_preglueEndChart_comp_le
    PSSPlane.isEndChart_realChart_positive hH hJ hx hxper hκ hud hu hdu huF hvd hv hdv hvper hvF

end SymplecticForm

end TauCeti
