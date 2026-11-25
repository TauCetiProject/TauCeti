/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.Pregluing.EndChart

/-!
# Pre-gluing a Floer cylinder to an end of a pair of pants

Let `u` be a map on the pair of pants `S = ℂ ∖ {0, 1}`, in the real coordinates `ℝ × ℝ ≃ ℂ`, and
let `q` be one of its three ends. In the positive end chart `φ'_q`
(`TauCeti.Floer.positiveEndChart q`) the end is the half-cylinder `s > 0`, and a Floer pair of
pants is there a Floer half-cylinder `U = u ∘ φ'_q` for the cylindrical datum `H'_q(t) dt`
(`TauCeti.Floer.positiveEndHamiltonian`), converging to an orbit `x` as `s → ∞`. The boundary of
the one-dimensional moduli spaces of pairs of pants consists of pairs of pants broken at an end:
a pair of pants `u` together with a Floer cylinder `v`, read in the same coordinates, whose loops
converge to the same orbit `x` as `s → -∞`. On the input ends `0`, `1` the positive end chart is
the end chart itself and `v` is a Floer cylinder for `H_q` whose output is the input `x` of `u`; on
the output end `∞` it is `(s, t) ↦ φ_∞(-s, -t)`, and `(s, t) ↦ v(-s, -t)` is a Floer cylinder for
`H_∞` whose input is the output of `u`.

The first step of gluing such a pair is the *pre-glued pair of pants*
(`TauCeti.Floer.preglueEnd q x u v R`), the pre-glued map `TauCeti.Floer.preglueEndChart` of
`TauCeti.Geometry.Symplectic.Floer.Pregluing.EndChart` for the positive end chart
(`TauCeti.Floer.isEndChart_positiveEndChart`). Away from the end `q`, and on the end up to the
height `R - 1`, it is `u`; further out on the end it is the pre-glued map
`TauCeti.Floer.preglue x U v R` of `TauCeti.Geometry.Symplectic.Floer.Pregluing`, moved out along
the end by `R`. Explicitly, in the positive end coordinates `(s, t)` of a point of the end, the
end coordinate of `TauCeti.ThricePuncturedSphere.Puncture.endCoord` read with the sign of the end,
its value is `preglue x U v R (s - R, t)`. It interpolates through the orbit `x` on the neck
`R - 1 ≤ s ≤ R + 1` and is the translate `v(s - 2R, t)` beyond `R + 1`, so its end `q` is the
other end of the cylinder `v`.

* **Away from the neck it is `u`.** Where the signed longitudinal coordinate of the end `q` is at
  most `R - 1`, the pre-glued pair of pants is `u` (`TauCeti.Floer.preglueEnd_of_le`), and near
  such points with coordinate less than `R - 1`, other than the center
  `TauCeti.ThricePuncturedSphere.Puncture.endCenter` of the end coordinate, it agrees with `u`
  (`TauCeti.Floer.preglueEnd_eventuallyEq_of_lt`). So it has the same perturbed
  derivative `du - X_K` there, for any perturbation `K`, by
  `TauCeti.SymplecticForm.perturbedFDeriv_congr_of_eventuallyEq`: if `u` solves the Floer
  equation, so does the pre-glued pair of pants at these points.
* **In the end chart it is the translated pre-glued cylinder.** If the orbit `x` and the cylinder
  `v` have period one in `t`, then on the end the angular coordinate is determined only up to an
  integer, which periodicity absorbs, and for `R ≥ 1` the pre-glued pair of pants read in the
  positive end chart is `y ↦ preglue x U v R (y - (R, 0))` on the whole plane
  (`TauCeti.Floer.preglueEnd_comp_positiveEndChart`). Beyond the height `R + 1` it is
  `v(s - 2R, t)` (`TauCeti.Floer.preglueEnd_positiveEndChart_of_add_one_le`). In the signed end
  coordinates `(s, t)` themselves no periodicity is needed: for `R ≥ 0` it is `v(s - 2R, t)` where
  `s ≥ R + 1` (`TauCeti.Floer.preglueEnd_of_add_one_le`).
* **It is smooth.** For `R ≥ 1` the pre-glued pair of pants of `Cⁿ` data is `Cⁿ` on `S`
  (`TauCeti.Floer.contDiffOn_preglueEnd`): near each point it is the translated pre-glued
  cylinder composed with a local inverse of the end chart.
* **The pre-gluing error is exponentially small.** If `U` converges to `x` in `C¹` at an
  exponential rate `κ` and solves the cylindrical Floer equation beyond a height `T`, and `v`
  converges to `x` at the same rate at `-∞` and solves the Floer equation, then for every large
  `R` the Floer operator of the pre-glued pair of pants in the end chart is at most `C' e^{-κ R}`
  beyond the height `T`
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEnd_comp_le`). If `v` solves
  the Floer equation only below a height `T'`, the bound holds on the neck `T < s < 2R + T'`
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_Iio`). Both
  are cases of the bound at the heights `s > T` with `s - 2R` in a set `S` on which `v` solves the
  Floer equation
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_eqOn`). The
  error is measured in the cylindrical coordinates of the end, in which the gluing estimates are
  made.

The hypotheses on `U` are what the asymptotic analysis of the ends supplies for a finite-energy
Floer pair of pants whose almost complex structure is cylindrical on the end `q` and whose end
orbit is nondegenerate: `U` is a Floer half-cylinder for `H'_q`
(`TauCeti.SymplecticForm.floer_comp_positiveEndChart_of_cylindrical`), converging exponentially in
`C¹` (`TauCeti.SymplecticForm.`
`exists_pos_eventually_norm_fderiv_comp_positiveEndChart_sub_le_exp_of_cylindrical`).
The Sobolev setting, the right inverse of the linearized operator and the Newton iteration that
corrects the pre-glued pair of pants to a solution are not treated here.

## Main definitions

* `TauCeti.Floer.preglueEnd q x u v R`: the pre-glued pair of pants of `u` and of the Floer
  cylinder `v` at the end `q`, with gluing parameter `R`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the gluing of Floer cylinders to the ends of a pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the pre-gluing construction and its error estimate.
-/

public section

open Filter Set Topology Function ContinuousLinearMap TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Floer

/-- The positive end chart of an end `q` is a cylindrical end chart, with the signed end
coordinates of `q` as end coordinates. -/
theorem isEndChart_positiveEndChart (q : Puncture) :
    IsEndChart (positiveEndChart q) fun z ↦
      (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re,
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im) where
  chart_endCoord _ h₀ := positiveEndChart_endSign_mul_endCoord
    (q.ne_endCenter_of_endSign_mul_re_endCoord_pos h₀)
  exists_endCoord_chart := exists_endCoord_positiveEndChart q
  chart_add_one := positiveEndChart_add_one q

/-- **The pre-glued pair of pants** of a map `u` on the pair of pants and a map `v` at the end
`q`, through the loop `x`, with gluing parameter `R`: the pre-glued map
`TauCeti.Floer.preglueEndChart` of the positive end chart `φ'_q`. At a point whose signed end
coordinates `(s, t)` on the end `q` have `s > 0` it is the pre-glued map `preglue x (u ∘ φ'_q) v R`
at `(s - R, t)`; elsewhere it is `u`. It is `u` where `s ≤ R - 1`
(`TauCeti.Floer.preglueEnd_of_le`), and `v(s - 2R, t)` where `s ≥ R + 1` when `R ≥ 0`
(`TauCeti.Floer.preglueEnd_of_add_one_le`). -/
noncomputable def preglueEnd (q : Puncture) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ)
    (z : ℝ × ℝ) : V :=
  preglueEndChart (positiveEndChart q)
    (fun z ↦ (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im)) x u v R z

theorem preglueEnd_def (q : Puncture) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) :
    preglueEnd q x u v R z =
      if 0 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re then
        preglue x (u ∘ positiveEndChart q) v R
          (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re - R,
            q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im)
      else u z := by
  rw [preglueEnd, preglueEndChart_def]

variable {q : Puncture} {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ}

/-- **Away from the neck the pre-glued pair of pants is `u`.** At a point whose signed
longitudinal coordinate on the end `q` is at most `R - 1`, the pre-glued pair of pants is `u`. -/
theorem preglueEnd_of_le (h : (positiveEndCoord q z).1 ≤ R - 1) : preglueEnd q x u v R z = u z :=
  preglueEndChart_of_le (isEndChart_positiveEndChart q) (by rwa [fst_positiveEndCoord] at h)

/-- **Beyond the neck the pre-glued pair of pants is the translated cylinder.** For `R ≥ 0`, at a
point whose signed end coordinates `(s, t)` on the end `q` have `s ≥ R + 1`, the pre-glued pair of
pants is `v(s - 2R, t)`. -/
theorem preglueEnd_of_add_one_le (hR : 0 ≤ R)
    (h : R + 1 ≤ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    preglueEnd q x u v R z =
      v (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re - 2 * R,
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im) := by
  rw [preglueEnd_def, ite_eq_left (by linarith), preglue_of_one_le (by dsimp only; linarith),
    Prod.mk_sub_mk, sub_zero, sub_sub, ← two_mul]

/-- Near a point other than the center of the end `q` whose signed longitudinal coordinate on `q`
is less than `R - 1`, such as a point of `S` away from the neck, the pre-glued pair of pants agrees
with `u`. -/
theorem preglueEnd_eventuallyEq_of_lt (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : (positiveEndCoord q z).1 < R - 1) : preglueEnd q x u v R =ᶠ[𝓝 z] u :=
  ((continuousAt_fst_positiveEndCoord q hz).eventually_lt continuousAt_const h).mono
    fun _ hw ↦ preglueEnd_of_le hw.le

/-- **The pre-glued pair of pants on the end.** At the image under the positive end chart of a
point `(s, t)` with `s > 0`, the pre-glued pair of pants is the pre-glued map at `(s - R, t)`,
when the loop `x` and the map `v` have period one in `t`. -/
theorem preglueEnd_positiveEndChart (hx : Periodic x 1) (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    preglueEnd q x u v R (positiveEndChart q (s, t)) =
      preglue x (u ∘ positiveEndChart q) v R (s - R, t) :=
  preglueEndChart_chart (isEndChart_positiveEndChart q) hx hv hs t

/-- **The pre-glued pair of pants in the end chart.** If the loop `x` and the map `v` have period
one in `t` and `R ≥ 1`, the pre-glued pair of pants read in the positive end chart of `q` is the
pre-glued map of `u ∘ φ'_q` and `v`, translated by `R`. -/
theorem preglueEnd_comp_positiveEndChart (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 1 ≤ R) :
    preglueEnd q x u v R ∘ positiveEndChart q =
      fun y ↦ preglue x (u ∘ positiveEndChart q) v R (y - (R, 0)) :=
  preglueEndChart_comp_chart (isEndChart_positiveEndChart q) hx hv hR

/-- **Far out on the end the pre-glued pair of pants is the cylinder.** If the loop `x` and the
map `v` have period one in `t` and `R ≥ 0`, then at the image under the positive end chart of a
point `(s, t)` with `s ≥ R + 1` the pre-glued pair of pants is `v(s - 2R, t)`. -/
theorem preglueEnd_positiveEndChart_of_add_one_le (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 0 ≤ R) {s : ℝ} (hs : R + 1 ≤ s) (t : ℝ) :
    preglueEnd q x u v R (positiveEndChart q (s, t)) = v (s - 2 * R, t) :=
  preglueEndChart_chart_of_add_one_le (isEndChart_positiveEndChart q) hx hv hR hs t

/-- **The pre-glued pair of pants is smooth at a point of the end chart.** If the loop `x` is `Cⁿ`,
`x` and the map `v` have period one in `t`, and `R ≥ 1`, then the pre-glued pair of pants is `Cⁿ`
at `φ'_q(y)` whenever `u` is `Cⁿ` there and `v` is `Cⁿ` at `y - (2R, 0)`. -/
theorem contDiffAt_preglueEnd_positiveEndChart {n : ℕ∞} (hx : ContDiff ℝ n x)
    (hxper : Periodic x 1) (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 1 ≤ R)
    {y : ℝ × ℝ} (hu : ContDiffAt ℝ n u (positiveEndChart q y))
    (hv : ContDiffAt ℝ n v (y - (2 * R, 0))) :
    ContDiffAt ℝ n (preglueEnd q x u v R) (positiveEndChart q y) :=
  contDiffAt_preglueEndChart (isEndChart_positiveEndChart q)
    (contDiff_positiveEndChart q _).contDiffAt (det_fderiv_positiveEndChart_pos q y).ne' hx hxper
    (hu.comp y (contDiff_positiveEndChart q _).contDiffAt) hv hvper hR

/-- **The pre-glued pair of pants is smooth.** If `u` is `Cⁿ` on `S`, the loop `x` and the map `v`
are `Cⁿ` and of period one in `t`, and `R ≥ 1`, the pre-glued pair of pants is `Cⁿ` on `S`. -/
theorem contDiffOn_preglueEnd {n : ℕ∞} (hx : ContDiff ℝ n x) (hxper : Periodic x 1)
    (hu : ContDiffOn ℝ n u thricePuncturedSphereReal) (hv : ContDiff ℝ n v)
    (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 1 ≤ R) :
    ContDiffOn ℝ n (preglueEnd q x u v R) thricePuncturedSphereReal := by
  intro z hz
  have hy : positiveEndChart q
      (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re,
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im) = z :=
    positiveEndChart_endSign_mul_endCoord (ne_endCenter hz q)
  rw [← hy] at hz ⊢
  exact (contDiffAt_preglueEnd_positiveEndChart hx hxper hvper hR
    (hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)) hv.contDiffAt
    ).contDiffWithinAt

end Floer

namespace SymplecticForm

open Floer

variable [FiniteDimensional ℝ V]

/-- **The pre-gluing error at an end of a pair of pants, on the heights where `v` solves the
Floer equation.** Let `H` be a `C²` Hamiltonian and `J_t(y)` a continuous family of endomorphisms,
the cylindrical data of the end `q` in its positive end chart `φ'_q`, and let `x` be an orbit of
`X_{H_t}` of period one. Suppose that `U = u ∘ φ'_q` converges to `x` in `C¹` at the exponential
rate `κ > 0` as `s → ∞` and solves the Floer equation of the datum `H_t dt` beyond the height `T`,
and that `v`, of period one in `t`, converges to `x` in `C¹` at the rate `κ` as `s → -∞` and solves
the Floer equation on `S × [0, 1]`. Then for every large gluing parameter `R`, the Floer operator
of the pre-glued pair of pants, read in the positive end chart, is at most `C' e^{-κ R}` at every
point `(s, t)` of `(T, ∞) × [0, 1]` with `s - 2R ∈ S`. -/
theorem exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_eqOn (ω : SymplecticForm V)
    (q : Puncture) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V}
    {C κ T : ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u ∘ positiveEndChart q) z = 0)
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    {S : Set ℝ}
    (hvF : EqOn (ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v) 0
      (S ×ˢ Icc (0 : ℝ) 1)) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, z.1 - 2 * R ∈ S →
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglueEnd q x u v R ∘ positiveEndChart q) z‖ ≤ C' * Real.exp (-(κ * R)) :=
  ω.exists_eventually_norm_floerOperator_preglueEndChart_comp_le_of_eqOn
    (isEndChart_positiveEndChart q) hH hJ hx hxper hκ hud hu hdu huF hvd hv hdv hvper hvF

/-- **The pre-gluing error at an end of a pair of pants is exponentially small.** Let `H` be a
`C²` Hamiltonian and `J_t(y)` a continuous family of endomorphisms, the cylindrical data of the
end `q` in its positive end chart `φ'_q`, and let `x` be an orbit of `X_{H_t}` of period one.
Suppose that `U = u ∘ φ'_q` converges to `x` in `C¹` at the exponential rate `κ > 0` as `s → ∞`
and solves the Floer equation of the datum `H_t dt` beyond the height `T`, and that `v`, of period
one in `t`, converges to `x` in `C¹` at the rate `κ` as `s → -∞` and solves the Floer equation on
`ℝ × [0, 1]`. Then for every large gluing parameter `R`, the Floer operator of the pre-glued pair
of pants, read in the positive end chart, is at most `C' e^{-κ R}` on `(T, ∞) × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglueEnd_comp_le (ω : SymplecticForm V)
    (q : Puncture) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V}
    {C κ T : ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u ∘ positiveEndChart q) z = 0)
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
          (preglueEnd q x u v R ∘ positiveEndChart q) z‖ ≤ C' * Real.exp (-(κ * R)) :=
  ω.exists_eventually_norm_floerOperator_preglueEndChart_comp_le
    (isEndChart_positiveEndChart q) hH hJ hx hxper hκ hud hu hdu huF hvd hv hdv hvper hvF

/-- **The pre-gluing error on the neck at an end of a pair of pants is exponentially small.** Under
the hypotheses of `TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEnd_comp_le`,
suppose that `v` solves the Floer equation only below the height `T'`, as the end of a pair of
pants does. Then for every large gluing parameter `R`, the Floer operator of the pre-glued pair of
pants, read in the positive end chart, is at most `C' e^{-κ R}` on the neck
`(T, 2R + T') × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_Iio (ω : SymplecticForm V)
    (q : Puncture) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V}
    {C κ T T' : ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u ∘ positiveEndChart q) z = 0)
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hvF : ∀ z ∈ Iio T' ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglueEnd q x u v R ∘ positiveEndChart q) z‖ ≤ C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ := ω.exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_eqOn q hH hJ
    hx hxper hκ hud hu hdu huF hvd hv hdv hvper fun z hz ↦ hvF z hz
  refine ⟨C', hC'.mono fun R hR z hz ↦ hR z ⟨hz.1.1, hz.2⟩ ?_⟩
  rw [mem_Iio]
  linarith [hz.1.2]

end SymplecticForm

end TauCeti
