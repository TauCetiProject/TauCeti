/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Comp

/-!
# Pre-gluing a Floer cylinder at a cylindrical end

Let `u` be a map on a Riemann surface with a cylindrical end, in real coordinates `ℝ × ℝ`. The end
is described by a chart `φ : ℝ × ℝ → ℝ × ℝ` of period one in `t`, in which it is the half-cylinder
`s > 0`, together with end coordinates `e : ℝ × ℝ → ℝ × ℝ` inverting it there: `φ (e z) = z`
where `(e z).1 > 0`, and the end coordinates of `φ (s, t)` are `(s, t)` up to an integer in `t`
(`TauCeti.Floer.IsEndChart`). The ends of a pair of pants and of a PSS plane are of this kind.

Given a Floer cylinder `v` whose loops converge as `s → -∞` to the orbit `x` that `u ∘ φ`
converges to as `s → ∞`, the *pre-glued map* `TauCeti.Floer.preglueEndChart φ e x u v R` is `u`
up to the height `R - 1` of the end and further out the pre-glued map
`TauCeti.Floer.preglue x (u ∘ φ) v R` of `TauCeti.Geometry.Symplectic.Floer.Pregluing`, moved out
along the end by `R`. It interpolates through `x` on the neck `R - 1 ≤ s ≤ R + 1` and is the
translate `v(s - 2R, t)` beyond `R + 1`.

* **Away from the neck it is `u`.** At a point of height at most `R - 1` it is `u`
  (`TauCeti.Floer.preglueEndChart_of_le`), and near a point of height less than `R - 1` at which
  the height is continuous it agrees with `u` (`TauCeti.Floer.preglueEndChart_eventuallyEq_of_lt`).
* **In the end chart it is the translated pre-glued cylinder.** If `x` and `v` have period one in
  `t`, the integer ambiguity of the angular coordinate is absorbed, and for `R ≥ 1` the pre-glued
  map read in `φ` is `y ↦ preglue x (u ∘ φ) v R (y - (R, 0))`
  (`TauCeti.Floer.preglueEndChart_comp_chart`); beyond the height `R + 1` it is `v(s - 2R, t)`
  (`TauCeti.Floer.preglueEndChart_chart_of_add_one_le`).
* **It is smooth.** Where `φ` is smooth with invertible derivative and `u ∘ φ` is `Cⁿ`, the
  pre-glued map of `Cⁿ` data is `Cⁿ` (`TauCeti.Floer.contDiffAt_preglueEndChart`): it is the
  translated pre-glued cylinder composed with a local inverse of `φ`.
* **The pre-gluing error is exponentially small.** If `u ∘ φ` and `v` converge to `x` in `C¹` at
  an exponential rate `κ` and solve the cylindrical Floer equation, then for every large `R` the
  Floer operator of the pre-glued map read in `φ` is at most `C' e^{-κ R}` beyond the height where
  `u ∘ φ` solves it
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEndChart_comp_le`). If `v`
  solves it only on `S × [0, 1]`, the bound holds at the heights `s` with `s - 2R ∈ S`
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueEndChart_comp_le_of_eqOn`).

## Main definitions

* `TauCeti.Floer.IsEndChart φ e`: `φ` is a chart of period one of a cylindrical end `s > 0`, with
  end coordinates `e`.
* `TauCeti.Floer.preglueEndChart φ e x u v R`: the pre-glued map of `u` and of the Floer cylinder
  `v` at that end, with gluing parameter `R`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the pre-gluing construction and its error estimate.
-/

public section

open Filter Set Topology Function ContinuousLinearMap

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Floer

/-- **A cylindrical end chart.** The map `φ : ℝ × ℝ → ℝ × ℝ` is a chart of period one in `t` of a
cylindrical end, the half-cylinder `s > 0`, with end coordinates `e : ℝ × ℝ → ℝ × ℝ`: the chart
recovers a point of the end from its end coordinates, and the end coordinates of `φ (s, t)` are
`(s, t)` up to an integer in `t`. -/
structure IsEndChart (φ e : ℝ × ℝ → ℝ × ℝ) : Prop where
  /-- The chart recovers a point of the end from its end coordinates. -/
  chart_endCoord : ∀ z, 0 < (e z).1 → φ (e z) = z
  /-- The end coordinates of `φ (s, t)` are `(s, t)` up to an integer in `t`. -/
  exists_endCoord_chart : ∀ y, ∃ k : ℤ, (e (φ y)).1 = y.1 ∧ (e (φ y)).2 = y.2 + k
  /-- The chart has period one in `t`. -/
  chart_add_one : ∀ s t, φ (s, t + 1) = φ (s, t)

/-- **The pre-glued map at a cylindrical end** of a map `u` and a map `v` on the cylinder, through
the loop `x`, with gluing parameter `R`, for the end chart `φ` with end coordinates `e`. At a point
`z` with end coordinates `e z = (s, t)`, `s > 0`, it is the pre-glued map `preglue x (u ∘ φ) v R`
at `(s - R, t)`; elsewhere it is `u`. -/
noncomputable def preglueEndChart (φ e : ℝ × ℝ → ℝ × ℝ) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ)
    (z : ℝ × ℝ) : V :=
  if 0 < (e z).1 then preglue x (u ∘ φ) v R ((e z).1 - R, (e z).2) else u z

theorem preglueEndChart_def (φ e : ℝ × ℝ → ℝ × ℝ) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ)
    (z : ℝ × ℝ) :
    preglueEndChart φ e x u v R z =
      if 0 < (e z).1 then preglue x (u ∘ φ) v R ((e z).1 - R, (e z).2) else u z :=
  (rfl)

variable {φ e : ℝ × ℝ → ℝ × ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ}

/-- **Away from the neck the pre-glued map is `u`.** At a point of height at most `R - 1` on the
end, the pre-glued map is `u`. -/
theorem preglueEndChart_of_le (hφ : IsEndChart φ e) (h : (e z).1 ≤ R - 1) :
    preglueEndChart φ e x u v R z = u z := by
  rw [preglueEndChart_def]
  split_ifs with h₀
  · rw [preglue_of_le_neg_one (by dsimp only; linarith), Prod.mk_add_mk, sub_add_cancel, add_zero,
      comp_apply, Prod.mk.eta, hφ.chart_endCoord z h₀]
  · rfl

/-- Near a point of height less than `R - 1` at which the height is continuous, the pre-glued map
agrees with `u`. -/
theorem preglueEndChart_eventuallyEq_of_lt (hφ : IsEndChart φ e)
    (hc : ContinuousAt (fun w ↦ (e w).1) z) (h : (e z).1 < R - 1) :
    preglueEndChart φ e x u v R =ᶠ[𝓝 z] u :=
  (hc.eventually_lt continuousAt_const h).mono fun _ hw ↦ preglueEndChart_of_le hφ hw.le

/-- **The pre-glued map on the end.** At the image under the end chart of a point `(s, t)` with
`s > 0`, the pre-glued map is `preglue x (u ∘ φ) v R` at `(s - R, t)`, when the loop `x` and the
map `v` have period one in `t`. -/
theorem preglueEndChart_chart (hφ : IsEndChart φ e) (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    preglueEndChart φ e x u v R (φ (s, t)) = preglue x (u ∘ φ) v R (s - R, t) := by
  obtain ⟨k, h₁, h₂⟩ := hφ.exists_endCoord_chart (s, t)
  have hU (s : ℝ) : Periodic (fun t ↦ (u ∘ φ) (s, t)) 1 := fun t ↦ by
    simp only [comp_apply, hφ.chart_add_one]
  have hper := (periodic_preglue hx hU hv (R := R) (s - R)).int_mul k t
  rw [mul_one] at hper
  simpa only [preglueEndChart_def, h₁, h₂, hs, ↓reduceIte] using hper

/-- **The pre-glued map in the end chart.** If the loop `x` and the map `v` have period one in `t`
and `R ≥ 1`, the pre-glued map read in the end chart `φ` is the pre-glued map of `u ∘ φ` and `v`,
translated by `R`. -/
theorem preglueEndChart_comp_chart (hφ : IsEndChart φ e) (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 1 ≤ R) :
    preglueEndChart φ e x u v R ∘ φ = fun y ↦ preglue x (u ∘ φ) v R (y - (R, 0)) := by
  funext ⟨s, t⟩
  rw [comp_apply, Prod.mk_sub_mk, sub_zero]
  rcases lt_or_ge 0 s with hs | hs
  · exact preglueEndChart_chart hφ hx hv hs t
  · obtain ⟨k, h₁, -⟩ := hφ.exists_endCoord_chart (s, t)
    rw [preglueEndChart_of_le hφ (by rw [h₁]; dsimp only; linarith),
      preglue_of_le_neg_one (by dsimp only; linarith), Prod.mk_add_mk, sub_add_cancel, add_zero,
      comp_apply]

/-- **Far out on the end the pre-glued map is the cylinder.** If the loop `x` and the map `v` have
period one in `t` and `R ≥ 0`, then at the image under the end chart of a point `(s, t)` with
`s ≥ R + 1` the pre-glued map is `v(s - 2R, t)`. -/
theorem preglueEndChart_chart_of_add_one_le (hφ : IsEndChart φ e) (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hR : 0 ≤ R) {s : ℝ} (hs : R + 1 ≤ s) (t : ℝ) :
    preglueEndChart φ e x u v R (φ (s, t)) = v (s - 2 * R, t) := by
  rw [preglueEndChart_chart hφ hx hv (by linarith) t, preglue_of_one_le (by dsimp only; linarith),
    Prod.mk_sub_mk, sub_zero, sub_sub, ← two_mul]

/-- **The pre-glued map is smooth.** Let the end chart `φ` be smooth at `y` with invertible
derivative there, `u ∘ φ` be `Cⁿ` at `y`, the loop `x` be `Cⁿ`, `x` and the map `v` have period
one in `t`, `v` be `Cⁿ` at `y - (2R, 0)`, and `R ≥ 1`. Then the pre-glued map is `Cⁿ` at `φ y`. -/
theorem contDiffAt_preglueEndChart {n : ℕ∞} (hφ : IsEndChart φ e) {y : ℝ × ℝ}
    (hφy : ContDiffAt ℝ (⊤ : ℕ∞) φ y) (hdet : (fderiv ℝ φ y).det ≠ 0) (hx : ContDiff ℝ n x)
    (hxper : Periodic x 1) (hu : ContDiffAt ℝ n (u ∘ φ) y)
    (hv : ContDiffAt ℝ n v (y - (2 * R, 0))) (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hR : 1 ≤ R) :
    ContDiffAt ℝ n (preglueEndChart φ e x u v R) (φ y) := by
  refine ContDiffAt.of_comp_right (L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv)
    ?_ hφy (hφy.differentiableAt (by simp)).hasFDerivAt (by simp) (by exact_mod_cast le_top)
  rw [preglueEndChart_comp_chart hφ hxper hvper hR]
  refine (contDiffAt_preglue hx.contDiffAt ?_ ?_).comp y (contDiffAt_id.sub contDiffAt_const)
  · rwa [sub_add_cancel]
  · rwa [sub_sub, Prod.mk_add_mk, add_zero, ← two_mul]

end Floer

namespace SymplecticForm

open Floer

variable [FiniteDimensional ℝ V] {φ e : ℝ × ℝ → ℝ × ℝ}

/-- **The pre-gluing error at a cylindrical end, on the heights where `v` solves the Floer
equation.** Let `H` be a `C²` Hamiltonian and `J_t(y)` a continuous family of endomorphisms, the
cylindrical data of the end in its chart `φ`, and let `x` be an orbit of `X_{H_t}` of period one.
Suppose that `U = u ∘ φ` converges to `x` in `C¹` at the exponential rate `κ > 0` as `s → ∞` and
solves the Floer equation of the datum `H_t dt` beyond the height `T`, and that `v`, of period one
in `t`, converges to `x` in `C¹` at the rate `κ` as `s → -∞` and solves the Floer equation on
`S × [0, 1]`. Then for every large gluing parameter `R`, the Floer operator of the pre-glued map,
read in the end chart, is at most `C' e^{-κ R}` at every point `(s, t)` of `(T, ∞) × [0, 1]` with
`s - 2R ∈ S`. -/
theorem exists_eventually_norm_floerOperator_preglueEndChart_comp_le_of_eqOn (ω : SymplecticForm V)
    (hφ : IsEndChart φ e) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
    {u v : ℝ × ℝ → V} {C κ T : ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u ∘ φ) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (φ (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ φ) (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (u ∘ φ) z = 0)
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hvper : ∀ s, Periodic (fun t ↦ v (s, t)) 1) {S : Set ℝ}
    (hvF : EqOn (ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v) 0
      (S ×ˢ Icc (0 : ℝ) 1)) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, z.1 - 2 * R ∈ S →
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglueEndChart φ e x u v R ∘ φ) z‖ ≤ C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ := ω.exists_eventually_norm_floerOperator_preglue_le_of_eqOn hH hJ hx hκ hud
    hu hdu hvd hv hdv (fun z hz ↦ huF z hz) hvF
  refine ⟨C', (hC'.and (eventually_ge_atTop 1)).mono fun R ⟨hR, hR₁⟩ z hz hzS ↦ ?_⟩
  rw [preglueEndChart_comp_chart hφ hxper hvper hR₁, floerOperator_comp_sub]
  refine hR _ (by simpa using hz.2) (fun _ ↦ ⟨?_, by simpa using hz.2⟩)
    fun _ ↦ ⟨?_, by simpa using hz.2⟩
  · simpa using hz.1
  · simpa [sub_sub, ← two_mul] using hzS

/-- **The pre-gluing error at a cylindrical end is exponentially small.** Let `H` be a `C²`
Hamiltonian and `J_t(y)` a continuous family of endomorphisms, the cylindrical data of the end in
its chart `φ`, and let `x` be an orbit of `X_{H_t}` of period one. Suppose that `U = u ∘ φ`
converges to `x` in `C¹` at the exponential rate `κ > 0` as `s → ∞` and solves the Floer equation
of the datum `H_t dt` beyond the height `T`, and that `v`, of period one in `t`, converges to `x`
in `C¹` at the rate `κ` as `s → -∞` and solves the Floer equation on `ℝ × [0, 1]`. Then for every
large gluing parameter `R`, the Floer operator of the pre-glued map, read in the end chart, is at
most `C' e^{-κ R}` on `(T, ∞) × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglueEndChart_comp_le (ω : SymplecticForm V)
    (hφ : IsEndChart φ e) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
    {u v : ℝ × ℝ → V} {C κ T : ℝ} (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u ∘ φ) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (φ (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ φ) (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (u ∘ φ) z = 0)
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
          (preglueEndChart φ e x u v R ∘ φ) z‖ ≤ C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ := ω.exists_eventually_norm_floerOperator_preglueEndChart_comp_le_of_eqOn hφ
    hH hJ hx hxper hκ hud hu hdu huF hvd hv hdv hvper fun z hz ↦ hvF z hz
  exact ⟨C', hC'.mono fun R hR z hz ↦ hR z hz (mem_univ _)⟩

end SymplecticForm

end TauCeti
