/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothFamily

/-!
# Smooth families of compactly supported functions in `H^s`

Let `X` be a finite-dimensional real normed space of parameters and `F : X → E → ℂ` a family of
functions on a finite-dimensional real inner product space `E`, jointly smooth in the parameter and
the point, and vanishing wherever `‖x‖ ≥ R`, for one `R` and every parameter. Then `c ↦ F c` is a
smooth map into every Bessel-potential space `H^s(E)`, `s ≥ 0`
(`BesselPotentialSpace.exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm`).

This is how families built from a fixed cutoff and smooth coefficients, such as the core of a
family of plane vortices over a window of divisors, enter Sobolev-space arguments.

The proof is by induction on the integer order. In `L²` the family factors through the bounded
continuous functions: `c ↦ F c` is a superposition `f ↦ G ∘ f` applied to the affine family
`c ↦ (x ↦ (c, ρ x))`, where `ρ` is the radial retraction onto the ball, and superposition operators
are smooth for the sup norm (`BoundedContinuousFunction.exists_contDiff_apply_eq`).
Multiplication by the indicator of the ball, an element of `L²`, is a bounded operator from the
bounded continuous functions to `L²` (`BoundedContinuousFunction.mulLpL`). The
derivatives `x ↦ ∂_v F c x` form a family of the same kind, so a family that is smooth in `H^k`
together with its first derivatives is smooth in `H^(k+1)`
(`BesselPotentialSpace.isSmoothFamilyAt_add_one`).
-/

public section

noncomputable section

open MeasureTheory Module Filter Metric Set TemperedDistribution
open scoped ContDiff BesselPotentialSpace BoundedContinuousFunction Topology LineDeriv ENNReal

namespace BesselPotentialSpace

/-! ### The radial retraction onto a ball -/

section Retract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction `x ↦ (R / max R ‖x‖) • x` onto the closed ball of radius `R`. -/
private def retract (R : ℝ) (x : E) : E :=
  (R * (max R ‖x‖)⁻¹) • x

private theorem continuous_retract {R : ℝ} (hR : 0 < R) : Continuous (retract (E := E) R) :=
  (continuous_const.mul ((continuous_const.max continuous_norm).inv₀ fun _ ↦
    (hR.trans_le (le_max_left _ _)).ne')).smul continuous_id

private theorem norm_retract_le {R : ℝ} (hR : 0 < R) (x : E) : ‖retract R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [retract, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
  calc R * ((max R ‖x‖)⁻¹ * ‖x‖) ≤ R * 1 := by
        gcongr
        exact inv_mul_le_one_of_le₀ (le_max_right _ _) hm.le
    _ = R := mul_one R

/-- A function vanishing outside the ball of radius `R` does not see the retraction. -/
private theorem apply_retract {R : ℝ} (hR : 0 < R) {f : E → ℂ} (hf : ∀ x, R ≤ ‖x‖ → f x = 0)
    (x : E) : f (retract R x) = f x := by
  rcases le_or_gt ‖x‖ R with hx | hx
  · rw [retract, max_eq_left hx, mul_inv_cancel₀ hR.ne', one_smul]
  · rw [hf x hx.le, hf]
    rw [retract, max_eq_right hx.le, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ (hR.trans hx).ne', mul_one]

end Retract

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- **The case `L²`.** A jointly smooth family of functions vanishing outside a fixed ball is
smooth in `H⁰(E) = L²(E)`. -/
private theorem isSmoothFamilyAt_zero_of_forall_le_norm {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) (c₀ : X) :
    IsSmoothFamilyAt 0 2 le_rfl c₀ F := by
  set R' := max R 1
  have hR' : 0 < R' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨Ψ, hΨc, hΨ⟩ := BoundedContinuousFunction.exists_contDiff_apply_eq hF
    (continuous_retract hR') (norm_retract_le hR')
  -- Multiplication by the indicator of the ball, from the bounded continuous functions to `L²`.
  have hB : volume (closedBall (0 : E) R') ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  set M : (E →ᵇ ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    (BoundedContinuousFunction.mulLpL volume 2).flip
      (indicatorConstLp 2 measurableSet_closedBall hB (1 : ℂ))
  refine .of_contDiff_Lp (g := fun c ↦ M (Ψ c)) ((M.restrictScalars ℝ).contDiff.comp hΨc)
    fun c ↦ ?_
  filter_upwards [BoundedContinuousFunction.coeFn_mulLpL (E := ℂ) volume 2 (Ψ c)
    (indicatorConstLp 2 measurableSet_closedBall hB (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_closedBall) (hμs := hB) (c := (1 : ℂ))]
    with x h₁ h₂
  rw [ContinuousLinearMap.flip_apply, h₁, h₂]
  by_cases hxB : x ∈ closedBall (0 : E) R'
  · rw [indicator_of_mem hxB, smul_eq_mul, mul_one, hΨ, Function.uncurry_apply_pair,
      apply_retract hR' fun y hy ↦ hR c y ((le_max_left _ _).trans hy)]
  · have hxR : R' < ‖x‖ := by simpa using hxB
    rw [indicator_of_notMem hxB, smul_zero, hR c x ((le_max_left _ _).trans hxR.le)]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The derivatives of a family vanishing outside a ball vanish outside a slightly larger ball. -/
private theorem fderiv_eq_zero_of_forall_le_norm {f : E → ℂ} {R : ℝ} (hf : ∀ x, R ≤ ‖x‖ → f x = 0)
    {x : E} (hx : R + 1 ≤ ‖x‖) : fderiv ℝ f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [ball_mem_nhds x one_pos] with y hy
    refine hf y ?_
    have := norm_sub_norm_le x y
    rw [← dist_eq_norm, dist_comm] at this
    linarith [mem_ball.1 hy]
  rw [hev.fderiv_eq, fderiv_const_apply]

/-- **The case of an integer order.** -/
private theorem isSmoothFamilyAt_natCast_of_forall_le_norm (k : ℕ) {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) (c₀ : X) :
    IsSmoothFamilyAt k 2 k.cast_nonneg c₀ F := by
  induction k generalizing F R c₀ with
  | zero => exact (isSmoothFamilyAt_zero_of_forall_le_norm hF hR c₀).mono Nat.cast_zero.le
  | succ k ih =>
    -- The derivatives `x ↦ ∂_v F c x` form a family of the same kind.
    have hF' (v : E) : ContDiff ℝ ∞ (Function.uncurry fun c x ↦ fderiv ℝ (F c) x v) := by
      have h : ContDiff ℝ ∞ fun p : X × E ↦ fderiv ℝ (F p.1) p.2 :=
        ContDiff.fderiv (f := fun p : X × E ↦ F p.1)
          (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by simp)
      exact h.clm_apply contDiff_const
    set b := stdOrthonormalBasis ℝ E
    exact (isSmoothFamilyAt_add_one (u := F) b
      (fun c ↦ (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) (ih hF hR)
      (fun i ↦ ih (hF' (b i)) (R := R + 1) fun c x hx ↦ by
        simp [fderiv_eq_zero_of_forall_le_norm (hR c) hx]) c₀).mono (Nat.cast_succ k).le

/-- **Compactly supported smooth families are smooth in every `H^s`.** Let `F : X → E → ℂ` be
jointly smooth in the parameter `c ∈ X` and the point `x ∈ E`, and let every `F c` vanish wherever
`‖x‖ ≥ R`. Then for every `s ≥ 0` there is a smooth map `Φ : X → H^s(E)` whose `L²` function at
`c` is `F c`. -/
theorem exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) {s : ℝ}
    (hs : 0 ≤ s) :
    ∃ Φ : X → H^{s}(E), ContDiff ℝ ∞ Φ ∧ ∀ c, ⇑(inclusionLp hs (Φ c)) =ᵐ[volume] F c :=
  exists_contDiff_of_forall_isSmoothFamilyAt fun c₀ ↦
    (isSmoothFamilyAt_natCast_of_forall_le_norm ⌈s⌉₊ hF hR c₀).mono (Nat.le_ceil s)

end BesselPotentialSpace
