/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Exponential decay of subsolutions of `-Δ + c²` outside a ball

Let `u` be a function on the exterior `‖x‖ ≥ R` of a ball in a finite-dimensional real inner
product space, with `u → 0` at infinity and `c² u ≤ Δ u` for some `c ≥ 0`, so that `u` is a
subsolution of the screened operator `-Δ + c²`. Then `u` decays at the exponential rate `c`:
if `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then

`u x ≤ M exp (-c (‖x‖ - R))` for `‖x‖ ≥ R`.

The barrier `M exp (-c (‖x‖ - R))` is a supersolution of `-Δ + c²` away from the origin: its
Laplacian is `(c² - (dim E - 1) c / ‖x‖)` times itself (`ContDiffAt.laplacian_comp_norm`). The
comparison principle for `-Δ + c²` on the compact annuli `R ≤ ‖x‖ ≤ R'`
(`TauCeti.le_of_mul_le_laplacian_le_of_le_frontier`) and the limit at infinity, which controls the
outer sphere as `R' → ∞`, then give the bound.

The same bound holds for subsolutions of `-Δ + V` with a variable potential `V ≥ c²`, since the
barrier is nonnegative and hence also a supersolution of `-Δ + V`. Such potentials arise for
solutions of a linear equation `Δ u = V u` of indefinite sign, to which the constant form does not
apply: both `u` and `-u` are subsolutions of `-Δ + V`, so `|u|` decays at the rate `c`.

A forcing term decaying at the same rate does not change the conclusion, provided the potential
has a margin `V ≥ c² + δ` with `δ > 0`: if `V u - G exp (-c ‖x‖) ≤ Δ u`, then
`u x ≤ M exp (-c (‖x‖ - R)) + (G / δ) exp (-c ‖x‖)`. Indeed `u - (G / δ) exp (-c ‖x‖)` is then a
subsolution of `-Δ + V`. Testing against continuous linear functionals gives the same bound for
the norm of a vector-valued solution of `Δ D = V • D + H` with `‖H x‖ ≤ G exp (-c ‖x‖)`. This is
how the derivatives of a solution of a semilinear equation are shown to decay: they solve linear
equations whose forcing involves only lower derivatives.

This is the decay mechanism of massive fields: for instance, outside a large disc the logarithmic
modulus defect `-log |α|²` of a plane vortex is such a subsolution for every rate `c < 1 / 2`.

## Main declarations

* `TauCeti.le_mul_exp_of_mul_le_laplacian`: a subsolution of `-Δ + V`, `V ≥ c²`, on the exterior of
  a ball which tends to zero at infinity is bounded by `M exp (-c (‖x‖ - R))`.
* `TauCeti.le_mul_exp_of_sq_mul_le_laplacian`: the case of the constant potential `c²`.
* `TauCeti.le_mul_exp_add_mul_exp_of_mul_sub_le_laplacian`: the forced version, for a potential
  `V ≥ c² + δ` and a forcing bounded by `G exp (-c ‖x‖)`.
* `TauCeti.norm_le_mul_exp_add_mul_exp_of_laplacian_eq`: the forced version for the norm of a
  vector-valued solution of `Δ D = V • D + H`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (the maximum principle and comparison with barriers).
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric Set Topology InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The barrier `A exp (-c ‖x‖) + ε` is a supersolution of `-Δ + c²` away from the origin when
`A ≥ 0`, `c ≥ 0` and `ε ≥ 0`. -/
private theorem laplacian_exp_barrier_le {A c ε : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ A * Real.exp (-(c * ‖y‖)) + ε) x ≤
      c ^ 2 * (A * Real.exp (-(c * ‖x‖)) + ε) := by
  have hF : ContDiffAt ℝ 2 (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) ‖x‖ := by fun_prop
  have hd : deriv (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) =
      fun t ↦ -(c * (A * Real.exp (-(c * t)))) := by
    funext t
    simp (disch := fun_prop)
    ring
  have hdd : deriv (deriv fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) =
      fun t ↦ c ^ 2 * (A * Real.exp (-(c * t))) := by
    funext t
    simp (disch := fun_prop)
    ring
  rw [hF.laplacian_comp_norm hx, hdd, hd]
  dsimp only
  have hdim : (0 : ℝ) ≤ Module.finrank ℝ E - 1 := by
    have : 0 < Module.finrank ℝ E := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
    have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast this
    linarith
  have hterm : 0 ≤ (Module.finrank ℝ E - 1) * (c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖ := by
    positivity
  have hneg : (Module.finrank ℝ E - 1) * -(c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖ =
      -((Module.finrank ℝ E - 1) * (c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖) := by ring
  have hε' : 0 ≤ c ^ 2 * ε := by positivity
  rw [hneg, mul_add]
  linarith

/-- **Exponential decay of subsolutions of `-Δ + V` with `V ≥ c²`.** Let `u` be continuous on the
exterior `‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with `V u ≤ Δ u` there for a
potential `V ≥ c²`, `c ≥ 0`, and `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with
`M ≥ 0`, then `u x ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_of_mul_le_laplacian {u V : E → ℝ} {R c M : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hM : 0 ≤ M) (hcont : ContinuousOn u {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x) (hV : ∀ x, R < ‖x‖ → c ^ 2 ≤ V x)
    (hsub : ∀ x, R < ‖x‖ → V x * u x ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
  have hx₀ : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have : Nontrivial E := ⟨⟨x, 0, hx₀⟩⟩
  -- The barrier, rewritten as a radial profile with amplitude `A = M exp (c R)`.
  set A := M * Real.exp (c * R) with hA
  have hAnn : 0 ≤ A := by positivity
  have hbar : ∀ y : E, M * Real.exp (-(c * (‖y‖ - R))) = A * Real.exp (-(c * ‖y‖)) := by
    intro y
    rw [hA, exp_neg_mul_sub, mul_assoc]
  rw [hbar]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Beyond some radius `R₁`, `u ≤ ε`; compare on the annulus `R ≤ ‖y‖ ≤ max R₁ ‖x‖`.
  obtain ⟨R₁, hR₁⟩ := (hasBasis_cobounded_norm.eventually_iff).mp
    (cobounded_eq_cocompact (α := E) ▸ hlim.eventually (eventually_le_nhds hε))
  set R' := max R₁ ‖x‖
  set K := closedBall (0 : E) R' ∩ (ball 0 R)ᶜ
  have hK : IsCompact K := (isCompact_closedBall 0 R').inter_right isOpen_ball.isClosed_compl
  have hKsub : K ⊆ {y | R ≤ ‖y‖} := fun y hy ↦ by simpa using hy.2
  -- Interior points of the annulus lie outside the closed inner ball.
  have hint : ∀ ⦃y : E⦄, y ∈ interior K → R < ‖y‖ := fun y hy ↦ by
    rw [interior_inter, interior_compl, closure_ball 0 hR.ne'] at hy
    simpa using hy.2
  -- Frontier points of the annulus lie on the outer or the inner sphere.
  have hfront : ∀ ⦃y : E⦄, y ∈ frontier K → ‖y‖ = R' ∨ ‖y‖ = R := fun y hy ↦ by
    rcases frontier_closedBall_sdiff_ball_subset (0 : E) R R' (by rwa [sdiff_eq]) with hy | hy
    · exact .inl (by simpa using hy)
    · exact .inr (by simpa using hy)
  have hyne : ∀ ⦃y : E⦄, y ∈ interior K → y ≠ 0 := fun y hy ↦
    norm_pos_iff.mp (hR.trans (hint hy))
  refine le_of_mul_le_laplacian_le_of_le_frontier (c := V)
    (g := fun y ↦ A * Real.exp (-(c * ‖y‖)) + ε) hK (hcont.mono hKsub) (by fun_prop)
    (fun y hy ↦ hcd y (hint hy))
    (fun y hy ↦ (((contDiffAt_norm ℝ (hyne hy)).const_smul c).neg.exp.const_smul A).add
      contDiffAt_const)
    (fun y hy ↦ (sq_nonneg c).trans (hV y (hint hy))) (fun y hy ↦ hsub y (hint hy))
    (fun y hy ↦ (laplacian_exp_barrier_le hAnn hc hε.le (hyne hy)).trans
      (mul_le_mul_of_nonneg_right (hV y (hint hy)) (by positivity))) (fun y hy ↦ ?_)
    ⟨mem_closedBall_zero_iff.mpr (le_max_right _ _), by simpa using hx⟩
  rcases hfront hy with hy' | hy'
  · have hR₁y : R₁ ≤ ‖y‖ := hy' ▸ le_max_left _ _
    have h₁ : u y ≤ ε := hR₁.2 hR₁y
    have : 0 ≤ A * Real.exp (-(c * ‖y‖)) := by positivity
    linarith
  · have h₁ := hbdry y hy'
    rw [← hbar, hy', sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith

/-- **Exponential decay of subsolutions of `-Δ + c²`.** Let `u` be continuous on the exterior
`‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with `c² u ≤ Δ u` there for some `c ≥ 0`
and `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then
`u x ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_of_sq_mul_le_laplacian {u : E → ℝ} {R c M : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hM : 0 ≤ M) (hcont : ContinuousOn u {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x) (hsub : ∀ x, R < ‖x‖ → c ^ 2 * u x ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) :=
  le_mul_exp_of_mul_le_laplacian (V := fun _ ↦ c ^ 2) hR hc hM hcont hcd (fun _ _ ↦ le_rfl) hsub
    hbdry hlim hx

/-- **Exponential decay of subsolutions of a forced equation.** Let `u` be continuous on the
exterior `‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with
`V u - G exp (-c ‖x‖) ≤ Δ u` there for a potential `V ≥ c² + δ`, where `c > 0`, `δ > 0` and
`G ≥ 0`, and with `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then
`u x ≤ M exp (-c (‖x‖ - R)) + (G / δ) exp (-c ‖x‖)` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_add_mul_exp_of_mul_sub_le_laplacian {u V : E → ℝ} {R c δ M G : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hδ : 0 < δ) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hcont : ContinuousOn u {x | R ≤ ‖x‖}) (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x)
    (hV : ∀ x, R < ‖x‖ → c ^ 2 + δ ≤ V x)
    (hsub : ∀ x, R < ‖x‖ → V x * u x - G * Real.exp (-(c * ‖x‖)) ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) + G / δ * Real.exp (-(c * ‖x‖)) := by
  set A := G / δ with hA
  have hA₀ : 0 ≤ A := by positivity
  have hGA : G = δ * A := by rw [hA]; field_simp
  -- Subtracting the barrier `A exp (-c ‖x‖)` removes the forcing.
  set b : E → ℝ := fun y ↦ A * Real.exp (-(c * ‖y‖)) + 0
  have hbcd : ∀ y : E, y ≠ 0 → ContDiffAt ℝ 2 b y := fun y hy ↦
    (((contDiffAt_norm ℝ hy).const_smul c).neg.exp.const_smul A).add contDiffAt_const
  have hwcd : ∀ y, R < ‖y‖ → ContDiffAt ℝ 2 (u - b) y := fun y hy ↦
    (hcd y hy).sub (hbcd y (norm_pos_iff.mp (hR.trans hy)))
  have hbnn : ∀ y, 0 ≤ b y := fun y ↦ by positivity
  have hw := le_mul_exp_of_mul_le_laplacian (u := u - b) (V := V) hR hc.le hM
    (hcont.sub (fun y hy ↦ (hbcd y (norm_pos_iff.mp
      (hR.trans_le hy))).continuousAt.continuousWithinAt)) hwcd
    (fun y hy ↦ by nlinarith [hV y hy])
    (fun y hy ↦ by
      have hy₀ : y ≠ 0 := norm_pos_iff.mp (hR.trans hy)
      have hlap := laplacian_exp_barrier_le hA₀ hc.le le_rfl hy₀
      have he : 0 < Real.exp (-(c * ‖y‖)) := Real.exp_pos _
      rw [(hcd y hy).laplacian_sub (hbcd y hy₀)]
      have hVy := hV y hy
      have hsy := hsub y hy
      have hGe : G * Real.exp (-(c * ‖y‖)) = δ * (A * Real.exp (-(c * ‖y‖))) := by
        rw [hGA]; ring
      simp only [b, add_zero, Pi.sub_apply] at hlap ⊢
      nlinarith [mul_nonneg (mul_nonneg hA₀ he.le) (sub_nonneg.2 hVy)])
    (fun y hy ↦ by
      have := hbdry y hy
      simp only [Pi.sub_apply]
      linarith [hbnn y])
    (by
      have hb : Tendsto b (cocompact E) (𝓝 (A * 0 + 0)) :=
        ((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_norm_cocompact_atTop.const_mul_atTop hc))).const_mul A).add_const 0
      exact (by simpa using hlim.sub hb : Tendsto (fun y ↦ u y - b y) (cocompact E) (𝓝 0))) hx
  simp only [Pi.sub_apply, b, add_zero] at hw
  linarith

/-- **Exponential decay of vector-valued solutions of a forced equation.** Let `D` be a map into a
real normed space, continuous on the exterior `‖x‖ ≥ R` of a ball of radius `R > 0` and `C²` on
`‖x‖ > R`, solving `Δ D = V • D + H` there for a potential `V ≥ c² + δ`, where `c > 0` and
`δ > 0`, and a forcing with `‖H x‖ ≤ G exp (-c ‖x‖)`. If `D → 0` at infinity and `‖D‖ ≤ M` on the
sphere `‖x‖ = R`, then `‖D x‖ ≤ M exp (-c (‖x‖ - R)) + (G / δ) exp (-c ‖x‖)` for `‖x‖ ≥ R`. -/
theorem norm_le_mul_exp_add_mul_exp_of_laplacian_eq {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {D H : E → B} {V : E → ℝ} {R c δ M G : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hcont : ContinuousOn D {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 D x) (hV : ∀ x, R < ‖x‖ → c ^ 2 + δ ≤ V x)
    (heq : ∀ x, R < ‖x‖ → Δ D x = V x • D x + H x)
    (hH : ∀ x, R < ‖x‖ → ‖H x‖ ≤ G * Real.exp (-(c * ‖x‖)))
    (hbdry : ∀ x, ‖x‖ = R → ‖D x‖ ≤ M) (hlim : Tendsto D (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    ‖D x‖ ≤ M * Real.exp (-(c * (‖x‖ - R))) + G / δ * Real.exp (-(c * ‖x‖)) := by
  -- Each functional `φ` of norm `‖φ‖` turns `D` into a forced scalar subsolution.
  have hscalar (φ : StrongDual ℝ B) : φ (D x) ≤
      (M * Real.exp (-(c * (‖x‖ - R))) + G / δ * Real.exp (-(c * ‖x‖))) * ‖φ‖ := by
    have h := le_mul_exp_add_mul_exp_of_mul_sub_le_laplacian (u := φ ∘ D) (V := V)
      (M := M * ‖φ‖) (G := G * ‖φ‖) hR hc hδ (by positivity) (by positivity)
      (φ.continuous.comp_continuousOn hcont) (fun y hy ↦ φ.contDiff.contDiffAt.comp y (hcd y hy))
      hV (fun y hy ↦ by
        rw [(hcd y hy).laplacian_CLM_comp_left]
        simp only [Function.comp_apply]
        rw [heq y hy, map_add, map_smul, smul_eq_mul]
        have h₁ : -(G * ‖φ‖ * Real.exp (-(c * ‖y‖))) ≤ φ (H y) := by
          have := (le_abs_self (-(φ (H y)))).trans ((abs_neg _).trans_le (φ.le_opNorm (H y)))
          have h₂ := mul_le_mul_of_nonneg_left (hH y hy) (norm_nonneg φ)
          nlinarith
        linarith)
      (fun y hy ↦ (le_abs_self _).trans ((φ.le_opNorm (D y)).trans
        (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hbdry y hy) (norm_nonneg φ))))
      (by simpa using (φ.continuous.tendsto 0).comp hlim) hx
    simp only [Function.comp_apply] at h
    calc φ (D x) ≤ _ := h
      _ = _ := by field_simp
  refine NormedSpace.norm_le_dual_bound ℝ (D x) (by positivity) fun φ ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, hscalar φ⟩
  have := hscalar (-φ)
  rw [neg_apply, norm_neg] at this
  linarith

end TauCeti
