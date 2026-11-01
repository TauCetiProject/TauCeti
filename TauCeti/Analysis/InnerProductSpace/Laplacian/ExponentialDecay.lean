/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

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

This is the decay mechanism of massive fields: for instance, outside a large disc the logarithmic
modulus defect `-log |α|²` of a plane vortex is such a subsolution for every rate `c < 1 / 2`.

## Main declarations

* `TauCeti.le_mul_exp_of_sq_mul_le_laplacian`: a subsolution of `-Δ + c²` on the exterior of a ball
  which tends to zero at infinity is bounded by `M exp (-c (‖x‖ - R))`.

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

/-- **Exponential decay of subsolutions of `-Δ + c²`.** Let `u` be continuous on the exterior
`‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with `c² u ≤ Δ u` there for some `c ≥ 0`
and `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then
`u x ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_of_sq_mul_le_laplacian {u : E → ℝ} {R c M : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hM : 0 ≤ M) (hcont : ContinuousOn u {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x) (hsub : ∀ x, R < ‖x‖ → c ^ 2 * u x ≤ Δ u x)
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
    rcases frontier_inter_subset _ _ hy with ⟨hy₁, -⟩ | ⟨-, hy₂⟩
    · exact .inl (by simpa using frontier_closedBall_subset_sphere hy₁)
    · rw [frontier_compl, frontier_ball 0 hR.ne'] at hy₂
      exact .inr (by simpa using hy₂)
  have hyne : ∀ ⦃y : E⦄, y ∈ interior K → y ≠ 0 := fun y hy ↦
    norm_pos_iff.mp (hR.trans (hint hy))
  refine le_of_mul_le_laplacian_le_of_le_frontier (c := fun _ ↦ c ^ 2)
    (g := fun y ↦ A * Real.exp (-(c * ‖y‖)) + ε) hK (hcont.mono hKsub) (by fun_prop)
    (fun y hy ↦ hcd y (hint hy))
    (fun y hy ↦ (((contDiffAt_norm ℝ (hyne hy)).const_smul c).neg.exp.const_smul A).add
      contDiffAt_const)
    (fun _ _ ↦ sq_nonneg c) (fun y hy ↦ hsub y (hint hy))
    (fun y hy ↦ laplacian_exp_barrier_le hAnn hc hε.le (hyne hy)) (fun y hy ↦ ?_)
    ⟨mem_closedBall_zero_iff.mpr (le_max_right _ _), by simpa using hx⟩
  rcases hfront hy with hy' | hy'
  · have hR₁y : R₁ ≤ ‖y‖ := hy' ▸ le_max_left _ _
    have h₁ : u y ≤ ε := hR₁.2 hR₁y
    have : 0 ≤ A * Real.exp (-(c * ‖y‖)) := by positivity
    linarith
  · have h₁ := hbdry y hy'
    rw [← hbar, hy', sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith

end TauCeti
