/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.NormPow

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

/-- The exponential barrier `A exp (-c t) + ε` of the comparison argument, as a radial profile. -/
private theorem deriv_exp_barrier (A c ε : ℝ) :
    deriv (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) = fun t ↦ -(c * (A * Real.exp (-(c * t)))) :=
  funext fun t ↦ by
    have h : HasDerivAt (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε)
        (A * (Real.exp (-(c * t)) * -(c * 1))) t :=
      (((hasDerivAt_id t).const_mul c).neg.exp.const_mul A).add_const ε
    rw [h.deriv]
    ring

/-- The barrier `A exp (-c ‖x‖) + ε` is a supersolution of `-Δ + c²` away from the origin when
`A ≥ 0`, `c ≥ 0` and `ε ≥ 0`. -/
private theorem laplacian_exp_barrier_le {A c ε : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ A * Real.exp (-(c * ‖y‖)) + ε) x ≤
      c ^ 2 * (A * Real.exp (-(c * ‖x‖)) + ε) := by
  have hF : ContDiffAt ℝ 2 (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) ‖x‖ := by fun_prop
  have hdd : deriv (deriv fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) =
      fun t ↦ c ^ 2 * (A * Real.exp (-(c * t))) := by
    rw [deriv_exp_barrier]
    funext t
    have h := deriv_exp_barrier (-(c * A)) c 0
    simp only [add_zero] at h
    rw [show (fun t : ℝ ↦ -(c * (A * Real.exp (-(c * t))))) =
      fun t ↦ -(c * A) * Real.exp (-(c * t)) by funext; ring, h]
    ring
  rw [hF.laplacian_comp_norm hx, hdd, deriv_exp_barrier]
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

omit [FiniteDimensional ℝ E] in
/-- On the closed annulus `R ≤ ‖x‖ ≤ R'`, with `0 < R`, interior points have `R < ‖x‖` and
frontier points lie on one of the two spheres. -/
private theorem annulus_interior_frontier {R R' : ℝ} (hR : 0 < R) :
    (∀ ⦃x : E⦄, x ∈ interior (closedBall 0 R' ∩ {y | R ≤ ‖y‖}) → R < ‖x‖) ∧
      ∀ ⦃x : E⦄, x ∈ frontier (closedBall 0 R' ∩ {y | R ≤ ‖y‖}) → ‖x‖ = R' ∨ ‖x‖ = R := by
  have hcompl : {y : E | R ≤ ‖y‖} = (ball 0 R)ᶜ := by
    ext y
    simp
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' := interior_mono inter_subset_right hx
    rw [hcompl, interior_compl, closure_ball 0 hR.ne'] at hx'
    simpa using hx'
  · rcases frontier_inter_subset _ _ hx with ⟨hx₁, -⟩ | ⟨-, hx₂⟩
    · exact .inl (by simpa using frontier_closedBall_subset_sphere hx₁)
    · rw [hcompl, frontier_compl] at hx₂
      exact .inr (by simpa using frontier_ball_subset_sphere hx₂)

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
    rw [hA, mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hbar]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Beyond some radius `R₁`, `u ≤ ε`; compare on the annulus `R ≤ ‖y‖ ≤ max R₁ ‖x‖`.
  obtain ⟨R₁, hR₁⟩ := (hasBasis_cobounded_norm.eventually_iff).mp
    (cobounded_eq_cocompact (α := E) ▸ hlim.eventually (eventually_le_nhds hε))
  set R' := max R₁ ‖x‖
  set K := closedBall (0 : E) R' ∩ {y | R ≤ ‖y‖}
  have hK : IsCompact K := (isCompact_closedBall 0 R').inter_right (isClosed_le
    continuous_const continuous_norm)
  have hKsub : K ⊆ {y | R ≤ ‖y‖} := inter_subset_right
  obtain ⟨hint, hfront⟩ := annulus_interior_frontier (E := E) (R' := R') hR
  have hyne : ∀ ⦃y : E⦄, y ∈ interior K → y ≠ 0 := fun y hy ↦
    norm_pos_iff.mp (hR.trans (hint hy))
  refine le_of_mul_le_laplacian_le_of_le_frontier (c := fun _ ↦ c ^ 2)
    (g := fun y ↦ A * Real.exp (-(c * ‖y‖)) + ε) hK (hcont.mono hKsub) (by fun_prop)
    (fun y hy ↦ hcd y (hint hy))
    (fun y hy ↦ (((contDiffAt_norm ℝ (hyne hy)).const_smul c).neg.exp.const_smul A).add
      contDiffAt_const)
    (fun _ _ ↦ sq_nonneg c) (fun y hy ↦ hsub y (hint hy))
    (fun y hy ↦ laplacian_exp_barrier_le hAnn hc hε.le (hyne hy)) (fun y hy ↦ ?_)
    ⟨mem_closedBall_zero_iff.mpr (le_max_right _ _), hx⟩
  rcases hfront hy with hy' | hy'
  · have h₁ : u y ≤ ε := hR₁.2 (show R₁ ≤ ‖y‖ from hy' ▸ le_max_left _ _)
    have : 0 ≤ A * Real.exp (-(c * ‖y‖)) := by positivity
    linarith
  · have h₁ := hbdry y hy'
    rw [← hbar, hy', sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith

end TauCeti
