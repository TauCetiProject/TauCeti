/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple

/-!
# The comparison principle and Dirichlet uniqueness for the Laplacian

`TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple` proves the weak maximum
principle: a continuous, `C²`, subharmonic (`0 ≤ Δ f`) function on a compact set is bounded on all
of `K` by any bound it respects on `frontier K`. This file turns that one-sided statement into the
two-function **comparison principle** and its consequence, **uniqueness for the Dirichlet problem**.

Applied to the difference `f - g`, the weak maximum principle says: if `Δ g ≤ Δ f` on the interior
and `f ≤ g` on the frontier, then `f ≤ g` throughout `K`. Comparing in both directions gives that a
solution of the Poisson equation `Δ u = h` in `interior K` is determined on all of `K` by its
boundary values on `frontier K`; specialized to `h = 0` this is uniqueness of the Dirichlet problem
for the Laplace equation. The maximum and minimum of a harmonic function are attained on the
frontier, so a harmonic function is bounded by the supremum of `|·|` over `frontier K`.

## Main declarations

* `TauCeti.le_of_laplacian_le_of_le_frontier`: **comparison principle**. If `Δ g ≤ Δ f` on the
  interior of a compact set and `f ≤ g` on its frontier, then `f ≤ g` on all of `K`.
* `TauCeti.eqOn_of_laplacian_eqOn_of_eqOn_frontier`: **uniqueness for the Poisson equation**. Two
  functions with the same Laplacian on the interior and the same boundary values agree on `K`.
* `TauCeti.eqOn_of_harmonicOnNhd_of_eqOn_frontier`: **uniqueness of the Dirichlet problem** for the
  Laplace equation: two harmonic functions with the same boundary values agree on `K`.
* `TauCeti.exists_mem_frontier_isMaxOn_of_harmonicOnNhd` /
  `TauCeti.exists_mem_frontier_isMinOn_of_harmonicOnNhd`: a harmonic function attains its
  maximum and its minimum on the frontier.
* `TauCeti.abs_le_of_harmonicOnNhd_of_abs_le_frontier`: a harmonic function is bounded on `K` by any
  bound its absolute value respects on `frontier K`.
* `TauCeti.abs_le_add_mul_sq_div_of_abs_laplacian_le`: a function with `|Δ u| ≤ C` on a ball of
  radius `R` and `|u| ≤ ε` outside it is bounded by `ε + C R² / (2 dim E)`.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Nontrivial

variable [Nontrivial E] {K : Set E} {f g : E → ℝ}

/-- **Comparison principle for the Laplacian.**

Let `K` be compact, and let `f`, `g` be continuous on `K` and `C²` on `interior K`. If `f` is at
least as subharmonic as `g` there (`Δ g ≤ Δ f`) and `f ≤ g` on `frontier K`, then `f ≤ g` on all of
`K`. This is the two-function form of the weak maximum principle
`le_of_laplacian_nonneg_le_frontier`, applied to the difference `f - g`. -/
theorem le_of_laplacian_le_of_le_frontier (hK : IsCompact K)
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ g x ≤ Δ f x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hxK
  -- Bound the difference `f - g` above by `0` via the weak maximum principle.
  have hdiff : ∀ ⦃y⦄, y ∈ K → (f - g) y ≤ 0 :=
    le_of_laplacian_nonneg_le_frontier hK (hfcont.sub hgcont)
      (fun y hy => (hfcd hy).sub (hgcd hy))
      (fun y hy => by
        rw [(hfcd hy).laplacian_sub (hgcd hy)]
        linarith [hlap hy])
      (fun y hy => by
        rw [Pi.sub_apply]
        linarith [hbdry hy])
  have := hdiff hxK
  rw [Pi.sub_apply] at this
  linarith

/-- **Uniqueness for the Poisson equation.**

If `f` and `g` are continuous on a compact set `K`, `C²` on `interior K` with the *same* Laplacian
there, and agree on `frontier K`, then they agree on all of `K`. A solution of `Δ u = h` in
`interior K` is thus determined by its boundary values. -/
theorem eqOn_of_laplacian_eqOn_of_eqOn_frontier (hK : IsCompact K)
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x = Δ g x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x = g x) :
    Set.EqOn f g K := by
  intro x hxK
  refine le_antisymm ?_ ?_
  · exact le_of_laplacian_le_of_le_frontier hK hfcont hgcont hfcd hgcd
      (fun y hy => (hlap hy).ge) (fun y hy => (hbdry hy).le) hxK
  · exact le_of_laplacian_le_of_le_frontier hK hgcont hfcont hgcd hfcd
      (fun y hy => (hlap hy).le) (fun y hy => (hbdry hy).ge) hxK

end Nontrivial

section Harmonic

variable [Nontrivial E] {K : Set E} {f g : E → ℝ}

omit [Nontrivial E] in
/-- The Laplacian of a function harmonic near `x` vanishes at `x`. -/
private theorem laplacian_eq_zero_of_harmonicAt {x : E} (hf : HarmonicAt f x) : Δ f x = 0 := by
  simpa using hf.2.self_of_nhds

/-- **Uniqueness of the Dirichlet problem for the Laplace equation.**

Two functions that are harmonic on the interior of a compact set `K`, continuous on `K`, and equal
on `frontier K` are equal on all of `K`. -/
theorem eqOn_of_harmonicOnNhd_of_eqOn_frontier (hK : IsCompact K)
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hf : HarmonicOnNhd f (interior K)) (hg : HarmonicOnNhd g (interior K))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x = g x) :
    Set.EqOn f g K :=
  eqOn_of_laplacian_eqOn_of_eqOn_frontier hK hfcont hgcont
    (fun x hx => (hf x hx).1) (fun x hx => (hg x hx).1)
    (fun x hx => by
      rw [laplacian_eq_zero_of_harmonicAt (hf x hx), laplacian_eq_zero_of_harmonicAt (hg x hx)])
    hbdry

variable (hK : IsCompact K) (hne : K.Nonempty)
  (hcont : ContinuousOn f K) (hf : HarmonicOnNhd f (interior K))

include hK hne hcont hf

/-- A function harmonic on the interior of a nonempty compact set and continuous on `K` attains its
maximum on `frontier K`. -/
theorem exists_mem_frontier_isMaxOn_of_harmonicOnNhd : ∃ x ∈ frontier K, IsMaxOn f K x :=
  exists_mem_frontier_isMaxOn_of_laplacian_nonneg hK hne hcont
    (fun x hx => (hf x hx).1) (fun x hx => (laplacian_eq_zero_of_harmonicAt (hf x hx)).ge)

/-- A function harmonic on the interior of a nonempty compact set and continuous on `K` attains its
minimum on `frontier K`. -/
theorem exists_mem_frontier_isMinOn_of_harmonicOnNhd : ∃ x ∈ frontier K, IsMinOn f K x :=
  exists_mem_frontier_isMinOn_of_laplacian_nonpos hK hne hcont
    (fun x hx => (hf x hx).1) (fun x hx => (laplacian_eq_zero_of_harmonicAt (hf x hx)).le)

end Harmonic

section Bound

variable [Nontrivial E] {K : Set E} {f : E → ℝ} {M : ℝ}

/-- A function harmonic on the interior of a compact set `K` and continuous on `K` is bounded on all
of `K` by any bound `M` its absolute value respects on `frontier K`. This is the two-sided
consequence of the maximum principle for harmonic functions. -/
theorem abs_le_of_harmonicOnNhd_of_abs_le_frontier (hK : IsCompact K)
    (hcont : ContinuousOn f K) (hf : HarmonicOnNhd f (interior K))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M := by
  intro x hxK
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · exact ge_of_laplacian_nonpos_ge_frontier hK hcont (fun y hy => (hf y hy).1)
      (fun y hy => (laplacian_eq_zero_of_harmonicAt (hf y hy)).le)
      (fun y hy => (abs_le.mp (hbdry hy)).1) hxK
  · exact le_of_laplacian_nonneg_le_frontier hK hcont (fun y hy => (hf y hy).1)
      (fun y hy => (laplacian_eq_zero_of_harmonicAt (hf y hy)).ge)
      (fun y hy => (abs_le.mp (hbdry hy)).2) hxK

end Bound

section BallBound

variable [Nontrivial E] {u : E → ℝ} {C ε R : ℝ}

/-- The barrier `ε + C (R² - ‖y‖²) / (2 dim E)` has Laplacian `-C`. -/
private theorem laplacian_barrier_ball (ε C R : ℝ) (y : E) :
    Δ (fun y : E ↦ (ε + C * (R ^ 2 - ‖y‖ ^ 2) / (2 * Module.finrank ℝ E) : ℝ)) y = -C := by
  have hfun : (fun y : E ↦ (ε + C * (R ^ 2 - ‖y‖ ^ 2) / (2 * Module.finrank ℝ E) : ℝ)) =
      (fun _ ↦ ε + C * R ^ 2 / (2 * Module.finrank ℝ E)) +
        (-(C / (2 * Module.finrank ℝ E))) • fun y : E ↦ ‖y‖ ^ 2 := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : ContDiffAt ℝ 2 ((-(C / (2 * Module.finrank ℝ E))) • fun y : E ↦ ‖y‖ ^ 2) y :=
    contDiffAt_const.smul (contDiff_norm_sq ℝ).contDiffAt
  have : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [hfun, contDiffAt_const.laplacian_add h2, laplacian_smul _ (contDiff_norm_sq ℝ).contDiffAt]
  simp [laplacian_norm_sq]
  field_simp

/-- **A bounded Laplacian and smallness outside a ball bound a function.** Let `u` be continuous
on the closed ball of radius `R ≥ 0` about the origin and `C²` on the open ball, with `|Δ u| ≤ C`
there, and suppose `|u| ≤ ε` wherever `‖x‖ ≥ R`. Then `|u| ≤ ε + C R² / (2 dim E)` everywhere.
-/
theorem abs_le_add_mul_sq_div_of_abs_laplacian_le (hR : 0 ≤ R)
    (hcont : ContinuousOn u (Metric.closedBall 0 R))
    (hu : ∀ x ∈ Metric.ball (0 : E) R, ContDiffAt ℝ 2 u x)
    (hΔ : ∀ x ∈ Metric.ball (0 : E) R, |Δ u x| ≤ C) (hout : ∀ x, R ≤ ‖x‖ → |u x| ≤ ε) (x : E) :
    |u x| ≤ ε + C * R ^ 2 / (2 * Module.finrank ℝ E) := by
  rcases hR.eq_or_lt with rfl | hR
  · simpa using hout x (norm_nonneg x)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hΔ 0 (by simpa using hR))
  rcases lt_or_ge ‖x‖ R with hx | hx
  swap
  · -- Outside the open ball the bound is the hypothesis, as `C ≥ 0`.
    exact (hout x hx).trans (le_add_of_nonneg_right (by positivity))
  have hxb : x ∈ Metric.ball (0 : E) R := by simpa using hx
  have hd : (0 : ℝ) < 2 * Module.finrank ℝ E := by
    have := Module.finrank_pos (R := ℝ) (M := E)
    positivity
  -- The barrier `g y = ε + C (R² - ‖y‖²) / (2 dim E)` has `Δ g = -C`.
  set g : E → ℝ := fun y ↦ ε + C * (R ^ 2 - ‖y‖ ^ 2) / (2 * Module.finrank ℝ E) with hg
  have hgd : ContDiff ℝ 2 g :=
    contDiff_const.add ((contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))).div_const _)
  have hgΔ (y : E) : Δ g y = -C := laplacian_barrier_ball ε C R y
  have hK : IsCompact (Metric.closedBall (0 : E) R) := isCompact_closedBall 0 R
  have hfr {y : E} (hy : y ∈ frontier (Metric.closedBall (0 : E) R)) : ‖y‖ = R := by
    simpa using Metric.frontier_closedBall_subset_sphere hy
  have hgfr {y : E} (hy : y ∈ frontier (Metric.closedBall (0 : E) R)) : g y = ε := by
    simp [hg, hfr hy]
  have hint : interior (Metric.closedBall (0 : E) R) = Metric.ball 0 R := interior_closedBall' 0 R
  have hxK : x ∈ Metric.closedBall (0 : E) R := Metric.ball_subset_closedBall hxb
  -- A function with `Δ v ≥ -C` on the ball and `v ≤ ε` outside it lies below the barrier.
  have hside (v : E → ℝ) (hvc : ContinuousOn v (Metric.closedBall 0 R))
      (hv : ∀ y ∈ Metric.ball (0 : E) R, ContDiffAt ℝ 2 v y)
      (hvΔ : ∀ y ∈ Metric.ball (0 : E) R, -C ≤ Δ v y) (hvout : ∀ y, R ≤ ‖y‖ → v y ≤ ε) :
      v x ≤ g x :=
    le_of_laplacian_le_of_le_frontier hK hvc hgd.continuous.continuousOn
      (fun y hy ↦ hv y (hint ▸ hy)) (fun y _ ↦ hgd.contDiffAt)
      (fun y hy ↦ by rw [hgΔ]; exact hvΔ y (hint ▸ hy))
      (fun y hy ↦ (hvout y (hfr hy).ge).trans (hgfr hy).ge) hxK
  have hup : u x ≤ g x := hside u hcont hu (fun y hy ↦ neg_le_of_abs_le (hΔ y hy))
    (fun y hy ↦ (le_abs_self _).trans (hout y hy))
  have hlo : -u x ≤ g x := hside (-u) hcont.neg (fun y hy ↦ (hu y hy).neg)
    (fun y hy ↦ by
      rw [laplacian_neg, Pi.neg_apply, neg_le_neg_iff]
      exact le_of_abs_le (hΔ y hy))
    (fun y hy ↦ (neg_le_abs _).trans (hout y hy))
  have hgx : g x ≤ ε + C * R ^ 2 / (2 * Module.finrank ℝ E) := by
    simp only [hg]
    gcongr
    nlinarith [norm_nonneg x]
  exact abs_le.2 ⟨by linarith, hup.trans hgx⟩

end BallBound

end TauCeti

end

end
