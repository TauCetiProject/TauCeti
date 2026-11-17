/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.ODE.Gronwall
import TauCeti.Algebra.Order.Floor.Semifield

/-!
# Two-step error estimate for Moreau–Yosida minimizing movements

Let `φ : X → EReal` be an energy on a pseudometric space and `m : ℝ`. Given two minimizing movement
sequences `U` (step `τ > 0`) and `V` (step `η > 0`) of `φ` with real energies under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` (Ambrosio–Gigli–Savaré,
Assumption 4.0.1), this file proves the quantitative two-time-step comparison bound
`TauCeti.dist_ceil_sq_le_of_penalizedConvex` (Ambrosio–Gigli–Savaré, Theorem 4.0.4 / Section 4.1).

Interpolating the matrix `a_{n,k} = d(U n, V k)² / 2` bilinearly across the product grid
`[n τ, (n + 1) τ] × [k η, (k + 1) η]` produces a continuous function `B(t)` whose right derivative
on `[0, ∞)` is a convex combination of difference quotients in `n` and `k`. Summing the four
one-step discrete variational inequalities
(`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent`) cancels the cross-evaluated
energies identically into `α_n(t) (φ(U n) - φ(U (n + 1))) + β_k(t) (φ(V k) - φ(V (k + 1)))`, while
the one-step dissipations `-d(U n, U (n + 1))² / (2τ)` and `-d(V k, V (k + 1))² / (2η)` absorb the
metric shift terms coming from `-m`. Integrating by Grönwall's inequality bounds
`d(U ⌈t / τ⌉₊, V ⌈t / η⌉₊)²` in terms of `d(U 0, V 0)²` and `(τ + η)` times the energy dissipated
up to steps `⌊t / τ⌋₊ + 1` and `⌊t / η⌋₊ + 1`.

## Main results

* `TauCeti.dist_ceil_sq_le_of_penalizedConvex`: quantitative two-step error bound between two
  minimizing movement sequences under penalized convexity.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Section 4.1.
-/

public section

noncomputable section

open Set Topology Real
open scoped NNReal

namespace TauCeti

/-! ### Piecewise smooth functions on a uniform time grid -/

section PiecewiseStep

/-- Glues a family of real functions `g n` along the uniform grid `[n τ, (n + 1) τ)` via the floor
index `⌊t / τ⌋₊`. -/
private def piecewiseStep (τ : ℝ) (g : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  g ⌊t / τ⌋₊ t

/-- When adjacent pieces agree at `(n + 1) τ`, `piecewiseStep τ g` agrees with `g n` on the entire
closed interval `[n τ, (n + 1) τ]`. -/
private theorem piecewiseStep_eq_of_mem_Icc {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → ℝ}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ)) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    piecewiseStep τ g t = g n t := by
  rcases ht.2.eq_or_lt with rfl | hlt
  · have hfl : ⌊(((n : ℝ) + 1) * τ) / τ⌋₊ = n + 1 := by
      rw [mul_div_cancel_right₀ _ hτ.ne', ← Nat.cast_add_one, Nat.floor_natCast]
    simp [piecewiseStep, hfl, hjoin n]
  · have ht0 : 0 ≤ t / τ := div_nonneg ((mul_nonneg n.cast_nonneg hτ.le).trans ht.1) hτ.le
    have hfl : ⌊t / τ⌋₊ = n :=
      (Nat.floor_eq_iff ht0).2 ⟨(le_div_iff₀ hτ).2 ht.1, (div_lt_iff₀ hτ).2 hlt⟩
    simp [piecewiseStep, hfl]

/-- A `piecewiseStep` function whose pieces are continuous on `[n τ, (n + 1) τ]` and match at the
grid points is continuous on `[0, ∞)`. -/
private theorem continuousOn_piecewiseStep {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → ℝ}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    (hcont : ∀ n : ℕ, ContinuousOn (g n) (Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))) :
    ContinuousOn (piecewiseStep τ g) (Ici 0) := by
  have hcongr (k : ℕ) : ContinuousOn (piecewiseStep τ g) (Icc ((k : ℝ) * τ) (((k : ℝ) + 1) * τ)) :=
    (hcont k).congr fun s hs ↦ piecewiseStep_eq_of_mem_Icc hτ hjoin k hs
  intro t ht
  set n := ⌊t / τ⌋₊
  have hmem : t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := mem_Ico_floor_mul hτ ht
  have hright : ContinuousWithinAt (piecewiseStep τ g) (Ici t) t :=
    (hcongr n t (Ico_subset_Icc_self hmem)).mono_of_mem_nhdsWithin <|
      mem_nhdsWithin.2 ⟨Iio (((n : ℝ) + 1) * τ), isOpen_Iio, hmem.2,
        fun _ hs ↦ ⟨hmem.1.trans hs.2, hs.1.le⟩⟩
  rcases hmem.1.eq_or_lt with heq | hlt
  · rcases n with _ | m
    · simpa [← heq] using hright
    · have heq' : ((m : ℝ) + 1) * τ = t := by push_cast at heq; exact heq
      have hm_lt : (m : ℝ) * τ < t := by rw [← heq']; linarith
      have hleft : ContinuousWithinAt (piecewiseStep τ g) (Iic t) t :=
        (hcongr m t ⟨hm_lt.le, heq'.symm.le⟩).mono_of_mem_nhdsWithin <|
          mem_nhdsWithin.2 ⟨Ioi ((m : ℝ) * τ), isOpen_Ioi, hm_lt,
            fun _ hs ↦ ⟨hs.1.le, hs.2.trans_eq heq'.symm⟩⟩
      exact (continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩).continuousWithinAt
  · exact ((hcongr n).continuousAt (Icc_mem_nhds hlt hmem.2)).continuousWithinAt

/-- Right-hand derivative of `piecewiseStep τ g` at `t ≥ 0`. -/
private theorem hasDerivWithinAt_piecewiseStep {τ : ℝ} (hτ : 0 < τ) {g g' : ℕ → ℝ → ℝ}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    (hderiv : ∀ (n : ℕ), ∀ t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ),
      HasDerivWithinAt (g n) (g' n t) (Ici t) t)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (piecewiseStep τ g) (g' ⌊t / τ⌋₊ t) (Ici t) t := by
  set n := ⌊t / τ⌋₊
  have hmem : t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := mem_Ico_floor_mul hτ ht
  have hev : piecewiseStep τ g =ᶠ[𝓝[Ici t] t] g n := by
    filter_upwards [mem_nhdsWithin.2 ⟨Iio (((n : ℝ) + 1) * τ), isOpen_Iio, hmem.2,
      Subset.rfl⟩] with s hs
    exact piecewiseStep_eq_of_mem_Icc hτ hjoin n ⟨hmem.1.trans hs.2, hs.1.le⟩
  exact (hderiv n t hmem).congr_of_eventuallyEq_of_mem hev self_mem_Ici

/-- Barycentric weight `((n + 1) τ - t) / τ` on `[n τ, (n + 1) τ]`. -/
private def stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (((n : ℝ) + 1) * τ - t) / τ

private theorem stepWeight_succ_mul {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    stepWeight τ n (((n : ℝ) + 1) * τ) = 0 ∧ stepWeight τ (n + 1) (((n : ℝ) + 1) * τ) = 1 :=
  ⟨by simp [stepWeight], by simp only [stepWeight, Nat.cast_add, Nat.cast_one]; field_simp; ring⟩

private theorem stepWeight_mem_Icc {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    stepWeight τ ⌊t / τ⌋₊ t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := mem_Ico_floor_mul hτ ht
  exact ⟨div_nonneg (sub_nonneg.2 h2.le) hτ.le, (div_le_one hτ).2 (by linarith)⟩

private theorem hasDerivAt_stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (stepWeight τ n) (-τ⁻¹) t :=
  (((hasDerivAt_id t).const_sub (((n : ℝ) + 1) * τ)).div_const τ).congr_deriv
    (by simp [neg_div, one_div])

/-- Piecewise linear interpolant of a sequence `c : ℕ → ℝ` with step `τ`. -/
private def linInterp (τ : ℝ) (c : ℕ → ℝ) : ℝ → ℝ :=
  piecewiseStep τ fun n t ↦ stepWeight τ n t * c n + (1 - stepWeight τ n t) * c (n + 1)

private theorem linInterp_apply {τ t : ℝ} (c : ℕ → ℝ) :
    linInterp τ c t =
      stepWeight τ ⌊t / τ⌋₊ t * c ⌊t / τ⌋₊ + (1 - stepWeight τ ⌊t / τ⌋₊ t) * c (⌊t / τ⌋₊ + 1) :=
  rfl

private theorem continuousOn_linInterp {τ : ℝ} (hτ : 0 < τ) (c : ℕ → ℝ) :
    ContinuousOn (linInterp τ c) (Ici 0) := by
  refine continuousOn_piecewiseStep hτ (fun n ↦ ?_) (fun _ ↦ by unfold stepWeight; fun_prop)
  obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring

private theorem hasDerivWithinAt_linInterp {τ : ℝ} (hτ : 0 < τ) (c : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (linInterp τ c) ((c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊) / τ) (Ici t) t := by
  refine hasDerivWithinAt_piecewiseStep (g' := fun n _ ↦ (c (n + 1) - c n) / τ) hτ
    (fun n ↦ ?_) (fun n s _ ↦ ?_) ht
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring
  · have hd := ((hasDerivAt_stepWeight τ n s).mul_const (c n)).add
      (((hasDerivAt_stepWeight τ n s).const_sub 1).mul_const (c (n + 1)))
    exact (hd.congr_deriv (by field_simp; ring)).hasDerivWithinAt

/-- Bilinear interpolant of `a : ℕ → ℕ → ℝ` with steps `τ` and `η`. -/
private def bilinInterp (τ η : ℝ) (a : ℕ → ℕ → ℝ) : ℝ → ℝ :=
  piecewiseStep η fun k t ↦
    stepWeight η k t * linInterp τ (a · k) t + (1 - stepWeight η k t) * linInterp τ (a · (k + 1)) t

/-- Right-hand derivative formula for `bilinInterp τ η a` on the `k`-th `η`-cell. -/
private def bilinDerivAt (τ η : ℝ) (a : ℕ → ℕ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  stepWeight η k s * (a (⌊s / τ⌋₊ + 1) k - a ⌊s / τ⌋₊ k) / τ +
    (1 - stepWeight η k s) * (a (⌊s / τ⌋₊ + 1) (k + 1) - a ⌊s / τ⌋₊ (k + 1)) / τ +
    stepWeight τ ⌊s / τ⌋₊ s * (a ⌊s / τ⌋₊ (k + 1) - a ⌊s / τ⌋₊ k) / η +
    (1 - stepWeight τ ⌊s / τ⌋₊ s) * (a (⌊s / τ⌋₊ + 1) (k + 1) - a (⌊s / τ⌋₊ + 1) k) / η

private theorem bilinInterp_apply {τ η t : ℝ} (a : ℕ → ℕ → ℝ) :
    bilinInterp τ η a t =
      stepWeight η ⌊t / η⌋₊ t *
        (stepWeight τ ⌊t / τ⌋₊ t * a ⌊t / τ⌋₊ ⌊t / η⌋₊ +
          (1 - stepWeight τ ⌊t / τ⌋₊ t) * a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊) +
      (1 - stepWeight η ⌊t / η⌋₊ t) *
        (stepWeight τ ⌊t / τ⌋₊ t * a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) +
          (1 - stepWeight τ ⌊t / τ⌋₊ t) * a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)) :=
  rfl

private theorem bilinInterp_zero {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → ℝ) :
    bilinInterp τ η a 0 = a 0 0 := by
  simp [bilinInterp_apply, stepWeight, div_self hτ.ne', div_self hη.ne']

private theorem continuousOn_bilinInterp {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → ℝ) :
    ContinuousOn (bilinInterp τ η a) (Ici 0) := by
  refine continuousOn_piecewiseStep hη (fun k ↦ ?_) (fun k ↦ ?_)
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hη k; rw [h1, h2]; ring
  · have hsub : Icc ((k : ℝ) * η) (((k : ℝ) + 1) * η) ⊆ Ici 0 :=
      fun _ hs ↦ (mul_nonneg k.cast_nonneg hη.le).trans hs.1
    have hw : Continuous (stepWeight η k) := by unfold stepWeight; fun_prop
    exact (hw.continuousOn.mul ((continuousOn_linInterp hτ (a · k)).mono hsub)).add
      ((continuousOn_const.sub hw.continuousOn).mul
        ((continuousOn_linInterp hτ (a · (k + 1))).mono hsub))

private theorem hasDerivWithinAt_bilinInterp {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (bilinInterp τ η a) (bilinDerivAt τ η a ⌊t / η⌋₊ t) (Ici t) t := by
  refine hasDerivWithinAt_piecewiseStep (g' := bilinDerivAt τ η a) hη
    (fun k ↦ ?_) (fun k s hs ↦ ?_) ht
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hη k; rw [h1, h2]; ring
  · have hs0 : 0 ≤ s := (mul_nonneg k.cast_nonneg hη.le).trans hs.1
    have hd1 := ((hasDerivAt_stepWeight η k s).hasDerivWithinAt).mul
      (hasDerivWithinAt_linInterp hτ (a · k) hs0)
    have hd2 := (((hasDerivAt_stepWeight η k s).const_sub 1).hasDerivWithinAt).mul
      (hasDerivWithinAt_linInterp hτ (a · (k + 1)) hs0)
    refine (hd1.add hd2).congr_deriv ?_
    simp only [bilinDerivAt, linInterp_apply]
    field_simp
    ring

/-- Piecewise quadratic primitive of `t ↦ stepWeight τ ⌊t / τ⌋₊ t * (e ⌊t / τ⌋₊ - e (⌊t / τ⌋₊ + 1))`
starting at `0`. -/
private def energyPrim (τ : ℝ) (e : ℕ → ℝ) : ℝ → ℝ :=
  piecewiseStep τ fun n t ↦
    (τ / 2) * (e 0 - e (n + 1) + stepWeight τ n t ^ 2 * (e (n + 1) - e n))

private theorem energyPrim_zero {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) : energyPrim τ e 0 = 0 := by
  simp [energyPrim, piecewiseStep, stepWeight, div_self hτ.ne']

private theorem energyPrim_le {τ t : ℝ} (hτ : 0 < τ) {e : ℕ → ℝ} (he : Antitone e) :
    energyPrim τ e t ≤ (τ / 2) * (e 0 - e (⌊t / τ⌋₊ + 1)) := by
  simp only [energyPrim, piecewiseStep]
  have hle : stepWeight τ ⌊t / τ⌋₊ t ^ 2 * (e (⌊t / τ⌋₊ + 1) - e ⌊t / τ⌋₊) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.2 (he (Nat.le_succ _)))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem continuousOn_energyPrim {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) :
    ContinuousOn (energyPrim τ e) (Ici 0) := by
  refine continuousOn_piecewiseStep hτ (fun n ↦ ?_) (fun _ ↦ by unfold stepWeight; fun_prop)
  obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring

private theorem hasDerivWithinAt_energyPrim {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (energyPrim τ e)
      (stepWeight τ ⌊t / τ⌋₊ t * (e ⌊t / τ⌋₊ - e (⌊t / τ⌋₊ + 1))) (Ici t) t := by
  refine hasDerivWithinAt_piecewiseStep (g' := fun n s ↦ stepWeight τ n s * (e n - e (n + 1))) hτ
    (fun n ↦ ?_) (fun n s _ ↦ ?_) ht
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring
  · have hd := ((((hasDerivAt_stepWeight τ n s).pow 2).mul_const
      (e (n + 1) - e n)).const_add (e 0 - e (n + 1))).const_mul (τ / 2)
    exact (hd.congr_deriv (by have := hτ.ne'; field_simp; ring)).hasDerivWithinAt

end PiecewiseStep

/-! ### Discrete two-step error estimate -/

section TwoStepBound

/-- Absorbs one metric shift `α m (d(x, y)² / 2 - d(x', y)² / 2)` into the one-step dissipation
`-d(x, x')² / (2τ)` when `|m| τ ≤ 1 / 2` and `α ∈ [0, 1]`. -/
private theorem mul_half_dist_sq_sub_le {X : Type*} [PseudoMetricSpace X] (x x' y : X)
    {m τ α : ℝ} (hτ : 0 < τ) (hmτ : |m| * τ ≤ 1 / 2) (hα : α ∈ Icc (0 : ℝ) 1) :
    α * m * (dist x y ^ 2 / 2 - dist x' y ^ 2 / 2) - dist x x' ^ 2 / (2 * τ) ≤
      2 * m ^ 2 * τ * (α * (dist x y ^ 2 / 2)) := by
  set d := dist x y; set d' := dist x' y; set Δ := dist x x'
  have hd0 : 0 ≤ d := dist_nonneg
  have hd'0 : 0 ≤ d' := dist_nonneg
  have hdiff : |d ^ 2 - d' ^ 2| ≤ 2 * d * Δ + Δ ^ 2 := by
    have h1 : |d - d'| ≤ Δ := abs_dist_sub_le x x' y
    have h2 : d + d' ≤ 2 * d + Δ := by linarith [dist_triangle_left x' y x]
    calc |d ^ 2 - d' ^ 2| = |d - d'| * (d + d') := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hd0 hd'0), mul_comm]
      _ ≤ Δ * (2 * d + Δ) := mul_le_mul h1 h2 (add_nonneg hd0 hd'0) dist_nonneg
      _ = 2 * d * Δ + Δ ^ 2 := by ring
  have hm_bd : m * (d ^ 2 / 2 - d' ^ 2 / 2) ≤ |m| * d * Δ + |m| * Δ ^ 2 / 2 := by
    have h : m * (d ^ 2 - d' ^ 2) ≤ |m| * (2 * d * Δ + Δ ^ 2) := (le_abs_self _).trans <| by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg m)
    linarith
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 4 * τ)
  have hclear : (α * m * (d ^ 2 / 2 - d' ^ 2 / 2) - Δ ^ 2 / (2 * τ)) * (4 * τ) =
      4 * τ * α * (m * (d ^ 2 / 2 - d' ^ 2 / 2)) - 2 * Δ ^ 2 := by field_simp; ring
  have hα0 : 0 ≤ α := hα.1
  have h1 := mul_le_mul_of_nonneg_left hm_bd (by positivity : 0 ≤ 4 * τ * α)
  have hΔ : 2 * τ * α * |m| * Δ ^ 2 ≤ Δ ^ 2 :=
    (mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2, hmτ, abs_nonneg m] :
      2 * τ * α * |m| ≤ 1) (sq_nonneg Δ)).trans_eq (one_mul _)
  have hαm : 4 * τ ^ 2 * α ^ 2 * |m| ^ 2 * d ^ 2 ≤ 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 := by
    rw [sq_abs]
    have := mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2] : α ^ 2 ≤ α)
      (by positivity : 0 ≤ 4 * τ ^ 2 * m ^ 2 * d ^ 2)
    linarith
  rw [hclear]
  nlinarith [sq_nonneg (Δ - 2 * τ * α * |m| * d), h1, hΔ, hαm]

/-- One-step real-valued discrete variational inequality for `d(U (n + 1), v)² / 2 - d(U n, v)² / 2`
along a minimizing movement sequence with real energies. -/
private theorem div_sub_half_dist_sq_le {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ : ℝ≥0}
    {φ : X → EReal} (h : PenalizedConvex m τ φ) (hτ : 0 < τ) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {eU : ℕ → ℝ}
    (heU : ∀ n, φ (U n) = eU n) {v : X} {ev : ℝ} (hev : φ v = ev) (n : ℕ) :
    (dist (U (n + 1)) v ^ 2 / 2 - dist (U n) v ^ 2 / 2) / τ ≤
      ev - eU (n + 1) - dist (U n) (U (n + 1)) ^ 2 / (2 * τ) -
        m * (dist (U (n + 1)) v ^ 2 / 2) := by
  have hvi := h.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) (hev ▸ EReal.coe_ne_top ev)
  rw [heU (n + 1), hev, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hvi
  have hτr : (0 : ℝ) < τ := hτ
  rw [div_le_iff₀ hτr]
  have := mul_le_mul_of_nonneg_right hvi hτr.le
  field_simp at this ⊢
  linarith

/-- Algebraic four-corner bound combining discrete variational inequalities and metric shift bounds
into the bilinear interpolation derivative estimate. -/
private theorem bilin_deriv_algebraic_le {a₀₀ a₁₀ a₀₁ a₁₁ eU₀ eU₁ eV₀ eV₁ dU dV m τ η α β : ℝ}
    (ha₀₀ : 0 ≤ a₀₀) (ha₁₀ : 0 ≤ a₁₀) (ha₀₁ : 0 ≤ a₀₁) (ha₁₁ : 0 ≤ a₁₁)
    (hτ : 0 ≤ τ) (hη : 0 ≤ η) (hα : α ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hUk : (a₁₀ - a₀₀) / τ ≤ eV₀ - eU₁ - dU - m * a₁₀)
    (hUk1 : (a₁₁ - a₀₁) / τ ≤ eV₁ - eU₁ - dU - m * a₁₁)
    (hVn : (a₀₁ - a₀₀) / η ≤ eU₀ - eV₁ - dV - m * a₀₁)
    (hVn1 : (a₁₁ - a₁₀) / η ≤ eU₁ - eV₁ - dV - m * a₁₁)
    (hs1 : α * m * (a₀₀ - a₁₀) - dU ≤ 2 * m ^ 2 * τ * (α * a₀₀))
    (hs2 : α * m * (a₀₁ - a₁₁) - dU ≤ 2 * m ^ 2 * τ * (α * a₀₁))
    (hs3 : β * m * (a₀₀ - a₀₁) - dV ≤ 2 * m ^ 2 * η * (β * a₀₀))
    (hs4 : β * m * (a₁₀ - a₁₁) - dV ≤ 2 * m ^ 2 * η * (β * a₁₀)) :
    β * (a₁₀ - a₀₀) / τ + (1 - β) * (a₁₁ - a₀₁) / τ +
      α * (a₀₁ - a₀₀) / η + (1 - α) * (a₁₁ - a₁₀) / η ≤
      max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) *
        (β * (α * a₀₀ + (1 - α) * a₁₀) + (1 - β) * (α * a₀₁ + (1 - α) * a₁₁)) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by
  set b := β * (α * a₀₀ + (1 - α) * a₁₀) + (1 - β) * (α * a₀₁ + (1 - α) * a₁₁)
  have hα0 := hα.1; have hα1 := sub_nonneg.2 hα.2
  have hβ0 := hβ.1; have hβ1 := sub_nonneg.2 hβ.2
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hα_le : β * (α * a₀₀) + (1 - β) * (α * a₀₁) ≤ b := by
    have : 0 ≤ β * ((1 - α) * a₁₀) + (1 - β) * ((1 - α) * a₁₁) := by positivity
    dsimp [b]; linarith
  have hbτ := mul_le_mul_of_nonneg_left hα_le (by positivity : 0 ≤ 2 * m ^ 2 * τ)
  have hβ_le : α * (β * a₀₀) + (1 - α) * (β * a₁₀) ≤ b := by
    have : 0 ≤ (1 - β) * (α * a₀₁ + (1 - α) * a₁₁) := by positivity
    dsimp [b]; linarith
  have hbη := mul_le_mul_of_nonneg_left hβ_le (by positivity : 0 ≤ 2 * m ^ 2 * η)
  have hK := mul_le_mul_of_nonneg_right
    (le_max_right 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)) hb0
  have hdecomp : β * (eV₀ - eU₁ - dU - m * a₁₀) + (1 - β) * (eV₁ - eU₁ - dU - m * a₁₁) +
      α * (eU₀ - eV₁ - dV - m * a₀₁) + (1 - α) * (eU₁ - eV₁ - dV - m * a₁₁) =
      -2 * m * b + β * (α * m * (a₀₀ - a₁₀) - dU) + (1 - β) * (α * m * (a₀₁ - a₁₁) - dU) +
        α * (β * m * (a₀₀ - a₀₁) - dV) + (1 - α) * (β * m * (a₁₀ - a₁₁) - dV) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by dsimp [b]; ring
  simp only [mul_div_assoc]
  linarith [hdecomp, hbτ, hbη, hK,
    mul_le_mul_of_nonneg_left hUk hβ0, mul_le_mul_of_nonneg_left hUk1 hβ1,
    mul_le_mul_of_nonneg_left hVn hα0, mul_le_mul_of_nonneg_left hVn1 hα1,
    mul_le_mul_of_nonneg_left hs1 hβ0, mul_le_mul_of_nonneg_left hs2 hβ1,
    mul_le_mul_of_nonneg_left hs3 hα0, mul_le_mul_of_nonneg_left hs4 hα1]

/-- Exponential Grönwall rate for the discrete two-step comparison at time steps `τ` and `η`. -/
private def twoStepRate (m : ℝ) (τ η : ℝ≥0) : ℝ :=
  max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)

/-- Matrix of half-squared distances `d(U n, V k)² / 2` between two discrete trajectories. -/
private def halfDistSq {X : Type*} [PseudoMetricSpace X] (U V : ℕ → X) (n k : ℕ) : ℝ :=
  dist (U n) (V k) ^ 2 / 2

/-- Pointwise differential inequality for the bilinear interpolant of `d(U n, V k)² / 2` along two
minimizing movement sequences. -/
private theorem bilin_deriv_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X] {m : ℝ}
    {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ) (hηc : PenalizedConvex m η φ)
    (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2) (hmη : |m| * η ≤ 1 / 2)
    {U V : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    bilinDerivAt τ η (halfDistSq U V) ⌊t / η⌋₊ t ≤
      twoStepRate m τ η * bilinInterp τ η (halfDistSq U V) t +
        stepWeight τ ⌊t / τ⌋₊ t * (eU ⌊t / τ⌋₊ - eU (⌊t / τ⌋₊ + 1)) +
        stepWeight η ⌊t / η⌋₊ t * (eV ⌊t / η⌋₊ - eV (⌊t / η⌋₊ + 1)) := by
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  have hα : stepWeight τ n t ∈ Icc (0 : ℝ) 1 := stepWeight_mem_Icc hτ ht
  have hβ : stepWeight η k t ∈ Icc (0 : ℝ) 1 := stepWeight_mem_Icc hη ht
  have hVn := div_sub_half_dist_sq_le hηc hη hV heV (heU n) k
  have hVn1 := div_sub_half_dist_sq_le hηc hη hV heV (heU (n + 1)) k
  have hs3 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U n) hη hmη hβ
  have hs4 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U (n + 1)) hη hmη hβ
  simp only [dist_comm (V _) (U _)] at hVn hVn1 hs3 hs4
  rw [bilinInterp_apply]
  dsimp only [bilinDerivAt, twoStepRate, halfDistSq]
  exact bilin_deriv_algebraic_le (by positivity) (by positivity) (by positivity) (by positivity)
    (NNReal.coe_nonneg τ) (NNReal.coe_nonneg η) hα hβ
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV k) n)
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV (k + 1)) n) hVn hVn1
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V k) hτ hmτ hα)
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V (k + 1)) hτ hmτ hα) hs3 hs4

/-- Nonpositive right-hand derivative of the Grönwall auxiliary function
`s ↦ exp (-twoStepRate m τ η * s) * bilinInterp τ η (halfDistSq U V) s - ...` for `s ≥ 0`. -/
private theorem exists_hasDerivWithinAt_exp_bilinInterp_sub {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {s : ℝ} (hs : 0 ≤ s) :
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivWithinAt
      (fun r ↦ exp (-twoStepRate m τ η * r) * bilinInterp τ η (halfDistSq U V) r -
        energyPrim τ eU r - energyPrim η eV r) d (Ici s) s := by
  set K := twoStepRate m τ η
  have hK0 : 0 ≤ K := le_max_left _ _
  have hexp : HasDerivWithinAt (fun r ↦ exp (-K * r)) (-K * exp (-K * s)) (Ici s) s :=
    (((hasDerivAt_id' s).const_mul (-K)).exp).hasDerivWithinAt.congr_deriv (by ring)
  refine ⟨_, ?_, ((hexp.mul (hasDerivWithinAt_bilinInterp hτ hη (halfDistSq U V) hs)).sub
    (hasDerivWithinAt_energyPrim hτ eU hs)).sub (hasDerivWithinAt_energyPrim hη eV hs)⟩
  have hbd := bilin_deriv_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV hs
  set pU := stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1))
  set pV := stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1))
  have hpU : 0 ≤ pU :=
    mul_nonneg (stepWeight_mem_Icc hτ hs).1 (sub_nonneg.2 (hantiU (Nat.le_succ _)))
  have hpV : 0 ≤ pV :=
    mul_nonneg (stepWeight_mem_Icc hη hs).1 (sub_nonneg.2 (hantiV (Nat.le_succ _)))
  have hexp1 : exp (-K * s) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hs, hK0])
  have h1 := add_le_add_left (mul_le_mul_of_nonneg_left hbd (exp_pos (-K * s)).le)
    ((-K * exp (-K * s)) * bilinInterp τ η (halfDistSq U V) s)
  have h2 := (mul_le_mul_of_nonneg_right hexp1 (add_nonneg hpU hpV)).trans_eq (one_mul _)
  rw [sub_sub, sub_nonpos, add_comm]
  exact (h1.trans_eq (by dsimp only [K]; ring)).trans h2

/-- Grönwall integration of `bilin_deriv_le_of_penalizedConvex` bounds
`2 * bilinInterp τ η (halfDistSq U V) t`. -/
private theorem two_mul_bilinInterp_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {t : ℝ} (ht : 0 ≤ t) :
    2 * bilinInterp τ η (halfDistSq U V) t ≤
      exp (twoStepRate m τ η * t) * dist (U 0) (V 0) ^ 2 +
        exp (twoStepRate m τ η * t) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  set K := twoStepRate m τ η
  set G : ℝ → ℝ := fun s ↦
    exp (-K * s) * bilinInterp τ η (halfDistSq U V) s - energyPrim τ eU s - energyPrim η eV s
  have hGcont : ContinuousOn G (Icc 0 t) :=
    ((((by fun_prop : ContinuousOn (fun s ↦ exp (-K * s)) (Icc 0 t))).mul
      ((continuousOn_bilinInterp hτ hη (halfDistSq U V)).mono Icc_subset_Ici_self)).sub
      ((continuousOn_energyPrim hτ eU).mono Icc_subset_Ici_self)).sub
      ((continuousOn_energyPrim hη eV).mono Icc_subset_Ici_self)
  have hGderiv (s : ℝ) : ∃ d : ℝ, s ∈ Ico 0 t → d ≤ 0 ∧ HasDerivWithinAt G d (Ici s) s := by
    by_cases hs : s ∈ Ico 0 t
    · obtain ⟨d, hd0, hd⟩ := exists_hasDerivWithinAt_exp_bilinInterp_sub hτc hηc hτ hη hmτ hmη
        hU hV heU heV hantiU hantiV hs.1
      exact ⟨d, fun _ ↦ ⟨hd0, hd⟩⟩
    · exact ⟨0, fun h ↦ absurd h hs⟩
  choose d hdG using hGderiv
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := d) (δ := G 0) (K := 0)
    (ε := 0) hGcont (fun s hs r hr ↦ ((hdG s hs).2).liminf_right_slope_le hr) le_rfl
    (fun s hs ↦ by linarith [(hdG s hs).1]) t ⟨ht, le_rfl⟩
  simp only [gronwallBound_K0, zero_mul, add_zero] at hgr
  have hG0 : G 0 = dist (U 0) (V 0) ^ 2 / 2 := by
    simp only [G, mul_zero, exp_zero, one_mul, bilinInterp_zero (τ := τ) (η := η) hτ hη,
      energyPrim_zero (τ := τ) hτ, energyPrim_zero (τ := η) hη, sub_zero, halfDistSq]
  have hcan : exp (K * t) * exp (-K * t) = 1 := by rw [← exp_add]; simp [neg_mul]
  have hmul := mul_le_mul_of_nonneg_left (by
      linarith [hgr, hG0, energyPrim_le (τ := τ) (t := t) hτ hantiU,
        energyPrim_le (τ := η) (t := t) hη hantiV] :
      exp (-K * t) * bilinInterp τ η (halfDistSq U V) t ≤ dist (U 0) (V 0) ^ 2 / 2 +
        ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1)))
    (by positivity : 0 ≤ 2 * exp (K * t))
  rw [← mul_assoc, mul_assoc 2, hcan, mul_one] at hmul
  have hrhs : 2 * exp (K * t) * (dist (U 0) (V 0) ^ 2 / 2 +
      ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1))) =
    exp (K * t) * dist (U 0) (V 0) ^ 2 +
      exp (K * t) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by ring
  linarith [hmul, hrhs]

/-- One-step dissipation bound `d(U n, U (n + 1))² ≤ 2τ (e 0 - e (n + 1))` along a minimizing
movement sequence with real antitone energies. -/
private theorem dist_succ_sq_le_of_forall_mem_moreauYosidaResolvent {X : Type*}
    [PseudoMetricSpace X] {τ : ℝ≥0} {φ : X → EReal} (hτ : 0 < τ) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {e : ℕ → ℝ}
    (he : ∀ n, φ (U n) = e n) (hanti : Antitone e) (n : ℕ) :
    dist (U n) (U (n + 1)) ^ 2 ≤ 2 * τ * (e 0 - e (n + 1)) := by
  have h1 := apply_add_le_of_mem_moreauYosidaResolvent (hU n)
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ, he (n + 1), he n, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h1
  have h2 : dist (U n) (U (n + 1)) ^ 2 ≤ (e n - e (n + 1)) * (2 * τ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * τ)).1 (by linarith)
  nlinarith [hanti (Nat.zero_le n), NNReal.coe_nonneg τ, h2]

/-- **Quantitative two-step error bound for minimizing movements.** Under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` with `|m| τ ≤ 1 / 2` and
`|m| η ≤ 1 / 2`, the piecewise constant interpolants of two minimizing movement sequences with real
energies satisfy an explicit bound in terms of `d(U 0, V 0)²` and `(τ + η)` times the energy
dissipated up to steps `⌊t / τ⌋₊ + 1` and `⌊t / η⌋₊ + 1`. -/
theorem dist_ceil_sq_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤
      2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) * dist (U 0) (V 0) ^ 2 +
        (2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  have hantiU : Antitone eU := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heU j ▸ heU i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hU hij)
  have hantiV : Antitone eV := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heV j ▸ heV i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hV hij)
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  set ΔU := dist (U n) (U (n + 1)); set ΔV := dist (V k) (V (k + 1))
  have hΔU := dist_succ_sq_le_of_forall_mem_moreauYosidaResolvent hτ hU heU hantiU n
  have hΔV := dist_succ_sq_le_of_forall_mem_moreauYosidaResolvent hη hV heV hantiV k
  have hdU (i : ℕ) (hi : i = n ∨ i = n + 1) : dist (U ⌈t / τ⌉₊) (U i) ≤ ΔU := by
    rcases ceil_eq_floor_or_add_one (t / (τ : ℝ)) with hc | hc <;>
      rcases hi with rfl | rfl <;> simp [hc, n, ΔU, dist_comm]
  have hdV (j : ℕ) (hj : j = k ∨ j = k + 1) : dist (V j) (V ⌈t / η⌉₊) ≤ ΔV := by
    rcases ceil_eq_floor_or_add_one (t / (η : ℝ)) with hc | hc <;>
      rcases hj with rfl | rfl <;> simp [hc, k, ΔV, dist_comm]
  have hcell (i j : ℕ) (hi : i = n ∨ i = n + 1) (hj : j = k ∨ j = k + 1) :
      dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤ 2 * dist (U i) (V j) ^ 2 + 4 * ΔU ^ 2 + 4 * ΔV ^ 2 := by
    have htri : dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ≤ dist (U i) (V j) + ΔU + ΔV :=
      (dist_triangle4 (U ⌈t / τ⌉₊) (U i) (V j) (V ⌈t / η⌉₊)).trans
        (by linarith [hdU i hi, hdV j hj])
    nlinarith [sq_nonneg (dist (U i) (V j) - ΔU - ΔV), sq_nonneg (ΔU - ΔV),
      pow_le_pow_left₀ dist_nonneg htri 2]
  obtain ⟨hα0, hα1⟩ := stepWeight_mem_Icc (τ := τ) hτ ht
  obtain ⟨hβ0, hβ1⟩ := stepWeight_mem_Icc (τ := η) hη ht
  have hb := two_mul_bilinInterp_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV
    hantiU hantiV ht
  rw [bilinInterp_apply] at hb
  dsimp only [twoStepRate, halfDistSq] at hb
  nlinarith [hΔU, hΔV, hb,
    mul_le_mul_of_nonneg_left (hcell n k (.inl rfl) (.inl rfl)) (mul_nonneg hβ0 hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) k (.inr rfl) (.inl rfl))
      (mul_nonneg hβ0 (sub_nonneg.2 hα1)),
    mul_le_mul_of_nonneg_left (hcell n (k + 1) (.inl rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) (k + 1) (.inr rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hα1))]

end TwoStepBound

end TauCeti
