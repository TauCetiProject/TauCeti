/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MinimizingMovement
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.GradientFlow.EVI.Stability
import TauCeti.Analysis.ODE.Gronwall

/-!
# Generation of `EVI_λ` flows by minimizing movements

Let `φ : X → EReal` be a lower semicontinuous energy on a complete pseudometric space and `λ : ℝ`.
When `φ` satisfies De Giorgi's penalized convexity condition `TauCeti.PenalizedConvex λ τ φ` for
all sufficiently small positive time steps `τ` (Assumption 4.0.1 of Ambrosio–Gigli–Savaré) and is
coercive (`φ_{τ₀}(x₁) > -∞`), the implicit Euler scheme converges in the metric — with no
compactness hypothesis on energy sublevels — to an `EVI_λ` solution
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, Theorem 4.0.4 of
Ambrosio–Gigli–Savaré).

The key is a discrete two-step comparison between any two minimizing movement sequences `U` (with
step `τ`) and `V` (with step `η`). Interpolating the matrix `a_{n,k} = d(U n, V k)² / 2`
bilinearly across the product grid `[n τ, (n + 1) τ] × [k η, (k + 1) η]` produces a continuous
function `B(t)` whose right derivative on `[0, ∞)` is a convex combination of difference quotients
in `n` and `k`. Summing the four one-step discrete variational inequalities
(`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent`) cancels the cross-evaluated
energies identically into `α_n(t) (φ(U n) - φ(U (n + 1))) + β_k(t) (φ(V k) - φ(V (k + 1)))`, while
the one-step dissipations `-d(U n, U (n + 1))² / (2τ)` and `-d(V k, V (k + 1))² / (2η)` absorb the
metric shift terms coming from `-λ`. Integrating by Grönwall's inequality bounds
`d(U ⌈t / τ⌉₊, V ⌈t / η⌉₊)²` in terms of `d(U 0, V 0)²` and `(τ + η)` times the total energy drop,
which is uniformly bounded on bounded time intervals by coercivity.

Consequently, for every `x₀` with `φ x₀ ≠ ⊤`:

* piecewise constant interpolants of minimizing movement sequences from `x₀` (or from initial
  points converging to `x₀` with bounded energy) form a uniformly Cauchy family on `[0, T]` and
  converge uniformly on `[0, T]` to a limit curve `u` with `u 0 = x₀`;
* `u` is `1/2`-Hölder continuous on `[0, T]`, and passing the discrete energy regularization
  estimate `TauCeti.PenalizedConvex.apply_le` to the limit shows that `u` is an `EVI_λ` solution;
* by `λ`-contraction of `EVI_λ` solutions (`TauCeti.IsEVISolution.dist_le`) and stability under
  pointwise convergence (`TauCeti.TendstoGamma.isEVISolution_of_tendsto`), the domain of the
  `EVI_λ` flow is the entire closure of the effective domain:
  `TauCeti.eviDomain λ φ = closure {x | φ x ≠ ⊤}`
  (`TauCeti.eviDomain_eq_closure_of_penalizedConvex`).

When `φ` is `λ`-convex along curves `γ` along which the squared distance `d(·, w)²` from every
base point `w` is `2`-convex (Assumption 3.24 and Theorem 3.25 of Ambrosio–Gigli), both penalized
convexity and coercivity (`TauCeti.moreauYosida_ne_bot_of_convexAlong`, obtained by taking
`w = γ 0`) hold automatically once `φ` never takes the value `⊥`
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_dist_sq_le`). In particular,
this applies to `λ`-geodesically convex energies on complete CAT(0) spaces
(`TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn`).

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of an `EVI_λ`
  solution and locally uniform convergence of minimizing movements under `TauCeti.PenalizedConvex`.
* `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`: on a complete metric
  space, every metric generalized minimizing movement is an `EVI_λ` solution.
* `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: the `EVI_λ` domain equals the closure of
  `{x | φ x ≠ ⊤}`.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_dist_sq_le` and
  `TauCeti.eviDomain_eq_closure_of_convexAlong_and_dist_sq_le`: generation of `EVI_λ` flows under
  `λ`-convexity of `φ` and `2`-convexity of `d(·, w)²` along curves.
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn` and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: specialization to complete CAT(0) spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Section 4.1.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Math. 2062,
  Springer 2013, Assumption 3.24 and Theorem 3.25.
-/

public section

noncomputable section

open Filter Set Topology Real Finset
open scoped NNReal ENNReal

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

/-- For `t ≥ 0` and `τ > 0`, `t` lies in `[⌊t / τ⌋₊ τ, (⌊t / τ⌋₊ + 1) τ)`. -/
private theorem mem_Ico_floor_mul {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    t ∈ Ico ((⌊t / τ⌋₊ : ℝ) * τ) (((⌊t / τ⌋₊ : ℝ) + 1) * τ) :=
  ⟨(le_div_iff₀ hτ).1 (Nat.floor_le (div_nonneg ht hτ.le)),
    (div_lt_iff₀ hτ).1 (Nat.lt_floor_add_one _)⟩

/-- A `piecewiseStep` function whose pieces are continuous on `[n τ, (n + 1) τ]` and match at the
grid points is continuous on `[0, ∞)`. -/
private theorem continuousOn_piecewiseStep {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → ℝ}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    (hcont : ∀ n : ℕ, ContinuousOn (g n) (Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))) :
    ContinuousOn (piecewiseStep τ g) (Ici 0) := by
  intro t ht
  rw [Set.mem_Ici] at ht
  set n := ⌊t / τ⌋₊
  have hmem : t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := mem_Ico_floor_mul hτ ht
  have hright : ContinuousWithinAt (piecewiseStep τ g) (Ici t) t := by
    have hnhds : Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) ∈ 𝓝[Ici t] t :=
      mem_nhdsWithin.2 ⟨Iio (((n : ℝ) + 1) * τ), isOpen_Iio, hmem.2,
        fun s hs ↦ ⟨hmem.1.trans hs.2, hs.1.le⟩⟩
    exact (((hcont n).congr fun s hs ↦ piecewiseStep_eq_of_mem_Icc hτ hjoin n hs) t
      (Ico_subset_Icc_self hmem)).mono_of_mem_nhdsWithin hnhds
  rcases hmem.1.eq_or_lt with heq | hlt
  · rcases n with _ | m
    · simpa [← heq] using hright
    · have heq' : ((m : ℝ) + 1) * τ = t := by push_cast at heq; exact heq
      have hm_lt : (m : ℝ) * τ < t := by rw [← heq']; linarith
      have hnhds : Icc ((m : ℝ) * τ) (((m : ℝ) + 1) * τ) ∈ 𝓝[Iic t] t :=
        mem_nhdsWithin.2 ⟨Ioi ((m : ℝ) * τ), isOpen_Ioi, hm_lt,
          fun s hs ↦ ⟨hs.1.le, hs.2.trans_eq heq'.symm⟩⟩
      have hleft : ContinuousWithinAt (piecewiseStep τ g) (Iic t) t :=
        (((hcont m).congr fun s hs ↦ piecewiseStep_eq_of_mem_Icc hτ hjoin m hs) t
          ⟨hm_lt.le, heq'.symm.le⟩).mono_of_mem_nhdsWithin hnhds
      exact (continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩).continuousWithinAt
  · exact (((hcont n).congr fun s hs ↦ piecewiseStep_eq_of_mem_Icc hτ hjoin n hs).continuousAt
      (Icc_mem_nhds hlt hmem.2)).continuousWithinAt

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
    stepWeight τ n (((n : ℝ) + 1) * τ) = 0 ∧ stepWeight τ (n + 1) (((n : ℝ) + 1) * τ) = 1 := by
  refine ⟨by simp [stepWeight], ?_⟩
  simp only [stepWeight, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

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
  refine continuousOn_piecewiseStep hτ (fun n ↦ ?_) (fun n ↦ ?_)
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring
  · unfold stepWeight; fun_prop

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
  have h1 : stepWeight τ 0 0 = 1 := by simp [stepWeight, div_self hτ.ne']
  have h2 : stepWeight η 0 0 = 1 := by simp [stepWeight, div_self hη.ne']
  simp [bilinInterp_apply, h1, h2]

private theorem bilinInterp_nonneg {τ η t : ℝ} (hτ : 0 < τ) (hη : 0 < η) (ht : 0 ≤ t)
    {a : ℕ → ℕ → ℝ} (ha : ∀ n k, 0 ≤ a n k) :
    0 ≤ bilinInterp τ η a t := by
  obtain ⟨hα0, hα1⟩ := stepWeight_mem_Icc hτ ht
  obtain ⟨hβ0, hβ1⟩ := stepWeight_mem_Icc hη ht
  have _ : 0 ≤ 1 - stepWeight τ ⌊t / τ⌋₊ t := sub_nonneg.2 hα1
  have _ : 0 ≤ 1 - stepWeight η ⌊t / η⌋₊ t := sub_nonneg.2 hβ1
  have _ := ha ⌊t / τ⌋₊ ⌊t / η⌋₊
  have _ := ha (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊
  have _ := ha ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)
  have _ := ha (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)
  rw [bilinInterp_apply]
  positivity

private theorem continuousOn_bilinInterp {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → ℝ) :
    ContinuousOn (bilinInterp τ η a) (Ici 0) := by
  refine continuousOn_piecewiseStep hη (fun k ↦ ?_) (fun k ↦ ?_)
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hη k; rw [h1, h2]; ring
  · have hsub : Icc ((k : ℝ) * η) (((k : ℝ) + 1) * η) ⊆ Ici 0 :=
      fun s hs ↦ (mul_nonneg k.cast_nonneg hη.le).trans hs.1
    have hc1 := (continuousOn_linInterp hτ (a · k)).mono hsub
    have hc2 := (continuousOn_linInterp hτ (a · (k + 1))).mono hsub
    have hw : Continuous (stepWeight η k) := by unfold stepWeight; fun_prop
    exact (hw.continuousOn.mul hc1).add ((continuousOn_const.sub hw.continuousOn).mul hc2)

private theorem hasDerivWithinAt_bilinInterp {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (bilinInterp τ η a)
      (stepWeight η ⌊t / η⌋₊ t * (a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - a ⌊t / τ⌋₊ ⌊t / η⌋₊) / τ +
        (1 - stepWeight η ⌊t / η⌋₊ t) *
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) / τ +
        stepWeight τ ⌊t / τ⌋₊ t * (a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ ⌊t / η⌋₊) / η +
        (1 - stepWeight τ ⌊t / τ⌋₊ t) *
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊) / η)
      (Ici t) t := by
  refine hasDerivWithinAt_piecewiseStep (g' := fun k s ↦
      stepWeight η k s * (a (⌊s / τ⌋₊ + 1) k - a ⌊s / τ⌋₊ k) / τ +
        (1 - stepWeight η k s) * (a (⌊s / τ⌋₊ + 1) (k + 1) - a ⌊s / τ⌋₊ (k + 1)) / τ +
        stepWeight τ ⌊s / τ⌋₊ s * (a ⌊s / τ⌋₊ (k + 1) - a ⌊s / τ⌋₊ k) / η +
        (1 - stepWeight τ ⌊s / τ⌋₊ s) * (a (⌊s / τ⌋₊ + 1) (k + 1) - a (⌊s / τ⌋₊ + 1) k) / η)
    hη (fun k ↦ ?_) (fun k s hs ↦ ?_) ht
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hη k; rw [h1, h2]; ring
  · have hs0 : 0 ≤ s := (mul_nonneg k.cast_nonneg hη.le).trans hs.1
    have hd1 := ((hasDerivAt_stepWeight η k s).hasDerivWithinAt).mul
      (hasDerivWithinAt_linInterp hτ (a · k) hs0)
    have hd2 := (((hasDerivAt_stepWeight η k s).const_sub 1).hasDerivWithinAt).mul
      (hasDerivWithinAt_linInterp hτ (a · (k + 1)) hs0)
    refine (hd1.add hd2).congr_deriv ?_
    simp only [linInterp_apply]
    field_simp
    ring

/-- Piecewise quadratic primitive of `t ↦ stepWeight τ ⌊t / τ⌋₊ t * (e ⌊t / τ⌋₊ - e (⌊t / τ⌋₊ + 1))`
starting at `0`. -/
private def energyPrim (τ : ℝ) (e : ℕ → ℝ) : ℝ → ℝ :=
  piecewiseStep τ fun n t ↦
    (τ / 2) * (e 0 - e (n + 1) + stepWeight τ n t ^ 2 * (e (n + 1) - e n))

private theorem energyPrim_zero {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) : energyPrim τ e 0 = 0 := by
  have h1 : stepWeight τ 0 0 = 1 := by simp [stepWeight, div_self hτ.ne']
  simp [energyPrim, piecewiseStep, h1]

private theorem energyPrim_le {τ t : ℝ} (hτ : 0 < τ) {e : ℕ → ℝ} (he : Antitone e) :
    energyPrim τ e t ≤ (τ / 2) * (e 0 - e (⌊t / τ⌋₊ + 1)) := by
  simp only [energyPrim, piecewiseStep]
  have hle : stepWeight τ ⌊t / τ⌋₊ t ^ 2 * (e (⌊t / τ⌋₊ + 1) - e ⌊t / τ⌋₊) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.2 (he (Nat.le_succ _)))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem continuousOn_energyPrim {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) :
    ContinuousOn (energyPrim τ e) (Ici 0) := by
  refine continuousOn_piecewiseStep hτ (fun n ↦ ?_) (fun n ↦ ?_)
  · obtain ⟨h1, h2⟩ := stepWeight_succ_mul hτ n; rw [h1, h2]; ring
  · unfold stepWeight; fun_prop

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
          rw [show d ^ 2 - d' ^ 2 = (d - d') * (d + d') by ring, abs_mul,
            abs_of_nonneg (add_nonneg hd0 hd'0)]
      _ ≤ Δ * (2 * d + Δ) := mul_le_mul h1 h2 (add_nonneg hd0 hd'0) dist_nonneg
      _ = 2 * d * Δ + Δ ^ 2 := by ring
  have hm_bd : m * (d ^ 2 / 2 - d' ^ 2 / 2) ≤ |m| * d * Δ + |m| * Δ ^ 2 / 2 :=
    calc m * (d ^ 2 / 2 - d' ^ 2 / 2) = (m * (d ^ 2 - d' ^ 2)) / 2 := by ring
      _ ≤ |m * (d ^ 2 - d' ^ 2)| / 2 := div_le_div_of_nonneg_right (le_abs_self _) zero_le_two
      _ = |m| * |d ^ 2 - d' ^ 2| / 2 := by rw [abs_mul]
      _ ≤ |m| * (2 * d * Δ + Δ ^ 2) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (abs_nonneg m)) zero_le_two
      _ = |m| * d * Δ + |m| * Δ ^ 2 / 2 := by ring
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 4 * τ)
  have hclear : (α * m * (d ^ 2 / 2 - d' ^ 2 / 2) - Δ ^ 2 / (2 * τ)) * (4 * τ) =
      4 * τ * (α * (m * (d ^ 2 / 2 - d' ^ 2 / 2))) - 2 * Δ ^ 2 := by field_simp; ring
  have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm_bd hα.1)
    (by positivity : 0 ≤ 4 * τ)
  have hΔ_term : 2 * τ * α * |m| * Δ ^ 2 ≤ Δ ^ 2 := by
    have : 2 * τ * α * |m| ≤ 1 := by nlinarith [hα.1, hα.2, hmτ, abs_nonneg m]
    exact (mul_le_mul_of_nonneg_right this (sq_nonneg Δ)).trans_eq (one_mul _)
  have hαm : 4 * τ ^ 2 * α ^ 2 * |m| ^ 2 * d ^ 2 ≤ 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 := by
    rw [sq_abs]
    have hα_sq : α ^ 2 ≤ α := by nlinarith [hα.1, hα.2]
    have := mul_le_mul_of_nonneg_right hα_sq (by positivity : 0 ≤ 4 * τ ^ 2 * m ^ 2 * d ^ 2)
    linarith [show α ^ 2 * (4 * τ ^ 2 * m ^ 2 * d ^ 2) = 4 * τ ^ 2 * α ^ 2 * m ^ 2 * d ^ 2 by ring,
      show α * (4 * τ ^ 2 * m ^ 2 * d ^ 2) = 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 by ring]
  have hquad : 4 * τ * α * |m| * d * Δ - Δ ^ 2 ≤ 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 := by
    linarith [sq_nonneg (Δ - 2 * τ * α * |m| * d), hαm,
      show (Δ - 2 * τ * α * |m| * d) ^ 2 =
        Δ ^ 2 - 4 * τ * α * |m| * d * Δ + 4 * τ ^ 2 * α ^ 2 * |m| ^ 2 * d ^ 2 by ring]
  rw [hclear]
  linarith [h1, hΔ_term, hquad,
    show 4 * τ * (α * (|m| * d * Δ + |m| * Δ ^ 2 / 2)) =
      4 * τ * α * |m| * d * Δ + 2 * τ * α * |m| * Δ ^ 2 by ring,
    show 2 * m ^ 2 * τ * (α * (d ^ 2 / 2)) * (4 * τ) = 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 by ring]

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
  have hbτ := mul_le_mul_of_nonneg_left
    (show β * (α * a₀₀) + (1 - β) * (α * a₀₁) ≤ b by
      have hrem : 0 ≤ β * ((1 - α) * a₁₀) + (1 - β) * ((1 - α) * a₁₁) := by positivity
      linarith [hrem, show b = β * (α * a₀₀) + (1 - β) * (α * a₀₁) +
        (β * ((1 - α) * a₁₀) + (1 - β) * ((1 - α) * a₁₁)) by dsimp [b]; ring])
    (by positivity : 0 ≤ 2 * m ^ 2 * τ)
  have hbη := mul_le_mul_of_nonneg_left
    (show α * (β * a₀₀) + (1 - α) * (β * a₁₀) ≤ b by
      have hrem : 0 ≤ (1 - β) * (α * a₀₁ + (1 - α) * a₁₁) := by positivity
      linarith [hrem, show b = α * (β * a₀₀) + (1 - α) * (β * a₁₀) +
        (1 - β) * (α * a₀₁ + (1 - α) * a₁₁) by dsimp [b]; ring])
    (by positivity : 0 ≤ 2 * m ^ 2 * η)
  have hK := mul_le_mul_of_nonneg_right
    (le_max_right 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)) hb0
  have hlhs : β * (a₁₀ - a₀₀) / τ + (1 - β) * (a₁₁ - a₀₁) / τ +
      α * (a₀₁ - a₀₀) / η + (1 - α) * (a₁₁ - a₁₀) / η =
      β * ((a₁₀ - a₀₀) / τ) + (1 - β) * ((a₁₁ - a₀₁) / τ) +
      α * ((a₀₁ - a₀₀) / η) + (1 - α) * ((a₁₁ - a₁₀) / η) := by ring
  have hdecomp : β * (eV₀ - eU₁ - dU - m * a₁₀) + (1 - β) * (eV₁ - eU₁ - dU - m * a₁₁) +
      α * (eU₀ - eV₁ - dV - m * a₀₁) + (1 - α) * (eU₁ - eV₁ - dV - m * a₁₁) =
      -2 * m * b + β * (α * m * (a₀₀ - a₁₀) - dU) + (1 - β) * (α * m * (a₀₁ - a₁₁) - dU) +
        α * (β * m * (a₀₀ - a₀₁) - dV) + (1 - α) * (β * m * (a₁₀ - a₁₁) - dV) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by dsimp [b]; ring
  have hr1 : β * (2 * m ^ 2 * τ * (α * a₀₀)) + (1 - β) * (2 * m ^ 2 * τ * (α * a₀₁)) =
      2 * m ^ 2 * τ * (β * (α * a₀₀) + (1 - β) * (α * a₀₁)) := by ring
  have hr2 : α * (2 * m ^ 2 * η * (β * a₀₀)) + (1 - α) * (2 * m ^ 2 * η * (β * a₁₀)) =
      2 * m ^ 2 * η * (α * (β * a₀₀) + (1 - α) * (β * a₁₀)) := by ring
  have hr3 : (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * b =
      -2 * m * b + 2 * m ^ 2 * τ * b + 2 * m ^ 2 * η * b := by ring
  linarith [hlhs, hdecomp, hbτ, hbη, hK, hr1, hr2, hr3,
    mul_le_mul_of_nonneg_left hUk hβ0, mul_le_mul_of_nonneg_left hUk1 hβ1,
    mul_le_mul_of_nonneg_left hVn hα0, mul_le_mul_of_nonneg_left hVn1 hα1,
    mul_le_mul_of_nonneg_left hs1 hβ0, mul_le_mul_of_nonneg_left hs2 hβ1,
    mul_le_mul_of_nonneg_left hs3 hα0, mul_le_mul_of_nonneg_left hs4 hα1]

/-- Pointwise differential inequality for the bilinear interpolant of `d(U n, V k)² / 2` along two
minimizing movement sequences. -/
private theorem bilin_deriv_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X] {m : ℝ}
    {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ) (hηc : PenalizedConvex m η φ)
    (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2) (hmη : |m| * η ≤ 1 / 2)
    {U V : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    let a : ℕ → ℕ → ℝ := fun n k ↦ dist (U n) (V k) ^ 2 / 2
    stepWeight η ⌊t / η⌋₊ t * (a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - a ⌊t / τ⌋₊ ⌊t / η⌋₊) / τ +
      (1 - stepWeight η ⌊t / η⌋₊ t) *
        (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) / τ +
      stepWeight τ ⌊t / τ⌋₊ t * (a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ ⌊t / η⌋₊) / η +
      (1 - stepWeight τ ⌊t / τ⌋₊ t) *
        (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊) / η ≤
      max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * bilinInterp τ η a t +
        stepWeight τ ⌊t / τ⌋₊ t * (eU ⌊t / τ⌋₊ - eU (⌊t / τ⌋₊ + 1)) +
        stepWeight η ⌊t / η⌋₊ t * (eV ⌊t / η⌋₊ - eV (⌊t / η⌋₊ + 1)) := by
  intro a
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  have hα : stepWeight τ n t ∈ Icc (0 : ℝ) 1 := stepWeight_mem_Icc hτ ht
  have hβ : stepWeight η k t ∈ Icc (0 : ℝ) 1 := stepWeight_mem_Icc hη ht
  have hVn := div_sub_half_dist_sq_le hηc hη hV heV (heU n) k
  have hVn1 := div_sub_half_dist_sq_le hηc hη hV heV (heU (n + 1)) k
  have hs3 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U n) hη hmη hβ
  have hs4 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U (n + 1)) hη hmη hβ
  simp only [dist_comm (V _) (U _)] at hVn hVn1 hs3 hs4
  rw [bilinInterp_apply]
  exact bilin_deriv_algebraic_le (by positivity) (by positivity) (by positivity) (by positivity)
    (NNReal.coe_nonneg τ) (NNReal.coe_nonneg η) hα hβ
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV k) n)
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV (k + 1)) n) hVn hVn1
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V k) hτ hmτ hα)
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V (k + 1)) hτ hmτ hα) hs3 hs4

/-- Nonpositive right-hand derivative of the Grönwall auxiliary function
`s ↦ exp (-K * s) * bilinInterp τ η a s - energyPrim τ eU s - energyPrim η eV s` for `s ≥ 0`. -/
private theorem exists_hasDerivWithinAt_exp_bilinInterp_sub {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {s : ℝ} (hs : 0 ≤ s) :
    let K := max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)
    let a : ℕ → ℕ → ℝ := fun n k ↦ dist (U n) (V k) ^ 2 / 2
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivWithinAt
      (fun r ↦ exp (-K * r) * bilinInterp τ η a r - energyPrim τ eU r - energyPrim η eV r)
      d (Ici s) s := by
  intro K a
  have hK0 : 0 ≤ K := le_max_left _ _
  have hexp : HasDerivWithinAt (fun r ↦ exp (-K * r)) (-K * exp (-K * s)) (Ici s) s :=
    (((hasDerivAt_id' s).const_mul (-K)).exp).hasDerivWithinAt.congr_deriv (by ring)
  refine ⟨_, ?_, ((hexp.mul (hasDerivWithinAt_bilinInterp hτ hη a hs)).sub
    (hasDerivWithinAt_energyPrim hτ eU hs)).sub (hasDerivWithinAt_energyPrim hη eV hs)⟩
  have hbd := bilin_deriv_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV hs
  change _ ≤ K * bilinInterp τ η a s +
    stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1)) +
    stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1)) at hbd
  have hpU : 0 ≤ stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1)) :=
    mul_nonneg (stepWeight_mem_Icc hτ hs).1 (sub_nonneg.2 (hantiU (Nat.le_succ _)))
  have hpV : 0 ≤ stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1)) :=
    mul_nonneg (stepWeight_mem_Icc hη hs).1 (sub_nonneg.2 (hantiV (Nat.le_succ _)))
  have hle1 := (add_le_add_right (mul_le_mul_of_nonneg_left hbd (exp_pos (-K * s)).le)
    (-K * exp (-K * s) * bilinInterp τ η a s)).trans_eq (by ring :
      -K * exp (-K * s) * bilinInterp τ η a s +
        exp (-K * s) * (K * bilinInterp τ η a s +
          stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1)) +
          stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1))) =
      exp (-K * s) * (stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1)) +
        stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1))))
  rw [sub_sub, sub_nonpos]
  exact hle1.trans ((mul_le_mul_of_nonneg_right
    (exp_le_one_iff.2 (by nlinarith [hs, hK0]) : exp (-K * s) ≤ 1)
    (add_nonneg hpU hpV)).trans_eq (one_mul _))

/-- Grönwall integration of `bilin_deriv_le_of_penalizedConvex` bounds `2 * bilinInterp τ η a t`. -/
private theorem two_mul_bilinInterp_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {t : ℝ} (ht : 0 ≤ t) :
    let K := max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)
    2 * bilinInterp τ η (fun n k ↦ dist (U n) (V k) ^ 2 / 2) t ≤
      exp (K * t) * dist (U 0) (V 0) ^ 2 +
        exp (K * t) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  intro K
  set a : ℕ → ℕ → ℝ := fun n k ↦ dist (U n) (V k) ^ 2 / 2
  set G : ℝ → ℝ := fun s ↦
    exp (-K * s) * bilinInterp τ η a s - energyPrim τ eU s - energyPrim η eV s
  have hGcont : ContinuousOn G (Icc 0 t) :=
    ((((by fun_prop : ContinuousOn (fun s ↦ exp (-K * s)) (Icc 0 t))).mul
      ((continuousOn_bilinInterp hτ hη a).mono Icc_subset_Ici_self)).sub
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
      energyPrim_zero (τ := τ) hτ, energyPrim_zero (τ := η) hη, sub_zero, a]
  have hcan : 2 * exp (K * t) * (exp (-K * t) * bilinInterp τ η a t) =
      2 * bilinInterp τ η a t := by rw [← mul_assoc, mul_assoc 2, ← exp_add]; simp [neg_mul]
  have hmul := mul_le_mul_of_nonneg_left (by
      linarith [hgr, hG0, energyPrim_le (τ := τ) (t := t) hτ hantiU,
        energyPrim_le (τ := η) (t := t) hη hantiV] :
      exp (-K * t) * bilinInterp τ η a t ≤ dist (U 0) (V 0) ^ 2 / 2 +
        ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1)))
    (by positivity : 0 ≤ 2 * exp (K * t))
  linarith [hcan, hmul, show 2 * exp (K * t) * (dist (U 0) (V 0) ^ 2 / 2 +
      ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1))) =
    exp (K * t) * dist (U 0) (V 0) ^ 2 +
      exp (K * t) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) by ring]

/-- For `x ≥ 0`, `⌈x⌉₊` is either `⌊x⌋₊` or `⌊x⌋₊ + 1`. -/
private theorem ceil_eq_floor_or_add_one {x : ℝ} (hx : 0 ≤ x) :
    ⌈x⌉₊ = ⌊x⌋₊ ∨ ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
  have h1 : ⌊x⌋₊ ≤ ⌈x⌉₊ := Nat.floor_le_ceil x
  have h2 : ⌈x⌉₊ < ⌊x⌋₊ + 2 := by
    rw [← Nat.cast_lt (α := ℝ)]; push_cast
    linarith [Nat.ceil_lt_add_one hx, Nat.lt_floor_add_one x]
  omega

/-- **Quantitative two-step error bound for minimizing movements.** Under `PenalizedConvex m τ φ`
and `PenalizedConvex m η φ` with `|m| τ ≤ 1 / 2` and `|m| η ≤ 1 / 2`, the piecewise constant
interpolants of two minimizing movement sequences with real energies satisfy an explicit bound in
terms of `d(U 0, V 0)²` and `(τ + η)` times the energy dissipated up to time `t + max τ η`. -/
private theorem dist_ceil_sq_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    let K := max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)
    dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤
      2 * exp (K * t) * dist (U 0) (V 0) ^ 2 +
        (2 * exp (K * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  intro K
  have hantiU : Antitone eU := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heU j ▸ heU i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hU hij)
  have hantiV : Antitone eV := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heV j ▸ heV i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hV hij)
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  set ΔU := dist (U n) (U (n + 1)); set ΔV := dist (V k) (V (k + 1))
  have hΔU : ΔU ^ 2 ≤ 2 * τ * (eU 0 - eU (n + 1)) := by
    have h1 := apply_add_le_of_mem_moreauYosidaResolvent (hU n)
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ, heU (n + 1), heU n, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h1
    have h2 : ΔU ^ 2 ≤ (eU n - eU (n + 1)) * (2 * τ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * τ)).1 (by dsimp [ΔU]; linarith)
    nlinarith [hantiU (Nat.zero_le n), NNReal.coe_nonneg τ, h2]
  have hΔV : ΔV ^ 2 ≤ 2 * η * (eV 0 - eV (k + 1)) := by
    have h1 := apply_add_le_of_mem_moreauYosidaResolvent (hV k)
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hη, heV (k + 1), heV k, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h1
    have h2 : ΔV ^ 2 ≤ (eV k - eV (k + 1)) * (2 * η) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η)).1 (by dsimp [ΔV]; linarith)
    nlinarith [hantiV (Nat.zero_le k), NNReal.coe_nonneg η, h2]
  have hdU (i : ℕ) (hi : i = n ∨ i = n + 1) : dist (U ⌈t / τ⌉₊) (U i) ≤ ΔU := by
    rcases ceil_eq_floor_or_add_one (div_nonneg ht (NNReal.coe_nonneg τ)) with hc | hc <;>
      rcases hi with rfl | rfl <;> simp [hc, n, ΔU, dist_comm]
  have hdV (j : ℕ) (hj : j = k ∨ j = k + 1) : dist (V j) (V ⌈t / η⌉₊) ≤ ΔV := by
    rcases ceil_eq_floor_or_add_one (div_nonneg ht (NNReal.coe_nonneg η)) with hc | hc <;>
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
  nlinarith [hΔU, hΔV, hb,
    mul_le_mul_of_nonneg_left (hcell n k (.inl rfl) (.inl rfl)) (mul_nonneg hβ0 hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) k (.inr rfl) (.inl rfl))
      (mul_nonneg hβ0 (sub_nonneg.2 hα1)),
    mul_le_mul_of_nonneg_left (hcell n (k + 1) (.inl rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) (k + 1) (.inr rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hα1))]

end TwoStepBound

/-! ### Discrete-to-continuous EVI passage and locally uniform convergence -/

section Convergence

/-- For `0 ≤ s ≤ t` and positive time steps `τ j → 0`, the discrete elapsed time
`(⌈t / τ j⌉₊ - ⌈s / τ j⌉₊) * τ j` converges to `t - s`. -/
private theorem tendsto_natCast_sub_ceil_mul {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun j ↦ ((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j) atTop (𝓝 (t - s)) := by
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub hτr) (by simpa using tendsto_const_nhds.add hτr)
    (fun j ↦ ?_) (fun j ↦ ?_)
  · have hτj : (0 : ℝ) < τ j := hτ j
    have hle : ⌈s / τ j⌉₊ ≤ ⌈t / τ j⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right hst hτj.le)
    have ht_le : t ≤ (⌈t / τ j⌉₊ : ℝ) * τ j := (div_le_iff₀ hτj).1 (Nat.le_ceil _)
    have hs_lt : (⌈s / τ j⌉₊ : ℝ) * τ j < s + τ j := by
      have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hs hτj.le)) hτj
      linarith [show (s / τ j + 1) * τ j = s + τ j by field_simp]
    linarith [show ((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j =
      (⌈t / τ j⌉₊ : ℝ) * τ j - (⌈s / τ j⌉₊ : ℝ) * τ j by rw [Nat.cast_sub hle, sub_mul]]
  · have hτj : (0 : ℝ) < τ j := hτ j
    have hlt := (natCast_ceil_div_sub_ceil_div_lt hτj.le hst).le
    rwa [div_add_one hτj.ne', le_div_iff₀ hτj] at hlt

/-- If `τ j > 0` tends to `0` and `N j * τ j → T`, then `(1 + lam * τ j) ^ N j → exp (lam * T)`
and `τ j * ∑_{k < N j} (1 + lam * τ j) ^ k → ∫ r in 0..T, exp (lam * r)`. -/
private theorem tendsto_one_add_mul_pow_and_sum (lam T : ℝ) {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) {N : ℕ → ℕ}
    (hN : Tendsto (fun j ↦ (N j : ℝ) * τ j) atTop (𝓝 T)) :
    Tendsto (fun j ↦ (1 + lam * τ j) ^ N j) atTop (𝓝 (exp (lam * T))) ∧
      Tendsto (fun j ↦ (τ j : ℝ) * ∑ k ∈ range (N j), (1 + lam * τ j) ^ k) atTop
        (𝓝 (∫ r in 0..T, exp (lam * r))) := by
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp only [zero_mul, add_zero, one_pow, exp_zero, sum_const, card_range, nsmul_eq_mul,
      mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    exact ⟨tendsto_const_nhds, by simpa [mul_comm] using hN⟩
  have hpow : Tendsto (fun j ↦ (1 + lam * τ j) ^ N j) atTop (𝓝 (exp (lam * T))) := by
    have hu : Tendsto (fun j ↦ lam * (τ j : ℝ)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (by simpa using hτr.const_mul lam)
        (Eventually.of_forall fun j ↦ mul_ne_zero hlam (NNReal.coe_pos.2 (hτ j)).ne')
    have hlog : Tendsto (fun j ↦ (lam * (τ j : ℝ))⁻¹ * log (1 + lam * τ j)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, log_one, sub_zero, smul_eq_mul, inv_one] using
        ((Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero).comp hu
    have hprod : Tendsto (fun j ↦ exp (((N j : ℝ) * τ j) * lam *
        ((lam * (τ j : ℝ))⁻¹ * log (1 + lam * τ j)))) atTop (𝓝 (exp (lam * T))) := by
      have := (hN.mul_const lam).mul hlog
      rw [mul_one, mul_comm T lam] at this
      exact (Real.continuous_exp.tendsto _).comp this
    refine hprod.congr' ?_
    filter_upwards [hτr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / |lam|))] with j hj
    have hpos : 0 < 1 + lam * (τ j : ℝ) := by
      have habs : -(lam * (τ j : ℝ)) ≤ |lam| * (τ j : ℝ) := by
        simpa [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)] using neg_le_abs (lam * (τ j : ℝ))
      linarith [(lt_div_iff₀ (abs_pos.2 hlam)).1 hj]
    have hne : lam * (τ j : ℝ) ≠ 0 := mul_ne_zero hlam (NNReal.coe_pos.2 (hτ j)).ne'
    have hmul : ((N j : ℝ) * τ j) * lam * ((lam * (τ j : ℝ))⁻¹ * log (1 + lam * τ j)) =
        (N j : ℝ) * (lam * (τ j : ℝ) * (lam * (τ j : ℝ))⁻¹) * log (1 + lam * τ j) := by ring
    rw [hmul, mul_inv_cancel₀ hne, mul_one, exp_nat_mul, exp_log hpos]
  refine ⟨hpow, ?_⟩
  rw [intervalIntegral.integral_comp_mul_left (fun r ↦ exp r) hlam, integral_exp]
  simp only [mul_zero, exp_zero, smul_eq_mul, ← div_eq_inv_mul]
  refine ((hpow.sub_const 1).div_const lam).congr' (Eventually.of_forall fun j ↦ ?_)
  have hτne : (τ j : ℝ) ≠ 0 := (NNReal.coe_pos.2 (hτ j)).ne'
  dsimp only
  rw [geom_sum_eq (by simp [hlam, hτne])]; field_simp; ring

/-- Extracts real energy values and bounds the energy drop `e 0 - e (⌊t / τ⌋₊ + 1)` along a
minimizing movement sequence satisfying a priori lower and upper energy bounds. -/
private theorem exists_toReal_apply_and_sub_le {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ τ : ℝ≥0} (hτ : 0 < τ) (hτ_lt : τ < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {S L T t : ℝ} (hS : φ (U 0) ≤ S) (ht : t ∈ Icc 0 T)
    (hL : ∀ n ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U n)) :
    ∃ e : ℕ → ℝ, (∀ n, φ (U n) = e n) ∧
      0 ≤ e 0 - e (⌊t / τ⌋₊ + 1) ∧ e 0 - e (⌊t / τ⌋₊ + 1) ≤ max 0 (S - L) := by
  have he (n : ℕ) : φ (U n) = ((φ (U n)).toReal : EReal) := (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top S)
      ((antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n)).trans hS))
    (ne_bot_of_le_ne_bot (moreauYosida_ne_bot_of_lt hτ_lt (edist_ne_top (U n) x₁) h₀)
      (moreauYosida_le_self φ τ (U n)))).symm
  have hn : ⌊t / (τ : ℝ)⌋₊ + 1 ≤ ⌈(T + 1) / τ⌉₊ := Nat.add_one_le_iff.2 (Nat.lt_ceil.2 <|
    (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg τ))).trans_lt
      ((div_lt_div_iff_of_pos_right (NNReal.coe_pos.2 hτ)).2 (by linarith [ht.2])))
  have ha0 : 0 ≤ (φ (U 0)).toReal - (φ (U (⌊t / τ⌋₊ + 1))).toReal := sub_nonneg.2
    (EReal.coe_le_coe_iff.1 (he 0 ▸ he _ ▸
      antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le _)))
  exact ⟨fun n ↦ (φ (U n)).toReal, he, ha0,
    (sub_le_sub (EReal.coe_le_coe_iff.1 (he 0 ▸ hS))
      (EReal.coe_le_coe_iff.1 (he _ ▸ hL _ hn))).trans (le_max_right _ _)⟩

/-- Uniform eventual bound on `d(U i ⌈t / τ i⌉₊, U j ⌈t / τ j⌉₊)²` over `t ∈ [0, T]` along a
minimizing movement family with `τ j → 0`. -/
private theorem exists_eventually_dist_ceil_sq_le {X : Type*} [PseudoMetricSpace X]
    {lam : ℝ} {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀)) {S : ℝ} (hS : ∀ j, φ (U j 0) ≤ S)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (C₁ C₂ : ℝ) (N₀ : ℕ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ i ≥ N₀, ∀ j ≥ N₀, ∀ t ∈ Icc 0 T,
      dist (U i ⌈t / τ i⌉₊) (U j ⌈t / τ j⌉₊) ^ 2 ≤
        C₁ * dist (U i 0) (U j 0) ^ 2 + C₂ * ((τ i : ℝ) + τ j) := by
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top x₀ x₁) hτ hτ0 hU hU0 hS (by positivity : 0 ≤ T + 1)
  obtain ⟨δ, hδ, hconv_ball⟩ := Metric.mem_nhdsWithin_iff.1 hconv
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 <| (hτr.eventually (gt_mem_nhds hδ)).and <|
    (hτr.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * (|lam| + 1))))).and <|
    (hτr.eventually (ge_mem_nhds one_pos)).and <| (hτ0.eventually (gt_mem_nhds hτ₀)).and hapriori
  set Kmax : ℝ := 2 * |lam| + 4 * lam ^ 2; set M : ℝ := max 0 (S - L)
  refine ⟨2 * exp (Kmax * T), (2 * exp (Kmax * T) + 8) * M, N₀, by positivity, by positivity,
    fun i hi j hj t ht ↦ ?_⟩
  have hgood (k : ℕ) (hk : N₀ ≤ k) : PenalizedConvex lam (τ k) φ ∧ |lam| * τ k ≤ 1 / 2 ∧
      (τ k : ℝ) ≤ 1 ∧ ∃ e : ℕ → ℝ, (∀ n, φ (U k n) = e n) ∧
        0 ≤ e 0 - e (⌊t / τ k⌋₊ + 1) ∧ e 0 - e (⌊t / τ k⌋₊ + 1) ≤ M := by
    obtain ⟨hkδ, hklam, hk1, hkτ₀, hkL⟩ := hN₀ k hk
    refine ⟨hconv_ball ⟨Metric.mem_ball.2
      (by simpa [NNReal.dist_eq, abs_of_nonneg (NNReal.coe_nonneg _)] using hkδ), hτ k⟩,
      (mul_le_mul_of_nonneg_left hklam (abs_nonneg lam)).trans
        (by rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]; linarith [abs_nonneg lam]),
      hk1, exists_toReal_apply_and_sub_le (hτ k) hkτ₀ h₀ (hU k) (hS k) ht fun n hn ↦ (hkL n hn).1⟩
  obtain ⟨hci, hmi, hi1, eU, heU, haU, hdropU⟩ := hgood i hi
  obtain ⟨hcj, hmj, hj1, eV, heV, haV, hdropV⟩ := hgood j hj
  have hbd := dist_ceil_sq_le_of_penalizedConvex hci hcj (hτ i) (hτ j) hmi hmj
    (hU i) (hU j) heU heV ht.1
  dsimp only at hbd
  have hexp_le : exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ i + 2 * lam ^ 2 * τ j) * t) ≤
      exp (Kmax * T) := exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
        dsimp [Kmax]
        linarith [neg_le_abs lam, mul_le_mul_of_nonneg_left hi1 (by positivity : 0 ≤ 2 * lam ^ 2),
          mul_le_mul_of_nonneg_left hj1 (by positivity : 0 ≤ 2 * lam ^ 2)]))
      ht.2 ht.1 (by positivity)
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le zero_le_two)
    (sq_nonneg (dist (U i 0) (U j 0)))
  have h2 := mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left hexp_le zero_le_two) 8)
    (add_le_add (mul_le_mul_of_nonneg_left hdropU (NNReal.coe_nonneg (τ i)))
      (mul_le_mul_of_nonneg_left hdropV (NNReal.coe_nonneg (τ j))))
    (add_nonneg (mul_nonneg (NNReal.coe_nonneg (τ i)) haU)
      (mul_nonneg (NNReal.coe_nonneg (τ j)) haV)) (by positivity)
  linarith [hbd, h1, h2, show (2 * exp (Kmax * T) + 8) * (τ i * M + τ j * M) =
    (2 * exp (Kmax * T) + 8) * M * ((τ i : ℝ) + τ j) by ring]

/-- Uniform Cauchy property of piecewise constant interpolants on `[0, T]` under
`PenalizedConvex`. -/
private theorem uniformCauchySeqOn_ceil_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {lam : ℝ} {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀)) {S : ℝ} (hS : ∀ j, φ (U j 0) ≤ S)
    {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) atTop (Icc 0 T) := by
  obtain ⟨C₁, C₂, N₀, hC₁, -, hbd⟩ :=
    exists_eventually_dist_ceil_sq_le hτ₀ h₀ hconv hτ hτ0 hU hU0 hS hT
  have hd0 : Tendsto (fun j ↦ dist (U j 0) x₀) atTop (𝓝 0) := by
    simpa using hU0.dist (tendsto_const_nhds (x := x₀))
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have herr : Tendsto (fun j ↦ 2 * C₁ * dist (U j 0) x₀ ^ 2 + C₂ * τ j) atTop (𝓝 0) := by
    simpa using ((hd0.pow 2).const_mul (2 * C₁)).add (hτr.const_mul C₂)
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (herr.eventually (gt_mem_nhds (half_pos (sq_pos_of_pos hε))))
  refine ⟨max N₀ N₁, fun i hi j hj t ht ↦ ?_⟩
  have htri : dist (U i 0) (U j 0) ^ 2 ≤ 2 * dist (U i 0) x₀ ^ 2 + 2 * dist (U j 0) x₀ ^ 2 := by
    have h1 := pow_le_pow_left₀ dist_nonneg (dist_triangle_right (U i 0) (U j 0) x₀) 2
    nlinarith [sq_nonneg (dist (U i 0) x₀ - dist (U j 0) x₀), h1]
  have hsq : dist (U i ⌈t / τ i⌉₊) (U j ⌈t / τ j⌉₊) ^ 2 < ε ^ 2 := by
    linarith [hbd i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) t ht,
      mul_le_mul_of_nonneg_left htri hC₁,
      hN₁ i ((le_max_right _ _).trans hi), hN₁ j ((le_max_right _ _).trans hj)]
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- `1/2`-Hölder continuity on `[0, T]` of a pointwise limit of minimizing movement interpolants
from `x₀`. -/
private theorem holderOnWith_of_tendsto_ceil {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (hU0 : ∀ j, U j 0 = x₀) {u : ℝ → X}
    (hlim : ∀ t ≥ 0, Tendsto (fun j ↦ U j ⌈t / (τ j : ℝ)⌉₊) atTop (𝓝 (u t))) (T : ℝ) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 2) u (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | _
  · exact ⟨0, by simp [HolderOnWith, Icc_eq_empty hT.not_ge]⟩
  set τ' : ℝ≥0 := τ₀ / 2
  have hτ' : 0 < (τ' : ℝ) := NNReal.coe_pos.2 (half_pos hτ₀)
  have hA_bot := moreauYosida_ne_bot_of_lt (half_lt_self hτ₀) (edist_ne_top x₀ x₁) h₀
  set A := (moreauYosida φ τ' x₀).toReal; set E := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A :=
    (EReal.coe_toReal (ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀)) hA_bot).symm
  have hE : φ x₀ = E :=
    (EReal.coe_toReal hx₀ (ne_bot_of_le_ne_bot hA_bot (moreauYosida_le_self φ τ' x₀))).symm
  have hAE : 0 ≤ E - A :=
    sub_nonneg.2 (EReal.coe_le_coe_iff.1 (hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀))
  set K : ℝ := 2 * (E - A) * (1 + exp (8 * (T + τ') / τ'))
  have hK : 0 ≤ K := by positivity
  set C : ℝ≥0 := ⟨Real.sqrt K, Real.sqrt_nonneg K⟩
  refine ⟨C, HolderOnWith.of_dist_le fun s hs t ht ↦ ?_⟩
  wlog hst : s ≤ t generalizing s t
  · simpa [dist_comm] using this t ht s hs (le_of_not_ge hst)
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have hrhs_lim : Tendsto (fun j ↦ 2 * (t - s + τ j) * (E - A) * (1 + exp (8 * (t + τ j) / τ')))
      atTop (𝓝 (2 * (t - s) * (E - A) * (1 + exp (8 * t / τ')))) := by
    simpa using (((tendsto_const_nhds.add hτr).const_mul 2).mul_const (E - A)).mul
      (((Real.continuous_exp.tendsto _).comp
        (((tendsto_const_nhds.add hτr).const_mul 8).div_const (τ' : ℝ))).const_add 1)
  have hle_ev : ∀ᶠ j in atTop, dist (U j ⌈s / τ j⌉₊) (U j ⌈t / τ j⌉₊) ^ 2 ≤
      2 * (t - s + τ j) * (E - A) * (1 + exp (8 * (t + τ j) / τ')) := by
    filter_upwards [hτ0.eventually (ge_mem_nhds (div_pos (half_pos hτ₀) four_pos))] with j hj4
    have h4 : 4 * τ j ≤ τ' :=
      (mul_le_mul_of_nonneg_left hj4 (by positivity)).trans_eq (mul_div_cancel₀ _ (by norm_num))
    have hed := edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent (hU j) (hτ j) h4
      (by simpa [hU0 j] using hA) (by simpa [hU0 j] using hE) hs.1 hst
    rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg] at hed
    exact (ENNReal.ofReal_le_ofReal_iff
      (by have := add_nonneg (sub_nonneg.2 hst) (NNReal.coe_nonneg (τ j)); positivity)).1 hed
  have hsq : dist (u s) (u t) ^ 2 ≤ K * dist s t := by
    have h1 := le_of_tendsto_of_tendsto (((hlim s hs.1).dist (hlim t ht.1)).pow 2) hrhs_lim hle_ev
    have hexp_le : exp (8 * t / τ') ≤ exp (8 * (T + τ') / τ') :=
      exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [ht.2, hτ'.le]) hτ'.le)
    rw [dist_comm s t, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hst)]
    exact h1.trans <| (mul_le_mul_of_nonneg_left
      (by linarith [hexp_le] : 1 + exp (8 * t / τ') ≤ 1 + exp (8 * (T + τ') / τ'))
      (mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 hst)) hAE)).trans_eq (by dsimp [K]; ring)
  refine (pow_le_pow_iff_left₀ dist_nonneg
    (mul_nonneg (NNReal.coe_nonneg C) (rpow_nonneg dist_nonneg _)) two_ne_zero).1 ?_
  have hrpow : dist s t ^ (((1 / 2 : ℝ≥0) : ℝ)) = Real.sqrt (dist s t) := by
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Real.sqrt_eq_rpow]
  rwa [show (C : ℝ) = Real.sqrt K from rfl, hrpow, mul_pow, Real.sq_sqrt hK,
    Real.sq_sqrt dist_nonneg]

/-- Passes `PenalizedConvex.apply_le` to a pointwise limit of minimizing movement interpolants on a
single positive-length interval `[s, t]`. -/
private theorem apply_le_of_tendsto_ceil {X : Type*} [PseudoMetricSpace X] {lam : ℝ}
    {φ : X → EReal} (hφ : LowerSemicontinuous φ) {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hconv : ∀ j, PenalizedConvex lam (τ j) φ)
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    {u : ℝ → X} (hlim : ∀ r ≥ 0, Tendsto (fun j ↦ U j ⌈r / (τ j : ℝ)⌉₊) atTop (𝓝 (u r)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) := by
  set N : ℕ → ℕ := fun j ↦ ⌈t / τ j⌉₊ - ⌈s / τ j⌉₊
  have hN_lim := tendsto_natCast_sub_ceil_mul hτ hτ0 hs hst.le
  obtain ⟨hpow, hsum⟩ := tendsto_one_add_mul_pow_and_sum lam (t - s) hτ hτ0 hN_lim
  have hIpos : 0 < 2 * ∫ r in 0..(t - s), exp (lam * r) :=
    mul_pos two_pos (integral_exp_mul_pos lam (sub_pos.2 hst))
  set R : ℕ → ℝ := fun j ↦
    (dist (U j ⌈s / τ j⌉₊) y ^ 2 - (1 + lam * τ j) ^ N j * dist (U j ⌈t / τ j⌉₊) y ^ 2) /
      (2 * τ j * ∑ n ∈ range (N j), (1 + lam * τ j) ^ n)
  have hR_lim : Tendsto (fun j ↦ (R j : EReal)) atTop (𝓝 ((((dist (u s) y ^ 2 -
      exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 <|
      ((((hlim s hs).dist tendsto_const_nhds).pow 2).sub
        (hpow.mul (((hlim t (hs.trans hst.le)).dist tendsto_const_nhds).pow 2))).div
      (by simpa [mul_assoc] using hsum.const_mul 2) hIpos.ne'
  have hev : ∀ᶠ j in atTop, φ (U j ⌈t / τ j⌉₊) ≤ φ y + (R j : EReal) := by
    have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
    filter_upwards [hN_lim.eventually (lt_mem_nhds (sub_pos.2 hst)),
      hτr.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (|lam| + 1)))] with j hjN hjlam
    have hNpos : 0 < N j := by
      by_contra h0; push Not at h0
      have h0' : ⌈t / (τ j : ℝ)⌉₊ - ⌈s / (τ j : ℝ)⌉₊ = 0 := Nat.le_zero.1 h0
      rw [h0', Nat.cast_zero, zero_mul] at hjN
      exact lt_irrefl 0 hjN
    have hle_st : ⌈s / τ j⌉₊ ≤ ⌈t / τ j⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (NNReal.coe_nonneg _))
    have hmτ : 0 ≤ 1 + lam * τ j := by
      have habs : -(lam * (τ j : ℝ)) ≤ |lam| * (τ j : ℝ) := by
        simpa [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)] using neg_le_abs (lam * (τ j : ℝ))
      nlinarith [(le_div_iff₀ (by positivity : 0 < |lam| + 1)).1 hjlam, abs_nonneg lam]
    have hap := (hconv j).apply_le (hτ j) hmτ
      (U := fun n ↦ U j (⌈s / τ j⌉₊ + n))
      (fun n ↦ by simpa [Nat.add_assoc] using hU j (⌈s / τ j⌉₊ + n)) hy hNpos
    simpa [R, N, Nat.add_sub_cancel' hle_st] using hap
  calc φ (u t) ≤ liminf (fun j ↦ φ (U j ⌈t / τ j⌉₊)) atTop :=
        (hφ.le_liminf (u t)).trans (hlim t (hs.trans hst.le)).liminf_le_liminf_comp
    _ ≤ limsup (fun j ↦ φ y + (R j : EReal)) atTop := (liminf_le_liminf hev).trans liminf_le_limsup
    _ ≤ limsup (fun _ : ℕ ↦ φ y) atTop + limsup (fun j ↦ (R j : EReal)) atTop :=
        EReal.limsup_add_le (.inr (by rw [hR_lim.limsup_eq]; exact EReal.coe_ne_top _))
          (.inr (by rw [hR_lim.limsup_eq]; exact EReal.coe_ne_bot _))
    _ = _ := by rw [limsup_const, hR_lim.limsup_eq]

/-- A curve on `[0, ∞)` is continuous when it is continuous on `[0, T]` for every `T ≥ 0`. -/
private theorem continuousOn_Ici_of_forall_Icc {X : Type*} [TopologicalSpace X] {u : ℝ → X}
    (h : ∀ T : ℝ, 0 ≤ T → ContinuousOn u (Icc 0 T)) : ContinuousOn u (Ici 0) := by
  intro t ht
  rw [Set.mem_Ici] at ht
  exact (h (t + 1) (by linarith) t ⟨ht, (lt_add_one t).le⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, Set.mem_Iio.2 (lt_add_one t),
      fun _ hs ↦ ⟨hs.2, hs.1.le⟩⟩)

/-- If `0 ≤ τ ≤ 1 / (2 (|lam| + 1))`, then `0 < 1 + lam * τ`. -/
private theorem one_add_mul_pos_of_le (lam : ℝ) {τ : ℝ} (h0 : 0 ≤ τ)
    (hτ : τ ≤ 1 / (2 * (|lam| + 1))) : 0 < 1 + lam * τ := by
  have habs : -(lam * τ) ≤ |lam| * τ :=
    by simpa [abs_mul, abs_of_nonneg h0] using neg_le_abs (lam * τ)
  have hlt : |lam| * (1 / (2 * (|lam| + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith [abs_nonneg lam]
  nlinarith [mul_le_mul_of_nonneg_left hτ (abs_nonneg lam), habs, hlt]

/-- Builds a concrete positive time-step sequence `τ_ref j → 0` small enough for penalized
convexity, `1 + lam * τ_ref j > 0`, and global coercivity. -/
private theorem exists_ref_step_seq {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    ∃ τ_ref : ℕ → ℝ≥0, (∀ j, 0 < τ_ref j) ∧ Tendsto τ_ref atTop (𝓝 0) ∧
      (∀ j, PenalizedConvex lam (τ_ref j) φ) ∧ (∀ j, 0 < 1 + lam * τ_ref j) ∧
      ∀ j z, moreauYosida φ (τ_ref j) z ≠ ⊥ := by
  obtain ⟨δ, hδ, hconv_ball⟩ := Metric.mem_nhdsWithin_iff.1 hconv
  set c : ℝ := min ((τ₀ : ℝ) / 2) (min (δ / 2) (1 / (2 * (|lam| + 1))))
  have hc_pos : 0 < c := by positivity
  set τ_ref : ℕ → ℝ≥0 := fun j ↦ ⟨c / (j + 1 : ℝ), by positivity⟩
  have hτ_pos (j : ℕ) : 0 < τ_ref j := NNReal.coe_pos.1 (div_pos hc_pos (Nat.cast_add_one_pos j))
  have hτ_le (j : ℕ) : (τ_ref j : ℝ) ≤ c :=
    div_le_self hc_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hτ_0 : Tendsto τ_ref atTop (𝓝 0) := NNReal.tendsto_coe.1 <| by
    change Tendsto (fun j : ℕ ↦ c / (j + 1 : ℝ)) atTop (𝓝 0)
    simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
  refine ⟨τ_ref, hτ_pos, hτ_0, fun j ↦ hconv_ball ⟨Metric.mem_ball.2 ?_, hτ_pos j⟩,
    fun j ↦ one_add_mul_pos_of_le lam (NNReal.coe_nonneg _)
      ((hτ_le j).trans ((min_le_right _ _).trans (min_le_right _ _))),
    fun j z ↦ moreauYosida_ne_bot_of_lt (NNReal.coe_lt_coe.1 <| (hτ_le j).trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self (NNReal.coe_pos.2 hτ₀)))) (edist_ne_top z x₁) h₀⟩
  rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact (hτ_le j).trans_lt ((min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt
    (half_lt_self hδ)))

/-- Constructs a reference minimizing movement family `(τ_ref, U_ref)` starting at `x₀` whose
piecewise constant interpolants converge pointwise on `[0, ∞)` to an `EVI_lam` solution `u` with
`u 0 = x₀`. -/
private theorem exists_ref_minimizingMovement {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {lam : ℝ} {φ : X → EReal} (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ (τ_ref : ℕ → ℝ≥0) (U_ref : ℕ → ℕ → X) (u : ℝ → X),
      (∀ j, 0 < τ_ref j) ∧ Tendsto τ_ref atTop (𝓝 0) ∧ (∀ j, U_ref j 0 = x₀) ∧
      (∀ j, φ (U_ref j 0) ≤ ((φ x₀).toReal : EReal)) ∧
      (∀ j n, U_ref j (n + 1) ∈ moreauYosidaResolvent φ (τ_ref j) (U_ref j n)) ∧
      u 0 = x₀ ∧ (∀ t ≥ 0, Tendsto (fun j ↦ U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) atTop (𝓝 (u t))) ∧
      IsEVISolution lam φ u := by
  have hbot_all (z : X) : φ z ≠ ⊥ := fun hb ↦
    h₀ (le_bot_iff.1 (by simpa [hb] using moreauYosida_le φ τ₀ (edist_ne_top x₁ z)))
  obtain ⟨τ_ref, hτ_pos, hτ_0, hconv_ref, hm_ref, hne_bot⟩ := exists_ref_step_seq hτ₀ h₀ hconv
  choose U_ref hU_ref0 hU_ref using fun j ↦
    (hconv_ref j).exists_forall_mem_moreauYosidaResolvent hφ (hτ_pos j) (hm_ref j) (hne_bot j) x₀
  have hS_ref (j : ℕ) : φ (U_ref j 0) ≤ ((φ x₀).toReal : EReal) := by
    rw [hU_ref0 j, EReal.coe_toReal hx₀ (hbot_all x₀)]
  have hcauchy_pt (t : ℝ) (ht : 0 < t) : CauchySeq (fun j ↦ U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) := by
    have huc := uniformCauchySeqOn_ceil_of_penalizedConvex hτ₀ h₀ hconv hτ_pos hτ_0 hU_ref
      (by simpa only [hU_ref0] using tendsto_const_nhds) hS_ref ht.le
    exact Metric.cauchySeq_iff.2 fun ε hε ↦
      let ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.1 huc) ε hε
      ⟨N, fun i hi j hj ↦ hN i hi j hj t ⟨ht.le, le_rfl⟩⟩
  choose u_pos hu_pos using fun (t : {t : ℝ // 0 < t}) ↦
    cauchySeq_tendsto_of_complete (hcauchy_pt t.1 t.2)
  set u : ℝ → X := fun t ↦ if ht : 0 < t then u_pos ⟨t, ht⟩ else x₀
  have hlim_ref (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun j ↦ U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) atTop (𝓝 (u t)) := by
    rcases ht.eq_or_lt with rfl | ht_pos
    · simpa only [u, lt_irrefl, ↓reduceDIte, Nat.ceil_zero, zero_div, hU_ref0] using
        tendsto_const_nhds
    · simpa [u, ht_pos] using hu_pos ⟨t, ht_pos⟩
  have hhold := holderOnWith_of_tendsto_ceil hτ₀ h₀ hx₀ hτ_pos hτ_0 hU_ref hU_ref0 hlim_ref
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T _ ↦
    let ⟨_, hC⟩ := hhold T; hC.continuousOn (by positivity)
  refine ⟨τ_ref, U_ref, u, hτ_pos, hτ_0, hU_ref0, hS_ref, hU_ref, by simp [u], hlim_ref, ?_⟩
  exact isEVISolution_of_apply_le hφ hu_cont
    (fun t ht ↦ ne_top_of_le_ne_top (EReal.add_ne_top hx₀ (EReal.coe_ne_top _))
      (apply_le_of_tendsto_ceil hφ hτ_pos hτ_0 hconv_ref hU_ref hlim_ref hx₀ le_rfl ht))
    (fun t _ ↦ hbot_all (u t))
    (fun _ hy _ _ hs hst ↦
      apply_le_of_tendsto_ceil hφ hτ_pos hτ_0 hconv_ref hU_ref hlim_ref hy hs hst)

/-- **Generation of `EVI_λ` solutions by minimizing movements** (Ambrosio–Gigli–Savaré,
Theorem 4.0.4). Let `φ` be a lower semicontinuous energy on a complete pseudometric space such that
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁`, and suppose `TauCeti.PenalizedConvex lam τ φ` holds
for all sufficiently small `τ > 0`. Then for every `x₀` with `φ x₀ ≠ ⊤` there exists an `EVI_lam`
solution `u` starting at `x₀` such that along any positive time steps `τ j → 0` and any minimizing
movement sequences `U j` whose initial points converge to `x₀` with uniformly bounded energy, the
piecewise constant interpolants `t ↦ U j ⌈t / τ j⌉₊` converge to `u` uniformly on `[0, T]` for
every `T`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ_ref, U_ref, u, hτ_ref_pos, hτ_ref_0, hU_ref0, hS_ref, hU_ref, hu0, hlim_ref, hevi⟩ :=
    exists_ref_minimizingMovement hφ hτ₀ h₀ hconv hx₀
  refine ⟨u, hu0, hevi, fun τ U hτ_ne hτ0 hU0 ⟨S, hS⟩ hU T ↦ ?_⟩
  rcases lt_or_ge T 0 with hT | hT
  · simp [Metric.tendstoUniformlyOn_iff, Icc_eq_empty hT.not_ge]
  have hτ_pos (j : ℕ) : 0 < τ j := pos_iff_ne_zero.2 (hτ_ne j)
  -- Interleave `(τ, U)` with `(τ_ref, U_ref)` so uniform Cauchy identifies both limits on `[0, T]`.
  let τ_mix : ℕ → ℝ≥0 := fun k ↦ if Even k then τ (k / 2) else τ_ref (k / 2)
  let U_mix : ℕ → ℕ → X := fun k ↦ if Even k then U (k / 2) else U_ref (k / 2)
  have hdiv : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop :=
    tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨2 * b, fun k hk ↦ by omega⟩
  have hτ_mix_pos (k : ℕ) : 0 < τ_mix k := by
    dsimp [τ_mix]; split_ifs <;> [exact hτ_pos _; exact hτ_ref_pos _]
  have hτ_mix_0 : Tendsto τ_mix atTop (𝓝 0) :=
    Tendsto.if' (hτ0.comp hdiv) (hτ_ref_0.comp hdiv)
  have hU_mix_0 : Tendsto (fun k ↦ U_mix k 0) atTop (𝓝 x₀) :=
    (Tendsto.if' (p := Even) (hU0.comp hdiv)
      (by simpa only [Function.comp_def, hU_ref0] using tendsto_const_nhds)).congr
      fun k ↦ by dsimp [U_mix]; split_ifs <;> simp [hU_ref0]
  have hS_mix (k : ℕ) : φ (U_mix k 0) ≤ ((max S (φ x₀).toReal : ℝ) : EReal) := by
    dsimp [U_mix]; split_ifs
    · exact (hS _).trans (EReal.coe_le_coe_iff.2 (le_max_left _ _))
    · exact (hS_ref _).trans (EReal.coe_le_coe_iff.2 (le_max_right _ _))
  have hU_mix (k n : ℕ) : U_mix k (n + 1) ∈ moreauYosidaResolvent φ (τ_mix k) (U_mix k n) := by
    dsimp [U_mix, τ_mix]; split_ifs <;> [exact hU _ n; exact hU_ref _ n]
  have huc_mix := uniformCauchySeqOn_ceil_of_penalizedConvex hτ₀ h₀ hconv hτ_mix_pos hτ_mix_0
    hU_mix hU_mix_0 hS_mix hT
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (Metric.uniformCauchySeqOn_iff.1 huc_mix) (ε / 2) (half_pos hε)
  have huc_ref := uniformCauchySeqOn_ceil_of_penalizedConvex hτ₀ h₀ hconv hτ_ref_pos hτ_ref_0
    hU_ref (by simpa only [hU_ref0] using tendsto_const_nhds) hS_ref hT
  have hunif_ref := huc_ref.tendstoUniformlyOn_of_tendsto fun t ht ↦ hlim_ref t ht.1
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.1 hunif_ref) (ε / 2) (half_pos hε))
  refine eventually_atTop.2 ⟨max N₁ N₂, fun j hj t ht ↦ ?_⟩
  have h1 := hN₁ (2 * j) (by omega) (2 * j + 1) (by omega) t ht
  have heven : Even (2 * j) := ⟨j, by ring⟩
  have hodd : ¬Even (2 * j + 1) := by intro ⟨m, hm⟩; omega
  have h1' : dist (U j ⌈t / (τ j : ℝ)⌉₊) (U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) < ε / 2 := by
    simpa [U_mix, τ_mix, heven, hodd, show 2 * j / 2 = j by omega,
      show (2 * j + 1) / 2 = j by omega] using h1
  have h2 := hN₂ j ((le_max_right _ _).trans hj) t ht
  exact (dist_triangle _ (U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) _).trans_lt
    (by linarith [(dist_comm (U j ⌈t / (τ j : ℝ)⌉₊) (U_ref j ⌈t / (τ_ref j : ℝ)⌉₊))])

/-- On a complete metric space, under coercivity and `TauCeti.PenalizedConvex` for small time
steps, every metric generalized minimizing movement of a lower semicontinuous energy is an
`EVI_lam` solution. -/
theorem IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex {X : Type*}
    [MetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal} {x₀ : X} {v : ℝ → X}
    (hv : IsGeneralizedMinimizingMovement 𝓝 φ x₀ v) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    IsEVISolution lam φ v := by
  obtain ⟨τ, U, hτ, hτ0, hU, hU0, ⟨S, hS⟩, hlim⟩ := isGeneralizedMinimizingMovement_iff.1 hv
  have hx₀ : φ x₀ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top S) <|
    ((hφ.le_liminf x₀).trans hU0.liminf_le_liminf_comp).trans
      ((liminf_le_liminf (Eventually.of_forall hS)).trans_eq (by simp [liminf_const]))
  obtain ⟨u, -, hu, hunif⟩ :=
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv hx₀
  refine hu.congr fun t (ht : 0 ≤ t) ↦ ?_
  have h1 := (hunif τ U (fun j ↦ (hτ j).ne') hτ0 hU0 ⟨S, hS⟩ hU t).tendsto_at
    (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  exact tendsto_nhds_unique h1 (hlim t ht)

/-- **Domain of the `EVI_λ` flow under penalized convexity** (Ambrosio–Gigli–Savaré,
Theorem 4.0.4). On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁`, and is penalized convex for all sufficiently small
positive time steps, then an `EVI_lam` solution starts from a point `x` if and only if `x` lies in
the closure of `{y | φ y ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal} (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} := by
  refine Subset.antisymm eviDomain_subset_closure fun x hx ↦ ?_
  have hbot_all (z : X) : φ z ≠ ⊥ := fun hb ↦
    h₀ (le_bot_iff.1 (by simpa [hb] using moreauYosida_le φ τ₀ (edist_ne_top x₁ z)))
  obtain ⟨x_seq, hx_top, hx_lim⟩ := mem_closure_iff_seq_limit.1 hx
  choose u_seq hu_seq0 hu_seq _ using fun k ↦
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv (hx_top k)
  have huc (T : ℝ) : UniformCauchySeqOn u_seq atTop (Icc 0 T) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 hx_lim.cauchySeq)
      (ε / (exp (|lam| * T) + 1)) (by positivity)
    refine ⟨N, fun i hi j hj t ht ↦ ?_⟩
    have hd := (hu_seq i).dist_le (hu_seq j) hφ ht.1
    rw [hu_seq0 i, hu_seq0 j] at hd
    have hexp : exp (-(lam * t)) ≤ exp (|lam| * T) := exp_le_exp.2 <|
      calc -(lam * t) = -lam * t := by ring
        _ ≤ |lam| * t := mul_le_mul_of_nonneg_right (neg_le_abs lam) ht.1
        _ ≤ |lam| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg lam)
    calc dist (u_seq i t) (u_seq j t)
        ≤ exp (|lam| * T) * dist (x_seq i) (x_seq j) :=
          hd.trans (mul_le_mul_of_nonneg_right hexp dist_nonneg)
      _ < (exp (|lam| * T) + 1) * (ε / (exp (|lam| * T) + 1)) := by
          have hlt := hN i hi j hj
          nlinarith [dist_nonneg (x := x_seq i) (y := x_seq j), exp_pos (|lam| * T)]
      _ = ε := mul_div_cancel₀ _ (by positivity)
  have hcauchy_pt (t : ℝ) (ht : 0 < t) : CauchySeq (fun k ↦ u_seq k t) :=
    Metric.cauchySeq_iff.2 fun ε hε ↦
      let ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.1 (huc t)) ε hε
      ⟨N, fun i hi j hj ↦ hN i hi j hj t ⟨ht.le, le_rfl⟩⟩
  choose u_pos hu_pos using fun (t : {t : ℝ // 0 < t}) ↦
    cauchySeq_tendsto_of_complete (hcauchy_pt t.1 t.2)
  set u : ℝ → X := fun t ↦ if ht : 0 < t then u_pos ⟨t, ht⟩ else x
  have hlim (t : ℝ) (ht : 0 ≤ t) : Tendsto (fun k ↦ u_seq k t) atTop (𝓝 (u t)) := by
    rcases ht.eq_or_lt with rfl | ht_pos
    · simpa [u, hu_seq0] using hx_lim
    · simpa [u, ht_pos] using hu_pos ⟨t, ht_pos⟩
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T _ ↦
    ((huc T).tendstoUniformlyOn_of_tendsto fun t ht ↦ hlim t ht.1).continuousOn
      (Eventually.of_forall fun k ↦ (hu_seq k).continuousOn.mono Icc_subset_Ici_self).frequently
  exact mem_eviDomain.2 ⟨u, (hφ.tendstoGamma_const).isEVISolution_of_tendsto (fun _ ↦ hφ)
    hu_seq hlim hu_cont ⟨x_seq 0, hx_top 0⟩ (fun t _ ↦ hbot_all (u t)), by simp [u]⟩

end Convergence

/-! ### Convexity along curves with `2`-convex squared distance and CAT(0) spaces -/

section CurveConvexity

/-- Under Ambrosio–Gigli Assumption 3.24 (`lam`-convexity of `φ` and `2`-convexity of `d(·, w)²`
along connecting curves for every base `w`), `φ` is penalized convex for every positive time step,
and choosing `w = v₀` yields `d(v₀, γ t) ≤ t d(v₀, v₁)`. -/
private theorem penalizedConvex_and_dist_le_of_convexAlong_and_dist_sq_le {X : Type*}
    [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ) :
    (∀ τ : ℝ≥0, 0 < τ → PenalizedConvex lam τ φ) ∧
      ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, dist v₀ (γ t) ≤ t * dist v₀ v₁) ∧ ConvexAlong lam φ γ := by
  refine ⟨fun τ hτ ↦ penalizedConvex_def.2 fun w v₀ v₁ hv₀ hv₁ ↦ ?_, fun v₀ v₁ hv₀ hv₁ ↦ ?_⟩
  · obtain ⟨γ, h0, h1, hφγ, hdγ⟩ := hconv w hv₀ hv₁
    refine ⟨γ, h0, h1, ?_⟩
    have hd := hdγ.const_mul (c := 1 / (2 * (τ : ℝ))) (by positivity)
    convert hφγ.add hd using 1
    · ring
    · funext z
      rw [Pi.add_apply, ← EReal.coe_mul, dist_comm]
      congr 2; ring
  · obtain ⟨γ, h0, h1, hφγ, hdγ⟩ := hconv v₀ hv₀ hv₁
    refine ⟨γ, h0, h1, fun t ht ↦ ?_, hφγ⟩
    have hd := convexAlong_def.1 hdγ t ht
    rw [h0, h1, dist_self, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
      EReal.coe_le_coe_iff, dist_comm v₁ v₀] at hd
    have hsq : dist v₀ (γ t) ^ 2 ≤ (t * dist v₀ v₁) ^ 2 := by
      rw [dist_comm v₀ (γ t)]; nlinarith [hd]
    exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg ht.1 dist_nonneg) two_ne_zero).1 hsq

/-- **Generation of `EVI_λ` flows under convexity along curves** (Ambrosio–Gigli, Theorem 3.25).
Let `φ` be a lower semicontinuous energy on a complete pseudometric space that never takes the
value `⊥`. Suppose that for every base point `w` and any two points `v₀`, `v₁` of `{y | φ y ≠ ⊤}`
there is a curve `γ` from `v₀` to `v₁` along which `φ` is `lam`-convex and `z ↦ d(z, w)²` is
`2`-convex. Then coercivity holds automatically, and for every `x₀` with `φ x₀ ≠ ⊤` there is an
`EVI_lam` solution `u` from `x₀` to which minimizing movement interpolants converge locally
uniformly. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_dist_sq_le {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨hp, hlin⟩ := penalizedConvex_and_dist_le_of_convexAlong_and_dist_sq_le hconv
  set τ₀ : ℝ≥0 := ⟨1 / (2 * (|lam| + 1)), by positivity⟩
  have hτ₀ : 0 < τ₀ := NNReal.coe_pos.1 (div_pos one_pos (by positivity))
  have hmτ₀ : 0 < 1 + lam * τ₀ := one_add_mul_pos_of_le lam (NNReal.coe_nonneg τ₀) le_rfl
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀
    (moreauYosida_ne_bot_of_convexAlong hφ hbot hlin hmτ₀ x₀)
    (eventually_nhdsWithin_of_forall fun τ (hτ : 0 < τ) ↦ hp τ hτ) hx₀

/-- Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_dist_sq_le`, the domain of the
`EVI_lam` flow equals `closure {y | φ y ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_convexAlong_and_dist_sq_le {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {y : X | φ y ≠ ⊤} with hemp | ⟨x₁, -⟩
  · exact Subset.antisymm (eviDomain_subset_closure.trans (by simp [hemp]))
      (by simp [hemp])
  obtain ⟨hp, hlin⟩ := penalizedConvex_and_dist_le_of_convexAlong_and_dist_sq_le hconv
  set τ₀ : ℝ≥0 := ⟨1 / (2 * (|lam| + 1)), by positivity⟩
  have hτ₀ : 0 < τ₀ := NNReal.coe_pos.1 (div_pos one_pos (by positivity))
  have hmτ₀ : 0 < 1 + lam * τ₀ := one_add_mul_pos_of_le lam (NNReal.coe_nonneg τ₀) le_rfl
  exact eviDomain_eq_closure_of_penalizedConvex hφ hτ₀
    (moreauYosida_ne_bot_of_convexAlong hφ hbot hlin hmτ₀ x₁)
    (eventually_nhdsWithin_of_forall fun τ (hτ : 0 < τ) ↦ hp τ hτ)

/-- **Generation of `EVI_λ` flows on CAT(0) spaces.** On a complete CAT(0) space, every lower
semicontinuous `lam`-geodesically convex energy that never takes the value `⊥` generates an
`EVI_lam` solution from each `x₀` with `φ x₀ ≠ ⊤`, obtained as the locally uniform metric limit of
minimizing movement interpolants. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X] {lam : ℝ} {φ : X → EReal}
    (h : GeodesicallyConvex lam φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) :=
  exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_dist_sq_le hφ hbot
    (fun w _ _ h₀ h₁ ↦
      let ⟨γ, hγ, hc⟩ := geodesicallyConvex_def.1 h h₀ h₁
      ⟨γ, hγ.source, hγ.target, hc,
        convexAlongGeodesics_def.1 (convexAlongGeodesics_dist_sq w)
          (EReal.coe_ne_top _) (EReal.coe_ne_top _) hγ⟩)
    hx₀

/-- On a complete CAT(0) space, the `EVI_lam` domain of a lower semicontinuous `lam`-geodesically
convex energy that never takes the value `⊥` equals `closure {y | φ y ≠ ⊤}`. -/
theorem GeodesicallyConvex.eviDomain_eq_closure {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X] {lam : ℝ} {φ : X → EReal}
    (h : GeodesicallyConvex lam φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} :=
  eviDomain_eq_closure_of_convexAlong_and_dist_sq_le hφ hbot fun w _ _ h₀ h₁ ↦
    let ⟨γ, hγ, hc⟩ := geodesicallyConvex_def.1 h h₀ h₁
    ⟨γ, hγ.source, hγ.target, hc,
      convexAlongGeodesics_def.1 (convexAlongGeodesics_dist_sq w)
        (EReal.coe_ne_top _) (EReal.coe_ne_top _) hγ⟩

end CurveConvexity

end TauCeti
