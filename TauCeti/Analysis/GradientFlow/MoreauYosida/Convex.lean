/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic

/-!
# The discrete variational inequality for resolvents of convex energies

Let `φ : X → EReal` be an energy on a metric space, `m : ℝ` and `τ > 0` a time step. The
convexity hypothesis under which Ambrosio–Gigli–Savaré prove that minimizing movements converge to
the `EVI_m` gradient flow (their Assumption 4.0.1) is that the penalized energies of the resolvent
are uniformly convex along some curve: for every base point `w` and any two points `v₀`, `v₁` of
the effective domain `{x | φ x ≠ ⊤}` there is a curve `γ` from `v₀` to `v₁` along which

`z ↦ φ z + d(w, z)² / (2τ)` is `(m + 1 / τ)`-convex

(`TauCeti.PenalizedConvex m τ φ`). This holds when `φ` is `m`-geodesically convex on a CAT(0)
space, where the squared distance from `w` is `2`-convex along every geodesic
(`TauCeti.GeodesicallyConvex.penalizedConvex`), and, on the quadratic Wasserstein space, when `φ`
is `m`-convex along generalized geodesics based at every law and `1 + m τ ≥ 0`
(`TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`). Ordinary geodesic convexity is not
enough in general, because the squared distance from a point need not be convex along geodesics.
Ambrosio–Gigli–Savaré take the base point `w` in the effective domain; it is arbitrary here, as in
both examples.

Under this hypothesis a resolvent step `y ∈ J_τ x` satisfies the *discrete variational inequality*
(`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent`): for every `v` with
`φ v ≠ ⊤`,

`φ y + d(x, y)² / (2τ) + d(y, v)² / (2τ) + (m / 2) d(y, v)² ≤ φ v + d(x, v)² / (2τ)`.

The penalized energy at `x` is smallest at `y`, so it grows at least quadratically along the curve
from `y` to `v` (`TauCeti.ConvexAlong.apply_add_le_of_forall_le`). Read as
`(d(y, v)² - d(x, v)²) / (2τ) + (m / 2) d(y, v)² ≤ φ v - φ y - d(x, y)² / (2τ)`, this is the
implicit Euler discretization of the evolution variational inequality
`(1/2) d/dt d(u t, v)² + (m / 2) d(u t, v)² ≤ φ v - φ (u t)` (`TauCeti.IsEVISolution`). In
particular, when `1 + m τ > 0` and `φ` never takes the value `⊥` and is finite somewhere, the
resolvent has at most one point (`TauCeti.PenalizedConvex.subsingleton_moreauYosidaResolvent`).

Along a minimizing movement sequence `U` with `U (n + 1) ∈ J_τ (U n)`, the discrete variational
inequality reads `r d(U (n + 1), v)² - d(U n, v)² ≤ 2τ (φ v - φ (U (n + 1)))` with
`r = 1 + m τ`. When `r ≥ 0`, multiplying by `r ^ n` and summing, with the energy nonincreasing,
gives the discrete integrated inequality (`TauCeti.PenalizedConvex.pow_mul_dist_sq_sub_le`)

`r ^ N d(U N, v)² / 2 - d(U 0, v)² / 2 ≤ τ (∑_{n < N} r ^ n) (φ v - φ (U N))`.

This is the discrete form of the integrated evolution variational inequality
`TauCeti.IsEVISolution.exp_mul_dist_sq_sub_le`: `r ^ N` replaces `e^{m N τ}` and
`τ ∑_{n < N} r ^ n` replaces `∫₀^{Nτ} e^{m s} ds`. Still for `r ≥ 0`, it gives the energy
regularization estimate
`φ (U N) ≤ φ v + (d(U 0, v)² - r ^ N d(U N, v)²) / (2τ ∑_{n < N} r ^ n)` for `N ≥ 1`
(`TauCeti.PenalizedConvex.apply_le`), which for `m = 0` is the rate
`φ (U N) ≤ φ v + d(U 0, v)² / (2 N τ)`, and the weighted distance estimate
`r ^ N d(U N, v)² ≤ d(U 0, v)²` towards a point `v` of smaller energy, such as a minimizer of `φ`
(`TauCeti.PenalizedConvex.pow_mul_dist_sq_le`). For `m > 0` and a fixed minimizer `v` of finite
energy, this is geometric convergence of the scheme to `v`. These are the a priori estimates on
which the convergence of minimizing movements to the `EVI_m` flow rests.

## Main definitions

* `TauCeti.PenalizedConvex m τ φ`: the penalized energies `φ + d(w, ·)² / (2τ)` are
  `(m + 1 / τ)`-convex along some curve between any two points of finite energy.

## Main results

* `TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent`: the discrete variational
  inequality.
* `TauCeti.PenalizedConvex.eq_of_mem_moreauYosidaResolvent` and
  `TauCeti.PenalizedConvex.subsingleton_moreauYosidaResolvent`: uniqueness of the resolvent step
  when `1 + m τ > 0`, for a resolvent step of finite energy, respectively for an energy that
  never takes the value `⊥` and is finite somewhere.
* `TauCeti.PenalizedConvex.pow_mul_dist_sq_sub_le`: the discrete integrated evolution variational
  inequality along a minimizing movement sequence, when `1 + m τ ≥ 0`.
* `TauCeti.PenalizedConvex.apply_le`: the discrete energy regularization estimate, when
  `1 + m τ ≥ 0`.
* `TauCeti.PenalizedConvex.pow_mul_dist_sq_le`: the weighted distance estimate of a minimizing
  movement sequence towards points of smaller energy, when `1 + m τ ≥ 0`.
* `TauCeti.GeodesicallyConvex.penalizedConvex`: on a CAT(0) space, an `m`-geodesically convex
  energy satisfies the hypothesis for every time step.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Assumption 4.0.1, Theorem 4.1.2 and
  Section 4.1.
-/

public section

open Finset Set
open scoped NNReal ENNReal

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {m m' : ℝ} {τ : ℝ≥0} {φ : X → EReal} {x y v : X}

/-- The energy `φ` is *penalized convex* with parameter `m` and time step `τ`: for every base point
`w` and any two points `v₀`, `v₁` with `φ v₀ ≠ ⊤` and `φ v₁ ≠ ⊤` (energy `⊥` is allowed), some
curve `γ` from `v₀` to `v₁` makes the penalized energy `z ↦ φ z + d(w, z)² / (2τ)` of the resolvent
`(m + 1 / τ)`-convex along it. This is Assumption 4.0.1 of Ambrosio–Gigli–Savaré at the time step
`τ`, there stated with the coefficient `(1 + m τ) / τ = m + 1 / τ`. -/
def PenalizedConvex (m : ℝ) (τ : ℝ≥0) (φ : X → EReal) : Prop :=
  ∀ ⦃w v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
    ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist w z ^ 2 / (2 * τ) : ℝ) : EReal)) γ

/-- The defining condition of penalized convexity. -/
theorem penalizedConvex_def :
    PenalizedConvex m τ φ ↔ ∀ ⦃w v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧
      γ 1 = v₁ ∧
        ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist w z ^ 2 / (2 * τ) : ℝ) : EReal)) γ :=
  Iff.rfl

/-- Penalized convexity with a parameter `m` implies it for every smaller parameter. -/
theorem PenalizedConvex.mono (h : PenalizedConvex m τ φ) (hm : m' ≤ m) :
    PenalizedConvex m' τ φ := fun _ _ _ h₀ h₁ ↦
  (h h₀ h₁).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.1, hγ.2.2.mono (by linarith)⟩

/-- On a CAT(0) space, an `m`-geodesically convex energy is penalized convex with parameter `m`
for every time step, along the geodesics that witness its convexity: the squared distance from a
point is `2`-convex along every geodesic. -/
theorem GeodesicallyConvex.penalizedConvex [IsCATZeroSpace X] (h : GeodesicallyConvex m φ) :
    PenalizedConvex m τ φ := by
  intro w v₀ v₁ h₀ h₁
  obtain ⟨γ, hγ, hφγ⟩ := geodesicallyConvex_def.1 h h₀ h₁
  refine ⟨γ, hγ.source, hγ.target, ?_⟩
  have hd := (convexAlongGeodesics_def.1 (convexAlongGeodesics_dist_sq w) (EReal.coe_ne_top _)
    (EReal.coe_ne_top _) hγ).const_mul (c := 1 / (2 * τ)) (by positivity)
  convert hφγ.add hd using 1
  · ring
  · funext z
    rw [Pi.add_apply, ← EReal.coe_mul, dist_comm]
    congr 2
    ring

/-- **The discrete variational inequality.** If `φ` is penalized convex with parameter `m` and time
step `τ > 0`, then a resolvent step `y ∈ J_τ x` satisfies, for every `v` with `φ v ≠ ⊤`,

`φ y + d(x, y)² / (2τ) + d(y, v)² / (2τ) + (m / 2) d(y, v)² ≤ φ v + d(x, v)² / (2τ)`.

This is the implicit Euler form of the evolution variational inequality `EVI_m`. -/
theorem PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent (h : PenalizedConvex m τ φ)
    (hτ : 0 < τ) (hy : y ∈ moreauYosidaResolvent φ τ x) (hv : φ v ≠ ⊤) :
    φ y + ((dist x y ^ 2 / (2 * τ) + dist y v ^ 2 / (2 * τ) + m / 2 * dist y v ^ 2 : ℝ) : EReal) ≤
      φ v + ((dist x v ^ 2 / (2 * τ) : ℝ) : EReal) := by
  have hmin := apply_add_le_apply_add_of_mem_moreauYosidaResolvent hτ hy
  have hy' : φ y ≠ ⊤ := by
    intro hy'
    have := (hmin v).trans_lt (EReal.add_lt_top hv (EReal.coe_ne_top _))
    simp [hy'] at this
  obtain ⟨γ, h₀, h₁, hγ⟩ := h (w := x) hy' hv
  have key := hγ.apply_add_le_of_forall_le fun t _ ↦ h₀ ▸ hmin (γ t)
  simp only [h₀, h₁] at key
  rw [add_assoc, ← EReal.coe_add] at key
  have hτ' : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.2 hτ).ne'
  have hc : dist x y ^ 2 / (2 * τ) + dist y v ^ 2 / (2 * τ) + m / 2 * dist y v ^ 2 =
      dist x y ^ 2 / (2 * τ) + (m + (τ : ℝ)⁻¹) / 2 * dist y v ^ 2 := by
    field_simp
    ring
  rwa [hc]

end PseudoMetricSpace

section MetricSpace

variable {X : Type*} [MetricSpace X] {m : ℝ} {τ : ℝ≥0} {φ : X → EReal} {x y y' : X}

/-- **Uniqueness of the resolvent step.** If `φ` is penalized convex with parameter `m` and time
step `τ > 0` with `1 + m τ > 0`, then two resolvent steps `y, y' ∈ J_τ x`, the first of finite
energy, are equal. -/
theorem PenalizedConvex.eq_of_mem_moreauYosidaResolvent (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hy : y ∈ moreauYosidaResolvent φ τ x)
    (hy' : y' ∈ moreauYosidaResolvent φ τ x) (htop : φ y ≠ ⊤) (hbot : φ y ≠ ⊥) : y = y' := by
  have heq := le_antisymm (apply_add_le_apply_add_of_mem_moreauYosidaResolvent hτ hy y')
    (apply_add_le_apply_add_of_mem_moreauYosidaResolvent hτ hy' y)
  have hy't : φ y' ≠ ⊤ := by
    intro h'
    rw [h', EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at heq
    exact htop (by simpa using heq)
  have hvi := h.apply_add_le_of_mem_moreauYosidaResolvent hτ hy hy't
  rw [← heq] at hvi
  lift φ y to ℝ using ⟨htop, hbot⟩ with a
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hvi
  have hτ' : (0 : ℝ) < τ := hτ
  -- The discrete variational inequality at `v = y'` leaves `(1 + m τ) / (2τ) d(y, y')² ≤ 0`.
  have hd : (1 + m * τ) / (2 * τ) * dist y y' ^ 2 ≤ 0 := by
    have : (1 + m * τ) / (2 * τ) * dist y y' ^ 2 =
        dist y y' ^ 2 / (2 * τ) + m / 2 * dist y y' ^ 2 := by
      field_simp
    linarith
  have hk : 0 < (1 + m * τ) / (2 * τ) := by positivity
  have hd' : dist y y' ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hd hk
  exact dist_le_zero.1 (by nlinarith [dist_nonneg (x := y) (y := y')])

/-- **Uniqueness of the resolvent step.** If `φ` never takes the value `⊥`, is finite somewhere,
and is penalized convex with parameter `m` and time step `τ > 0` with `1 + m τ > 0`, then every
resolvent `J_τ x` has at most one point. -/
theorem PenalizedConvex.subsingleton_moreauYosidaResolvent (h : PenalizedConvex m τ φ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (hbot : ∀ z, φ z ≠ ⊥) (hdom : ∃ z, φ z ≠ ⊤) (x : X) :
    (moreauYosidaResolvent φ τ x).Subsingleton := by
  obtain ⟨z, hz⟩ := hdom
  intro y hy y' hy'
  refine h.eq_of_mem_moreauYosidaResolvent hτ hmτ hy hy' (fun htop ↦ ?_) (hbot y)
  have := (apply_add_le_apply_add_of_mem_moreauYosidaResolvent hτ hy z).trans_lt
    (EReal.add_lt_top hz (EReal.coe_ne_top _))
  simp [htop] at this

end MetricSpace

section MinimizingMovement

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ : ℝ≥0} {φ : X → EReal} {v : X}
  {U : ℕ → X}

/-- One step of a minimizing movement sequence in the discrete variational inequality, with the
energy of the step bounded below by the energy `φ (U N)` reached later. -/
private theorem PenalizedConvex.mul_dist_sq_sub_le (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) (hv : φ v ≠ ⊤) {N : ℕ}
    (hN : φ (U N) ≠ ⊥) {c : ℝ} (hc : φ v - φ (U N) ≤ c) {n : ℕ} (hn : n < N) :
    (1 + m * τ) * dist (U (n + 1)) v ^ 2 - dist (U n) v ^ 2 ≤ 2 * τ * c := by
  have hvi := h.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) hv
  have hmono : φ (U N) ≤ φ (U (n + 1)) := antitone_comp_of_forall_mem_moreauYosidaResolvent hU hn
  have hp_bot : φ (U (n + 1)) ≠ ⊥ := ne_bot_of_le_ne_bot hN hmono
  have hp_top : φ (U (n + 1)) ≠ ⊤ := by
    intro hp
    have := hvi.trans_lt (EReal.add_lt_top hv (EReal.coe_ne_top _))
    rw [hp, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at this
    exact lt_irrefl _ this
  have hq_top : φ (U N) ≠ ⊤ := ne_top_of_le_ne_top hp_top hmono
  have hv_bot : φ v ≠ ⊥ := by
    intro hv'
    rw [hv', EReal.bot_add, le_bot_iff] at hvi
    exact hp_bot ((EReal.add_eq_bot_iff.1 hvi).resolve_right (EReal.coe_ne_bot _))
  lift φ (U (n + 1)) to ℝ using ⟨hp_top, hp_bot⟩ with p
  lift φ (U N) to ℝ using ⟨hq_top, hN⟩ with q
  lift φ v to ℝ using ⟨hv, hv_bot⟩ with w
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hvi
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hc
  rw [EReal.coe_le_coe_iff] at hmono
  have hτ' : (0 : ℝ) < τ := hτ
  have h2τ := mul_le_mul_of_nonneg_left hvi (by positivity : (0 : ℝ) ≤ 2 * τ)
  field_simp at h2τ
  nlinarith [sq_nonneg (dist (U n) (U (n + 1)))]

/-- **The discrete integrated evolution variational inequality.** Let `φ` be penalized convex
with parameter `m` and time step `τ > 0` with `1 + m τ ≥ 0`, and let `U` be a minimizing movement
sequence, `U (n + 1) ∈ J_τ (U n)`. For a point `v` with `φ v ≠ ⊤`, a step `N` with
`φ (U N) ≠ ⊥` and a real bound `φ v - φ (U N) ≤ c`, with `r = 1 + m τ`,

`r ^ N d(U N, v)² / 2 - d(U 0, v)² / 2 ≤ τ (∑_{n < N} r ^ n) c`.

This is the discrete form of `TauCeti.IsEVISolution.exp_mul_dist_sq_sub_le`. -/
theorem PenalizedConvex.pow_mul_dist_sq_sub_le (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 ≤ 1 + m * τ) (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hv : φ v ≠ ⊤) {N : ℕ} (hN : φ (U N) ≠ ⊥) {c : ℝ} (hc : φ v - φ (U N) ≤ c) :
    (1 + m * τ) ^ N * (dist (U N) v ^ 2 / 2) - dist (U 0) v ^ 2 / 2 ≤
      (τ * ∑ n ∈ range N, (1 + m * τ) ^ n) * c := by
  -- Multiply the one-step inequalities by `r ^ n` and telescope.
  suffices ∀ k ≤ N, (1 + m * τ) ^ k * (dist (U k) v ^ 2 / 2) - dist (U 0) v ^ 2 / 2 ≤
      (τ * ∑ n ∈ range k, (1 + m * τ) ^ n) * c from this N le_rfl
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := mul_le_mul_of_nonneg_left (h.mul_dist_sq_sub_le hτ hU hv hN hc hk)
      (pow_nonneg hmτ k)
    have ih := ih (Nat.le_of_succ_le hk)
    rw [sum_range_succ, pow_succ]
    nlinarith

/-- **The discrete energy regularization estimate.** Let `φ` be penalized convex with parameter
`m` and time step `τ > 0` with `1 + m τ ≥ 0`, and let `U` be a minimizing movement sequence,
`U (n + 1) ∈ J_τ (U n)`. For a point `v` with `φ v ≠ ⊤` and a step `N ≥ 1`, with `r = 1 + m τ`,

`φ (U N) ≤ φ v + (d(U 0, v)² - r ^ N d(U N, v)²) / (2τ ∑_{n < N} r ^ n)`.

For `m = 0` this is `φ (U N) ≤ φ v + (d(U 0, v)² - d(U N, v)²) / (2 N τ)`. This is the discrete
form of `TauCeti.IsEVISolution.apply_le`. -/
theorem PenalizedConvex.apply_le (h : PenalizedConvex m τ φ) (hτ : 0 < τ) (hmτ : 0 ≤ 1 + m * τ)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) (hv : φ v ≠ ⊤) {N : ℕ} (hN : 0 < N) :
    φ (U N) ≤ φ v + (((dist (U 0) v ^ 2 - (1 + m * τ) ^ N * dist (U N) v ^ 2) /
      (2 * τ * ∑ n ∈ range N, (1 + m * τ) ^ n) : ℝ) : EReal) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN.ne'
  have hvi := h.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU k) hv
  induction hp : φ (U (k + 1)) using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := hvi.trans_lt (EReal.add_lt_top hv (EReal.coe_ne_top _))
    rw [hp, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at this
    exact absurd this (lt_irrefl _)
  | coe p =>
    induction hw : φ v using EReal.rec with
    | bot =>
      rw [hp, hw, EReal.bot_add, le_bot_iff, ← EReal.coe_add] at hvi
      exact absurd hvi (EReal.coe_ne_bot _)
    | top => exact absurd hw hv
    | coe w =>
      have hS : 0 < ∑ n ∈ range (k + 1), (1 + m * τ) ^ n :=
        sum_pos' (fun n _ ↦ pow_nonneg hmτ n) ⟨0, by simp⟩
      have hτ' : (0 : ℝ) < τ := hτ
      have hint := h.pow_mul_dist_sq_sub_le hτ hmτ hU hv (hp ▸ EReal.coe_ne_bot p)
        (c := w - p) (by rw [hp, hw, EReal.coe_sub])
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← sub_le_iff_le_add',
        le_div_iff₀ (by positivity)]
      nlinarith

/-- **Weighted distance estimate towards points of smaller energy.** Let `φ` be penalized convex
with parameter `m` and time step `τ > 0` with `1 + m τ ≥ 0`, and let `U` be a minimizing movement
sequence, `U (n + 1) ∈ J_τ (U n)`. If `v` has finite energy `φ v ≤ φ (U N)`, for instance if `v`
minimizes `φ`, then

`(1 + m τ) ^ N d(U N, v)² ≤ d(U 0, v)²`.

For `m > 0` and a fixed minimizer `v` of finite energy, the scheme therefore converges
geometrically to `v`; this is the discrete form of the contraction of the `EVI_m` flow. -/
theorem PenalizedConvex.pow_mul_dist_sq_le (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 ≤ 1 + m * τ) (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hv : φ v ≠ ⊤) (hv' : φ v ≠ ⊥) {N : ℕ} (hvN : φ v ≤ φ (U N)) :
    (1 + m * τ) ^ N * dist (U N) v ^ 2 ≤ dist (U 0) v ^ 2 := by
  have hc : φ v - φ (U N) ≤ ((0 : ℝ) : EReal) := by
    rw [EReal.coe_zero]
    exact EReal.sub_nonpos.2 hvN
  have := h.pow_mul_dist_sq_sub_le hτ hmτ hU hv (ne_bot_of_le_ne_bot hv' hvN) hc
  rw [mul_zero] at this
  linarith

end MinimizingMovement

end TauCeti
