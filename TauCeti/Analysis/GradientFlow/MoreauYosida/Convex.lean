/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
import Mathlib.Analysis.SpecificLimits.Basic

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
* `TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`,
  `TauCeti.PenalizedConvex.existsUnique_mem_moreauYosidaResolvent`, and
  `TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`: existence and uniqueness of
  resolvent steps and minimizing movement sequences in complete metric spaces without compactness
  of sublevels.
* `TauCeti.GeodesicallyConvex.penalizedConvex`: on a CAT(0) space, an `m`-geodesically convex
  energy satisfies the hypothesis for every time step.
* `TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`: lower semicontinuous geodesically convex
  energies are automatically coercive.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Assumption 4.0.1, Lemma 2.2.1, Theorem 4.1.2,
  and Section 4.1.
-/

public section

open Filter Finset Set Topology
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

section Existence

variable {X : Type*} [MetricSpace X] {m : ℝ} {τ τ₀ : ℝ≥0} {φ : X → EReal} {x x₀ : X}

/-- **Existence of resolvent steps under penalized convexity** (Ambrosio–Gigli–Savaré, Theorem
4.1.2 / Lemma 2.2.1). In a complete metric space, if `φ` is lower semicontinuous and penalized
convex with parameter `m` and time step `τ > 0` satisfying `1 + m τ > 0`, and if `φ_τ(x) > -∞`,
then the resolvent `J_τ x` is nonempty: every minimizing sequence for `z ↦ φ z + d(x, z)² / (2τ)`
is Cauchy by strong convexity along the connecting curves. No compactness of sublevels is needed. -/
theorem PenalizedConvex.moreauYosidaResolvent_nonempty [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hbot : moreauYosida φ τ x ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  rcases eq_or_ne (moreauYosida φ τ x) ⊤ with htop | htop
  · refine ⟨x, mem_moreauYosidaResolvent_iff.2 ⟨by simp, fun z hz ↦ ?_⟩⟩
    have := moreauYosida_le φ τ hz
    rw [htop, top_le_iff] at this
    exact this ▸ le_top
  set M : ℝ := (moreauYosida φ τ x).toReal
  have hM : moreauYosida φ τ x = M := (EReal.coe_toReal htop hbot).symm
  -- Choose a minimizing sequence `v` with penalized energies below `M + 1 / (n + 1)`.
  have hseq : ∀ n : ℕ, ∃ v : X,
      φ v + (edist x v ^ 2 / (2 * τ) : ℝ≥0∞) < ((M + 1 / (n + 1) : ℝ) : EReal) := fun n ↦ by
    have hlt : moreauYosida φ τ x < ((M + 1 / (n + 1) : ℝ) : EReal) := by
      rw [hM, EReal.coe_lt_coe_iff]
      linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
    simpa only [moreauYosida_eq_iInf, iInf_lt_iff] using hlt
  choose v hv using hseq
  have hφ_ne_top : ∀ n, φ (v n) ≠ ⊤ := fun n hvn ↦ by
    have := hv n
    rw [hvn, coe_edist_sq_div_eq_coe_dist_sq_div hτ,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at this
    exact not_top_lt this
  have hψ_ge : ∀ y : X, (M : EReal) ≤ φ y + ((dist x y ^ 2 / (2 * τ) : ℝ) : EReal) := fun y ↦ by
    rw [← coe_edist_sq_div_eq_coe_dist_sq_div hτ, ← hM]
    exact moreauYosida_le φ τ (edist_ne_top x y)
  have hφ_ne_bot : ∀ n, φ (v n) ≠ ⊥ := fun n hvn ↦ by
    have := hψ_ge (v n)
    rw [hvn, EReal.bot_add, le_bot_iff] at this
    exact EReal.coe_ne_bot M this
  -- Compare `M ≤ Ψ (γ (1 / 2))` against `Ψ (v n)` and `Ψ (v k)` via penalized convexity.
  have : (0 : ℝ) < τ := hτ
  have hc : 0 < (1 + m * τ) / (8 * τ) := by positivity
  have hdist_sq : ∀ n k : ℕ, (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2 ≤
      1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) := fun n k ↦ by
    obtain ⟨γ, hγ0, hγ1, hγ⟩ := h (w := x) (hφ_ne_top n) (hφ_ne_top k)
    have hmid := convexAlong_def.1 hγ (1 / 2) ⟨by norm_num, by norm_num⟩
    have hlow : (M : EReal) ≤ φ (γ (1 / 2)) + ((dist x (γ (1 / 2)) ^ 2 / (2 * τ) : ℝ) : EReal) :=
      hψ_ge (γ (1 / 2))
    have hcomb := hlow.trans hmid
    rw [hγ0, hγ1] at hcomb
    set an : ℝ := (φ (v n)).toReal
    set ak : ℝ := (φ (v k)).toReal
    have han : φ (v n) = an := (EReal.coe_toReal (hφ_ne_top n) (hφ_ne_bot n)).symm
    have hak : φ (v k) = ak := (EReal.coe_toReal (hφ_ne_top k) (hφ_ne_bot k)).symm
    have hvn' : an + dist x (v n) ^ 2 / (2 * τ) < M + 1 / (n + 1) := by
      have := hv n
      rwa [coe_edist_sq_div_eq_coe_dist_sq_div hτ, han, ← EReal.coe_add,
        EReal.coe_lt_coe_iff] at this
    have hvk' : ak + dist x (v k) ^ 2 / (2 * τ) < M + 1 / (k + 1) := by
      have := hv k
      rwa [coe_edist_sq_div_eq_coe_dist_sq_div hτ, hak, ← EReal.coe_add,
        EReal.coe_lt_coe_iff] at this
    rw [han, hak] at hcomb
    norm_cast at hcomb
    push_cast at hcomb
    have hcoef : (1 + m * (τ : ℝ)) / (8 * τ) =
        (m + (τ : ℝ)⁻¹) / 2 * (1 / 2) * (1 - 1 / 2) := by
      field_simp
      ring
    rw [hcoef]
    have hvn'' : (1 - 1 / 2) * (an + dist x (v n) ^ 2 / (2 * ↑τ)) <
        1 / 2 * M + 1 / (2 * ((n : ℝ) + 1)) := by
      have : 1 / (2 * ((n : ℝ) + 1)) = (1 - 1 / 2) * (1 / ((n : ℝ) + 1)) := by
        norm_num [div_eq_mul_inv, mul_comm, mul_assoc]
      nlinarith
    have hvk'' : (1 / 2) * (ak + dist x (v k) ^ 2 / (2 * ↑τ)) <
        1 / 2 * M + 1 / (2 * ((k : ℝ) + 1)) := by
      have : 1 / (2 * ((k : ℝ) + 1)) = (1 / 2) * (1 / ((k : ℝ) + 1)) := by
        norm_num [div_eq_mul_inv, mul_comm, mul_assoc]
      nlinarith
    linarith
  have hcauchy : CauchySeq v := Metric.cauchySeq_iff.2 fun ε hε ↦ by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (mul_pos (pow_pos hε 2) hc)
    refine ⟨N, fun n hn k hk ↦ ?_⟩
    have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    have hsq : (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2 <
        (1 + m * τ) / (8 * τ) * ε ^ 2 := by
      calc (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2
          ≤ 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) := hdist_sq n k
        _ = (1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1)) / 2 := by field_simp
        _ ≤ 1 / ((N : ℝ) + 1) := by linarith
        _ < ε ^ 2 * ((1 + m * τ) / (8 * τ)) := hN
        _ = (1 + m * τ) / (8 * τ) * ε ^ 2 := mul_comm _ _
    have hd_lt : dist (v n) (v k) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left hsq hc.le
    exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hd_lt
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hliminf := le_liminf_apply_add_edist_sq_div (φ := φ) (τ := τ) (x := x)
    ((((continuous_const.edist continuous_id).tendsto y).comp hy).liminf_eq.ge)
    ((hφ.le_liminf y).trans hy.liminf_le_liminf_comp)
  have hlim : Tendsto (fun n : ℕ ↦ ((M + 1 / (n + 1) : ℝ) : EReal)) atTop (𝓝 (M : EReal)) :=
    EReal.tendsto_coe.2 (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add M)
  refine ⟨y, mem_moreauYosidaResolvent_iff_eq_moreauYosida.2
    ⟨edist_ne_top x y, le_antisymm ?_ (moreauYosida_le φ τ (edist_ne_top x y))⟩⟩
  rw [hM, ← hlim.liminf_eq]
  exact hliminf.trans (liminf_le_liminf (Eventually.of_forall fun n ↦ (hv n).le))

/-- **Existence and uniqueness of the resolvent step under penalized convexity.** Under the
hypotheses of `TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`, if moreover `φ` never takes
the value `⊥` and is finite somewhere, then `J_τ x` contains a unique point. -/
theorem PenalizedConvex.existsUnique_mem_moreauYosidaResolvent [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hmoreau : moreauYosida φ τ x ≠ ⊥)
    (hbot : ∀ z, φ z ≠ ⊥) (hdom : ∃ z, φ z ≠ ⊤) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x := by
  obtain ⟨y, hy⟩ := h.moreauYosidaResolvent_nonempty hφ hτ hmτ hmoreau
  exact ⟨y, hy, fun y' hy' ↦ h.subsingleton_moreauYosidaResolvent hτ hmτ hbot hdom x hy' hy⟩

/-- **Existence of minimizing movement sequences under penalized convexity.** In a complete metric
space, if `φ` is lower semicontinuous, penalized convex with parameter `m` at time step `τ > 0`
satisfying `1 + m τ > 0`, and coercive `φ_{τ₀}(x₀) > -∞` at a larger time step `τ₀ > τ`, then
every point `x` starts a minimizing movement sequence `u` with `u 0 = x` and `u (n + 1) ∈ J_τ (u n)`
for all `n`. -/
theorem PenalizedConvex.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) (x : X) :
    ∃ u : ℕ → X, u 0 = x ∧ ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) := by
  have step : ∀ z : X, ∃ y, y ∈ moreauYosidaResolvent φ τ z := fun z ↦
    h.moreauYosidaResolvent_nonempty hφ hτ hmτ
      (moreauYosida_ne_bot_of_lt hττ₀ (edist_ne_top z x₀) h₀)
  choose f hf using step
  exact ⟨fun n ↦ f^[n] x, rfl, fun n ↦ by simpa only [Function.iterate_succ_apply'] using hf _⟩

/-- **Coercivity of geodesically convex energies.** A lower semicontinuous `m`-geodesically convex
energy `φ` that is finite at a point `x` has `φ_τ(x) > -∞` for every time step `τ > 0` with
`1 + m τ > 0`: local boundedness below near `x` extends to a quadratic lower bound along geodesic
segments leaving `x`. -/
theorem GeodesicallyConvex.moreauYosida_ne_bot (hφ : LowerSemicontinuous φ)
    (h : GeodesicallyConvex m φ) (hxtop : φ x ≠ ⊤) (hxbot : φ x ≠ ⊥) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) : moreauYosida φ τ x ≠ ⊥ := by
  set a : ℝ := (φ x).toReal
  have ha : φ x = a := (EReal.coe_toReal hxtop hxbot).symm
  have hnhds : ∀ᶠ z in 𝓝 x, ((a - 1 : ℝ) : EReal) < φ z :=
    hφ x _ (by simpa [ha] using EReal.coe_lt_coe_iff.2 (sub_one_lt a))
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.eventually_iff.1 hnhds
  set c : ℝ := min 1 (1 + m * τ)
  have : 0 < c := lt_min one_pos hmτ
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcm : c ≤ 1 + m * τ := min_le_right _ _
  have hτr : (0 : ℝ) < τ := hτ
  set k : ℝ := c / (2 * τ)
  have hkpos : 0 < k := by positivity
  set L : ℝ := min (a - 1) (a - 1 / (k * δ ^ 2))
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_moreauYosida_iff.2 fun z _ ↦ ?_)
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
  rcases lt_or_ge (dist x z) δ with hxz | hxz
  · refine (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans ?_
    exact (hball (Metric.mem_ball'.2 hxz)).le.trans (le_add_of_nonneg_right (by positivity))
  rcases eq_or_ne (φ z) ⊤ with hztop | hztop
  · rw [hztop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  set r : ℝ := dist x z
  have hrpos : 0 < r := hδ.trans_le hxz
  set t : ℝ := δ / (2 * r)
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht1.trans (by norm_num)⟩
  obtain ⟨γ, hγ, hconv⟩ := geodesicallyConvex_def.1 h hxtop hztop
  have hγball : γ t ∈ Metric.ball x δ := by
    rw [Metric.mem_ball', hγ.dist_source_apply htIcc, show t * dist x z = δ / 2 by
      change δ / (2 * r) * r = δ / 2
      field_simp]
    linarith
  have hlow : ((a - 1 : ℝ) : EReal) < φ (γ t) := hball hγball
  have hconv_t := hγ.convexAlong_iff.1 hconv t htIcc
  have hzbot : φ z ≠ ⊥ := fun hzbot ↦ by
    rw [hzbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot, EReal.bot_sub, le_bot_iff] at hconv_t
    rw [hconv_t] at hlow
    exact not_lt_bot hlow
  set b : ℝ := (φ z).toReal
  have hb : φ z = b := (EReal.coe_toReal hztop hzbot).symm
  rw [ha, hb] at hconv_t
  norm_cast at hconv_t
  have hmid : a - 1 ≤ (1 - t) * a + t * b - m / 2 * t * (1 - t) * r ^ 2 := by
    exact_mod_cast (hlow.le.trans hconv_t)
  -- Divide out `t = δ / (2r) > 0` and absorb `(1 - t) m + 1 / τ ≥ c / τ = 2k`.
  have hslope : a - 2 * r / δ ≤ b - m / 2 * (1 - t) * r ^ 2 := by
    have hmul : t * (a - 2 * r / δ) ≤ t * (b - m / 2 * (1 - t) * r ^ 2) := by
      have : t * (2 * r / δ) = 1 := by dsimp [t]; field_simp
      linarith
    exact le_of_mul_le_mul_left hmul htpos
  have hcm' : (c - 1) / τ ≤ (1 - t) * m := by
    rcases le_or_gt 0 m with hm | hm
    · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) hτr.le).trans
        (mul_nonneg (sub_nonneg.2 htIcc.2) hm)
    · have : m ≤ (1 - t) * m := by nlinarith
      exact ((div_le_iff₀ hτr).2 (by linarith)).trans this
  have hquad : k * r ^ 2 ≤ m / 2 * (1 - t) * r ^ 2 + r ^ 2 / (2 * τ) := by
    have hkc : k = ((c - 1) / τ + (τ : ℝ)⁻¹) / 2 := by
      dsimp [k]
      field_simp
      ring
    calc k * r ^ 2 = ((c - 1) / τ / 2 + (2 * (τ : ℝ))⁻¹) * r ^ 2 := by
          rw [hkc]
          ring
      _ ≤ ((1 - t) * m / 2 + (2 * (τ : ℝ))⁻¹) * r ^ 2 := by gcongr
      _ = m / 2 * (1 - t) * r ^ 2 + r ^ 2 / (2 * τ) := by ring
  have hsq : -(1 / (k * δ ^ 2)) ≤ k * r ^ 2 - 2 * r / δ := by
    rw [← sub_nonneg]
    calc k * r ^ 2 - 2 * r / δ - -(1 / (k * δ ^ 2))
        = (k * δ * r - 1) ^ 2 / (k * δ ^ 2) := by field_simp; ring
      _ ≥ 0 := div_nonneg (sq_nonneg _) (by positivity)
  have hfin : L ≤ b + r ^ 2 / (2 * τ) :=
    (min_le_right _ _).trans (by linarith)
  rw [hb, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.2 hfin

end Existence

end TauCeti
