/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence

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

Uniform convexity of the penalized energy also gives existence of resolvent steps on any complete
pseudometric space, without compactness of energy sublevels: when `1 + m τ > 0`, `φ` is lower
semicontinuous, and `φ_τ(x) > -∞`, the midpoint inequality makes every minimizing sequence Cauchy
(`TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`). For an `m`-geodesically convex lower
semicontinuous energy that never takes the value `⊥`, coercivity holds automatically whenever
`1 + m τ > 0`, from a global quadratic lower bound around any point of finite energy
(`TauCeti.GeodesicallyConvex.exists_forall_sub_add_le` and
`TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`).

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
* `TauCeti.moreauYosida_ne_bot_of_forall_sub_add_le`,
  `TauCeti.GeodesicallyConvex.exists_forall_sub_add_le`, and
  `TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`: quadratic lower bounds and automatic coercivity
  of lower semicontinuous `m`-geodesically convex energies when `1 + m τ > 0`.
* `TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty` and
  `TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`: existence of resolvent steps
  and minimizing movement sequences on complete pseudometric spaces when `1 + m τ > 0`.
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
  Probability Measures*, 2nd ed., Birkhäuser 2008, Lemma 2.4.8, Assumption 4.0.1, Lemma 4.1.1,
  Theorem 4.1.2 and Section 4.1.
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

section CoercivityAndExistence

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ : ℝ≥0} {φ : X → EReal}

/-- **Quadratic lower bounds give coercivity.** If `φ` is bounded below by
`z ↦ c - a d(x₀, z) + (m / 2) d(x₀, z)²`, then `φ_τ(x) > -∞` for every `x` and every time step
`τ` with `1 + m τ > 0`. -/
theorem moreauYosida_ne_bot_of_forall_sub_add_le {c a : ℝ} {x₀ : X}
    (h : ∀ z, ((c - a * dist x₀ z + m / 2 * dist x₀ z ^ 2 : ℝ) : EReal) ≤ φ z)
    (hmτ : 0 < 1 + m * τ) (x : X) : moreauYosida φ τ x ≠ ⊥ := by
  -- Choose a slightly larger time step `τ₀ > τ` still satisfying `1 + m τ₀ > 0`.
  set δ : ℝ := (1 + m * τ) / (2 * (|m| + 1))
  have hδ : 0 < δ := by positivity
  set τ₀ : ℝ≥0 := τ + Real.toNNReal δ
  have hτ₀_coe : (τ₀ : ℝ) = τ + δ := by simp [τ₀, Real.coe_toNNReal _ hδ.le]
  have hττ₀ : τ < τ₀ := NNReal.coe_lt_coe.1 (by linarith)
  have hτ₀ : 0 < τ₀ := zero_le.trans_lt hττ₀
  have hmτ₀ : 0 < 1 + m * τ₀ := by
    have habs : |m| * δ < (1 + m * τ) / 2 := by
      have : (|m| + 1) * δ = (1 + m * τ) / 2 := by
        dsimp [δ]
        field_simp
      nlinarith
    rw [hτ₀_coe]
    nlinarith [neg_abs_le m]
  refine moreauYosida_ne_bot_of_lt hττ₀ (edist_ne_top x x₀) ?_
  set α : ℝ := (1 + m * τ₀) / (2 * τ₀)
  have hα : 0 < α := by positivity
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (c - a ^ 2 / (4 * α)))
    (le_moreauYosida_iff.2 fun z _ ↦ ?_)
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ₀]
  refine le_trans ?_ (add_le_add_left (h z) _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  set D := dist x₀ z
  have hαD : m / 2 * D ^ 2 + D ^ 2 / (2 * τ₀) = α * D ^ 2 := by
    dsimp [α]
    have : (τ₀ : ℝ) ≠ 0 := (NNReal.coe_pos.2 hτ₀).ne'
    field_simp
    ring
  have hcomp : α * (D - a / (2 * α)) ^ 2 = α * D ^ 2 - a * D + a ^ 2 / (4 * α) := by
    have := hα.ne'
    field_simp
    ring
  nlinarith [sq_nonneg (D - a / (2 * α))]

/-- Outside the ball of radius `r` where `φ ≥ c₀ - 1`, evaluating `m`-convexity along a curve from
`x₀` to `z` at `t = r / d(x₀, z)` yields the quadratic lower bound at `z`. -/
private lemma sub_add_le_of_gt {c₀ p r : ℝ} {x₀ z : X} (hr0 : 0 < r) (hDr : r < dist x₀ z)
    (hc₀ : φ x₀ = c₀) (hp : φ z = p) (hball : ∀ y, dist x₀ y ≤ r → ((c₀ - 1 : ℝ) : EReal) ≤ φ y)
    {γ : ℝ → X} (h0 : γ 0 = x₀) (h1 : γ 1 = z)
    (hdγ : ∀ t ∈ Icc (0 : ℝ) 1, dist x₀ (γ t) ≤ t * dist x₀ z) (hconv : ConvexAlong m φ γ) :
    c₀ - 1 - |m| / 2 * r ^ 2 - (1 / r + |m| * r / 2) * dist x₀ z + m / 2 * dist x₀ z ^ 2 ≤ p := by
  set D := dist x₀ z
  have hD0 : 0 < D := hr0.trans hDr
  set t := r / D
  have ht0 : 0 < t := div_pos hr0 hD0
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, (div_le_one hD0).2 hDr.le⟩
  have htD : t * D = r := div_mul_cancel₀ r hD0.ne'
  have hw1 : ((c₀ - 1 : ℝ) : EReal) ≤ φ (γ t) := hball _ ((hdγ t ht).trans_eq htD)
  have hw2 := convexAlong_def.1 hconv t ht
  rw [h0, h1, hc₀, hp] at hw2
  have hreal : c₀ - 1 ≤ (1 - t) * c₀ + t * p - m / 2 * t * (1 - t) * D ^ 2 := by
    exact_mod_cast hw1.trans hw2
  refine le_of_mul_le_mul_left ?_ ht0
  have h1' : t * ((1 / r + |m| * r / 2) * D) = 1 + |m| / 2 * r ^ 2 := by
    calc t * ((1 / r + |m| * r / 2) * D) = (t * D) * (1 / r + |m| * r / 2) := by ring
      _ = r * (1 / r + |m| * r / 2) := by rw [htD]
      _ = 1 + |m| / 2 * r ^ 2 := by field_simp
  have h2' : m / 2 * t * (1 - t) * D ^ 2 = m / 2 * r * D - m / 2 * r ^ 2 := by
    calc m / 2 * t * (1 - t) * D ^ 2 = m / 2 * (t * D) * (D - t * D) := by ring
      _ = m / 2 * r * (D - r) := by rw [htD]
      _ = m / 2 * r * D - m / 2 * r ^ 2 := by ring
  have h3' : t * (c₀ - 1 - |m| / 2 * r ^ 2 - (1 / r + |m| * r / 2) * D + m / 2 * D ^ 2) =
      t * c₀ - t - t * (|m| / 2 * r ^ 2) - t * ((1 / r + |m| * r / 2) * D) +
        m / 2 * (t * D) * D := by ring
  rw [h3', h1', htD]
  rw [h2'] at hreal
  have hmr : m * r ^ 2 ≤ |m| * r ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self m) (sq_nonneg r)
  have htr : 0 ≤ t * (|m| / 2 * r ^ 2) := by positivity
  linarith

/-- Convexity along curves out of a base point `x₀` where `φ` is finite and bounded below on a
closed ball rules out the value `⊥` everywhere. -/
private lemma apply_ne_bot_of_ball_le {c₀ r : ℝ} {x₀ : X} (hr0 : 0 < r) (hc₀ : φ x₀ = c₀)
    (hball : ∀ y, dist x₀ y ≤ r → ((c₀ - 1 : ℝ) : EReal) ≤ φ y)
    (hγ : ∀ z, φ z ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = x₀ ∧ γ 1 = z ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist x₀ (γ t) ≤ t * dist x₀ z) ∧ ConvexAlong m φ γ)
    (z : X) : φ z ≠ ⊥ := fun hz ↦ by
  rcases le_or_gt (dist x₀ z) r with hDr | hDr
  · exact not_le_of_gt (EReal.bot_lt_coe (c₀ - 1)) (hz ▸ hball z hDr)
  · obtain ⟨γ, h0, h1, hdγ, hconv⟩ := hγ z (by simp [hz])
    have hD0 : 0 < dist x₀ z := hr0.trans hDr
    set t := r / dist x₀ z
    have ht0 : 0 < t := div_pos hr0 hD0
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, (div_le_one hD0).2 hDr.le⟩
    have hw1 := hball _ ((hdγ t ht).trans_eq (div_mul_cancel₀ r hD0.ne'))
    have hw2 := convexAlong_def.1 hconv t ht
    rw [h0, h1, hc₀, hz, EReal.coe_mul_bot_of_pos ht0, EReal.add_bot, EReal.bot_sub] at hw2
    exact not_le_of_gt (EReal.bot_lt_coe (c₀ - 1)) (hw1.trans hw2)

/-- **Quadratic lower bound from convexity along curves out of a base point.** Let `φ` be finite
and lower semicontinuous at `x₀`, and suppose every `z` with `φ z ≠ ⊤` is joined from `x₀` by a
curve `γ` with `d(x₀, γ t) ≤ t d(x₀, z)` on `[0, 1]` along which `φ` is `m`-convex. Then `φ` is
bounded below by `z ↦ c - a d(x₀, z) + (m / 2) d(x₀, z)²` for some `c, a : ℝ`. -/
theorem exists_forall_sub_add_le_of_lowerSemicontinuousAt {x₀ : X} (hx₀ : φ x₀ ≠ ⊤)
    (hx₀_bot : φ x₀ ≠ ⊥) (hlsc : LowerSemicontinuousAt φ x₀)
    (hγ : ∀ z, φ z ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = x₀ ∧ γ 1 = z ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist x₀ (γ t) ≤ t * dist x₀ z) ∧ ConvexAlong m φ γ) :
    ∃ c a : ℝ, ∀ z, ((c - a * dist x₀ z + m / 2 * dist x₀ z ^ 2 : ℝ) : EReal) ≤ φ z := by
  set c₀ := (φ x₀).toReal
  have hc₀ : φ x₀ = c₀ := (EReal.coe_toReal hx₀ hx₀_bot).symm
  have hlt : ((c₀ - 1 : ℝ) : EReal) < φ x₀ := by
    rw [hc₀, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨r', hr'0, hr'⟩ := Metric.mem_nhds_iff.1 (hlsc ((c₀ - 1 : ℝ) : EReal) hlt)
  set r := r' / 2
  have hr0 : 0 < r := half_pos hr'0
  have hball : ∀ y, dist x₀ y ≤ r → ((c₀ - 1 : ℝ) : EReal) ≤ φ y := fun y hy ↦
    (hr' (Metric.mem_ball'.2 (hy.trans_lt (half_lt_self hr'0)))).le
  have hbot : ∀ z, φ z ≠ ⊥ := apply_ne_bot_of_ball_le hr0 hc₀ hball hγ
  refine ⟨c₀ - 1 - |m| / 2 * r ^ 2, 1 / r + |m| * r / 2, fun z ↦ ?_⟩
  rcases eq_or_ne (φ z) ⊤ with hzt | hzt
  · simp [hzt]
  set p := (φ z).toReal
  have hp : φ z = p := (EReal.coe_toReal hzt (hbot z)).symm
  rw [hp, EReal.coe_le_coe_iff]
  rcases le_or_gt (dist x₀ z) r with hDr | hDr
  · have hp0 : c₀ - 1 ≤ p := EReal.coe_le_coe_iff.1 (hp ▸ hball z hDr)
    have hD2 : dist x₀ z ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ dist_nonneg hDr 2
    have haD : 0 ≤ (1 / r + |m| * r / 2) * dist x₀ z := mul_nonneg (by positivity) dist_nonneg
    have hmD : m * dist x₀ z ^ 2 ≤ |m| * r ^ 2 :=
      (mul_le_mul_of_nonneg_right (le_abs_self m) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hD2 (abs_nonneg m))
    linarith
  · obtain ⟨γ, h0, h1, hdγ, hconv⟩ := hγ z hzt
    exact sub_add_le_of_gt hr0 hDr hc₀ hp hball h0 h1 hdγ hconv

/-- **Quadratic lower bound for geodesically convex energies** (Ambrosio–Gigli–Savaré, Lemma
2.4.8). If `φ` is `m`-geodesically convex and is finite and lower semicontinuous at `x₀`, then `φ`
satisfies a global lower bound `c - a d(x₀, z) + (m / 2) d(x₀, z)² ≤ φ z`. -/
theorem GeodesicallyConvex.exists_forall_sub_add_le (h : GeodesicallyConvex m φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hx₀_bot : φ x₀ ≠ ⊥) (hlsc : LowerSemicontinuousAt φ x₀) :
    ∃ c a : ℝ, ∀ z, ((c - a * dist x₀ z + m / 2 * dist x₀ z ^ 2 : ℝ) : EReal) ≤ φ z :=
  exists_forall_sub_add_le_of_lowerSemicontinuousAt hx₀ hx₀_bot hlsc fun z hz ↦ by
    obtain ⟨γ, hγ, hconv⟩ := geodesicallyConvex_def.1 h hx₀ hz
    exact ⟨γ, hγ.source, hγ.target, fun t ht ↦ (hγ.dist_source_apply ht).le, hconv⟩

/-- **Coercivity of lower semicontinuous geodesically convex energies.** If `φ` is `m`-geodesically
convex, lower semicontinuous, and never takes the value `⊥`, then `φ_τ(x) > -∞` for every `x` and
every time step `τ` with `1 + m τ > 0`. -/
theorem GeodesicallyConvex.moreauYosida_ne_bot (h : GeodesicallyConvex m φ)
    (hφ : LowerSemicontinuous φ) (hbot : ∀ z, φ z ≠ ⊥) (hmτ : 0 < 1 + m * τ) (x : X) :
    moreauYosida φ τ x ≠ ⊥ := by
  by_cases hdom : ∃ x₀, φ x₀ ≠ ⊤
  · obtain ⟨x₀, hx₀⟩ := hdom
    obtain ⟨c, a, hle⟩ := h.exists_forall_sub_add_le hx₀ (hbot x₀) (hφ x₀)
    exact moreauYosida_ne_bot_of_forall_sub_add_le hle hmτ x
  · push Not at hdom
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
      (le_moreauYosida_iff.2 fun z _ ↦ by simp [hdom z])

/-- Under `(m + 1 / τ)`-convexity of the penalized energy anchored at `x` with `1 + m τ > 0`, a
minimizing sequence for `φ_τ(x) = M` is Cauchy, by evaluating convexity at midpoints. -/
private theorem cauchySeq_of_apply_add_lt (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) {x : X}
    (h : ∀ ⦃x₀ x₁ : X⦄, φ x₀ ≠ ⊤ → φ x₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = x₀ ∧ γ 1 = x₁ ∧
      ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal)) γ)
    {M : ℝ} (hM : moreauYosida φ τ x = M)
    {z : ℕ → X} (hz : ∀ n : ℕ,
      φ (z n) + ((dist x (z n) ^ 2 / (2 * τ) : ℝ) : EReal) < ((M + 1 / (n + 1) : ℝ) : EReal)) :
    CauchySeq z := by
  have hMle : ∀ y, (M : EReal) ≤ φ y + ((dist x y ^ 2 / (2 * τ) : ℝ) : EReal) := fun y ↦ by
    simpa only [hM, coe_edist_sq_div_eq_coe_dist_sq_div hτ] using
      moreauYosida_le φ τ (edist_ne_top x y)
  have htop : ∀ n, φ (z n) ≠ ⊤ := fun n ht ↦ by
    have hlt := hz n
    rw [ht, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hlt
    exact not_top_lt hlt
  set κ : ℝ := (m + (τ : ℝ)⁻¹) / 8
  have hκ : 0 < κ := by
    have : m + (τ : ℝ)⁻¹ = (1 + m * τ) / τ := by
      have : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.2 hτ).ne'
      field_simp
      ring
    dsimp [κ]
    rw [this]
    positivity
  have hpair : ∀ j k, κ * dist (z j) (z k) ^ 2 ≤
      (1 / 2 : ℝ) * (1 / ((j : ℝ) + 1)) + (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := fun j k ↦ by
    obtain ⟨γ, h0, h1, hγ⟩ := h (htop j) (htop k)
    have hmid := (hMle (γ (1 / 2))).trans (convexAlong_def.1 hγ (1 / 2) ⟨by norm_num, by norm_num⟩)
    rw [h0, h1] at hmid
    set ψj := φ (z j) + ((dist x (z j) ^ 2 / (2 * τ) : ℝ) : EReal)
    set ψk := φ (z k) + ((dist x (z k) ^ 2 / (2 * τ) : ℝ) : EReal)
    lift ψj to ℝ using
      ⟨(hz j).ne_top, ne_bot_of_le_ne_bot (EReal.coe_ne_bot M) (hMle _)⟩ with pj hpj
    lift ψk to ℝ using
      ⟨(hz k).ne_top, ne_bot_of_le_ne_bot (EReal.coe_ne_bot M) (hMle _)⟩ with pk hpk
    have hpj' : pj ≤ M + 1 / ((j : ℝ) + 1) := EReal.coe_le_coe_iff.1 (hpj ▸ (hz j).le)
    have hpk' : pk ≤ M + 1 / ((k : ℝ) + 1) := EReal.coe_le_coe_iff.1 (hpk ▸ (hz k).le)
    have hmid' : M ≤ (1 - (1 / 2 : ℝ)) * pj + (1 / 2 : ℝ) * pk -
        (m + (τ : ℝ)⁻¹) / 2 * (1 / 2) * (1 - 1 / 2) * dist (z j) (z k) ^ 2 := by
      exact_mod_cast hmid
    dsimp [κ]
    linarith
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  have hlim : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2⁻¹ : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by positivity :
    0 < κ * ε ^ 2 / 2)))
  refine ⟨N, fun j hj k hk ↦ ?_⟩
  have hsq : dist (z j) (z k) ^ 2 < ε ^ 2 :=
    lt_of_mul_lt_mul_left (by linarith [hpair j k, hN j hj, hN k hk]) hκ.le
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- When the Moreau–Yosida approximation `φ_τ(x) = M` is real and `1 + m τ > 0`, the limit in a
complete space of a minimizing sequence lies in `J_τ x`. -/
private theorem moreauYosidaResolvent_nonempty_of_eq_coe [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) {x : X}
    (h : ∀ ⦃x₀ x₁ : X⦄, φ x₀ ≠ ⊤ → φ x₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = x₀ ∧ γ 1 = x₁ ∧
      ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal)) γ)
    {M : ℝ} (hM : moreauYosida φ τ x = M) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  have hseq : ∀ n : ℕ, ∃ z,
      φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal) < ((M + 1 / (n + 1) : ℝ) : EReal) := fun n ↦ by
    have hlt : moreauYosida φ τ x < ((M + 1 / (n + 1) : ℝ) : EReal) := by
      rw [hM, EReal.coe_lt_coe_iff]
      linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
    rw [moreauYosida_eq_iInf, iInf_lt_iff] at hlt
    simpa only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] using hlt
  choose z hz using hseq
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_apply_add_lt hτ hmτ h hM hz)
  have hlim : Tendsto (fun n : ℕ ↦ ((M + 1 / ((n : ℝ) + 1) : ℝ) : EReal)) atTop (𝓝 (M : EReal)) :=
    EReal.tendsto_coe.2 (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add M)
  refine ⟨y, mem_moreauYosidaResolvent_iff_eq_moreauYosida.2
    ⟨edist_ne_top x y, le_antisymm ?_ (moreauYosida_le φ τ (edist_ne_top x y))⟩⟩
  rw [hM, ← hlim.liminf_eq]
  have hed : edist x y ≤ liminf (fun n ↦ edist x (z n)) atTop :=
    ((tendsto_const_nhds.edist hy).liminf_eq).ge
  refine (le_liminf_apply_add_edist_sq_div hed
    ((hφ.le_liminf y).trans hy.liminf_le_liminf_comp)).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ?_))
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
  exact (hz n).le

/-- **Pointwise existence of a resolvent step from convexity of the penalized energy.** On a
complete pseudometric space, if `φ` is lower semicontinuous, `1 + m τ > 0`, `φ_τ(x) > -∞`, and for
`τ > 0` the penalized energy `z ↦ φ z + d(x, z)² / (2τ)` is `(m + 1 / τ)`-convex along curves
between points of finite energy, then `J_τ x` is nonempty. -/
theorem moreauYosidaResolvent_nonempty_of_forall_exists_convexAlong [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (hmτ : 0 < 1 + m * τ) {x : X}
    (h : τ ≠ 0 → ∀ ⦃x₀ x₁ : X⦄, φ x₀ ≠ ⊤ → φ x₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = x₀ ∧ γ 1 = x₁ ∧
      ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal)) γ)
    (h₀ : moreauYosida φ τ x ≠ ⊥) : (moreauYosidaResolvent φ τ x).Nonempty := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · refine ⟨x, mem_moreauYosidaResolvent_iff_isMinOn.2 (isMinOn_univ_iff.2 fun z ↦ ?_)⟩
    by_cases hxz : edist x z = 0
    · have hnhds : 𝓝 x = 𝓝 z := (EMetric.inseparable_iff.2 hxz).nhds_eq
      have hle : φ x ≤ φ z := le_of_forall_lt fun c hc ↦ mem_of_mem_nhds (hnhds ▸ hφ x c hc)
      simpa [hxz] using hle
    · have hzbot : φ z ≠ ⊥ := fun hz ↦ h₀ <| le_bot_iff.1 <| by
        simpa [hz] using moreauYosida_le φ 0 (edist_ne_top x z)
      rw [ENNReal.coe_zero, mul_zero, ENNReal.div_zero (pow_ne_zero 2 hxz), EReal.coe_ennreal_top,
        EReal.add_top_of_ne_bot hzbot]
      exact le_top
  rcases eq_or_ne (moreauYosida φ τ x) ⊤ with htop | htop
  · refine ⟨x, mem_moreauYosidaResolvent_iff.2 ⟨edist_ne_top x x, fun z hz ↦ ?_⟩⟩
    have := moreauYosida_le φ τ hz
    rw [htop, top_le_iff] at this
    exact this ▸ le_top
  exact moreauYosidaResolvent_nonempty_of_eq_coe hφ (pos_iff_ne_zero.2 hτ) hmτ (h hτ)
    (EReal.coe_toReal htop h₀).symm

/-- **Existence of resolvent steps under penalized convexity** (Ambrosio–Gigli–Savaré, Lemma
4.1.1). On a complete pseudometric space, if `φ` is lower semicontinuous and penalized convex with
`1 + m τ > 0` and `φ_τ(x) > -∞`, then the resolvent `J_τ x` is nonempty, without any compactness
assumption on energy sublevels. -/
theorem PenalizedConvex.moreauYosidaResolvent_nonempty [CompleteSpace X]
    (h : PenalizedConvex m τ φ) (hφ : LowerSemicontinuous φ) (hmτ : 0 < 1 + m * τ) {x : X}
    (h₀ : moreauYosida φ τ x ≠ ⊥) : (moreauYosidaResolvent φ τ x).Nonempty :=
  moreauYosidaResolvent_nonempty_of_forall_exists_convexAlong hφ hmτ
    (fun _ _ _ h₀ h₁ ↦ penalizedConvex_def.1 h h₀ h₁) h₀

/-- **Existence of minimizing movement sequences under penalized convexity.** On a complete
pseudometric space, if `φ` is lower semicontinuous and penalized convex with `1 + m τ > 0` and
`φ_τ(z) > -∞` at every point, then every `x` starts a minimizing movement sequence
`u (n + 1) ∈ J_τ (u n)`. -/
theorem PenalizedConvex.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    (h : PenalizedConvex m τ φ) (hφ : LowerSemicontinuous φ) (hmτ : 0 < 1 + m * τ)
    (h₀ : ∀ z, moreauYosida φ τ z ≠ ⊥) (x : X) :
    ∃ u : ℕ → X, u 0 = x ∧ ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) := by
  choose f hf using fun z ↦ h.moreauYosidaResolvent_nonempty hφ hmτ (h₀ z)
  exact ⟨fun n ↦ f^[n] x, rfl, fun n ↦ by simpa only [Function.iterate_succ_apply'] using hf _⟩

end CoercivityAndExistence

end TauCeti
