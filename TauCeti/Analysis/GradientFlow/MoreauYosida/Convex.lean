/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Data.EReal.Operations

/-!
# The discrete variational inequality and resolvent existence for convex energies

Let `φ : X → EReal` be an energy on a pseudometric space, `m : ℝ` and `τ > 0` a time step. The
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
`(1/2) d/dt d(u t, v)² + (m / 2) d(u t, v)² ≤ φ v - φ (u t)` (`TauCeti.IsEVISolution`). On a
metric space, when `1 + m τ > 0` and `φ` never takes the value `⊥` and is finite somewhere, the
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

In a complete pseudometric space, `(m + 1 / τ)`-convexity of the penalized energy with `1 + m τ > 0`
also yields existence of resolvent steps and minimizing movement sequences without any compactness
hypothesis on sublevels (`TauCeti.moreauYosidaResolvent_nonempty_of_convexAlong`,
`TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`,
`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`). Moreover, an `m`-geodesically
convex energy that is lower semicontinuous and finite at a single point `x₀` is automatically
coercive at every point for `1 + m τ > 0` (`TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`,
`TauCeti.GeodesicallyConvex.exists_moreauYosida_ne_bot`), via the abstract coercivity criteria
`TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt` and
`TauCeti.moreauYosida_ne_bot_of_lowerSemicontinuousAt`.

## Main definitions

* `TauCeti.PenalizedConvex m τ φ`: the penalized energies `φ + d(w, ·)² / (2τ)` are
  `(m + 1 / τ)`-convex along some curve between any two points of finite energy.
* `TauCeti.ConvexWithDistSq m φ`: Ambrosio–Gigli Assumption 3.24, requiring `m`-convexity of `φ`
  and `2`-convexity of `d(·, w)²` along a shared connecting curve.

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
* `TauCeti.moreauYosidaResolvent_nonempty_of_convexAlong`,
  `TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`,
  `TauCeti.PenalizedConvex.existsUnique_mem_moreauYosidaResolvent`, and
  `TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`: existence and uniqueness of
  resolvent steps and minimizing movement sequences in complete spaces without compactness of
  sublevels.
* `TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt` and
  `TauCeti.moreauYosida_ne_bot_of_lowerSemicontinuousAt`: coercivity (`⨅ z, Ψ z ≠ ⊥` and
  `φ_τ(x) ≠ ⊥` for `1 + m τ > 0`) from pointwise lower semicontinuity at a point of finite energy
  and `κ`-convex interpolation with `κ > 0`.
* `TauCeti.ConvexWithDistSq.penalizedConvex`, `TauCeti.ConvexWithDistSq.moreauYosida_ne_bot`,
  `TauCeti.ConvexWithDistSq.exists_moreauYosida_ne_bot`,
  `TauCeti.ConvexWithDistSq.moreauYosidaResolvent_nonempty`,
  `TauCeti.ConvexWithDistSq.existsUnique_mem_moreauYosidaResolvent`, and
  `TauCeti.ConvexWithDistSq.exists_forall_mem_moreauYosidaResolvent`: penalized convexity,
  coercivity, existence, and uniqueness under Ambrosio–Gigli Assumption 3.24.
* `TauCeti.GeodesicallyConvex.convexWithDistSq`, `TauCeti.GeodesicallyConvex.penalizedConvex`,
  `TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`,
  `TauCeti.GeodesicallyConvex.exists_moreauYosida_ne_bot`,
  `TauCeti.GeodesicallyConvex.moreauYosidaResolvent_nonempty`,
  `TauCeti.GeodesicallyConvex.existsUnique_mem_moreauYosidaResolvent`, and
  `TauCeti.GeodesicallyConvex.exists_forall_mem_moreauYosidaResolvent`: coercivity of geodesically
  convex energies, and existence and uniqueness of resolvent steps and minimizing movement
  sequences on complete CAT(0) spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Lemma 2.4.8, Assumption 4.0.1, Theorem 4.1.2,
  and Section 4.1.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Math. 2062,
  Springer 2013, Assumption 3.24.
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

/-- An energy `φ : X → EReal` satisfies Ambrosio–Gigli Assumption 3.24 with parameter `m` if for
every base point `w` and any two points `v₀`, `v₁` of `{z | φ z ≠ ⊤}` there is a curve `γ` from
`v₀` to `v₁` along which `φ` is `m`-convex and `z ↦ d(z, w)²` is `2`-convex. -/
def ConvexWithDistSq (m : ℝ) (φ : X → EReal) : Prop :=
  ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
    ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ

/-- The defining condition of `ConvexWithDistSq`. -/
theorem convexWithDistSq_def :
    ConvexWithDistSq m φ ↔ ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ →
      ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
        ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ :=
  Iff.rfl

/-- `ConvexWithDistSq` with a parameter `m` implies it for every smaller parameter. -/
theorem ConvexWithDistSq.mono (h : ConvexWithDistSq m φ) (hm : m' ≤ m) :
    ConvexWithDistSq m' φ := fun w _ _ h₀ h₁ ↦
  (h w h₀ h₁).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.1, hγ.2.2.1.mono hm, hγ.2.2.2⟩

/-- **Penalized convexity from curve convexity of the energy and of the squared distance**
(Ambrosio–Gigli, Assumption 3.24). An energy satisfying `ConvexWithDistSq m φ` is penalized convex
with parameter `m` for every time step `τ`. -/
theorem ConvexWithDistSq.penalizedConvex (h : ConvexWithDistSq m φ) :
    PenalizedConvex m τ φ := by
  intro w v₀ v₁ h₀ h₁
  obtain ⟨γ, hγ0, hγ1, hφγ, hdγ⟩ := h w h₀ h₁
  refine ⟨γ, hγ0, hγ1, ?_⟩
  have hd := hdγ.const_mul (c := 1 / (2 * τ)) (by positivity)
  convert hφγ.add hd using 1
  · ring
  · funext z
    rw [Pi.add_apply, ← EReal.coe_mul, dist_comm]
    congr 2
    ring

/-- On a CAT(0) space, an `m`-geodesically convex energy satisfies `ConvexWithDistSq m φ` along
its witnessing geodesics: the squared distance from any base point is `2`-convex along every
geodesic. -/
theorem GeodesicallyConvex.convexWithDistSq [IsCATZeroSpace X] (h : GeodesicallyConvex m φ) :
    ConvexWithDistSq m φ := fun w _ _ h₀ h₁ ↦
  let ⟨γ, hγ, hφγ⟩ := geodesicallyConvex_def.1 h h₀ h₁
  ⟨γ, hγ.source, hγ.target, hφγ, convexAlongGeodesics_def.1 (convexAlongGeodesics_dist_sq w)
    (EReal.coe_ne_top _) (EReal.coe_ne_top _) hγ⟩

/-- On a CAT(0) space, an `m`-geodesically convex energy is penalized convex with parameter `m`
for every time step. -/
theorem GeodesicallyConvex.penalizedConvex [IsCATZeroSpace X] (h : GeodesicallyConvex m φ) :
    PenalizedConvex m τ φ :=
  h.convexWithDistSq.penalizedConvex

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
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
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

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ τ₀ : ℝ≥0} {φ : X → EReal} {x x₀ : X}

/-- Midpoint quantitative stability for two points with penalized energy near the infimum `M`: if
`z ↦ φ z + d(x, z)² / (2τ)` is bounded below by `M` and `(m + 1 / τ)`-convex along a curve from
`v₀` to `v₁`, then `(1 + m τ) / (8τ) d(v₀, v₁)² ≤ (Ψ v₀ - M) / 2 + (Ψ v₁ - M) / 2`. -/
private lemma mul_dist_sq_le_of_convexAlong (hτ : 0 < τ) {M ε₀ ε₁ : ℝ} {v₀ v₁ : X}
    {γ : ℝ → X} (hγ0 : γ 0 = v₀) (hγ1 : γ 1 = v₁)
    (hγ : ConvexAlong (m + (τ : ℝ)⁻¹)
      (fun z ↦ φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal)) γ)
    (hlow : (M : EReal) ≤ φ (γ (1 / 2)) + ((dist x (γ (1 / 2)) ^ 2 / (2 * τ) : ℝ) : EReal))
    (htop₀ : φ v₀ ≠ ⊤) (hbot₀ : φ v₀ ≠ ⊥) (htop₁ : φ v₁ ≠ ⊤) (hbot₁ : φ v₁ ≠ ⊥)
    (hv₀ : φ v₀ + (edist x v₀ ^ 2 / (2 * τ) : ℝ≥0∞) < ((M + ε₀ : ℝ) : EReal))
    (hv₁ : φ v₁ + (edist x v₁ ^ 2 / (2 * τ) : ℝ≥0∞) < ((M + ε₁ : ℝ) : EReal)) :
    (1 + m * τ) / (8 * τ) * dist v₀ v₁ ^ 2 ≤ ε₀ / 2 + ε₁ / 2 := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hcomb := hlow.trans (convexAlong_def.1 hγ (1 / 2) ⟨by norm_num, by norm_num⟩)
  rw [hγ0, hγ1] at hcomb
  set a₀ : ℝ := (φ v₀).toReal
  set a₁ : ℝ := (φ v₁).toReal
  have ha₀ : φ v₀ = a₀ := (EReal.coe_toReal htop₀ hbot₀).symm
  have ha₁ : φ v₁ = a₁ := (EReal.coe_toReal htop₁ hbot₁).symm
  have hv₀' : a₀ + dist x v₀ ^ 2 / (2 * τ) < M + ε₀ := by
    rwa [coe_edist_sq_div_eq_coe_dist_sq_div hτ, ha₀, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hv₀
  have hv₁' : a₁ + dist x v₁ ^ 2 / (2 * τ) < M + ε₁ := by
    rwa [coe_edist_sq_div_eq_coe_dist_sq_div hτ, ha₁, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hv₁
  rw [ha₀, ha₁] at hcomb
  norm_cast at hcomb
  push_cast at hcomb
  have hcoef : (1 + m * (τ : ℝ)) / (8 * τ) = (m + (τ : ℝ)⁻¹) / 2 * (1 / 2) * (1 - 1 / 2) := by
    field_simp
    ring
  rw [hcoef]
  linarith

/-- **Existence of a resolvent step from convexity of the penalized energy** (Ambrosio–Gigli–Savaré,
Theorem 4.1.2). In a complete pseudometric space, if `φ` is lower semicontinuous, `τ > 0` satisfies
`1 + m τ > 0`, `φ_τ(x) ≠ ⊥`, and any two points of finite energy are joined by a curve along which
`z ↦ φ z + d(x, z)² / (2τ)` is `(m + 1 / τ)`-convex, then the resolvent `J_τ x` is nonempty. No
compactness of sublevels is needed. -/
theorem moreauYosidaResolvent_nonempty_of_convexAlong [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (h : ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong (m + (τ : ℝ)⁻¹) (fun z ↦ φ z + ((dist x z ^ 2 / (2 * τ) : ℝ) : EReal)) γ)
    (hbot : moreauYosida φ τ x ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  -- Every minimizing sequence for `z ↦ φ z + d(x, z)² / (2τ)` is Cauchy by strong convexity along
  -- the connecting curves.
  rcases eq_or_ne (moreauYosida φ τ x) ⊤ with htop | htop
  · exact ⟨x, self_mem_moreauYosidaResolvent_of_eq_top htop⟩
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
  have hφ_ne_bot : ∀ n, φ (v n) ≠ ⊥ := fun n ↦
    apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x (v n)) hbot
  have hc : 0 < (1 + m * τ) / (8 * τ) := by positivity
  have hdist_sq : ∀ n k : ℕ, (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2 ≤
      (1 / ((n : ℝ) + 1)) / 2 + (1 / ((k : ℝ) + 1)) / 2 := fun n k ↦ by
    obtain ⟨γ, hγ0, hγ1, hγ⟩ := h (hφ_ne_top n) (hφ_ne_top k)
    exact mul_dist_sq_le_of_convexAlong hτ hγ0 hγ1 hγ (hψ_ge (γ (1 / 2)))
      (hφ_ne_top n) (hφ_ne_bot n) (hφ_ne_top k) (hφ_ne_bot k) (hv n) (hv k)
  have hcauchy : CauchySeq v := Metric.cauchySeq_iff.2 fun ε hε ↦ by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (mul_pos (pow_pos hε 2) hc)
    refine ⟨N, fun n hn k hk ↦ ?_⟩
    have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    have hsq : (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2 <
        (1 + m * τ) / (8 * τ) * ε ^ 2 := by
      calc (1 + m * τ) / (8 * τ) * dist (v n) (v k) ^ 2
          ≤ (1 / ((n : ℝ) + 1)) / 2 + (1 / ((k : ℝ) + 1)) / 2 := hdist_sq n k
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

/-- **Existence of resolvent steps under penalized convexity** (Ambrosio–Gigli–Savaré, Theorem
4.1.2). In a complete pseudometric space, if `φ` is lower semicontinuous and penalized convex with
parameter `m` and time step `τ > 0` satisfying `1 + m τ > 0`, and if `φ_τ(x) ≠ ⊥`, then the
resolvent `J_τ x` is nonempty. No compactness of sublevels is needed. -/
theorem PenalizedConvex.moreauYosidaResolvent_nonempty [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hbot : moreauYosida φ τ x ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty :=
  moreauYosidaResolvent_nonempty_of_convexAlong hφ hτ hmτ (@h x) hbot

/-- **Existence and uniqueness of the resolvent step under penalized convexity.** In a complete
metric space, if `φ` is lower semicontinuous, finite somewhere (`∃ z, φ z ≠ ⊤`), and penalized
convex with parameter `m` and time step `τ > 0` satisfying `1 + m τ > 0`, and if `φ_τ(x) ≠ ⊥`,
then `J_τ x` contains a unique point. -/
theorem PenalizedConvex.existsUnique_mem_moreauYosidaResolvent {X : Type*} [MetricSpace X]
    [CompleteSpace X] {φ : X → EReal} {x : X} (hφ : LowerSemicontinuous φ)
    (h : PenalizedConvex m τ φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (hmoreau : moreauYosida φ τ x ≠ ⊥) (hdom : ∃ z, φ z ≠ ⊤) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x := by
  have hbot : ∀ z, φ z ≠ ⊥ := fun z ↦
    apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x z) hmoreau
  obtain ⟨y, hy⟩ := h.moreauYosidaResolvent_nonempty hφ hτ hmτ hmoreau
  exact ⟨y, hy, fun y' hy' ↦ h.subsingleton_moreauYosidaResolvent hτ hmτ hbot hdom x hy' hy⟩

/-- **Existence of minimizing movement sequences under penalized convexity.** In a complete
pseudometric space, if `φ` is lower semicontinuous, penalized convex with parameter `m` at time
step `τ > 0` satisfying `1 + m τ > 0`, and coercive (`φ_{τ₀}(x₀) ≠ ⊥`) at a larger time step
`τ₀ > τ`, then every point `x` starts a minimizing movement sequence `u` with `u 0 = x` and
`u (n + 1) ∈ J_τ (u n)` for all `n`. -/
theorem PenalizedConvex.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) (x : X) :
    ∃ u : ℕ → X, u 0 = x ∧ ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) := by
  have step : ∀ z : X, ∃ y, y ∈ moreauYosidaResolvent φ τ z := fun z ↦
    h.moreauYosidaResolvent_nonempty hφ hτ hmτ
      (moreauYosida_ne_bot_of_lt hττ₀ (edist_ne_top z x₀) h₀)
  choose f hf using step
  exact ⟨fun n ↦ f^[n] x, rfl, fun n ↦ by simpa only [Function.iterate_succ_apply'] using hf _⟩

/-- **Metric coercivity from local lower semicontinuity and `κ`-convex interpolation**
(Ambrosio–Gigli–Savaré, Lemma 2.4.8). Let `Ψ : X → EReal` be lower semicontinuous and finite at a
point `x₀`, and let `κ > 0`. Suppose that every point `z` with `Ψ z ≠ ⊤` can be interpolated
towards `x₀` at some scale `R : ℝ` so that for every `t ∈ [0, 1]` there is a point `y` at distance
at most `t R` from `x₀` satisfying
`Ψ y ≤ (1 - t) Ψ x₀ + t Ψ z - (κ / 2) t (1 - t) R ^ 2`.
Then `Ψ` is bounded below by a real constant; in particular `⨅ z, Ψ z ≠ ⊥`. -/
theorem iInf_ne_bot_of_lowerSemicontinuousAt {Ψ : X → EReal} {x₀ : X} {κ : ℝ}
    (hΨ : LowerSemicontinuousAt Ψ x₀) (htop : Ψ x₀ ≠ ⊤) (hbot : Ψ x₀ ≠ ⊥) (hκ : 0 < κ)
    (hinterp : ∀ z, Ψ z ≠ ⊤ → ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y, dist x₀ y ≤ t * R ∧
      Ψ y ≤ ((1 - t : ℝ) : EReal) * Ψ x₀ + (t : EReal) * Ψ z -
        ((κ / 2 * t * (1 - t) * R ^ 2 : ℝ) : EReal)) :
    (⨅ z, Ψ z) ≠ ⊥ := by
  -- Local boundedness below near `x₀` extends to a global lower bound by choosing `t = 1` when
  -- `R < δ` and `t = δ / (2R)` when `R ≥ δ`, then completing the square against `(κ / 4) R²`.
  set a : ℝ := (Ψ x₀).toReal
  have ha : Ψ x₀ = a := (EReal.coe_toReal htop hbot).symm
  have hnhds : ∀ᶠ y in 𝓝 x₀, ((a - 1 : ℝ) : EReal) < Ψ y :=
    hΨ _ (by simp only [gt_iff_lt, ha, EReal.coe_lt_coe_iff]; exact sub_one_lt a)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.eventually_iff.1 hnhds
  set L : ℝ := min (a - 1) (a - 4 / (κ * δ ^ 2))
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_iInf fun z ↦ ?_)
  rcases eq_or_ne (Ψ z) ⊤ with hztop | hztop
  · exact hztop ▸ le_top
  obtain ⟨R, hinterp_z⟩ := hinterp z hztop
  rcases lt_or_ge R δ with hR | hR
  · obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z 1 ⟨zero_le_one, le_rfl⟩
    have hy_ball : y ∈ Metric.ball x₀ δ :=
      Metric.mem_ball'.2 (hy_dist.trans_lt (by simpa only [one_mul] using hR))
    have h1 : Ψ y ≤ Ψ z := by simpa [ha] using hy_le
    exact (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans ((hball hy_ball).le.trans h1)
  have hRpos : 0 < R := hδ.trans_le hR
  set t : ℝ := δ / (2 * R)
  have htpos : 0 < t := by positivity
  have ht12 : t ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) two_pos).2 (by linarith)
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht12.trans (by norm_num)⟩
  obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z t htIcc
  have hy_ball : y ∈ Metric.ball x₀ δ := by
    rw [Metric.mem_ball']
    have htR : t * R = δ / 2 := by dsimp [t]; field_simp
    linarith
  have hlow : ((a - 1 : ℝ) : EReal) < Ψ y := hball hy_ball
  have hzbot : Ψ z ≠ ⊥ := fun hzbot ↦ by
    rw [hzbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot, EReal.bot_sub, le_bot_iff] at hy_le
    exact not_lt_bot (hy_le ▸ hlow)
  set b : ℝ := (Ψ z).toReal
  have hb : Ψ z = b := (EReal.coe_toReal hztop hzbot).symm
  rw [ha, hb] at hy_le
  norm_cast at hy_le
  have hmid : a - 1 ≤ (1 - t) * a + t * b - κ / 2 * t * (1 - t) * R ^ 2 := by
    exact_mod_cast hlow.le.trans hy_le
  have hslope : a - 2 * R / δ ≤ b - κ / 2 * (1 - t) * R ^ 2 := by
    refine le_of_mul_le_mul_left ?_ htpos
    have : t * (2 * R / δ) = 1 := by dsimp [t]; field_simp
    linarith
  have hquad : κ / 4 * R ^ 2 ≤ κ / 2 * (1 - t) * R ^ 2 := by
    calc κ / 4 * R ^ 2 = 1 / 4 * (κ * R ^ 2) := by ring
      _ ≤ (1 - t) / 2 * (κ * R ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = κ / 2 * (1 - t) * R ^ 2 := by ring
  have hsq : -(4 / (κ * δ ^ 2)) ≤ κ / 4 * R ^ 2 - 2 * R / δ := by
    rw [← sub_nonneg]
    calc κ / 4 * R ^ 2 - 2 * R / δ - -(4 / (κ * δ ^ 2))
        = (κ * δ * R - 4) ^ 2 / (4 * κ * δ ^ 2) := by field_simp; ring
      _ ≥ 0 := div_nonneg (sq_nonneg _) (by positivity)
  rw [hb]
  exact EReal.coe_le_coe_iff.2 ((min_le_right _ _).trans (by linarith))

/-- **Coercivity of `φ_τ` from local lower semicontinuity and penalized `(m + 1 / σ)`-convex
interpolation** (Ambrosio–Gigli–Savaré, Lemma 2.4.8). Let `φ` be lower semicontinuous and finite at
a point `x₀`, let `x₁` be a base point, and suppose that for every `σ > 0` with `1 + m σ > 0` and
every `z` with `φ z ≠ ⊤`, the penalized energy `w ↦ φ w + d(x₁, w)² / (2σ)` admits an
`(m + 1 / σ)`-convex interpolation from `x₀` to `z` at some scale `R : ℝ`. Then `φ_τ(x) ≠ ⊥` for
every `τ ≥ 0` with `1 + m τ > 0` and every `x : X`. -/
theorem moreauYosida_ne_bot_of_lowerSemicontinuousAt {x₀ x₁ : X}
    (hx₀ : LowerSemicontinuousAt φ x₀) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥)
    (hmτ : 0 < 1 + m * τ)
    (hinterp : ∀ {σ : ℝ≥0}, 0 < σ → 0 < 1 + m * σ → ∀ z, φ z ≠ ⊤ →
      ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y, dist x₀ y ≤ t * R ∧
        φ y + ((dist x₁ y ^ 2 / (2 * σ) : ℝ) : EReal) ≤
          ((1 - t : ℝ) : EReal) * (φ x₀ + ((dist x₁ x₀ ^ 2 / (2 * σ) : ℝ) : EReal)) +
            (t : EReal) * (φ z + ((dist x₁ z ^ 2 / (2 * σ) : ℝ) : EReal)) -
            (((m + (σ : ℝ)⁻¹) / 2 * t * (1 - t) * R ^ 2 : ℝ) : EReal))
    (x : X) :
    moreauYosida φ τ x ≠ ⊥ := by
  refine moreauYosida_ne_bot_of_forall_one_add_mul_pos hmτ (edist_ne_top x x₁)
    fun {σ} hσ hmσ ↦ ?_
  set Ψ : X → EReal := fun z ↦ φ z + ((dist x₁ z ^ 2 / (2 * σ) : ℝ) : EReal)
  have hΨ_eq : moreauYosida φ σ x₁ = ⨅ z, Ψ z := by
    rw [moreauYosida_eq_iInf]
    exact iInf_congr fun z ↦ congr_arg (φ z + ·) (coe_edist_sq_div_eq_coe_dist_sq_div hσ x₁ z)
  rw [hΨ_eq]
  have hΨtop : Ψ x₀ ≠ ⊤ := EReal.add_ne_top hx₀top (EReal.coe_ne_top _)
  have hΨbot : Ψ x₀ ≠ ⊥ := EReal.add_ne_bot_iff.2 ⟨hx₀bot, EReal.coe_ne_bot _⟩
  have hcont : Continuous (fun z : X ↦ ((dist x₁ z ^ 2 / (2 * σ) : ℝ) : EReal)) :=
    EReal.continuous_coe_iff.2 (((continuous_const.dist continuous_id).pow 2).div_const _)
  refine iInf_ne_bot_of_lowerSemicontinuousAt (x₀ := x₀) (κ := m + (σ : ℝ)⁻¹)
    (hx₀.add' hcont.continuousAt.lowerSemicontinuousAt
      (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))))
    hΨtop hΨbot ?_ fun z hz ↦ ?_
  · have : m + (σ : ℝ)⁻¹ = (1 + m * σ) / σ := by field_simp; ring
    rw [this]
    positivity
  · exact hinterp hσ hmσ z
      ((EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).1 hz)

/-- Shared coercivity criterion at a base point `z₀` where `φ` is lower semicontinuous and finite,
given `m`-convexity of `φ` and `2`-convexity of `d(·, z₀)²` along curves starting at `z₀`. -/
private lemma moreauYosida_ne_bot_of_convexAlong_dist_sq_at {z₀ : X}
    (hz₀ : LowerSemicontinuousAt φ z₀) (hz₀top : φ z₀ ≠ ⊤) (hz₀bot : φ z₀ ≠ ⊥)
    (hconv : ∀ ⦃v₁ : X⦄, φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = z₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z z₀ ^ 2 : ℝ) : EReal)) γ)
    (hmτ : 0 < 1 + m * τ) (x : X) :
    moreauYosida φ τ x ≠ ⊥ := by
  refine moreauYosida_ne_bot_of_lowerSemicontinuousAt (x₁ := z₀) hz₀ hz₀top hz₀bot hmτ
    (fun {σ} hσ _ z hz ↦ ?_) x
  obtain ⟨γ, h0, h1, hφγ, hdγ⟩ := hconv hz
  have hd_mul : ∀ t ∈ Icc (0 : ℝ) 1, dist z₀ (γ t) ≤ t * dist z₀ z := fun t ht ↦ by
    have hd0 : ConvexAlong 2 (fun z ↦ ((dist z (γ 0) ^ 2 : ℝ) : EReal)) γ := by
      simpa only [h0] using hdγ
    simpa only [h0, h1] using hd0.dist_le_mul ht
  have hd : ConvexAlong (σ : ℝ)⁻¹ (fun y ↦ ((dist z₀ y ^ 2 / (2 * σ) : ℝ) : EReal)) γ := by
    have hscaled := hdγ.const_mul (c := 1 / (2 * (σ : ℝ))) (by positivity)
    have hm : (1 / (2 * (σ : ℝ))) * 2 = (σ : ℝ)⁻¹ := by field_simp
    have hf : (fun x ↦ (((1 / (2 * (σ : ℝ))) : ℝ) : EReal) * ((dist x z₀ ^ 2 : ℝ) : EReal)) =
        (fun y ↦ ((dist z₀ y ^ 2 / (2 * σ) : ℝ) : EReal)) := by
      funext y; rw [← EReal.coe_mul, dist_comm]; congr 1; ring
    rwa [hm, hf] at hscaled
  have hΨ := convexAlong_def.1 (hφγ.add hd)
  refine ⟨dist z₀ z, fun t ht ↦ ⟨γ t, ⟨hd_mul t ht, ?_⟩⟩⟩
  simpa only [h0, h1, Pi.add_apply] using hΨ t ht

/-- **Coercivity under Ambrosio–Gigli Assumption 3.24.** If `φ` satisfies `ConvexWithDistSq m φ`
and is lower semicontinuous and finite at a point `x₀`, then `φ_τ(x) ≠ ⊥` whenever
`1 + m τ > 0`. -/
theorem ConvexWithDistSq.moreauYosida_ne_bot (h : ConvexWithDistSq m φ)
    (hx₀ : LowerSemicontinuousAt φ x₀) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥)
    (hmτ : 0 < 1 + m * τ) (x : X) :
    moreauYosida φ τ x ≠ ⊥ :=
  moreauYosida_ne_bot_of_convexAlong_dist_sq_at hx₀ hx₀top hx₀bot (fun _ h₁ ↦ h x₀ hx₀top h₁) hmτ x

/-- **Coercivity of geodesically convex energies** (Ambrosio–Gigli–Savaré, Lemma 2.4.8). Let `φ` be
`m`-geodesically convex on a pseudometric space, and lower semicontinuous and finite at some point
`x₀`. Then for every time step `τ ≥ 0` with `1 + m τ > 0` and every point `x : X`,
`φ_τ(x) ≠ ⊥`. -/
theorem GeodesicallyConvex.moreauYosida_ne_bot (h : GeodesicallyConvex m φ)
    (hx₀ : LowerSemicontinuousAt φ x₀) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥)
    (hmτ : 0 < 1 + m * τ) (x : X) :
    moreauYosida φ τ x ≠ ⊥ :=
  moreauYosida_ne_bot_of_convexAlong_dist_sq_at hx₀ hx₀top hx₀bot (fun _ hv₁ ↦ by
    obtain ⟨γ, hγ, hφγ⟩ := geodesicallyConvex_def.1 h hx₀top hv₁
    refine ⟨γ, hγ.source, hγ.target, hφγ, convexAlong_def.2 fun t ht ↦ ?_⟩
    rw [hγ.source, hγ.target, dist_comm _ x₀, hγ.dist_source_apply ht, dist_self,
      dist_comm _ x₀]
    norm_cast
    exact le_of_eq (by ring)) hmτ x

end Existence

section StepSize

open NNReal

/-- For any `m : ℝ`, `c > 0`, and bound `b > 0`, there exists a positive step size `τ : ℝ≥0` below
`b` such that `|m| * δ ≤ c` for every `δ ≤ τ`. -/
theorem exists_pos_abs_mul_le (m : ℝ) {c : ℝ} (hc : 0 < c) {b : ℝ≥0} (hb : 0 < b) :
    ∃ τ : ℝ≥0, 0 < τ ∧ τ < b ∧ ∀ ⦃δ : ℝ≥0⦄, δ ≤ τ → |m| * (δ : ℝ) ≤ c := by
  set r : ℝ := c / (|m| + 1)
  have hr : 0 < r := by positivity
  refine ⟨min (b / 2) r.toNNReal, lt_min (half_pos hb) (Real.toNNReal_pos.2 hr),
    (min_le_left _ _).trans_lt (half_lt_self hb), fun δ hδ ↦ ?_⟩
  have hδr : (δ : ℝ) ≤ r :=
    (NNReal.coe_le_coe.2 (hδ.trans (min_le_right _ _))).trans_eq (Real.coe_toNNReal r hr.le)
  calc |m| * (δ : ℝ) ≤ (|m| + 1) * r :=
        mul_le_mul (by linarith) hδr (NNReal.coe_nonneg δ) (by positivity)
    _ = c := by dsimp [r]; field_simp

/-- If `0 ≤ δ` and `|m| * δ ≤ 1 / 2`, then `0 < 1 + m * δ`. -/
theorem one_add_mul_pos_of_abs_mul_le_half {m δ : ℝ} (hδ : 0 ≤ δ) (h : |m| * δ ≤ 1 / 2) :
    0 < 1 + m * δ := by
  nlinarith [neg_abs_le m, hδ]

end StepSize

section Assumption324AndCATZero

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ : ℝ≥0} {φ : X → EReal} {x x₀ : X}

/-- **Existence of a coercive time step under Assumption 3.24.** If `φ` satisfies
`ConvexWithDistSq m φ` and is lower semicontinuous and finite at some point `x₀`, then for every
`x : X` there exists `τ₀ > 0` with `φ_{τ₀}(x) ≠ ⊥`. -/
theorem ConvexWithDistSq.exists_moreauYosida_ne_bot (h : ConvexWithDistSq m φ)
    (hx₀ : LowerSemicontinuousAt φ x₀) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) (x : X) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida φ τ₀ x ≠ ⊥ :=
  let ⟨τ₀, hτ₀, _, hm⟩ := exists_pos_abs_mul_le m (by norm_num : (0 : ℝ) < 1 / 2) one_pos
  ⟨τ₀, hτ₀, h.moreauYosida_ne_bot hx₀ hx₀top hx₀bot
    (one_add_mul_pos_of_abs_mul_le_half τ₀.property (hm le_rfl)) x⟩

/-- **Existence of a coercive time step for geodesically convex energies.** If `φ` is
`m`-geodesically convex on a pseudometric space, and is lower semicontinuous and finite at some
point `x₀`, then for every `x : X` there exists `τ₀ > 0` with `φ_{τ₀}(x) ≠ ⊥`. -/
theorem GeodesicallyConvex.exists_moreauYosida_ne_bot (h : GeodesicallyConvex m φ)
    (hx₀ : LowerSemicontinuousAt φ x₀) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) (x : X) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida φ τ₀ x ≠ ⊥ :=
  let ⟨τ₀, hτ₀, _, hm⟩ := exists_pos_abs_mul_le m (by norm_num : (0 : ℝ) < 1 / 2) one_pos
  ⟨τ₀, hτ₀, h.moreauYosida_ne_bot hx₀ hx₀top hx₀bot
    (one_add_mul_pos_of_abs_mul_le_half τ₀.property (hm le_rfl)) x⟩

/-- **Existence of resolvent steps under curve convexity of the energy and of the squared distance**
(Ambrosio–Gigli, Assumption 3.24). In a complete pseudometric space, if `φ` is lower
semicontinuous, never takes `⊥`, and satisfies `ConvexWithDistSq m φ`, then `J_τ x` is nonempty
whenever `τ > 0` and `1 + m τ > 0`. -/
theorem ConvexWithDistSq.moreauYosidaResolvent_nonempty [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : ConvexWithDistSq m φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  refine h.penalizedConvex.moreauYosidaResolvent_nonempty hφ hτ hmτ ?_
  by_cases hdom : ∃ z₀, φ z₀ ≠ ⊤
  · obtain ⟨z₀, hz₀⟩ := hdom
    exact h.moreauYosida_ne_bot (hφ.lowerSemicontinuousAt z₀) hz₀ (hbot z₀) hmτ x
  · rw [moreauYosida_eq_top_of_forall_eq_top fun z _ ↦ not_ne_iff.1 fun hz ↦ hdom ⟨z, hz⟩]
    exact top_ne_bot

/-- **Existence and uniqueness of resolvent steps under curve convexity of the energy and of the
squared distance** (Ambrosio–Gigli, Assumption 3.24). -/
theorem ConvexWithDistSq.existsUnique_mem_moreauYosidaResolvent {X : Type*} [MetricSpace X]
    [CompleteSpace X] {φ : X → EReal} {x₀ : X} (hφ : LowerSemicontinuous φ)
    (h : ConvexWithDistSq m φ) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x :=
  h.penalizedConvex.existsUnique_mem_moreauYosidaResolvent hφ hτ hmτ
    (h.moreauYosida_ne_bot (hφ.lowerSemicontinuousAt x₀) hx₀top hx₀bot hmτ x) ⟨x₀, hx₀top⟩

/-- **Existence of minimizing movement sequences under curve convexity of the energy and of the
squared distance** (Ambrosio–Gigli, Assumption 3.24). -/
theorem ConvexWithDistSq.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (h : ConvexWithDistSq m φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x₀ : X) :
    ∃ U : ℕ → X, U 0 = x₀ ∧ ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n) := by
  choose f hf using h.moreauYosidaResolvent_nonempty hφ hbot hτ hmτ
  exact ⟨fun n ↦ f^[n] x₀, rfl, fun n ↦ by simpa only [Function.iterate_succ_apply'] using hf _⟩

/-- **Existence of resolvent steps for geodesically convex energies on CAT(0) spaces.** In a
complete CAT(0) pseudometric space, if `φ` is lower semicontinuous, `m`-geodesically convex, and
never takes the value `⊥`, then for every time step `τ > 0` with `1 + m τ > 0` and every `x : X`,
the resolvent `J_τ x` is nonempty. -/
theorem GeodesicallyConvex.moreauYosidaResolvent_nonempty [CompleteSpace X] [IsCATZeroSpace X]
    (hφ : LowerSemicontinuous φ) (h : GeodesicallyConvex m φ) (hbot : ∀ z, φ z ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    (moreauYosidaResolvent φ τ x).Nonempty :=
  h.convexWithDistSq.moreauYosidaResolvent_nonempty hφ hbot hτ hmτ x

/-- **Existence and uniqueness of the resolvent step for geodesically convex energies on CAT(0)
metric spaces.** In a complete CAT(0) metric space, if `φ` is lower semicontinuous,
`m`-geodesically convex, and finite at some point `x₀`, then for every time step `τ > 0` with
`1 + m τ > 0` and every `x : X`, the resolvent `J_τ x` contains a unique point. -/
theorem GeodesicallyConvex.existsUnique_mem_moreauYosidaResolvent {X : Type*} [MetricSpace X]
    [CompleteSpace X] [IsCATZeroSpace X] {φ : X → EReal} {x₀ : X} (hφ : LowerSemicontinuous φ)
    (h : GeodesicallyConvex m φ) (hx₀top : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x :=
  h.convexWithDistSq.existsUnique_mem_moreauYosidaResolvent hφ hx₀top hx₀bot hτ hmτ x

/-- **Existence of minimizing movement sequences for geodesically convex energies on CAT(0)
spaces.** In a complete CAT(0) pseudometric space, if `φ` is lower semicontinuous, `m`-geodesically
convex, and never takes the value `⊥`, then for every time step `τ > 0` with `1 + m τ > 0` and
every `x : X`, there is a minimizing movement sequence starting at `x`. -/
theorem GeodesicallyConvex.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    [IsCATZeroSpace X] (hφ : LowerSemicontinuous φ) (h : GeodesicallyConvex m φ)
    (hbot : ∀ z, φ z ≠ ⊥) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    ∃ u : ℕ → X, u 0 = x ∧ ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) :=
  h.convexWithDistSq.exists_forall_mem_moreauYosidaResolvent hφ hbot hτ hmτ x

end Assumption324AndCATZero

end TauCeti
