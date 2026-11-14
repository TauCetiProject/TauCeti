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

(`TauCeti.PenalizedConvex m τ φ`). This holds whenever `φ` is `m`-convex and the squared distance
from `w` is `2`-convex along common connecting curves
(`TauCeti.penalizedConvex_of_convexAlong_and_convexAlong_dist_sq`, Assumption 3.24 of
Ambrosio–Gigli), in particular when `φ` is `m`-geodesically convex on a CAT(0) space
(`TauCeti.GeodesicallyConvex.penalizedConvex`), and, on the quadratic Wasserstein space, when `φ`
is `m`-convex along generalized geodesics based at every law and `1 + m τ ≥ 0`
(`TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`). Ordinary geodesic convexity is not
enough in general, because the squared distance from a point need not be convex along geodesics.
Ambrosio–Gigli–Savaré take the base point `w` in the effective domain; it is arbitrary here, as in
all these examples.

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
When the space is complete and `φ` is lower semicontinuous and coercive (`φ_τ(x) > -∞`), the same
strict convexity along midpoints makes every minimizing sequence Cauchy, so `J_τ x` is nonempty
without any sublevel compactness (`TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`,
Lemma 4.1.1 of Ambrosio–Gigli–Savaré). Moreover, if `φ` is lower semicontinuous, never takes the
value `⊥`, and is `m`-convex along connecting curves `γ` with `d(γ 0, γ t) ≤ t d(γ 0, γ 1)`, then
`φ_τ(x) > -∞` for every `x` and every `τ` with `1 + m τ > 0`
(`TauCeti.moreauYosida_ne_bot_of_convexAlong`, Lemma 2.4.8 of Ambrosio–Gigli–Savaré).

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
* `TauCeti.moreauYosida_ne_bot_of_convexAlong`,
  `TauCeti.moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq`, and
  `TauCeti.GeodesicallyConvex.moreauYosida_ne_bot`: coercivity `φ_τ(x) > -∞` when `1 + m τ > 0`
  and `φ` is lower semicontinuous, never `⊥`, and `m`-convex along curves with linear initial
  speed bound.
* `TauCeti.PenalizedConvex.moreauYosidaResolvent_nonempty`,
  `TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`, and
  `TauCeti.PenalizedConvex.existsUnique_mem_moreauYosidaResolvent` (with specializations under
  Assumption 3.24 and for `GeodesicallyConvex` on CAT(0) spaces): existence (and uniqueness) of
  resolvent steps on a complete space without sublevel compactness when `1 + m τ > 0`.
* `TauCeti.PenalizedConvex.pow_mul_dist_sq_sub_le`: the discrete integrated evolution variational
  inequality along a minimizing movement sequence, when `1 + m τ ≥ 0`.
* `TauCeti.PenalizedConvex.apply_le`: the discrete energy regularization estimate, when
  `1 + m τ ≥ 0`.
* `TauCeti.PenalizedConvex.pow_mul_dist_sq_le`: the weighted distance estimate of a minimizing
  movement sequence towards points of smaller energy, when `1 + m τ ≥ 0`.
* `TauCeti.penalizedConvex_of_convexAlong_and_convexAlong_dist_sq` and
  `TauCeti.GeodesicallyConvex.penalizedConvex`: penalized convexity for every time step under
  Assumption 3.24, and in particular on CAT(0) spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Lemma 2.4.8, Assumption 4.0.1, Lemma 4.1.1,
  Theorem 4.1.2 and Section 4.1.
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

/-- **Penalized convexity from curve convexity of the energy and of the squared distance**
(Ambrosio–Gigli, Assumption 3.24). If for every base point `w` and any two points `v₀`, `v₁` of
`{z | φ z ≠ ⊤}` there is a curve `γ` from `v₀` to `v₁` along which `φ` is `m`-convex and
`z ↦ d(z, w)²` is `2`-convex, then `φ` is penalized convex with parameter `m` for every time
step `τ`. -/
theorem penalizedConvex_of_convexAlong_and_convexAlong_dist_sq
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ) :
    PenalizedConvex m τ φ := by
  intro w v₀ v₁ h₀ h₁
  obtain ⟨γ, hγ0, hγ1, hφγ, hdγ⟩ := hconv w h₀ h₁
  refine ⟨γ, hγ0, hγ1, ?_⟩
  have hd := hdγ.const_mul (c := 1 / (2 * τ)) (by positivity)
  convert hφγ.add hd using 1
  · ring
  · funext z
    rw [Pi.add_apply, ← EReal.coe_mul, dist_comm]
    congr 2
    ring

/-- On a CAT(0) space, an `m`-geodesically convex energy is penalized convex with parameter `m`
for every time step, along the geodesics that witness its convexity: the squared distance from a
point is `2`-convex along every geodesic. -/
theorem GeodesicallyConvex.penalizedConvex [IsCATZeroSpace X] (h : GeodesicallyConvex m φ) :
    PenalizedConvex m τ φ :=
  penalizedConvex_of_convexAlong_and_convexAlong_dist_sq fun w _ _ h₀ h₁ ↦
    let ⟨γ, hγ, hφγ⟩ := geodesicallyConvex_def.1 h h₀ h₁
    ⟨γ, hγ.source, hγ.target, hφγ, convexAlongGeodesics_def.1 (convexAlongGeodesics_dist_sq w)
      (EReal.coe_ne_top _) (EReal.coe_ne_top _) hγ⟩

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

/-- If `φ` is bounded below by `ez - 1` on `Metric.ball z r` and `m`-convex along curves `γ` with
`d(z, γ t) ≤ t d(z, v)`, then `φ v` grows at least linearly-plus-quadratically in `d(z, v)` outside
`Metric.ball z (r / 2)`. -/
private theorem le_toReal_of_convexAlong_of_le_dist (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist v₀ (γ t) ≤ t * dist v₀ v₁) ∧ ConvexAlong m φ γ)
    {z : X} {ez r : ℝ} (hez : φ z = ez) (hr : 0 < r)
    (hr_ball : ∀ w, dist w z < r → ((ez - 1 : ℝ) : EReal) ≤ φ w)
    {v : X} (hvt : φ v ≠ ⊤) (hge : r / 2 ≤ dist z v) :
    ez - 2 / r * dist z v + min m 0 / 2 * dist z v ^ 2 ≤ (φ v).toReal := by
  set ev := (φ v).toReal
  have hev : φ v = ev := (EReal.coe_toReal hvt (hbot v)).symm
  have hD : 0 < dist z v := (half_pos hr).trans_le hge
  obtain ⟨γ, h0, h1, hdγ, hφγ⟩ := hconv (hez ▸ EReal.coe_ne_top ez) hvt
  set t : ℝ := r / (2 * dist z v)
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one (by positivity)).2 (by linarith)⟩
  have hc := convexAlong_def.1 hφγ t ht
  rw [h0, h1, hez, hev, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub] at hc
  have hγr : dist (γ t) z < r := by
    rw [dist_comm]
    refine (hdγ t ht).trans_lt ?_
    have heq : t * dist z v = r / 2 := by have := hD.ne'; dsimp [t]; field_simp
    linarith [half_lt_self hr]
  have hlow := EReal.coe_le_coe_iff.1 ((hr_ball (γ t) hγr).trans hc)
  set μ := min m 0
  have hμ0 : μ ≤ 0 := min_le_right m 0
  have hμm : μ / 2 * t * dist z v ^ 2 ≤ m / 2 * t * (1 - t) * dist z v ^ 2 := by
    have h1' : 0 ≤ (m - μ) / 2 := div_nonneg (sub_nonneg.2 (min_le_left m 0)) zero_le_two
    have h2' : 0 ≤ t * (1 - t) * dist z v ^ 2 :=
      mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (sq_nonneg _)
    linarith [mul_nonneg h1' h2', mul_nonneg (by linarith : 0 ≤ -μ / 2)
      (by positivity : 0 ≤ t ^ 2 * dist z v ^ 2),
      show m / 2 * t * (1 - t) * dist z v ^ 2 - μ / 2 * t * dist z v ^ 2 =
        (m - μ) / 2 * (t * (1 - t) * dist z v ^ 2) + (-μ / 2) * (t ^ 2 * dist z v ^ 2) by ring]
  have ht_mul := mul_le_mul_of_nonneg_left (by linarith [hlow, hμm] :
    t * ez - 1 ≤ t * (ev - μ / 2 * dist z v ^ 2)) (by positivity : 0 ≤ 2 * dist z v / r)
  have ht_inv : 2 * dist z v / r * t = 1 := by have := hD.ne'; dsimp [t]; field_simp
  have hL : 2 * dist z v / r * (t * ez - 1) = ez - 2 / r * dist z v := by
    calc 2 * dist z v / r * (t * ez - 1)
        = (2 * dist z v / r * t) * ez - 2 / r * dist z v := by ring
      _ = ez - 2 / r * dist z v := by rw [ht_inv, one_mul]
  have hR : 2 * dist z v / r * (t * (ev - μ / 2 * dist z v ^ 2)) =
      ev - μ / 2 * dist z v ^ 2 := by
    calc 2 * dist z v / r * (t * (ev - μ / 2 * dist z v ^ 2))
        = (2 * dist z v / r * t) * (ev - μ / 2 * dist z v ^ 2) := by ring
      _ = ev - μ / 2 * dist z v ^ 2 := by rw [ht_inv, one_mul]
  linarith [ht_mul, hL, hR]

/-- Uniform real lower bound on `v ↦ φ v + d(x, v)² / (2τ)` from a local lower bound on `φ` near
one finite-energy point `z` and `m`-convexity along curves with `d(z, γ t) ≤ t d(z, v)`. -/
private theorem exists_le_apply_add_dist_sq_div_of_convexAlong (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist v₀ (γ t) ≤ t * dist v₀ v₁) ∧ ConvexAlong m φ γ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) {z : X} {ez r : ℝ} (hez : φ z = ez) (hr : 0 < r)
    (hr_ball : ∀ w, dist w z < r → ((ez - 1 : ℝ) : EReal) ≤ φ w) (x : X) :
    ∃ B : ℝ, ∀ v, ((B : ℝ) : EReal) ≤ φ v + ((dist x v ^ 2 / (2 * τ) : ℝ) : EReal) := by
  set μ := min m 0
  have hμ0 : μ ≤ 0 := min_le_right m 0
  have h1μ : 0 < 1 + μ * τ := by
    dsimp [μ]
    rcases min_cases m 0 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [rwa [h1]; (rw [h1]; positivity)]
  set A : ℝ := (1 + μ * τ) / (2 * τ)
  have hA : 0 < A := div_pos h1μ (by positivity)
  set a : ℝ := dist z x; set L : ℝ := μ * a - 2 / r
  set C : ℝ := ez - 2 / r * a + μ / 2 * a ^ 2
  refine ⟨min (ez - 1) (C - L ^ 2 / (4 * A)), fun v ↦ ?_⟩
  rcases eq_or_ne (φ v) ⊤ with hvt | hvt
  · simp [hvt]
  set ev := (φ v).toReal
  have hev : φ v = ev := (EReal.coe_toReal hvt (hbot v)).symm
  rw [hev, ← EReal.coe_add, EReal.coe_le_coe_iff]
  rcases lt_or_ge (dist z v) (r / 2) with hlt | hge
  · have hzv : ez - 1 ≤ ev := EReal.coe_le_coe_iff.1
      (hev ▸ hr_ball v (by rw [dist_comm]; linarith))
    have hnn : 0 ≤ dist x v ^ 2 / (2 * τ) := by positivity
    exact (min_le_left _ _).trans (by linarith)
  have hev_bd : ez - 2 / r * dist z v + μ / 2 * dist z v ^ 2 ≤ ev :=
    le_toReal_of_convexAlong_of_le_dist hbot hconv hez hr hr_ball hvt hge
  have htri : dist z v ≤ a + dist x v := dist_triangle z x v
  have hmin_sq : C - L ^ 2 / (4 * A) ≤ A * dist x v ^ 2 + L * dist x v + C := by
    have hsq := mul_nonneg hA.le (sq_nonneg (dist x v + L / (2 * A)))
    linarith [hsq, show A * (dist x v + L / (2 * A)) ^ 2 =
      A * dist x v ^ 2 + L * dist x v + L ^ 2 / (4 * A) by have := hA.ne'; field_simp; ring]
  exact (min_le_right _ _).trans (by
    linarith [hev_bd, hmin_sq, mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 2 / r),
      mul_le_mul_of_nonpos_left (pow_le_pow_left₀ dist_nonneg htri 2) (by linarith : μ / 2 ≤ 0),
      show ez - 2 / r * (a + dist x v) + μ / 2 * (a + dist x v) ^ 2 + dist x v ^ 2 / (2 * τ) =
        A * dist x v ^ 2 + L * dist x v + C by
        dsimp [A, L, C]; have := (NNReal.coe_pos.2 hτ).ne'; field_simp; ring])

/-- **Coercivity from convexity along curves** (Ambrosio–Gigli–Savaré, Lemma 2.4.8). If `φ` is
lower semicontinuous, never takes the value `⊥`, and any two points `v₀`, `v₁` of `{z | φ z ≠ ⊤}`
are joined by a curve `γ` with `d(v₀, γ t) ≤ t d(v₀, v₁)` along which `φ` is `m`-convex, then
`φ_τ(x) > -∞` for every `x` and every `τ` with `1 + m τ > 0`. -/
theorem moreauYosida_ne_bot_of_convexAlong (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist v₀ (γ t) ≤ t * dist v₀ v₁) ∧ ConvexAlong m φ γ)
    (hmτ : 0 < 1 + m * τ) (x : X) : moreauYosida φ τ x ≠ ⊥ := by
  rcases (zero_le : 0 ≤ τ).eq_or_lt with hτ0 | hτ
  · obtain rfl := hτ0.symm
    set b : ℝ := if φ x = ⊤ then 0 else (φ x).toReal - 1
    have hb_lt : (b : EReal) < φ x := by
      dsimp [b]; split_ifs with hxt
      · simp [hxt]
      · conv_rhs => rw [← EReal.coe_toReal hxt (hbot x)]
        rw [EReal.coe_lt_coe_iff]; linarith
    obtain ⟨r, hr, hr_ball⟩ := Metric.mem_nhds_iff.1 ((hφ.isOpen_preimage b).mem_nhds hb_lt)
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (le_moreauYosida_iff.2 fun y _ ↦ ?_)
    by_cases hxy : edist x y = 0
    · have hd0 : dist y x = 0 := by rw [dist_comm, dist_edist, hxy, ENNReal.toReal_zero]
      simpa [hxy] using (hr_ball (by simpa [Metric.mem_ball, hd0] using hr)).le
    · rw [ENNReal.coe_zero, mul_zero, ENNReal.div_zero (pow_ne_zero 2 hxy), EReal.coe_ennreal_top,
        EReal.add_top_of_ne_bot (hbot y)]
      exact le_top
  rcases Set.eq_empty_or_nonempty {z : X | φ z ≠ ⊤} with hemp | ⟨z, hz⟩
  · have hall (y : X) : φ y = ⊤ := by by_contra hne; exact Set.notMem_empty y (hemp ▸ hne)
    exact ne_bot_of_le_ne_bot top_ne_bot (le_moreauYosida_iff.2 fun v _ ↦ by simp [hall v])
  set ez := (φ z).toReal
  have hez : φ z = ez := (EReal.coe_toReal hz (hbot z)).symm
  have hez_lt : ((ez - 1 : ℝ) : EReal) < φ z := by rw [hez, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨r, hr, hr_ball⟩ := Metric.mem_nhds_iff.1
    ((hφ.isOpen_preimage ((ez - 1 : ℝ) : EReal)).mem_nhds hez_lt)
  obtain ⟨B, hB⟩ := exists_le_apply_add_dist_sq_div_of_convexAlong hbot hconv hτ hmτ hez hr
    (fun w hw ↦ (hr_ball hw).le) x
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot B) (le_moreauYosida_iff.2 fun v _ ↦ by
    simpa only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] using hB v)

/-- **Coercivity from curve convexity of the energy and of the squared distance.** If `φ` is lower
semicontinuous, never takes the value `⊥`, and any two points `v₀`, `v₁` of `{z | φ z ≠ ⊤}` are
joined by a curve `γ` along which `φ` is `m`-convex and `z ↦ d(z, v₀)²` is `2`-convex, then
`φ_τ(x) > -∞` for every `x` and every `τ` with `1 + m τ > 0`. -/
theorem moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq (hφ : LowerSemicontinuous φ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z v₀ ^ 2 : ℝ) : EReal)) γ)
    (hmτ : 0 < 1 + m * τ) (x : X) : moreauYosida φ τ x ≠ ⊥ :=
  moreauYosida_ne_bot_of_convexAlong hφ hbot
    (fun _ _ h₀ h₁ ↦
      let ⟨γ, hγ0, hγ1, hφγ, hdγ⟩ := hconv h₀ h₁
      ⟨γ, hγ0, hγ1, fun _ ht ↦ hγ0 ▸ hγ1 ▸ (hγ0.symm ▸ hdγ).dist_le_mul ht, hφγ⟩)
    hmτ x

/-- **Coercivity of geodesically convex energies** (Ambrosio–Gigli–Savaré, Lemma 2.4.8). If `φ` is
lower semicontinuous, never takes the value `⊥`, and is `m`-geodesically convex, then `φ_τ(x) > -∞`
for every `x` and every `τ` with `1 + m τ > 0`. -/
theorem GeodesicallyConvex.moreauYosida_ne_bot (h : GeodesicallyConvex m φ)
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) (hmτ : 0 < 1 + m * τ) (x : X) :
    moreauYosida φ τ x ≠ ⊥ :=
  moreauYosida_ne_bot_of_convexAlong hφ hbot
    (fun _ _ h₀ h₁ ↦
      let ⟨γ, hγ, hc⟩ := geodesicallyConvex_def.1 h h₀ h₁
      ⟨γ, hγ.source, hγ.target, fun _ ht ↦ (hγ.dist_source_apply ht).le, hc⟩)
    hmτ x

/-- A minimizing sequence for the resolvent functional at `x` with geometric excess `(1 / 2) ^ n`
above `μ₀ = φ_τ(x)` is Cauchy whenever `φ` is penalized convex with `τ > 0` and `1 + m τ > 0`. -/
private theorem cauchySeq_of_penalizedConvex (h : PenalizedConvex m τ φ) (hτ : 0 < τ)
    (hmτ : 0 < 1 + m * τ) {μ₀ : ℝ} (hμ₀ : moreauYosida φ τ x = μ₀) {y : ℕ → X}
    (hy_top : ∀ n, φ (y n) ≠ ⊤) {p : ℕ → ℝ}
    (hp_eq : ∀ n, φ (y n) + ((dist x (y n) ^ 2 / (2 * τ) : ℝ) : EReal) = p n)
    (hp_lt : ∀ n, p n < μ₀ + (1 / 2 : ℝ) ^ n) :
    CauchySeq y := by
  set κ : ℝ := m + (τ : ℝ)⁻¹
  have hκ : 0 < κ := by
    have : κ = (1 + m * τ) / τ := by dsimp [κ]; field_simp; ring
    rw [this]; positivity
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hpow0 : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hpow0.eventually (gt_mem_nhds (by positivity : 0 < κ / 8 * ε ^ 2)))
  refine ⟨N, fun i hi j hj ↦ ?_⟩
  obtain ⟨γ, h0, h1, hγ⟩ := penalizedConvex_def.1 h (w := x) (hy_top i) (hy_top j)
  have hγ_ge : ((μ₀ : ℝ) : EReal) ≤
      φ (γ (1 / 2)) + ((dist x (γ (1 / 2)) ^ 2 / (2 * τ) : ℝ) : EReal) := by
    simpa only [hμ₀, coe_edist_sq_div_eq_coe_dist_sq_div hτ] using
      moreauYosida_le φ τ (edist_ne_top x (γ (1 / 2)))
  have hmid := hγ_ge.trans (convexAlong_def.1 hγ (1 / 2) ⟨by norm_num, by norm_num⟩)
  rw [h0, h1, hp_eq i, hp_eq j, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_sub, EReal.coe_le_coe_iff] at hmid
  have hmid' : κ / 8 * dist (y i) (y j) ^ 2 ≤ (p i - μ₀) / 2 + (p j - μ₀) / 2 := by
    dsimp [κ]; linarith
  have hlt_κ : κ / 8 * dist (y i) (y j) ^ 2 < κ / 8 * ε ^ 2 := by
    linarith [hmid', hN i hi, hN j hj, hp_lt i, hp_lt j]
  have hsq : dist (y i) (y j) ^ 2 < ε ^ 2 :=
    lt_of_mul_lt_mul_left hlt_κ (by positivity : 0 ≤ κ / 8)
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- **Existence of resolvent steps under penalized convexity** (Ambrosio–Gigli–Savaré, Lemma 4.1.1).
On a complete pseudometric space, if `φ` is lower semicontinuous, coercive at `x` (`φ_τ(x) > -∞`),
and penalized convex with `τ > 0` and `1 + m τ > 0`, then `J_τ x` is nonempty without any
compactness hypothesis on energy sublevels. -/
theorem PenalizedConvex.moreauYosidaResolvent_nonempty [CompleteSpace X]
    (h : PenalizedConvex m τ φ) (hφ : LowerSemicontinuous φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (hbot : moreauYosida φ τ x ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  rcases eq_or_ne (moreauYosida φ τ x) ⊤ with htop | htop
  · exact ⟨x, mem_moreauYosidaResolvent_iff_eq_moreauYosida.2
      ⟨edist_ne_top x x, le_antisymm (htop.symm ▸ le_top)
        (moreauYosida_le φ τ (edist_ne_top x x))⟩⟩
  set μ₀ := (moreauYosida φ τ x).toReal
  have hμ₀ : moreauYosida φ τ x = μ₀ := (EReal.coe_toReal htop hbot).symm
  have hex (n : ℕ) : ∃ y, φ y + ((dist x y ^ 2 / (2 * τ) : ℝ) : EReal) <
      ((μ₀ + (1 / 2 : ℝ) ^ n : ℝ) : EReal) := by
    have hlt : ⨅ y, φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) <
        ((μ₀ + (1 / 2 : ℝ) ^ n : ℝ) : EReal) := by
      rw [← moreauYosida_eq_iInf, hμ₀, EReal.coe_lt_coe_iff]
      exact lt_add_of_pos_right μ₀ (by positivity)
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hlt
    exact ⟨y, by simpa only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] using hy⟩
  choose y hy_lt using hex
  have hy_ge (n : ℕ) : ((μ₀ : ℝ) : EReal) ≤ φ (y n) + ((dist x (y n) ^ 2 / (2 * τ) : ℝ) : EReal) :=
    by simpa only [hμ₀, coe_edist_sq_div_eq_coe_dist_sq_div hτ] using
      moreauYosida_le φ τ (edist_ne_top x (y n))
  have hy_top (n : ℕ) : φ (y n) ≠ ⊤ := fun ht ↦ not_lt_of_ge (by simp [ht]) (hy_lt n)
  have hy_bot (n : ℕ) : φ (y n) ≠ ⊥ := fun hb ↦
    EReal.coe_ne_bot μ₀ (le_bot_iff.1 (by simpa [hb] using hy_ge n))
  set p : ℕ → ℝ := fun n ↦ (φ (y n)).toReal + dist x (y n) ^ 2 / (2 * τ)
  have hp_eq (n : ℕ) : φ (y n) + ((dist x (y n) ^ 2 / (2 * τ) : ℝ) : EReal) = p n := by
    rw [← EReal.coe_toReal (hy_top n) (hy_bot n), ← EReal.coe_add]
  have hp_bounds (n : ℕ) : μ₀ ≤ p n ∧ p n < μ₀ + (1 / 2 : ℝ) ^ n :=
    ⟨EReal.coe_le_coe_iff.1 (hp_eq n ▸ hy_ge n), EReal.coe_lt_coe_iff.1 (hp_eq n ▸ hy_lt n)⟩
  obtain ⟨y_lim, hy_lim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_penalizedConvex h hτ hmτ hμ₀ hy_top hp_eq fun n ↦ (hp_bounds n).2)
  refine ⟨y_lim, mem_moreauYosidaResolvent_iff_eq_moreauYosida.2 ⟨edist_ne_top x y_lim,
    le_antisymm ?_ (moreauYosida_le φ τ (edist_ne_top x y_lim))⟩⟩
  have hpow0 : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hp_lim : Tendsto p atTop (𝓝 μ₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hpow0.const_add μ₀) (fun n ↦ (hp_bounds n).1) (fun n ↦ (hp_bounds n).2.le)
  have htoReal_lim : Tendsto (fun n ↦ (φ (y n)).toReal) atTop
      (𝓝 (μ₀ - dist x y_lim ^ 2 / (2 * τ))) :=
    (hp_lim.sub (((tendsto_const_nhds.dist hy_lim).pow 2).div_const _)).congr fun n ↦ by
      dsimp [p]; ring
  have hφ_lim : Tendsto (fun n ↦ φ (y n)) atTop
      (𝓝 (((μ₀ - dist x y_lim ^ 2 / (2 * τ) : ℝ) : EReal))) :=
    (EReal.tendsto_coe.2 htoReal_lim).congr fun n ↦ EReal.coe_toReal (hy_top n) (hy_bot n)
  have hle_φ : φ y_lim ≤ ((μ₀ - dist x y_lim ^ 2 / (2 * τ) : ℝ) : EReal) :=
    ((hφ.le_liminf y_lim).trans hy_lim.liminf_le_liminf_comp).trans_eq hφ_lim.liminf_eq
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ, hμ₀]
  exact (add_le_add hle_φ le_rfl).trans_eq (by rw [← EReal.coe_add, sub_add_cancel])

/-- On a complete pseudometric space, under lower semicontinuity, coercivity at every point, and
`PenalizedConvex m τ φ` with `τ > 0` and `1 + m τ > 0`, from every initial point `x₀` starts an
infinite minimizing movement sequence `U` with `U 0 = x₀`. -/
theorem PenalizedConvex.exists_forall_mem_moreauYosidaResolvent [CompleteSpace X]
    (h : PenalizedConvex m τ φ) (hφ : LowerSemicontinuous φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (hbot : ∀ z, moreauYosida φ τ z ≠ ⊥) (x₀ : X) :
    ∃ U : ℕ → X, U 0 = x₀ ∧ ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n) := by
  choose step hstep_mem using fun z ↦ h.moreauYosidaResolvent_nonempty hφ hτ hmτ (hbot z)
  exact ⟨fun n ↦ step^[n] x₀, rfl, fun n ↦ by
    simpa only [Function.iterate_succ_apply'] using hstep_mem _⟩

/-- **Existence of resolvent steps under curve convexity of the energy and squared distance**
(Ambrosio–Gigli, Assumption 3.24). On a complete pseudometric space, if `φ` is lower semicontinuous,
never takes the value `⊥`, and satisfies Assumption 3.24 with parameter `m`, then `J_τ x` is
nonempty for every `x` and every `τ > 0` with `1 + m τ > 0`. -/
theorem moreauYosidaResolvent_nonempty_of_convexAlong_and_convexAlong_dist_sq [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    (moreauYosidaResolvent φ τ x).Nonempty :=
  (penalizedConvex_of_convexAlong_and_convexAlong_dist_sq hconv).moreauYosidaResolvent_nonempty
    hφ hτ hmτ (moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ x)

/-- Under lower semicontinuity, `∀ y, φ y ≠ ⊥`, and Assumption 3.24 with `τ > 0` and `1 + m τ > 0`
on a complete pseudometric space, from every initial point `x₀` starts an infinite minimizing
movement sequence `U` with `U 0 = x₀`. -/
theorem exists_forall_mem_moreauYosidaResolvent_of_convexAlong_and_convexAlong_dist_sq
    [CompleteSpace X] (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x₀ : X) :
    ∃ U : ℕ → X, U 0 = x₀ ∧ ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n) :=
  (penalizedConvex_of_convexAlong_and_convexAlong_dist_sq
    hconv).exists_forall_mem_moreauYosidaResolvent hφ hτ hmτ
    (moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ) x₀

/-- **Existence of resolvent steps on a complete CAT(0) space.** If `φ` is lower semicontinuous,
never takes the value `⊥`, and is `m`-geodesically convex on a complete CAT(0) space, then `J_τ x`
is nonempty for every `x` and every `τ > 0` with `1 + m τ > 0`. -/
theorem GeodesicallyConvex.moreauYosidaResolvent_nonempty [IsCATZeroSpace X] [CompleteSpace X]
    (h : GeodesicallyConvex m φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x : X) :
    (moreauYosidaResolvent φ τ x).Nonempty :=
  h.penalizedConvex.moreauYosidaResolvent_nonempty hφ hτ hmτ (h.moreauYosida_ne_bot hφ hbot hmτ x)

/-- On a complete CAT(0) space, if `φ` is lower semicontinuous, never takes the value `⊥`, and is
`m`-geodesically convex, then for every `τ > 0` with `1 + m τ > 0` and every `x₀` there exists an
infinite minimizing movement sequence `U` with `U 0 = x₀`. -/
theorem GeodesicallyConvex.exists_forall_mem_moreauYosidaResolvent [IsCATZeroSpace X]
    [CompleteSpace X] (h : GeodesicallyConvex m φ) (hφ : LowerSemicontinuous φ)
    (hbot : ∀ y, φ y ≠ ⊥) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (x₀ : X) :
    ∃ U : ℕ → X, U 0 = x₀ ∧ ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n) :=
  h.penalizedConvex.exists_forall_mem_moreauYosidaResolvent hφ hτ hmτ
    (h.moreauYosida_ne_bot hφ hbot hmτ) x₀

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

/-- **Existence and uniqueness of the resolvent step** (Ambrosio–Gigli–Savaré, Lemma 4.1.1). On a
complete metric space, if `φ` is lower semicontinuous, finite somewhere, coercive at `x`, and
penalized convex with `τ > 0` and `1 + m τ > 0`, then `J_τ x` consists of a unique point. -/
theorem PenalizedConvex.existsUnique_mem_moreauYosidaResolvent [CompleteSpace X]
    (h : PenalizedConvex m τ φ) (hφ : LowerSemicontinuous φ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (hbot : moreauYosida φ τ x ≠ ⊥) (hdom : ∃ z, φ z ≠ ⊤) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x := by
  obtain ⟨y, hy⟩ := h.moreauYosidaResolvent_nonempty hφ hτ hmτ hbot
  exact ⟨y, hy, fun y' hy' ↦ h.subsingleton_moreauYosidaResolvent hτ hmτ
    (fun z ↦ apply_ne_bot_of_moreauYosida_ne_bot hbot (edist_ne_top x z)) hdom x hy' hy⟩

/-- **Existence and uniqueness of the resolvent step under Assumption 3.24.** On a complete metric
space, if `φ` is lower semicontinuous, never takes the value `⊥`, is finite somewhere, and satisfies
Assumption 3.24 with parameter `m`, then `J_τ x` consists of a unique point for every `x` and every
`τ > 0` with `1 + m τ > 0`. -/
theorem existsUnique_mem_moreauYosidaResolvent_of_convexAlong_and_convexAlong_dist_sq
    [CompleteSpace X] (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong m φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (hdom : ∃ z, φ z ≠ ⊤) (x : X) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x :=
  (penalizedConvex_of_convexAlong_and_convexAlong_dist_sq
    hconv).existsUnique_mem_moreauYosidaResolvent hφ hτ hmτ
    (moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ x) hdom

/-- **Existence and uniqueness of the resolvent step on a complete CAT(0) space.** If `φ` is lower
semicontinuous, never takes the value `⊥`, is finite somewhere, and is `m`-geodesically convex on a
complete CAT(0) metric space, then `J_τ x` consists of a unique point for every `x` and every
`τ > 0` with `1 + m τ > 0`. -/
theorem GeodesicallyConvex.existsUnique_mem_moreauYosidaResolvent [IsCATZeroSpace X]
    [CompleteSpace X] (h : GeodesicallyConvex m φ) (hφ : LowerSemicontinuous φ)
    (hbot : ∀ y, φ y ≠ ⊥) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (hdom : ∃ z, φ z ≠ ⊤) (x : X) :
    ∃! y, y ∈ moreauYosidaResolvent φ τ x :=
  h.penalizedConvex.existsUnique_mem_moreauYosidaResolvent hφ hτ hmτ
    (h.moreauYosida_ne_bot hφ hbot hmτ x) hdom

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

end TauCeti
