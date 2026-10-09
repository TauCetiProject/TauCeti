/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.GradientFlow.Slope

/-!
# The Moreau–Yosida approximation and the resolvent of an energy

For an energy `φ : X → EReal` on an extended metric space and a time step `τ ≥ 0`, the
*Moreau–Yosida approximation* of `φ` is

`φ_τ(x) = inf_y (φ y + d(x, y)² / (2τ))`,

and the *resolvent* `J_τ x` is the set of points `y` at which this infimum is attained. A point of
`J_τ x` is one step of the implicit Euler scheme for the gradient flow of `φ` started at `x`, and
iterating resolvent steps gives the *minimizing movement* scheme of De Giorgi. The estimates proved
here are the discrete counterparts of the energy-dissipation inequality on which the convergence of
that scheme rests.

The squared-distance penalty `d(x, y)² / (2τ)` is computed in `ℝ≥0∞`, so it is `∞` at every point at
infinite distance from `x`: the infimum only sees the finite-distance component of `x`. Accordingly
a resolvent step of finite energy stays at finite distance from its starting point
(`TauCeti.edist_ne_top_of_mem_moreauYosidaResolvent`). Ambrosio–Gigli–Savaré take energies with
values in `(-∞, ∞]`; here `φ` may take the value `⊥`, and the results assume `φ ≠ ⊥` at the points
where they need it.

## Main definitions

* `TauCeti.moreauYosida φ τ x`: the Moreau–Yosida approximation `φ_τ(x)`.
* `TauCeti.moreauYosidaResolvent φ τ x`: the resolvent `J_τ x`, the set of minimizers of
  `y ↦ φ y + d(x, y)² / (2τ)`.

## Main results

* `TauCeti.apply_add_le_of_mem_moreauYosidaResolvent`: the one-step energy estimate
  `φ y + d(x, y)² / (2τ) ≤ φ x` for `y ∈ J_τ x`.
* `TauCeti.edist_ne_top_of_mem_moreauYosidaResolvent`: a resolvent step of finite energy has
  finite length.
* `TauCeti.edist_le_edist_of_mem_moreauYosidaResolvent` and
  `TauCeti.apply_le_apply_of_mem_moreauYosidaResolvent`: for `τ < σ`, a resolvent step of time `σ`
  goes at least as far as one of time `τ`, and reaches energy at most as large.
* `TauCeti.descendingSlope_le_of_mem_moreauYosidaResolvent`: the slope estimate
  `|∂φ|(y) ≤ d(x, y) / τ` for `y ∈ J_τ x`.
* `TauCeti.apply_add_sum_le_of_forall_mem_moreauYosidaResolvent`: the discrete energy estimate
  `φ (u N) + ∑_{n < N} d(u n, u (n + 1))² / (2τ) ≤ φ (u 0)` along a minimizing movement sequence.
* `TauCeti.moreauYosidaResolvent_half_norm_sq` and `TauCeti.moreauYosida_half_norm_sq`: on a real
  inner product space, the resolvent of `‖·‖² / 2` is `x ↦ x / (1 + τ)` and its Moreau–Yosida
  approximation is `‖x‖² / (2 (1 + τ))`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2 and Chapter 3, Section 3.1.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {φ ψ : X → EReal} {τ σ : ℝ≥0} {x y : X}

/-- The *Moreau–Yosida approximation* `φ_τ(x) = inf_y (φ y + d(x, y)² / (2τ))` of an energy `φ`
with time step `τ`. The penalty is computed in `ℝ≥0∞`, so points at infinite distance from `x` do
not contribute. -/
def moreauYosida (φ : X → EReal) (τ : ℝ≥0) (x : X) : EReal :=
  ⨅ y, φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞)

/-- The defining formula of the Moreau–Yosida approximation, as an infimum. -/
theorem moreauYosida_def (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x = ⨅ y, φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  (rfl)

/-- The Moreau–Yosida approximation at `x` is at most the penalized energy at any point `y`. -/
theorem moreauYosida_le (φ : X → EReal) (τ : ℝ≥0) (x y : X) :
    moreauYosida φ τ x ≤ φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  iInf_le (fun y ↦ φ y + ((edist x y ^ 2 / (2 * τ) : ℝ≥0∞) : EReal)) y

/-- A lower bound for the Moreau–Yosida approximation is a lower bound for the penalized energy
at every point. -/
theorem le_moreauYosida_iff {c : EReal} :
    c ≤ moreauYosida φ τ x ↔ ∀ y, c ≤ φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  le_iInf_iff

/-- The Moreau–Yosida approximation lies below the energy. -/
theorem moreauYosida_le_self (φ : X → EReal) (τ : ℝ≥0) (x : X) : moreauYosida φ τ x ≤ φ x := by
  simpa using moreauYosida_le φ τ x x

/-- The Moreau–Yosida approximation is monotone in the energy. -/
theorem moreauYosida_mono (h : φ ≤ ψ) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x ≤ moreauYosida ψ τ x :=
  iInf_mono fun y ↦ add_le_add_left (h y) _

/-- The Moreau–Yosida approximation decreases as the time step grows. -/
theorem antitone_moreauYosida (φ : X → EReal) (x : X) : Antitone (moreauYosida φ · x) :=
  fun _ _ h ↦ iInf_mono fun _ ↦ add_le_add_right (EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
    ENNReal.div_le_div_left (mul_le_mul_right (ENNReal.coe_le_coe.2 h) _) _) _

/-- The *resolvent* `J_τ x` of an energy `φ`: the set of points `y` minimizing
`y ↦ φ y + d(x, y)² / (2τ)`, that is, attaining the Moreau–Yosida approximation `φ_τ(x)`
(`TauCeti.mem_moreauYosidaResolvent_iff_eq_moreauYosida`). It may be empty or contain several
points. -/
def moreauYosidaResolvent (φ : X → EReal) (τ : ℝ≥0) (x : X) : Set X :=
  {y | ∀ z, φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ z + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞)}

/-- The defining property of the resolvent: `y` minimizes the penalized energy. -/
theorem mem_moreauYosidaResolvent_iff :
    y ∈ moreauYosidaResolvent φ τ x ↔
      ∀ z, φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ z + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞) :=
  Iff.rfl

/-- A point lies in the resolvent exactly when it attains the Moreau–Yosida approximation. -/
theorem mem_moreauYosidaResolvent_iff_eq_moreauYosida :
    y ∈ moreauYosidaResolvent φ τ x ↔
      φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) = moreauYosida φ τ x :=
  ⟨fun h ↦ le_antisymm (le_iInf h) (moreauYosida_le φ τ x y),
    fun h z ↦ h.le.trans (moreauYosida_le φ τ x z)⟩

/-- **One-step energy estimate.** A resolvent step `y ∈ J_τ x` lowers the energy by at least the
penalty `d(x, y)² / (2τ)`. -/
theorem apply_add_le_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x) :
    φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ x := by
  simpa using hy x

/-- A resolvent step does not increase the energy. -/
theorem apply_le_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x) :
    φ y ≤ φ x :=
  (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)).trans
    (apply_add_le_of_mem_moreauYosidaResolvent hy)

/-- A resolvent step from a point where the Moreau–Yosida approximation is finite has finite
energy. -/
theorem apply_ne_top_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x)
    (hx : moreauYosida φ τ x ≠ ⊤) : φ y ≠ ⊤ := by
  rintro h
  rw [← mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hy, h, EReal.top_add_of_ne_bot
    (EReal.coe_ennreal_ne_bot _)] at hx
  exact hx rfl

/-- **Resolvent steps stay in the finite-distance component.** A resolvent step `y ∈ J_τ x` from a
point where the Moreau–Yosida approximation is finite, to a point where `φ y ≠ ⊥`, has finite
length. -/
theorem edist_ne_top_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x)
    (hφy : φ y ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) : edist x y ≠ ⊤ := by
  rintro h
  rw [← mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hy, h, ENNReal.top_pow two_ne_zero,
    ENNReal.top_div_of_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top),
    EReal.coe_ennreal_top, EReal.add_top_of_ne_bot hφy] at hx
  exact hx rfl

/-- For a finite step, the penalty `d(x, y)² / (2τ)` is the real number
`(d(x, y).toReal)² / (2τ)`. -/
private theorem coe_edist_sq_div_eq (hτ : 0 < τ) (h : edist x y ≠ ⊤) :
    ((edist x y ^ 2 / (2 * τ) : ℝ≥0∞) : EReal) =
      (((edist x y).toReal ^ 2 / (2 * τ) : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal (ENNReal.div_ne_top (ENNReal.pow_ne_top h)
    (mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.2 hτ.ne')))]
  simp [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul]

/-- The real-number core of the monotonicity of resolvent steps in the time step: comparing the
two minimality inequalities for time steps `τ < σ`. -/
private theorem sq_le_sq_and_le_of_add_div_le {τ σ a₀ a₁ d₀ d₁ : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    (h₀ : a₀ + d₀ ^ 2 / (2 * τ) ≤ a₁ + d₁ ^ 2 / (2 * τ))
    (h₁ : a₁ + d₁ ^ 2 / (2 * σ) ≤ a₀ + d₀ ^ 2 / (2 * σ)) : d₀ ^ 2 ≤ d₁ ^ 2 ∧ a₁ ≤ a₀ := by
  have hk : 0 < 1 / (2 * τ) - 1 / (2 * σ) :=
    sub_pos.2 (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  have e : ∀ d : ℝ, d ^ 2 / (2 * τ) - d ^ 2 / (2 * σ) = d ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) :=
    fun d ↦ by ring
  have hd : d₀ ^ 2 ≤ d₁ ^ 2 :=
    le_of_mul_le_mul_right (by linarith [e d₀, e d₁]) hk
  refine ⟨hd, ?_⟩
  have : d₀ ^ 2 / (2 * σ) ≤ d₁ ^ 2 / (2 * σ) := div_le_div_of_nonneg_right hd (by linarith)
  linarith

/-- The energies and squared lengths of two resolvent steps from `x`, with time steps `0 < τ < σ`,
satisfy `d(x, y₀) ≤ d(x, y₁)` and `φ y₁ ≤ φ y₀`. -/
private theorem edist_le_edist_and_apply_le_apply (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x)
    (hφy₀ : φ y ≠ ⊥) (hφy₁ : φ y₁ ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    edist x y ≤ edist x y₁ ∧ φ y₁ ≤ φ y := by
  have hσ : 0 < σ := hτ.trans hτσ
  have hx₁ : moreauYosida φ σ x ≠ ⊤ :=
    ne_top_of_le_ne_top hx (antitone_moreauYosida φ x hτσ.le)
  have hd₀ := edist_ne_top_of_mem_moreauYosidaResolvent hy₀ hφy₀ hx
  have hd₁ := edist_ne_top_of_mem_moreauYosidaResolvent hy₁ hφy₁ hx₁
  obtain ⟨a₀, ha₀⟩ : ∃ a : ℝ, φ y = a :=
    ⟨_, (EReal.coe_toReal (apply_ne_top_of_mem_moreauYosidaResolvent hy₀ hx) hφy₀).symm⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, φ y₁ = a :=
    ⟨_, (EReal.coe_toReal (apply_ne_top_of_mem_moreauYosidaResolvent hy₁ hx₁) hφy₁).symm⟩
  have h₀ := hy₀ y₁
  have h₁ := hy₁ y
  rw [ha₀, ha₁, coe_edist_sq_div_eq hτ hd₀, coe_edist_sq_div_eq hτ hd₁, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h₀
  rw [ha₀, ha₁, coe_edist_sq_div_eq hσ hd₀, coe_edist_sq_div_eq hσ hd₁, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h₁
  obtain ⟨hd, ha⟩ := sq_le_sq_and_le_of_add_div_le (NNReal.coe_pos.2 hτ)
    (NNReal.coe_lt_coe.2 hτσ) h₀ h₁
  refine ⟨(ENNReal.toReal_le_toReal hd₀ hd₁).1 ?_, by rw [ha₀, ha₁]; exact_mod_cast ha⟩
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero).1 hd

/-- **Monotonicity of resolvent steps in the time step.** For time steps `0 < τ < σ`, a resolvent
step of time `σ` from `x` goes at least as far as a resolvent step of time `τ`, provided the
Moreau–Yosida approximation `φ_τ(x)` is finite and both steps reach points where `φ ≠ ⊥`. -/
theorem edist_le_edist_of_mem_moreauYosidaResolvent (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x)
    (hφy₀ : φ y ≠ ⊥) (hφy₁ : φ y₁ ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    edist x y ≤ edist x y₁ :=
  (edist_le_edist_and_apply_le_apply hτ hτσ hy₀ hy₁ hφy₀ hφy₁ hx).1

/-- **Monotonicity of resolvent steps in the time step.** For time steps `0 < τ < σ`, a resolvent
step of time `σ` from `x` reaches energy at most that of a resolvent step of time `τ`, provided the
Moreau–Yosida approximation `φ_τ(x)` is finite and both steps reach points where `φ ≠ ⊥`. -/
theorem apply_le_apply_of_mem_moreauYosidaResolvent (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x)
    (hφy₀ : φ y ≠ ⊥) (hφy₁ : φ y₁ ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    φ y₁ ≤ φ y :=
  (edist_le_edist_and_apply_le_apply hτ hτσ hy₀ hy₁ hφy₀ hφy₁ hx).2

/-- **Discrete energy estimate.** Along a minimizing movement sequence, in which each `u (n + 1)`
is a resolvent step from `u n`, the energy at time `N` plus the accumulated penalties
`∑_{n < N} d(u n, u (n + 1))² / (2τ)` is at most the initial energy. -/
theorem apply_add_sum_le_of_forall_mem_moreauYosidaResolvent {u : ℕ → X}
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (N : ℕ) :
    φ (u N) + (∑ n ∈ Finset.range N, edist (u n) (u (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) ≤
      φ (u 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc φ (u (N + 1)) + ((∑ n ∈ Finset.range (N + 1),
            edist (u n) (u (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) : EReal)
        = φ (u (N + 1)) + (edist (u N) (u (N + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) +
            (∑ n ∈ Finset.range N, edist (u n) (u (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) := by
          rw [Finset.sum_range_succ, EReal.coe_ennreal_add]
          ac_rfl
      _ ≤ φ (u N) + (∑ n ∈ Finset.range N, edist (u n) (u (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) :=
          add_le_add_left (apply_add_le_of_mem_moreauYosidaResolvent (hu N)) _
      _ ≤ φ (u 0) := ih

/-- Along a minimizing movement sequence the energy is nonincreasing. -/
theorem antitone_comp_of_forall_mem_moreauYosidaResolvent {u : ℕ → X}
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) : Antitone (φ ∘ u) :=
  antitone_nat_of_succ_le fun n ↦ (apply_le_of_mem_moreauYosidaResolvent (hu n) :)

end PseudoEMetricSpace

section EMetricSpace

/-- The real-number core of the slope estimate. With `d = d(x, y)`, `e = d(x, z)` and
`r = d(y, z) < 2τε`, minimality of `y` gives
`2τ (a - b) ≤ e² - d² ≤ (d + r)² - d² = 2dr + r² ≤ 2dr + 2τεr`. -/
private theorem sub_le_mul_of_add_sq_div_le {τ ε a b d e r : ℝ} (hτ : 0 < τ) (hr₀ : 0 ≤ r)
    (hr : r < 2 * τ * ε) (he₀ : 0 ≤ e) (he : e ≤ d + r)
    (h : a + d ^ 2 / (2 * τ) ≤ b + e ^ 2 / (2 * τ)) : a - b ≤ (d / τ + ε) * r := by
  have h₁ : a - b ≤ ((d + r) ^ 2 - d ^ 2) / (2 * τ) := by
    have : (e ^ 2 - d ^ 2) / (2 * τ) ≤ ((d + r) ^ 2 - d ^ 2) / (2 * τ) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    rw [sub_div] at this
    linarith
  refine h₁.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have e : (d / τ + ε) * r * (2 * τ) = 2 * d * r + 2 * τ * ε * r := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hr.le hr₀]

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {τ : ℝ≥0} {x y : X}

/-- **Slope estimate for resolvent steps.** If `y ∈ J_τ x` is a resolvent step with time step
`τ > 0` from a point where the Moreau–Yosida approximation is finite, and `φ y ≠ ⊥`, then the
descending slope of `φ` at `y` is at most `d(x, y) / τ`. -/
theorem descendingSlope_le_of_mem_moreauYosidaResolvent (hτ : 0 < τ)
    (hy : y ∈ moreauYosidaResolvent φ τ x) (hφy : φ y ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    descendingSlope φ y ≤ edist x y / τ := by
  have hd := edist_ne_top_of_mem_moreauYosidaResolvent hy hφy hx
  obtain ⟨a, ha⟩ : ∃ a : ℝ, φ y = a :=
    ⟨_, (EReal.coe_toReal (apply_ne_top_of_mem_moreauYosidaResolvent hy hx) hφy).symm⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ descendingSlope_le_of_eventually_le ?_
  have hδ : (0 : ℝ) < 2 * τ * ε := by have := NNReal.coe_pos.2 hτ; positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.eball_mem_nhds y (ENNReal.ofReal_pos.2 hδ))]
    with z hz
  rw [Metric.mem_eball, edist_comm] at hz
  have hyz := hy z
  rw [ha] at hyz ⊢
  -- If `φ z = ⊤` there is no decrease; `φ z = ⊥` contradicts minimality of `y`.
  by_cases htop : φ z = ⊤
  · simp [htop]
  have hbot : φ z ≠ ⊥ := by
    rintro hbot
    rw [hbot, EReal.bot_add] at hyz
    exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot a, EReal.coe_ennreal_ne_bot _⟩
      (le_bot_iff.1 hyz)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, φ z = b := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
  have hyz' : edist y z ≠ ⊤ := (hz.trans ENNReal.ofReal_lt_top).ne
  have hxz : edist x z ≤ edist x y + edist y z := edist_triangle x y z
  have hxz' : edist x z ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hd, hyz'⟩) hxz
  rw [hb, coe_edist_sq_div_eq hτ hd, coe_edist_sq_div_eq hτ hxz', ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hyz
  rw [hb, ← EReal.coe_sub, EReal.real_coe_toENNReal,
    ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.div_ne_top hd (ENNReal.coe_ne_zero.2 hτ.ne'), ENNReal.coe_ne_top⟩) hyz'),
    ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.div_ne_top hd (ENNReal.coe_ne_zero.2 hτ.ne'))
      ENNReal.coe_ne_top, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal]
  exact sub_le_mul_of_add_sq_div_le (NNReal.coe_pos.2 hτ) ENNReal.toReal_nonneg
    (ENNReal.toReal_lt_of_lt_ofReal hz) ENNReal.toReal_nonneg
    (ENNReal.toReal_le_add hxz hd hyz') hyz

end EMetricSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {τ : ℝ≥0}

/-- Completing the square: `‖y‖² / 2 + ‖x - y‖² / (2τ)` is its minimum value
`‖x‖² / (2 (1 + τ))` plus `(1 + τ) / (2τ)` times the squared distance from `y` to the minimizer
`x / (1 + τ)`. -/
private theorem half_norm_sq_add_norm_sub_sq_div {τ : ℝ} (hτ : 0 < τ) (x y : E) :
    ‖y‖ ^ 2 / 2 + ‖x - y‖ ^ 2 / (2 * τ) =
      ‖x‖ ^ 2 / (2 * (1 + τ)) + (1 + τ) / (2 * τ) * ‖y - (1 + τ)⁻¹ • x‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_right, real_inner_comm x y,
    Real.norm_of_nonneg (by positivity)]
  field_simp
  ring

/-- The objective `φ y + d(x, y)² / (2τ)` for `φ = ‖·‖² / 2`, as a real number. -/
private theorem half_norm_sq_add_edist_sq_div (hτ : 0 < τ) (x y : E) :
    ((‖y‖ ^ 2 / 2 : ℝ) : EReal) + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) =
      ((‖x‖ ^ 2 / (2 * (1 + τ)) + (1 + τ) / (2 * τ) * ‖y - (1 + (τ : ℝ))⁻¹ • x‖ ^ 2 : ℝ) :
        EReal) := by
  rw [coe_edist_sq_div_eq hτ (edist_ne_top x y), ← dist_edist, dist_eq_norm, ← EReal.coe_add,
    half_norm_sq_add_norm_sub_sq_div (NNReal.coe_pos.2 hτ)]

/-- On a real inner product space, the resolvent of the energy `‖·‖² / 2` with time step `τ > 0`
is the single point `x / (1 + τ)`. -/
theorem moreauYosidaResolvent_half_norm_sq (hτ : 0 < τ) (x : E) :
    moreauYosidaResolvent (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x = {(1 + (τ : ℝ))⁻¹ • x} := by
  have hk : 0 < (1 + (τ : ℝ)) / (2 * τ) := by have := NNReal.coe_pos.2 hτ; positivity
  ext y
  simp only [mem_moreauYosidaResolvent_iff, half_norm_sq_add_edist_sq_div hτ,
    EReal.coe_le_coe_iff, mem_singleton_iff]
  refine ⟨fun h ↦ ?_, fun h z ↦ ?_⟩
  · have := h ((1 + (τ : ℝ))⁻¹ • x)
    rw [sub_self, norm_zero] at this
    have : ‖y - (1 + (τ : ℝ))⁻¹ • x‖ ^ 2 ≤ 0 := by nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm this (sq_nonneg _))))
  · rw [h, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖z - (1 + (τ : ℝ))⁻¹ • x‖]

/-- On a real inner product space, the Moreau–Yosida approximation of the energy `‖·‖² / 2` with
time step `τ > 0` is `‖x‖² / (2 (1 + τ))`. -/
theorem moreauYosida_half_norm_sq (hτ : 0 < τ) (x : E) :
    moreauYosida (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x =
      ((‖x‖ ^ 2 / (2 * (1 + τ)) : ℝ) : EReal) := by
  have hmem : (1 + (τ : ℝ))⁻¹ • x ∈
      moreauYosidaResolvent (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x := by
    rw [moreauYosidaResolvent_half_norm_sq hτ]
    exact mem_singleton _
  rw [← mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hmem, half_norm_sq_add_edist_sq_div hτ,
    sub_self, norm_zero]
  simp

end InnerProductSpace

end TauCeti
