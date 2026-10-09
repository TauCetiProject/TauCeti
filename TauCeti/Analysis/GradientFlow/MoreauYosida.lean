/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.GradientFlow.Slope
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Data.EReal.Operations

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

The infimum and the minimization run only over the points at finite distance from `x`, so both
depend only on the finite-distance component of `x`, and a resolvent step stays at finite distance
from its starting point (`TauCeti.edist_ne_top_of_mem_moreauYosidaResolvent`). Ambrosio–Gigli–Savaré
take energies with values in `(-∞, ∞]`; here `φ` may take the value `⊥`, and the results assume
`φ ≠ ⊥` at the points where they need it.

## Main definitions

* `TauCeti.moreauYosida φ τ x`: the Moreau–Yosida approximation `φ_τ(x)`.
* `TauCeti.moreauYosidaResolvent φ τ x`: the resolvent `J_τ x`, the set of minimizers of
  `y ↦ φ y + d(x, y)² / (2τ)` over the points at finite distance from `x`.

## Main results

* `TauCeti.apply_add_le_of_mem_moreauYosidaResolvent`: the one-step energy estimate
  `φ y + d(x, y)² / (2τ) ≤ φ x` for `y ∈ J_τ x`.
* `TauCeti.edist_ne_top_of_mem_moreauYosidaResolvent`: a resolvent step has finite length.
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
with time step `τ`. The infimum runs over the points `y` at finite distance from `x`, so points
at infinite distance from `x` do not contribute, even where `φ y = ⊥`. -/
def moreauYosida (φ : X → EReal) (τ : ℝ≥0) (x : X) : EReal :=
  ⨅ (y) (_ : edist x y ≠ ⊤), φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞)

/-- The defining formula of the Moreau–Yosida approximation, as an infimum. -/
theorem moreauYosida_def (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x = ⨅ (y) (_ : edist x y ≠ ⊤), φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  (rfl)

/-- The Moreau–Yosida approximation at `x` is at most the penalized energy at any point `y` at
finite distance from `x`. -/
theorem moreauYosida_le (φ : X → EReal) (τ : ℝ≥0) {x y : X} (h : edist x y ≠ ⊤) :
    moreauYosida φ τ x ≤ φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  iInf₂_le (f := fun y (_ : edist x y ≠ ⊤) ↦ φ y + ((edist x y ^ 2 / (2 * τ) : ℝ≥0∞) : EReal)) y h

/-- A lower bound for the Moreau–Yosida approximation is a lower bound for the penalized energy
at every point at finite distance from `x`. -/
theorem le_moreauYosida_iff {c : EReal} :
    c ≤ moreauYosida φ τ x ↔
      ∀ y, edist x y ≠ ⊤ → c ≤ φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) :=
  le_iInf₂_iff

/-- The Moreau–Yosida approximation lies below the energy. -/
theorem moreauYosida_le_self (φ : X → EReal) (τ : ℝ≥0) (x : X) : moreauYosida φ τ x ≤ φ x := by
  simpa using moreauYosida_le φ τ (x := x) (y := x) (by simp)

/-- The Moreau–Yosida approximation is monotone in the energy. -/
theorem moreauYosida_mono (h : φ ≤ ψ) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x ≤ moreauYosida ψ τ x :=
  iInf₂_mono fun y _ ↦ add_le_add_left (h y) _

/-- The Moreau–Yosida approximation decreases as the time step grows. -/
theorem antitone_moreauYosida (φ : X → EReal) (x : X) : Antitone (moreauYosida φ · x) :=
  fun _ _ h ↦ iInf₂_mono fun _ _ ↦ add_le_add_right (EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
    ENNReal.div_le_div_left (mul_le_mul_right (ENNReal.coe_le_coe.2 h) _) _) _

/-- The *resolvent* `J_τ x` of an energy `φ`: the set of points `y` at finite distance from `x`
minimizing `y ↦ φ y + d(x, y)² / (2τ)` among the points at finite distance from `x`, that is,
attaining the Moreau–Yosida approximation `φ_τ(x)`
(`TauCeti.mem_moreauYosidaResolvent_iff_eq_moreauYosida`). It may be empty or contain several
points. -/
def moreauYosidaResolvent (φ : X → EReal) (τ : ℝ≥0) (x : X) : Set X :=
  {y | edist x y ≠ ⊤ ∧ ∀ z, edist x z ≠ ⊤ →
    φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ z + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞)}

/-- The defining property of the resolvent: `y` is at finite distance from `x` and minimizes the
penalized energy among the points at finite distance from `x`. -/
theorem mem_moreauYosidaResolvent_iff :
    y ∈ moreauYosidaResolvent φ τ x ↔ edist x y ≠ ⊤ ∧ ∀ z, edist x z ≠ ⊤ →
      φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ z + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞) :=
  Iff.rfl

/-- A point lies in the resolvent exactly when it is at finite distance from `x` and attains the
Moreau–Yosida approximation. -/
theorem mem_moreauYosidaResolvent_iff_eq_moreauYosida :
    y ∈ moreauYosidaResolvent φ τ x ↔
      edist x y ≠ ⊤ ∧ φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) = moreauYosida φ τ x :=
  ⟨fun h ↦ ⟨h.1, le_antisymm (le_iInf₂ h.2) (moreauYosida_le φ τ h.1)⟩,
    fun h ↦ ⟨h.1, fun _ hz ↦ h.2.le.trans (moreauYosida_le φ τ hz)⟩⟩

/-- **One-step energy estimate.** A resolvent step `y ∈ J_τ x` lowers the energy by at least the
penalty `d(x, y)² / (2τ)`. -/
theorem apply_add_le_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x) :
    φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ φ x := by
  simpa using hy.2 x (by simp)

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
  rw [← (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hy).2, h, EReal.top_add_of_ne_bot
    (EReal.coe_ennreal_ne_bot _)] at hx
  exact hx rfl

/-- **Resolvent steps stay in the finite-distance component.** A resolvent step `y ∈ J_τ x` has
finite length. -/
theorem edist_ne_top_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x) :
    edist x y ≠ ⊤ :=
  hy.1

/-- A resolvent step `y ∈ J_τ x` with `φ y ≠ ⊥` forces `φ ≠ ⊥` at every point at finite distance
from `x`: otherwise that point would have penalized energy `⊥`, below that of `y`. -/
theorem apply_ne_bot_of_mem_moreauYosidaResolvent (hy : y ∈ moreauYosidaResolvent φ τ x)
    (hφy : φ y ≠ ⊥) {z : X} (hz : edist x z ≠ ⊤) : φ z ≠ ⊥ := by
  intro h
  have := hy.2 z hz
  rw [h, EReal.bot_add, le_bot_iff, EReal.add_eq_bot_iff] at this
  exact this.elim hφy (EReal.coe_ennreal_ne_bot _)

/-- For real energies `a`, `b` and points `y`, `z` at finite distance from `x`, a comparison
`a + d(x, y)² / (2τ) ≤ b + d(x, z)² / (2τ)` of penalized energies is a real inequality. -/
private theorem add_toReal_sq_div_le_of_coe_add_le (hτ : 0 < τ) {z : X} (hy : edist x y ≠ ⊤)
    (hz : edist x z ≠ ⊤) {a b : ℝ}
    (h : (a : EReal) + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤ b + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞)) :
    a + (edist x y).toReal ^ 2 / (2 * τ) ≤ b + (edist x z).toReal ^ 2 / (2 * τ) := by
  rw [EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff (by finiteness) (by finiteness)] at h
  simpa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul] using h

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

/-- The distances and energies of two resolvent steps from `x`, with time steps `0 < τ < σ`,
satisfy `d(x, y₀) ≤ d(x, y₁)` and `φ y₁ ≤ φ y₀`, provided the energy `φ y₀` is real. -/
private theorem edist_le_edist_and_apply_le_apply (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x)
    (hφy₀ : φ y ≠ ⊥) (hφy₀' : φ y ≠ ⊤) :
    edist x y ≤ edist x y₁ ∧ φ y₁ ≤ φ y := by
  have hσ : 0 < σ := hτ.trans hτσ
  have hd₀ := edist_ne_top_of_mem_moreauYosidaResolvent hy₀
  have hd₁ := edist_ne_top_of_mem_moreauYosidaResolvent hy₁
  have hφy₁ := apply_ne_bot_of_mem_moreauYosidaResolvent hy₀ hφy₀ hd₁
  have h₀ := hy₀.2 y₁ hd₁
  have h₁ := hy₁.2 y hd₀
  obtain ⟨a₀, ha₀⟩ : ∃ a : ℝ, φ y = a := ⟨_, (EReal.coe_toReal hφy₀' hφy₀).symm⟩
  rw [ha₀] at h₀ h₁ ⊢
  -- `φ y₁ = ⊤` would make the left side of `h₁` infinite and its right side finite.
  have hφy₁' : φ y₁ ≠ ⊤ := by
    rintro h
    rw [h, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _), top_le_iff] at h₁
    exact (EReal.add_lt_top (EReal.coe_ne_top a₀)
      (EReal.coe_ennreal_eq_top_iff.not.2 (by finiteness))).ne h₁
  obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, φ y₁ = a := ⟨_, (EReal.coe_toReal hφy₁' hφy₁).symm⟩
  rw [ha₁] at h₀ h₁ ⊢
  obtain ⟨hd, ha⟩ := sq_le_sq_and_le_of_add_div_le (NNReal.coe_pos.2 hτ)
    (NNReal.coe_lt_coe.2 hτσ) (add_toReal_sq_div_le_of_coe_add_le hτ hd₀ hd₁ h₀)
    (add_toReal_sq_div_le_of_coe_add_le hσ hd₁ hd₀ h₁)
  refine ⟨(ENNReal.toReal_le_toReal hd₀ hd₁).1 ?_, EReal.coe_le_coe_iff.2 ha⟩
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero).1 hd

/-- **Monotonicity of resolvent steps in the time step.** For time steps `0 < τ < σ`, a resolvent
step of time `σ` from `x` goes at least as far as a resolvent step `y` of time `τ`, provided the
Moreau–Yosida approximation `φ_τ(x)` is finite and `φ y ≠ ⊥`. -/
theorem edist_le_edist_of_mem_moreauYosidaResolvent (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x)
    (hφy₀ : φ y ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    edist x y ≤ edist x y₁ :=
  (edist_le_edist_and_apply_le_apply hτ hτσ hy₀ hy₁ hφy₀
    (apply_ne_top_of_mem_moreauYosidaResolvent hy₀ hx)).1

/-- **Monotonicity of resolvent steps in the time step.** For time steps `0 < τ < σ`, a resolvent
step of time `σ` from `x` reaches energy at most that of a resolvent step of time `τ`. -/
theorem apply_le_apply_of_mem_moreauYosidaResolvent (hτ : 0 < τ) (hτσ : τ < σ)
    (hy₀ : y ∈ moreauYosidaResolvent φ τ x) {y₁ : X} (hy₁ : y₁ ∈ moreauYosidaResolvent φ σ x) :
    φ y₁ ≤ φ y := by
  -- If `φ y = ⊥`, then `φ y₁ = ⊥`: a step `y₁` with `φ y₁ ≠ ⊥` forces `φ y ≠ ⊥`.
  by_cases hbot : φ y = ⊥
  · by_contra h
    exact apply_ne_bot_of_mem_moreauYosidaResolvent hy₁ (fun h' ↦ h (h' ▸ bot_le))
      (edist_ne_top_of_mem_moreauYosidaResolvent hy₀) hbot
  by_cases htop : φ y = ⊤
  · exact htop ▸ le_top
  exact (edist_le_edist_and_apply_le_apply hτ hτσ hy₀ hy₁ hbot htop).2

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

/-- A real slope bound `c ≤ (d / τ + ε) r` with `d` finite gives the corresponding bound
`ofReal c ≤ (d / τ + ε) r` in `ℝ≥0∞`. -/
private theorem ofReal_le_div_add_mul {τ ε : ℝ≥0} (hτ : 0 < τ) {d r : ℝ≥0∞} (hd : d ≠ ⊤)
    {c : ℝ} (h : c ≤ (d.toReal / τ + ε) * r.toReal) :
    ENNReal.ofReal c ≤ (d / τ + ε) * r := by
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) ENNReal.coe_ne_top,
    ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal]

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {τ : ℝ≥0} {x y : X}

/-- **Slope estimate for resolvent steps.** If `y ∈ J_τ x` is a resolvent step with time step
`τ > 0` from a point where the Moreau–Yosida approximation is finite, and `φ y ≠ ⊥`, then the
descending slope of `φ` at `y` is at most `d(x, y) / τ`. -/
theorem descendingSlope_le_of_mem_moreauYosidaResolvent (hτ : 0 < τ)
    (hy : y ∈ moreauYosidaResolvent φ τ x) (hφy : φ y ≠ ⊥) (hx : moreauYosida φ τ x ≠ ⊤) :
    descendingSlope φ y ≤ edist x y / τ := by
  have hd := edist_ne_top_of_mem_moreauYosidaResolvent hy
  obtain ⟨a, ha⟩ : ∃ a : ℝ, φ y = a :=
    ⟨_, (EReal.coe_toReal (apply_ne_top_of_mem_moreauYosidaResolvent hy hx) hφy).symm⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ descendingSlope_le_of_eventually_le ?_
  have hδ : (0 : ℝ) < 2 * τ * ε := by have := NNReal.coe_pos.2 hτ; positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.eball_mem_nhds y (ENNReal.ofReal_pos.2 hδ))]
    with z hz
  rw [Metric.mem_eball, edist_comm] at hz
  have hyz' : edist y z ≠ ⊤ := (hz.trans ENNReal.ofReal_lt_top).ne
  have hxz : edist x z ≤ edist x y + edist y z := edist_triangle x y z
  have hxz' : edist x z ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hd, hyz'⟩) hxz
  have hyz := hy.2 z hxz'
  rw [ha] at hyz ⊢
  -- If `φ z = ⊤` there is no decrease.
  by_cases htop : φ z = ⊤
  · simp [htop]
  obtain ⟨b, hb⟩ : ∃ b : ℝ, φ z = b :=
    ⟨_, (EReal.coe_toReal htop (apply_ne_bot_of_mem_moreauYosidaResolvent hy hφy hxz')).symm⟩
  rw [hb] at hyz
  rw [hb, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  exact ofReal_le_div_add_mul hτ hd <| sub_le_mul_of_add_sq_div_le (NNReal.coe_pos.2 hτ)
    ENNReal.toReal_nonneg (ENNReal.toReal_lt_of_lt_ofReal hz) ENNReal.toReal_nonneg
    (ENNReal.toReal_le_add hxz hd hyz') (add_toReal_sq_div_le_of_coe_add_le hτ hd hxz' hyz)

end EMetricSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {τ : ℝ≥0}

/-- The objective `φ y + d(x, y)² / (2τ)` for `φ = ‖·‖² / 2`, as a real number, with the square
completed: its minimum value `‖x‖² / (2 (1 + τ))` plus `(1 + τ) / (2τ)` times the squared
distance from `y` to the minimizer `x / (1 + τ)`. -/
private theorem half_norm_sq_add_edist_sq_div (hτ : 0 < τ) (x y : E) :
    ((‖y‖ ^ 2 / 2 : ℝ) : EReal) + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) =
      ((‖x‖ ^ 2 / (2 * (1 + τ)) + (1 + τ) / (2 * τ) * ‖y - (1 + (τ : ℝ))⁻¹ • x‖ ^ 2 : ℝ) :
        EReal) := by
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have h := mul_norm_sq_add_mul_norm_sub_sq (a := 1 / 2) (b := 1 / (2 * τ)) (by positivity) x y
  have h₁ : 1 / (2 * (τ : ℝ)) / (1 / 2 + 1 / (2 * τ)) = (1 + (τ : ℝ))⁻¹ := by field_simp; ring
  have h₂ : 1 / 2 * (1 / (2 * (τ : ℝ))) / (1 / 2 + 1 / (2 * τ)) = 1 / (2 * (1 + τ)) := by
    field_simp; ring
  have h₃ : 1 / 2 + 1 / (2 * (τ : ℝ)) = (1 + τ) / (2 * τ) := by field_simp; ring
  rw [h₁, h₂, h₃] at h
  rw [← EReal.coe_ennreal_toReal (by finiteness), ← EReal.coe_add, EReal.coe_eq_coe_iff]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ← dist_edist,
    dist_eq_norm, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
  linear_combination h

/-- On a real inner product space, the resolvent of the energy `‖·‖² / 2` with time step `τ > 0`
is the single point `x / (1 + τ)`. -/
@[simp]
theorem moreauYosidaResolvent_half_norm_sq (hτ : 0 < τ) (x : E) :
    moreauYosidaResolvent (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x = {(1 + (τ : ℝ))⁻¹ • x} := by
  have hk : 0 < (1 + (τ : ℝ)) / (2 * τ) := by have := NNReal.coe_pos.2 hτ; positivity
  ext y
  simp only [mem_moreauYosidaResolvent_iff, half_norm_sq_add_edist_sq_div hτ,
    EReal.coe_le_coe_iff, mem_singleton_iff, ne_eq, edist_ne_top, not_false_eq_true, true_and,
    forall_const]
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
@[simp]
theorem moreauYosida_half_norm_sq (hτ : 0 < τ) (x : E) :
    moreauYosida (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x =
      ((‖x‖ ^ 2 / (2 * (1 + τ)) : ℝ) : EReal) := by
  have hmem : (1 + (τ : ℝ))⁻¹ • x ∈
      moreauYosidaResolvent (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) τ x := by
    rw [moreauYosidaResolvent_half_norm_sq hτ]
    exact mem_singleton _
  rw [← (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hmem).2, half_norm_sq_add_edist_sq_div hτ,
    sub_self, norm_zero]
  simp

end InnerProductSpace

end TauCeti
