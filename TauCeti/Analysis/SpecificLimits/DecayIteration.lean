/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The iteration lemma for decay estimates on concentric balls

Let `φ` be nonnegative and nondecreasing on `(0, R]`, and suppose that

`φ ρ ≤ A ((ρ / r)^α + ε) φ r + B r^β` whenever `0 < ρ ≤ r ≤ R`,

with `A, B ≥ 0` and `β < α`. Fix `γ < α`. If `ε ≤ ε₀`, then

`φ ρ ≤ C ((ρ / r)^γ φ r + B ρ^β)` whenever `0 < ρ ≤ r ≤ R`,

where `ε₀ > 0` and `C` depend only on `A`, `α`, `β` and `γ`. Taking `γ = β` gives the usual
form `φ ρ ≤ C ((ρ / r)^β φ r + B ρ^β)`. So a small perturbation `ε` costs only an arbitrarily
small part of the decay rate `α` of the unperturbed inequality, and the inhomogeneous term keeps
its rate `β`.

This is the device that turns a comparison argument into a Morrey or Campanato estimate. In the
Campanato approach to the Schauder estimates, `φ ρ` is an integral such as `∫_{B_ρ} ‖∇u‖²` or
`∫_{B_ρ} ‖∇u - (∇u)_ρ‖²` for a solution `u` of an equation with variable coefficients. Comparing
`u` on `B_r` with the solution of the equation with coefficients frozen at the centre gives the
hypothesis: `α` is the decay exponent of the frozen problem, `ε` measures the oscillation of the
coefficients on `B_r`, and `B r^β` comes from the data. With `γ = β` and `r = R`, the conclusion
is a power bound `φ ρ ≤ C' ρ^β`, the kind of growth condition that Morrey's Dirichlet growth
theorem and Campanato's characterization of Hölder continuity turn into Hölder estimates.

## Main declarations

* `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add`: the iteration lemma.

## References

* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter III, Lemma 2.1.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Lemma 5.13.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Lemma 3.4.
-/

public section

namespace TauCeti

open Set

/-- One step of the iteration, repeated `k` times. If `φ (τ s) ≤ τ^γ φ s + B s^β` for every
`s ∈ (0, R]`, with `0 < τ < 1`, `β < γ` and `B ≥ 0`, then for `r ∈ (0, R]`

`φ (τᵏ r) ≤ (τᵏ)^γ φ r + M B (τᵏ r)^β`, where `M = τ^{-β} / (1 - τ^{γ - β})`.

The constant `M` is the one for which the inductive step closes exactly:
`τ^γ M + 1 = τ^β M`. -/
private theorem le_rpow_mul_add_mul_rpow_of_forall_le {φ : ℝ → ℝ} {τ β γ R B r : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hβγ : β < γ) (hB : 0 ≤ B)
    (hstep : ∀ s ∈ Ioc 0 R, φ (τ * s) ≤ τ ^ γ * φ s + B * s ^ β) (hr : r ∈ Ioc 0 R)
    (k : ℕ) :
    φ (τ ^ k * r) ≤
      (τ ^ k) ^ γ * φ r + τ ^ (-β) / (1 - τ ^ (γ - β)) * B * (τ ^ k * r) ^ β := by
  have hq1 : τ ^ (γ - β) < 1 := Real.rpow_lt_one hτ0.le hτ1 (sub_pos.2 hβγ)
  have hM : 0 ≤ τ ^ (-β) / (1 - τ ^ (γ - β)) := div_nonneg (by positivity) (by linarith)
  induction k with
  | zero =>
    simp only [pow_zero, Real.one_rpow, one_mul, le_add_iff_nonneg_right]
    exact mul_nonneg (mul_nonneg hM hB) (Real.rpow_nonneg hr.1.le _)
  | succ k ih =>
    have hs : τ ^ k * r ∈ Ioc 0 R :=
      ⟨by have := hr.1; positivity,
        (mul_le_of_le_one_left hr.1.le (pow_le_one₀ hτ0.le hτ1.le)).trans hr.2⟩
    have hk : (0 : ℝ) ≤ τ ^ k := by positivity
    have hkr : 0 ≤ τ ^ k * r := hs.1.le
    -- The exponents of `τ` produced by the step: `τ^γ τ^{-β} = τ^{γ - β}` and
    -- `τ^{-β} τ^β = 1`.
    have hγβ : τ ^ γ * τ ^ (-β) = τ ^ (γ - β) := by
      rw [← Real.rpow_add hτ0, sub_eq_add_neg]
    have hββ : τ ^ (-β) * τ ^ β = 1 := by
      rw [← Real.rpow_add hτ0, neg_add_cancel, Real.rpow_zero]
    have hne : 1 - τ ^ (γ - β) ≠ 0 := by linarith
    calc φ (τ ^ (k + 1) * r) = φ (τ * (τ ^ k * r)) := by rw [pow_succ']; ring_nf
      _ ≤ τ ^ γ * φ (τ ^ k * r) + B * (τ ^ k * r) ^ β := hstep _ hs
      _ ≤ τ ^ γ * ((τ ^ k) ^ γ * φ r +
            τ ^ (-β) / (1 - τ ^ (γ - β)) * B * (τ ^ k * r) ^ β) +
            B * (τ ^ k * r) ^ β := by gcongr
      _ = (τ ^ (k + 1)) ^ γ * φ r +
            τ ^ (-β) / (1 - τ ^ (γ - β)) * B * (τ ^ (k + 1) * r) ^ β := by
        rw [pow_succ', mul_assoc τ, Real.mul_rpow hτ0.le hk, Real.mul_rpow hτ0.le hkr]
        field_simp
        linear_combination (B * (τ ^ k * r) ^ β) * (hγβ - hββ)

/-- **The iteration lemma.** Let `A ≥ 0` and `β < α`, and let `γ < α`.
There are `ε₀ > 0` and `C > 0`, depending only on `A`, `α`, `β` and `γ`, such that the following
holds. Let `φ` be nonnegative and nondecreasing on `(0, R]`, let `B ≥ 0` and `ε ≤ ε₀`, and
suppose that

`φ ρ ≤ A ((ρ / r)^α + ε) φ r + B r^β` whenever `0 < ρ ≤ r ≤ R`.

Then

`φ ρ ≤ C ((ρ / r)^γ φ r + B ρ^β)` whenever `0 < ρ ≤ r ≤ R`.

With `γ = β` this is the form `φ ρ ≤ C ((ρ / r)^β φ r + B ρ^β)` of the references. -/
theorem exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add {A α β γ : ℝ} (hA : 0 ≤ A)
    (hβ : β < α) (hγ : γ < α) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ {φ : ℝ → ℝ} {R B ε : ℝ}, 0 ≤ B → ε ≤ ε₀ →
      MonotoneOn φ (Ioc 0 R) → (∀ r ∈ Ioc 0 R, 0 ≤ φ r) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ A * ((ρ / r) ^ α + ε) * φ r + B * r ^ β) →
      ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ C * ((ρ / r) ^ γ * φ r + B * ρ ^ β) := by
  -- Proof sketch: fix a ratio `τ ∈ (0, 1)` with `2 A τ^α ≤ τ^γ'` for an exponent `γ'` strictly
  -- between `max β γ` and `α`, and take `ε₀ = τ^α`. Then `φ (τ s) ≤ τ^γ' φ s + B s^β`, and
  -- iterating this along the radii `τᵏ r` bounds `φ (τᵏ r)` by `τ^{kγ'} φ r` plus a geometric
  -- series in `τ^{γ' - β} < 1`. An arbitrary `ρ` lies between two consecutive radii.
  -- The working exponent `γ'` lies strictly between `max β γ` and `α`.
  set γ' := (max β γ + α) / 2
  have hβγ' : β < γ' := by have := le_max_left β γ; simp only [γ']; linarith
  have hγγ' : γ ≤ γ' := by have := le_max_right β γ; simp only [γ']; linarith
  have hγ'α : 0 < α - γ' := by have := max_lt hβ hγ; simp only [γ']; linarith
  -- The ratio `τ` satisfies `τ^{α - γ'} = (2A + 2)⁻¹`, so that `2 A τ^α ≤ τ^γ'`.
  set τ : ℝ := (2 * A + 2) ^ (-(α - γ')⁻¹)
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (neg_lt_zero.2 (inv_pos.2 hγ'α))
  have hτA : 2 * A * τ ^ α ≤ τ ^ γ' := by
    have hτα : τ ^ (α - γ') = (2 * A + 2)⁻¹ := by
      rw [← Real.rpow_mul (by positivity), neg_mul, inv_mul_cancel₀ hγ'α.ne', Real.rpow_neg_one]
    have hsplit : τ ^ α = τ ^ (α - γ') * τ ^ γ' := by
      rw [← Real.rpow_add hτ0, sub_add_cancel]
    rw [hsplit, hτα, ← mul_assoc, ← div_eq_mul_inv]
    refine mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  set M := τ ^ (-β) / (1 - τ ^ (γ' - β))
  have hM : 0 ≤ M := div_nonneg (by positivity)
    (by linarith [Real.rpow_lt_one hτ0.le hτ1 (sub_pos.2 hβγ')])
  set c₁ := max 1 (τ ^ (-γ'))
  set c₂ := max 1 (τ ^ (-β))
  refine ⟨τ ^ α, max c₁ (M * c₂), by positivity, lt_max_of_lt_left (lt_max_of_lt_left one_pos),
    ?_⟩
  intro φ R B ε hB hε hmono hφ0 hφ ρ r hρ hρr hrR
  have hr : 0 < r := hρ.trans_le hρr
  -- One step: `φ (τ s) ≤ τ^γ' φ s + B s^β`, since `A (τ^α + ε) ≤ 2 A τ^α ≤ τ^γ'`.
  have hstep : ∀ s ∈ Ioc 0 R, φ (τ * s) ≤ τ ^ γ' * φ s + B * s ^ β := by
    intro s hs
    have h := hφ (τ * s) s (by have := hs.1; positivity)
      (mul_le_of_le_one_left hs.1.le hτ1.le) hs.2
    rw [mul_div_cancel_right₀ τ hs.1.ne'] at h
    refine h.trans (add_le_add_left (mul_le_mul_of_nonneg_right ?_ (hφ0 s hs)) _)
    calc A * (τ ^ α + ε) ≤ A * (τ ^ α + τ ^ α) := by gcongr
      _ = 2 * A * τ ^ α := by ring
      _ ≤ τ ^ γ' := hτA
  -- Choose `k` with `τᵏ⁺¹ < ρ / r ≤ τᵏ`.
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (div_pos hρ hr)
    ((div_le_one hr).2 hρr) hτ0 hτ1
  have hρk : ρ ≤ τ ^ k * r := (div_le_iff₀ hr).1 hk2
  have hρk' : τ * (τ ^ k * r) ≤ ρ := by
    rw [← mul_assoc, ← pow_succ']
    exact ((lt_div_iff₀ hr).1 hk1).le
  -- Between two consecutive radii, a power changes by at most a factor `max 1 τ^{-s}`.
  have hcmp : ∀ {x y s : ℝ}, 0 < x → x ≤ y → τ * y ≤ x → y ^ s ≤ max 1 (τ ^ (-s)) * x ^ s := by
    intro x y s hx hxy hτy
    rcases le_total 0 s with hs | hs
    · calc y ^ s ≤ (τ⁻¹ * x) ^ s :=
            Real.rpow_le_rpow (hx.le.trans hxy) ((le_inv_mul_iff₀ hτ0).2 hτy) hs
        _ = τ ^ (-s) * x ^ s := by
            rw [Real.mul_rpow (by positivity) hx.le, Real.inv_rpow hτ0.le, Real.rpow_neg hτ0.le]
        _ ≤ _ := by gcongr; exact le_max_right _ _
    · calc y ^ s ≤ x ^ s := Real.rpow_le_rpow_of_nonpos hx hxy hs
        _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  have h1 : (τ ^ k) ^ γ' ≤ c₁ * (ρ / r) ^ γ := by
    refine (hcmp (div_pos hρ hr) hk2 (by rw [← pow_succ']; exact hk1.le)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (div_pos hρ hr) ((div_le_one hr).2 hρr) hγγ')
      (by positivity)
  have h2 : (τ ^ k * r) ^ β ≤ c₂ * ρ ^ β := hcmp hρ hρk hρk'
  have hφr : 0 ≤ φ r := hφ0 r ⟨hr, hrR⟩
  calc φ ρ ≤ φ (τ ^ k * r) :=
        hmono ⟨hρ, hρr.trans hrR⟩ ⟨hρ.trans_le hρk, (mul_le_of_le_one_left hr.le
          (pow_le_one₀ hτ0.le hτ1.le)).trans hrR⟩ hρk
    _ ≤ (τ ^ k) ^ γ' * φ r + M * B * (τ ^ k * r) ^ β :=
        le_rpow_mul_add_mul_rpow_of_forall_le hτ0 hτ1 hβγ' hB hstep ⟨hr, hrR⟩ k
    _ ≤ c₁ * (ρ / r) ^ γ * φ r + M * B * (c₂ * ρ ^ β) := by gcongr
    _ = c₁ * ((ρ / r) ^ γ * φ r) + M * c₂ * (B * ρ ^ β) := by ring
    _ ≤ max c₁ (M * c₂) * ((ρ / r) ^ γ * φ r) + max c₁ (M * c₂) * (B * ρ ^ β) := by
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]
    _ = _ := by ring

end TauCeti
