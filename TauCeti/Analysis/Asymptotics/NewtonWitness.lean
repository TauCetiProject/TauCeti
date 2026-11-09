/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Polynomial rates for the constants of a quantitative Newton step

Consider a nonlinear equation `e + D x + N x = 0` near an approximate solution, where `D` has a
right inverse `Q` of norm at most `C`, the remainder satisfies `N 0 = 0` and
`‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖` on the ball of radius `δ`, and the residual has
norm `ε = ‖e‖`. If `2 C² L ε < 1 / 4` and `2 C ε < δ / 4`, the map `x ↦ -Q (e + N x)` contracts
the ball of radius `2 C ε` and has a fixed point `x₀` there. Put `γ = min (δ / 2) (2 C L)⁻¹`.
Then `‖x₀‖ ≤ 2 C ε < γ / 2` (`TauCeti.IsNewtonWitness.two_mul_mul_lt_min_div_two`), and since
`C L γ ≤ 1 / 2`, two solutions in the range of `Q` inside the ball of radius `γ` coincide. A
solution recovered within `R ε` of the approximate solution, where `R` is the constant of a
recovery estimate, is therefore the fixed point `x₀` as soon as `R ε < γ`.
`TauCeti.IsNewtonWitness C L δ ε R` records the three inequalities
`2 C² L ε < 1 / 4`, `2 C ε < δ / 4` and `R ε < γ`.

In gluing constructions all five constants depend on a small scale `h → 0⁺`, and only
polynomial rates are known: `C ≤ K h^(-q)`, `L ≤ K h^(-p)`, `δ ≥ k h^a`, `ε ≤ K h^e` and
`R ≤ K h^(-b)`. Then the three inequalities hold for every sufficiently small `h` as soon as

`2 q + p < e`,  `q + a < e`,  `a + b < e`,  `q + p + b < e`

(`TauCeti.eventually_forall_isNewtonWitness`). The bounds may be uniform over a family of data
indexed by `ι`, and the conclusion is then uniform over the family as well.

When the approximate solution is a profile corrected to order `N`, its residual is
`ε_N ≤ K_N h^(N + 1 - π)`, where the loss `π` and the exponents `q`, `p`, `a`, `b` do not depend
on `N`, while the constants `K_N` of the residual and of the recovery estimate may. Every
sufficiently large order `N` then has a threshold `h_N` below which the three inequalities hold
for the same data, uniformly over the family
(`TauCeti.eventually_atTop_eventually_forall_isNewtonWitness`): the order is chosen first,
from the fixed exponents alone, and the scale is shrunk afterwards.

## Main declarations

* `TauCeti.IsNewtonWitness`: the contraction and recovery inequalities of a Newton step.
* `TauCeti.IsNewtonWitness.two_mul_mul_lt_min_div_two`: the fixed point lies in half the
  uniqueness ball.
* `TauCeti.eventually_forall_isNewtonWitness`: polynomial rates satisfying the four exponent
  inequalities give the witness for all small scales.
* `TauCeti.eventually_atTop_eventually_forall_isNewtonWitness`: the same for profiles of every
  large order, with order-dependent constants.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Proposition A.3.4.
-/

public section

open Filter Topology

namespace TauCeti

/-- The smallness conditions of a quantitative Newton step for an equation whose linearization
has a right inverse of norm at most `C`, whose quadratic remainder has constant `L` on the ball
of radius `δ`, and whose residual has norm `ε`, together with the condition that a solution
recovered within `R ε` lies in the uniqueness ball of radius `min (δ / 2) (2 C L)⁻¹`. -/
structure IsNewtonWitness (C L δ ε R : ℝ) : Prop where
  /-- The contraction condition `2 C² L ε < 1 / 4`. -/
  two_mul_sq_mul_mul_lt : 2 * C ^ 2 * L * ε < 1 / 4
  /-- The radius condition `2 C ε < δ / 4`. -/
  two_mul_mul_lt : 2 * C * ε < δ / 4
  /-- The recovery condition `R ε < min (δ / 2) (2 C L)⁻¹`. -/
  mul_lt_min : R * ε < min (δ / 2) (2 * C * L)⁻¹

namespace IsNewtonWitness

variable {C L δ ε R : ℝ}

/-- The fixed point of the Newton step, of norm at most `2 C ε`, lies in half the uniqueness
ball: `2 C ε < min (δ / 2) (2 C L)⁻¹ / 2`. -/
theorem two_mul_mul_lt_min_div_two (hw : IsNewtonWitness C L δ ε R) (hC : 0 < C) (hL : 0 < L) :
    2 * C * ε < min (δ / 2) (2 * C * L)⁻¹ / 2 := by
  have hCL : 0 < 2 * C * L := by positivity
  rw [lt_div_iff₀ two_pos, lt_min_iff, ← one_div, lt_div_iff₀ hCL]
  have h₁ := hw.two_mul_sq_mul_mul_lt
  have h₂ := hw.two_mul_mul_lt
  constructor <;> linarith

end IsNewtonWitness

/-- The pointwise step of `TauCeti.eventually_forall_isNewtonWitness`: at a scale `h > 0` where
the constants obey their rates and the four rate products are small, they form a Newton
witness. -/
private theorem isNewtonWitness_of_le_mul_rpow {C L δ ε R h q p a b e Kc Kl Ke Kr k : ℝ}
    (hh : 0 < h) (hC₀ : 0 < C) (hC : C ≤ Kc * h ^ (-q)) (hL₀ : 0 < L) (hL : L ≤ Kl * h ^ (-p))
    (hδ : k * h ^ a ≤ δ) (hε₀ : 0 ≤ ε) (hε : ε ≤ Ke * h ^ e) (hR₀ : 0 ≤ R)
    (hR : R ≤ Kr * h ^ (-b)) (t₁ : 2 * Kc ^ 2 * Kl * Ke * h ^ (e - 2 * q - p) < 1 / 4)
    (t₂ : 8 * Kc * Ke * h ^ (e - q - a) < k) (t₃ : 2 * Ke * Kr * h ^ (e - a - b) < k)
    (t₄ : 2 * Kc * Kl * Ke * Kr * h ^ (e - q - p - b) < 1) :
    IsNewtonWitness C L δ ε R := by
  have ha : 0 < h ^ a := Real.rpow_pos_of_pos hh a
  have hKc : 0 ≤ Kc * h ^ (-q) := hC₀.le.trans hC
  have hKl : 0 ≤ Kl * h ^ (-p) := hL₀.le.trans hL
  have hKe : 0 ≤ Ke * h ^ e := hε₀.trans hε
  -- Each product of the constants is at most the corresponding product of the rates, which is
  -- a single power of `h` (times `h ^ a` when it is compared with `δ`).
  have hpow (x y : ℝ) : h ^ x * h ^ y = h ^ (x + y) := (Real.rpow_add hh x y).symm
  have e₁ : C ^ 2 * L * ε ≤ Kc ^ 2 * Kl * Ke * h ^ (e - 2 * q - p) := by
    calc C ^ 2 * L * ε ≤ (Kc * h ^ (-q)) ^ 2 * (Kl * h ^ (-p)) * (Ke * h ^ e) := by
          gcongr
      _ = Kc ^ 2 * Kl * Ke * (h ^ (-q) * h ^ (-q) * h ^ (-p) * h ^ e) := by ring
      _ = Kc ^ 2 * Kl * Ke * h ^ (e - 2 * q - p) := by
          rw [hpow, hpow, hpow]
          ring_nf
  have e₂ : C * ε ≤ Kc * Ke * h ^ (e - q - a) * h ^ a := by
    calc C * ε ≤ Kc * h ^ (-q) * (Ke * h ^ e) := by gcongr
      _ = Kc * Ke * (h ^ (-q) * h ^ e) := by ring
      _ = Kc * Ke * h ^ (e - q - a) * h ^ a := by
          rw [hpow, mul_assoc (Kc * Ke), hpow]
          ring_nf
  have e₃ : ε * R ≤ Ke * Kr * h ^ (e - a - b) * h ^ a := by
    calc ε * R ≤ Ke * h ^ e * (Kr * h ^ (-b)) := by gcongr
      _ = Ke * Kr * (h ^ e * h ^ (-b)) := by ring
      _ = Ke * Kr * h ^ (e - a - b) * h ^ a := by
          rw [hpow, mul_assoc (Ke * Kr), hpow]
          ring_nf
  have e₄ : C * L * (ε * R) ≤ Kc * Kl * Ke * Kr * h ^ (e - q - p - b) := by
    calc C * L * (ε * R) ≤
          Kc * h ^ (-q) * (Kl * h ^ (-p)) * (Ke * h ^ e * (Kr * h ^ (-b))) := by
          gcongr
      _ = Kc * Kl * Ke * Kr * (h ^ (-q) * h ^ (-p) * h ^ e * h ^ (-b)) := by ring
      _ = Kc * Kl * Ke * Kr * h ^ (e - q - p - b) := by
          rw [hpow, hpow, hpow]
          ring_nf
  have t₂ := mul_lt_mul_of_pos_right t₂ ha
  have t₃ := mul_lt_mul_of_pos_right t₃ ha
  have hCL : 0 < 2 * C * L := by positivity
  refine ⟨by linarith, by linarith, lt_min (by linarith) ?_⟩
  rw [← one_div, lt_div_iff₀ hCL]
  linarith

variable {ι : Type*} {C L δ : ι → ℝ → ℝ} {q p a b Kc Kl k : ℝ}

/-- **Polynomial rates give a Newton witness.** Suppose that near `h = 0⁺`, uniformly in `i`,
`0 < C ≤ Kc h^(-q)`, `0 < L ≤ Kl h^(-p)`, `δ ≥ k h^a` with `k > 0`, `0 ≤ ε ≤ Ke h^e` and
`0 ≤ R ≤ Kr h^(-b)`. If `2 q + p < e`, `q + a < e`, `a + b < e` and `q + p + b < e`, then for
every sufficiently small `h > 0` the data `C, L, δ, ε, R` at `h` form a Newton witness for every
`i`. -/
theorem eventually_forall_isNewtonWitness {ε R : ι → ℝ → ℝ} {e Ke Kr : ℝ} (hk : 0 < k)
    (hC : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 < C i h ∧ C i h ≤ Kc * h ^ (-q))
    (hL : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 < L i h ∧ L i h ≤ Kl * h ^ (-p))
    (hδ : ∀ᶠ h in 𝓝[>] 0, ∀ i, k * h ^ a ≤ δ i h)
    (hε : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 ≤ ε i h ∧ ε i h ≤ Ke * h ^ e)
    (hR : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 ≤ R i h ∧ R i h ≤ Kr * h ^ (-b))
    (h₁ : 2 * q + p < e) (h₂ : q + a < e) (h₃ : a + b < e) (h₄ : q + p + b < e) :
    ∀ᶠ h in 𝓝[>] 0, ∀ i, IsNewtonWitness (C i h) (L i h) (δ i h) (ε i h) (R i h) := by
  -- Near `0⁺`, a positive power of `h` with any coefficient is below any positive constant.
  have eventually_mul_rpow_lt {θ : ℝ} (hθ : 0 < θ) (A : ℝ) {c : ℝ} (hc : 0 < c) :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), A * h ^ θ < c := by
    have ht := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.const_mul A
    rw [Real.zero_rpow hθ.ne', mul_zero] at ht
    exact (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hc)
  filter_upwards [hC, hL, hδ, hε, hR, self_mem_nhdsWithin,
    eventually_mul_rpow_lt (θ := e - 2 * q - p) (by linarith) (2 * Kc ^ 2 * Kl * Ke)
      (c := 1 / 4) (by norm_num),
    eventually_mul_rpow_lt (θ := e - q - a) (by linarith) (8 * Kc * Ke) hk,
    eventually_mul_rpow_lt (θ := e - a - b) (by linarith) (2 * Ke * Kr) hk,
    eventually_mul_rpow_lt (θ := e - q - p - b) (by linarith) (2 * Kc * Kl * Ke * Kr) one_pos]
    with h hC hL hδ hε hR (hh : 0 < h) t₁ t₂ t₃ t₄ i
  exact isNewtonWitness_of_le_mul_rpow hh (hC i).1 (hC i).2 (hL i).1 (hL i).2 (hδ i) (hε i).1
    (hε i).2 (hR i).1 (hR i).2 t₁ t₂ t₃ t₄

/-- **The order is chosen before the scale.** Let `ε N` be the residuals and `R N` the recovery
constants of approximate solutions corrected to order `N`, with `0 ≤ ε N ≤ K_N h^(N + 1 - π)` and
`0 ≤ R N ≤ K'_N h^(-b)` near `h = 0⁺`, uniformly in `i`. The constants `K_N` and `K'_N` may depend
on `N`, but the loss `π` and the exponent `b` do not. Suppose that `C`, `L` and `δ` satisfy the
hypotheses of `TauCeti.eventually_forall_isNewtonWitness`, independently of `N`. Then for every
sufficiently large `N`, every sufficiently small `h > 0` gives a Newton witness for every `i`. -/
theorem eventually_atTop_eventually_forall_isNewtonWitness {ε R : ℕ → ι → ℝ → ℝ} {π : ℝ}
    (hk : 0 < k)
    (hC : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 < C i h ∧ C i h ≤ Kc * h ^ (-q))
    (hL : ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 < L i h ∧ L i h ≤ Kl * h ^ (-p))
    (hδ : ∀ᶠ h in 𝓝[>] 0, ∀ i, k * h ^ a ≤ δ i h)
    (hε : ∀ N : ℕ, ∃ K, ∀ᶠ h in 𝓝[>] 0, ∀ i,
      0 ≤ ε N i h ∧ ε N i h ≤ K * h ^ ((N : ℝ) + 1 - π))
    (hR : ∀ N : ℕ, ∃ K, ∀ᶠ h in 𝓝[>] 0, ∀ i, 0 ≤ R N i h ∧ R N i h ≤ K * h ^ (-b)) :
    ∀ᶠ N in atTop, ∀ᶠ h in 𝓝[>] 0, ∀ i,
      IsNewtonWitness (C i h) (L i h) (δ i h) (ε N i h) (R N i h) := by
  set M := max (max (2 * q + p) (q + a)) (max (a + b) (q + p + b))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (M + π)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨Ke, hε⟩ := hε N
  obtain ⟨Kr, hR⟩ := hR N
  have hN : (N₀ : ℝ) ≤ N := Nat.cast_le.2 hN
  have m₁ : 2 * q + p ≤ M := le_max_of_le_left (le_max_left _ _)
  have m₂ : q + a ≤ M := le_max_of_le_left (le_max_right _ _)
  have m₃ : a + b ≤ M := le_max_of_le_right (le_max_left _ _)
  have m₄ : q + p + b ≤ M := le_max_of_le_right (le_max_right _ _)
  exact eventually_forall_isNewtonWitness hk hC hL hδ hε hR (by linarith) (by linarith)
    (by linarith) (by linarith)

end TauCeti
