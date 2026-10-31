/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Elementary asymptotic criteria

Four general criteria that supplement Mathlib's asymptotics API, an elementary estimate, and an
elementary limit of ratios.

For functions into a normed division ring, `f` satisfies `f = a g + o(g)` exactly when `f / g`
tends to `a`, provided `g` is eventually nonzero. This criterion converts little-o error estimates
into limits of normalized functions, and conversely recovers error estimates from ratio limits.
The quotient is right division: multiplication need not be commutative. For ordered fields,
the ratio formulation also supports order arguments.

In a seminormed group the norm is at most one on a neighbourhood of the origin, so there a higher
power of the norm is dominated by any lower one. This is the comparison that lets a Taylor
remainder of one order be read as a remainder of a smaller order.

An eventual big-O bound at `atTop` is uniform on a whole half-line `[a, ∞)` as soon as the
dominated function is bounded on compact intervals and the dominating one is bounded away from
zero. This is how an asymptotic estimate becomes an explicit inequality valid at every point,
which a summation argument can apply at infinitely many points at once.

A fixed power of a shifted natural number times a geometric sequence of ratio in `[0, 1)` tends
to zero. This is the form needed to absorb polynomial growth after shifting an index.

If the weighted terms `aₙ qⁿ` of a real sequence are bounded by `A` at a radius `q > 0`, then at
a radius `c` they are bounded by `A * (|c| / q)ⁿ`. For `|c| < q` this geometric bound is the
estimate behind every loss of radius for power series.

In an ordered field, the ratio `(t + x) / (t + y)` of two translates tends to `1` as `t → ∞`. This
is the limit at infinity of antiderivatives built from such ratios, for example in elementary
evaluations of elliptic integrals.

## Main results

* `Asymptotics.isLittleO_sub_mul_iff_tendsto_div`: `f - a g = o(g)` if and only if
  `f / g → a`, for an eventually nonzero `g`.
* `Asymptotics.isBigO_norm_pow_norm_pow_nhds_zero_of_le`: `‖x‖ ^ m = O(‖x‖ ^ n)` at the origin
  whenever `n ≤ m`.
* `Asymptotics.IsBigO.isBigO_principal_Ici`: `f = O(g)` at `atTop` gives `f = O(g)` on `[a, ∞)`
  when `f` is bounded on each `[a, b]` and `‖g‖` is bounded below there.
* `TauCeti.tendsto_add_pow_mul_pow_of_lt_one`: `(n + k) ^ k * ρ ^ n` tends to zero when
  `0 ≤ ρ < 1`.
* `TauCeti.mul_abs_pow_le_of_forall_mul_pow_le`: weighted terms bounded by `A` at a radius `q > 0`
  are bounded by `A * (|c| / q)ⁿ` at the radius `c`.
* `TauCeti.tendsto_add_div_add_atTop`: `(t + x) / (t + y) → 1` as `t → ∞`.

## Related results

Mathlib's `Asymptotics.isLittleO_iff_tendsto'` is the underlying zero-limit ratio criterion, and
`Asymptotics.isBigO_pow_pow_cobounded_of_le` is the comparison of powers at infinity.
-/

public section

open Filter Topology

namespace Asymptotics

/-- **A linear asymptotic is a limit of ratios.** For an eventually nonzero `g`, `f = a g + o(g)`
if and only if `f / g` tends to `a`. -/
theorem isLittleO_sub_mul_iff_tendsto_div {α 𝕜 : Type*} [NormedDivisionRing 𝕜]
    {l : Filter α} {f g : α → 𝕜} {a : 𝕜} (hg : ∀ᶠ x in l, g x ≠ 0) :
    (fun x ↦ f x - a * g x) =o[l] g ↔ Tendsto (fun x ↦ f x / g x) l (𝓝 a) := by
  rw [isLittleO_iff_tendsto' (hg.mono fun x hx ↦ by simp [hx])]
  refine (tendsto_congr' (hg.mono fun x hx ↦ ?_)).trans tendsto_sub_nhds_zero_iff
  rw [sub_div, mul_div_cancel_right₀ _ hx]

/-- **At the origin a higher power of the norm is dominated by a lower one.** The norm is at most
one near `0`, so `‖x‖ ^ m = O(‖x‖ ^ n)` whenever `n ≤ m`. -/
theorem isBigO_norm_pow_norm_pow_nhds_zero_of_le {E : Type*} [SeminormedAddCommGroup E]
    {m n : ℕ} (h : n ≤ m) :
    (fun x : E ↦ ‖x‖ ^ m) =O[𝓝 (0 : E)] fun x ↦ ‖x‖ ^ n := by
  refine isBigO_iff.2 ⟨1, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with x hx
  simp only [one_mul, norm_pow, norm_norm]
  exact pow_le_pow_of_le_one (norm_nonneg x) (by simpa [Metric.mem_closedBall] using hx) h

/-- **An eventual big-O bound holds on a whole half-line.** If `f = O(g)` at `atTop`, `f` is
bounded on every interval `[a, b]`, and `‖g‖` is bounded below by a positive constant on
`[a, ∞)`, then `f = O(g)` uniformly on `[a, ∞)`. -/
theorem IsBigO.isBigO_principal_Ici {E F : Type*} [Norm E] [Norm F] {f : ℝ → E} {g : ℝ → F}
    {a c : ℝ} (h : f =O[atTop] g) (hc : 0 < c) (hg : ∀ x, a ≤ x → c ≤ ‖g x‖)
    (hf : ∀ b, ∃ B, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) :
    f =O[𝓟 (Set.Ici a)] g := by
  obtain ⟨c₀, hc₀⟩ := h.bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hc₀
  obtain ⟨B, hB⟩ := hf b
  refine isBigO_principal.mpr ⟨max c₀ (max B 0 / c), fun x hx ↦ ?_⟩
  have hgx := hg x hx
  have hg0 : 0 ≤ ‖g x‖ := hc.le.trans hgx
  rcases le_or_gt b x with hbx | hbx
  · exact (hb x hbx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0)
  · calc ‖f x‖ ≤ max B 0 := (hB x ⟨hx, hbx.le⟩).trans (le_max_left _ _)
      _ ≤ max B 0 / c * ‖g x‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        exact mul_le_mul_of_nonneg_left hgx (le_max_right _ _)
      _ ≤ max c₀ (max B 0 / c) * ‖g x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) hg0

end Asymptotics

namespace TauCeti

/-- For `0 ≤ ρ < 1`, the shifted polynomial-times-geometric sequence `(n + k)ᵏ ρⁿ` tends to `0`.
This is useful for absorbing polynomial growth after shifting an index. -/
theorem tendsto_add_pow_mul_pow_of_lt_one (k : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ ↦ (n + k : ℝ) ^ k * ρ ^ n) atTop (𝓝 0) := by
  rcases hρ0.eq_or_lt with rfl | hρ
  · exact tendsto_const_nhds.congr' <| (eventually_ge_atTop 1).mono fun n hn ↦ by
      simp [zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  have h := ((tendsto_pow_const_mul_const_pow_of_lt_one k hρ0 hρ1).comp
    (tendsto_add_atTop_nat k)).const_mul (ρ⁻¹ ^ k)
  convert h using 1
  · ext n
    simp only [Function.comp_apply, Nat.cast_add, pow_add, inv_pow]
    field_simp [hρ.ne']
  · simp

/-- If the weighted terms `aₙ qⁿ` of a real sequence at a radius `q > 0` are bounded by `A`, then
at the radius `c` its weighted terms are bounded by `A * (|c| / q)ⁿ`. Applied to the coefficient
norms of a power series, this is the estimate behind every loss of radius. -/
theorem mul_abs_pow_le_of_forall_mul_pow_le {a : ℕ → ℝ} {q A c : ℝ} (hq : 0 < q)
    (hA : ∀ n, a n * q ^ n ≤ A) (n : ℕ) : a n * |c| ^ n ≤ A * (|c| / q) ^ n :=
  calc a n * |c| ^ n = a n * q ^ n * (|c| / q) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ A * (|c| / q) ^ n := by gcongr; exact hA n

/-- In an ordered field, the ratio `(t + x) / (t + y)` of two translates of `t` tends to `1` as
`t → ∞`. -/
theorem tendsto_add_div_add_atTop {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] (x y : 𝕜) :
    Tendsto (fun t : 𝕜 ↦ (t + x) / (t + y)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := x - y)).div_atTop
    (tendsto_atTop_add_const_right atTop y tendsto_id)
  rw [show (1 : 𝕜) = 1 + 0 by simp]
  refine (h.const_add 1).congr' ?_
  filter_upwards [eventually_gt_atTop (-y)] with t ht
  have : t + y ≠ 0 := by linarith
  simp only [id]
  field_simp
  ring

end TauCeti
