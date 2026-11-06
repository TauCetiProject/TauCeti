/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Borel summation of symbols

Given symbols `a j ∈ S^(m j)` whose orders `m j` decrease to `-∞`, an *asymptotic sum*
`b ∼ ∑ⱼ a j` is a symbol such that for every `N` the remainder `b - ∑_{j < N} a j` is a symbol of
order `m N`. The series itself need not converge (for instance `∑ⱼ (-1)ʲ ⟨ξ⟩^(-j-1)` diverges at
`ξ = 0`); Borel's construction instead sums the cut-off terms `χ(ξ / tⱼ) a j(x, ξ)` for radii
`tⱼ → ∞` growing fast enough. Each point has a neighbourhood on which only finitely many of these
terms are nonzero, so the sum is smooth.

## Main declarations

* `TauCeti.Symbol.cutoff χ ht a`: the symbol `χ(ξ / t) a(x, ξ)`, `a` cut off below the frequency
  radius `t ≥ 1`, with the estimates `exists_bound_mixedDeriv_cutoff`. They are uniform in `t`,
  and since the cut-off symbol vanishes for `‖ξ‖ < t` it gains the factor `t ^ (m - μ)` when
  estimated as a symbol of any order `μ ≥ m`.
* `TauCeti.Symbol.exists_coefficient_eq_cutoff_sub`: `χ(ξ / t) a - a` vanishes for `‖ξ‖ ≥ 2t`, so
  it is a symbol of every order.
* `TauCeti.Symbol.IsAsymptoticSum a b`: `b` is an asymptotic sum of the symbols `a j`.
* `TauCeti.Symbol.exists_isAsymptoticSum`: Borel's theorem, every sequence of symbols whose
  orders decrease to `-∞` has an asymptotic sum.
* `TauCeti.Symbol.IsAsymptoticSum.exists_coefficient_eq_sub`: two asymptotic sums differ by a
  symbol of every order.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, Proposition 2.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Metric Topology
open scoped ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Cutoff

variable (χ : FrequencyCutoff (CoordinateSpace n))

private theorem contDiff_cutoff_coefficient (t : ℝ) (a : Symbol n V W m) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) • a.coefficient p :=
  ((χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)).smul a.contDiff_coefficient

/-- The symbol estimates of `χ(ξ / t) a(x, ξ)` hold with constants independent of `t ≥ 1`. -/
private theorem exists_bound_mixedDeriv_cutoff_coefficient (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set l := β.length
  -- The derivatives of the rescaled cutoff, and the frequency derivatives of `∂_x^α a`.
  choose B hB0 hB using fun i : ℕ => χ.exists_norm_iteratedFDeriv_comp_smul_le i
  choose E hE0 hE using fun k : ℕ => a.exists_norm_iteratedFDeriv_coordinateDeriv_le hK α k
  refine ⟨∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * B i * E (l - i),
    Finset.sum_nonneg fun i _ => by have := hB0 i; have := hE0 (l - i); positivity,
    fun t ht x hx ξ => ?_⟩
  set A : CoordinateSpace n → V →L[ℂ] W :=
    fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x
  have hA : ContDiff ℝ ∞ A :=
    (a.contDiff_coefficient.coordinateDeriv_fst α).comp (contDiff_prodMk_right x)
  have hχt : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
    (χ.contDiff (n := ⊤)).comp (contDiff_id.const_smul t⁻¹)
  -- Take the position derivatives first: they do not see the cutoff.
  have hmd : mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ =
      coordinateDeriv β (fun η => χ (t⁻¹ • η) • A η) ξ := by
    rw [mixedDeriv_eq_coordinateDeriv_snd (contDiff_cutoff_coefficient χ t a)]
    congr 1
    funext η
    exact congrFun (coordinateDeriv_const_smul α
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_left η)) _)
      (χ (t⁻¹ • η))) x
  -- The Leibniz rule for the frequency derivatives of the product.
  rw [hmd]
  refine (norm_coordinateDeriv_le β (contDiff_infty.1 (hχt.smul hA) _) ξ).trans
    ((norm_iteratedFDeriv_smul_le hχt hA ξ (mod_cast le_top)).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hw : (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((l - i : ℕ) : ℝ)) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
    rw [← Real.rpow_add (by positivity), Nat.cast_sub hil]
    congr 1
    ring
  calc (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ *
        ‖iteratedFDeriv ℝ (l - i) A ξ‖
      ≤ (l.choose i : ℝ) * (B i * (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2)) *
          (E (l - i) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((l - i : ℕ) : ℝ)) / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hB i t ht ξ) (by positivity)) (hE (l - i) x hx ξ)
          (norm_nonneg _) (by have := hB0 i; positivity)
    _ = (l.choose i : ℝ) * B i * E (l - i) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
        rw [← hw]
        ring

/-- The symbol `χ(ξ / t) a(x, ξ)`: the symbol `a` cut off below the frequency radius `t ≥ 1` by
the frequency cutoff `χ`. It vanishes for `‖ξ‖ ≤ t` and agrees with `a` for `‖ξ‖ ≥ 2t`. -/
def cutoff {t : ℝ} (ht : 1 ≤ t) (a : Symbol n V W m) : Symbol n V W m where
  coefficient p := χ (t⁻¹ • p.2) • a.coefficient p
  contDiff_coefficient := contDiff_cutoff_coefficient χ t a
  exists_bound K hK α β := by
    obtain ⟨C, hC, h⟩ := exists_bound_mixedDeriv_cutoff_coefficient χ a hK α β
    exact ⟨C, hC, h t ht⟩

variable {χ} {t : ℝ} (ht : 1 ≤ t) (a : Symbol n V W m)

@[simp]
theorem coefficient_cutoff (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoff χ ht a).coefficient p = χ (t⁻¹ • p.2) • a.coefficient p := (rfl)

include ht in
private theorem norm_inv_smul (ξ : CoordinateSpace n) : ‖t⁻¹ • ξ‖ = t⁻¹ * ‖ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (one_pos.trans_le ht).le)]

theorem coefficient_cutoff_of_norm_le {x ξ : CoordinateSpace n} (hξ : ‖ξ‖ ≤ t) :
    (cutoff χ ht a).coefficient (x, ξ) = 0 := by
  rw [coefficient_cutoff, χ.apply_eq_zero_of_norm_le_one, zero_smul]
  rw [norm_inv_smul ht]
  exact inv_mul_le_one_of_le₀ hξ (one_pos.trans_le ht).le

theorem coefficient_cutoff_of_two_mul_le_norm {x ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    (cutoff χ ht a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  rw [coefficient_cutoff, χ.apply_eq_one_of_two_le_norm, one_smul]
  rw [norm_inv_smul ht]
  exact (le_inv_mul_iff₀ (one_pos.trans_le ht)).2 (by linarith)

/-- The cut-off symbol `χ(ξ / t) a(x, ξ)` satisfies the estimates of `a` uniformly in `t ≥ 1`.
Since it vanishes for `‖ξ‖ < t`, estimating it as a symbol of an order `μ ≥ m` gains the factor
`t ^ (m - μ)`, which is small for large `t` when `μ > m`. -/
theorem exists_bound_mixedDeriv_cutoff {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (t : ℝ) (ht : 1 ≤ t) (μ : ℝ), m ≤ μ → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (cutoff χ ht a).coefficient x ξ‖ ≤
        C * t ^ (m - μ) * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
  obtain ⟨C, hC, h⟩ := exists_bound_mixedDeriv_cutoff_coefficient χ a hK α β
  refine ⟨C, hC, fun t ht μ hμ x hx ξ => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  rcases lt_or_ge ‖ξ‖ t with hξ | hξ
  · -- Below the radius `t` the cut-off symbol vanishes identically.
    have hzero : (cutoff χ ht a).coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [(isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds
        (by simpa using hξ : (x, ξ) ∈ {p : CoordinateSpace n × CoordinateSpace n | ‖p.2‖ < t})]
        with p hp
      exact coefficient_cutoff_of_norm_le ht a hp.le
    rw [hzero.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    positivity
  · -- Above it, `⟨ξ⟩ ^ (m - μ) ≤ t ^ (m - μ)`.
    have hwt : (1 + ‖ξ‖ ^ 2) ^ ((m - μ) / 2) ≤ t ^ (m - μ) := by
      calc (1 + ‖ξ‖ ^ 2) ^ ((m - μ) / 2) ≤ (t ^ 2) ^ ((m - μ) / 2) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
        _ = t ^ (m - μ) := by
            rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
            congr 1
            push_cast
            ring
    calc ‖mixedDeriv α β (cutoff χ ht a).coefficient x ξ‖
        ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := h t ht x hx ξ
      _ = C * (1 + ‖ξ‖ ^ 2) ^ ((m - μ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity)]
        congr 2
        ring
      _ ≤ C * t ^ (m - μ) * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by gcongr

/-- The difference `χ(ξ / t) a - a` vanishes for `‖ξ‖ ≥ 2t`, so it is a symbol of every order. -/
theorem exists_coefficient_eq_cutoff_sub (μ : ℝ) :
    ∃ r : Symbol n V W μ, r.coefficient = (cutoff χ ht a).coefficient - a.coefficient := by
  refine ⟨⟨(cutoff χ ht a).coefficient - a.coefficient,
    (cutoff χ ht a).contDiff_coefficient.sub a.contDiff_coefficient, fun K hK α β => ?_⟩, rfl⟩
  obtain ⟨C₁, hC₁, h₁⟩ := (cutoff χ ht a).exists_bound K hK α β
  obtain ⟨C₂, hC₂, h₂⟩ := a.exists_bound K hK α β
  refine ⟨(C₁ + C₂) * (1 + (2 * t) ^ 2) ^ (|m - μ| / 2), by positivity, fun x hx ξ => ?_⟩
  rcases lt_or_ge (2 * t) ‖ξ‖ with hξ | hξ
  · -- Beyond the radius `2t` the difference vanishes identically.
    have hzero : (cutoff χ ht a).coefficient - a.coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
        (by simpa using hξ :
          (x, ξ) ∈ {p : CoordinateSpace n × CoordinateSpace n | 2 * t < ‖p.2‖})] with p hp
      rw [Pi.sub_apply, coefficient_cutoff_of_two_mul_le_norm ht a hp.le, sub_self, Pi.zero_apply]
    rw [hzero.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    positivity
  · have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - μ) / 2) ≤ (1 + (2 * t) ^ 2) ^ (|m - μ| / 2) :=
      (Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith [le_abs_self (m - μ)])).trans
        (Real.rpow_le_rpow (by positivity)
          (by nlinarith [norm_nonneg ξ, one_pos.trans_le ht]) (by positivity))
    rw [mixedDeriv_sub (cutoff χ ht a).contDiff_coefficient a.contDiff_coefficient]
    calc ‖mixedDeriv α β (cutoff χ ht a).coefficient x ξ - mixedDeriv α β a.coefficient x ξ‖
        ≤ (C₁ + C₂) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
          rw [add_mul]
          exact (norm_sub_le _ _).trans (add_le_add (h₁ x hx ξ) (h₂ x hx ξ))
      _ = (C₁ + C₂) * (1 + ‖ξ‖ ^ 2) ^ ((m - μ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
          rw [mul_assoc, ← Real.rpow_add (by positivity)]
          congr 2
          ring
      _ ≤ (C₁ + C₂) * (1 + (2 * t) ^ 2) ^ (|m - μ| / 2) *
            (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by gcongr

end Cutoff

section AsymptoticSum

variable {orders : ℕ → ℝ}

/-- The symbol `b` is an *asymptotic sum* of the symbols `a j` of orders `orders j`, written
`b ∼ ∑ⱼ a j`: for every `N`, the remainder `b - ∑_{j < N} a j` is a symbol of order `orders N`. -/
def IsAsymptoticSum (a : (j : ℕ) → Symbol n V W (orders j)) (b : Symbol n V W m) : Prop :=
  ∀ N : ℕ, ∃ r : Symbol n V W (orders N),
    r.coefficient = b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient

theorem isAsymptoticSum_iff {a : (j : ℕ) → Symbol n V W (orders j)} {b : Symbol n V W m} :
    IsAsymptoticSum a b ↔ ∀ N : ℕ, ∃ r : Symbol n V W (orders N),
      r.coefficient = b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient :=
  Iff.rfl

/-- Asymptotic sums are unique up to symbols of every order: when the orders tend to `-∞`, two
asymptotic sums of the same symbols differ by a symbol of every order `μ`. -/
theorem IsAsymptoticSum.exists_coefficient_eq_sub {m' : ℝ} {a : (j : ℕ) → Symbol n V W (orders j)}
    {b : Symbol n V W m} {b' : Symbol n V W m'} (hb : IsAsymptoticSum a b)
    (hb' : IsAsymptoticSum a b') (hlim : Tendsto orders atTop atBot) (μ : ℝ) :
    ∃ r : Symbol n V W μ, r.coefficient = b.coefficient - b'.coefficient := by
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_le_atBot μ)).exists
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨r', hr'⟩ := hb' N
  refine ⟨inclusion hN (r - r'), ?_⟩
  rw [coefficient_inclusion, coefficient_sub, hr, hr', sub_sub_sub_cancel_right]

/-! ### Borel's construction

The rest of this section proves `exists_isAsymptoticSum`. Fix radii `t j ≥ j + 1` and put
`b = ∑ⱼ χ(ξ / t j) a j`. Below the frequency radius `R`, only the terms with `t j < R` are nonzero,
so the sum is locally finite and smooth. To make `b - ∑_{j < N} a j` a symbol of order `orders N`,
the radii are chosen so large that the terms of order `orders j < orders N` have
order-`orders N` estimates at most `2⁻ʲ`. There are countably many estimates to satisfy, indexed
by a radius `k` of a closed ball of positions and two words of coordinate indices; enumerating
them as `e i`, the radius `t j` takes care of the estimates `e i` with `i ≤ j`. -/

/-- The estimate data `(k, α, β)`: positions in the closed ball of radius `k`, and the words `α`
and `β` of position and frequency derivatives. -/
private abbrev EstimateIndex (n : ℕ) := ℕ × List (Fin n) × List (Fin n)

/-- The sum of the cut-off terms of Borel's construction. Each point has a neighbourhood on which
only finitely many terms are nonzero (`borelSum_eventuallyEq`). -/
private def borelSum (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ} (ht : ∀ j, 1 ≤ t j)
    (a : (j : ℕ) → Symbol n V W (orders j)) : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
  fun p => ∑' j, (cutoff χ (ht j) (a j)).coefficient p

private theorem contDiff_sum_coefficient (s : Finset ℕ)
    (b : (j : ℕ) → Symbol n V W (orders j)) : ContDiff ℝ ∞ (∑ j ∈ s, (b j).coefficient) := by
  rw [Finset.sum_fn]
  exact ContDiff.sum fun j _ => (b j).contDiff_coefficient

/-- A sum over `[N, L)` of terms bounded by `C j`, and by `2⁻ʲ` from `M` on, is at most
`∑_{j < M} C j + 2`. -/
private theorem sum_Ico_le_sum_range_add_two {γ C : ℕ → ℝ} {M N L : ℕ} (hC : ∀ j, 0 ≤ C j)
    (hγC : ∀ j ∈ Finset.Ico N L, γ j ≤ C j)
    (hγ : ∀ j ∈ Finset.Ico N L, M ≤ j → γ j ≤ (1 / 2) ^ j) :
    ∑ j ∈ Finset.Ico N L, γ j ≤ ∑ j ∈ Finset.range M, C j + 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (· < M)]
  refine add_le_add ?_ ?_
  · refine (Finset.sum_le_sum fun j hj => hγC j (Finset.mem_filter.1 hj).1).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hC j)
    exact Finset.mem_range.2 (Finset.mem_filter.1 hj).2
  · refine (Finset.sum_le_sum fun j hj =>
      hγ j (Finset.mem_filter.1 hj).1 (not_lt.1 (Finset.mem_filter.1 hj).2)).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => by positivity).trans
        (sum_geometric_two_le L))
    exact Finset.mem_range.2 (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).2

variable (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
  (a : (j : ℕ) → Symbol n V W (orders j))

include ht in
private theorem one_le_radius (j : ℕ) : 1 ≤ t j :=
  le_trans (by simp) (ht j)

/-- Near every point, the Borel sum is a finite sum of cut-off terms, and the number of terms may
be taken as large as desired. -/
private theorem borelSum_eventuallyEq (p : CoordinateSpace n × CoordinateSpace n) (N : ℕ) :
    ∃ L, N ≤ L ∧ borelSum χ (one_le_radius ht) a =ᶠ[𝓝 p]
      ∑ j ∈ Finset.range L, (cutoff χ (one_le_radius ht j) (a j)).coefficient := by
  set R := ‖p.2‖ + 1
  refine ⟨max N ⌈R⌉₊, le_max_left _ _, ?_⟩
  filter_upwards [(isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds
    (by simp [R] : p ∈ {q : CoordinateSpace n × CoordinateSpace n | ‖q.2‖ < R})] with q hq
  rw [Finset.sum_apply]
  refine tsum_eq_sum fun j hj => coefficient_cutoff_of_norm_le _ _ (le_of_lt ?_)
  rw [Finset.mem_range, not_lt] at hj
  calc ‖q.2‖ < R := hq
    _ ≤ ⌈R⌉₊ := Nat.le_ceil R
    _ ≤ j := by exact_mod_cast (le_max_right _ _).trans hj
    _ ≤ t j := (le_add_of_nonneg_right zero_le_one).trans (ht j)

private theorem contDiff_borelSum : ContDiff ℝ ∞ (borelSum χ (one_le_radius ht) a) :=
  contDiff_iff_contDiffAt.2 fun p => by
    obtain ⟨L, -, hL⟩ := borelSum_eventuallyEq χ ht a p 0
    exact (contDiff_sum_coefficient _ _).contDiffAt.congr_of_eventuallyEq hL

/-- The remainder estimate of Borel's construction: if the radii make the order-`orders N`
estimates of the cut-off terms of order `orders j < orders N` at most `2⁻ʲ`, then
`b - ∑_{j < N} a j` satisfies the estimates of order `orders N`. -/
private theorem exists_bound_borelSum_sub (hmono : Antitone orders)
    (hlim : Tendsto orders atTop atBot) {e : ℕ → EstimateIndex n} (he : Function.Surjective e)
    {C : ℕ → EstimateIndex n → ℝ} (hC0 : ∀ j q, 0 ≤ C j q)
    (hC : ∀ j q (s : ℝ) (hs : 1 ≤ s) (μ : ℝ), orders j ≤ μ → ∀ x ∈ closedBall 0 (q.1 : ℝ), ∀ ξ,
      ‖mixedDeriv q.2.1 q.2.2 (cutoff χ hs (a j)).coefficient x ξ‖ ≤
        C j q * s ^ (orders j - μ) * (1 + ‖ξ‖ ^ 2) ^ ((μ - q.2.2.length) / 2))
    (hsmall : ∀ j, ∀ i ≤ j, ∀ N ≤ j, orders j < orders N →
      C j (e i) * t j ^ (orders j - orders N) ≤ (1 / 2) ^ j)
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (borelSum χ (one_le_radius ht) a -
          ∑ j ∈ Finset.range N, (a j).coefficient) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2) := by
  have ht1 := one_le_radius ht
  -- The estimate index of `K`, `α`, `β`, and the index `M` from which the terms are small.
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall 0).1 hK.isBounded
  have hKk : K ⊆ closedBall 0 (⌈r⌉₊ : ℝ) := hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))
  obtain ⟨i₀, hi₀⟩ := he (⌈r⌉₊, α, β)
  have hi₀α : (e i₀).2.1 = α := by rw [hi₀]
  have hi₀β : (e i₀).2.2 = β := by rw [hi₀]
  have hi₀K : K ⊆ closedBall 0 ((e i₀).1 : ℝ) := by rw [hi₀]; exact hKk
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_atBot (orders N)))
  set M := max J i₀
  -- The first `N` terms: `χ(ξ / t j) a j - a j` is a symbol of every order.
  choose s hs using fun j => exists_coefficient_eq_cutoff_sub (χ := χ) (ht1 j) (a j) (orders N)
  choose D hD0 hD using fun j => (s j).exists_bound K hK α β
  refine ⟨∑ j ∈ Finset.range N, D j + (∑ j ∈ Finset.range M, C j (e i₀) + 2),
    add_nonneg (Finset.sum_nonneg fun j _ => hD0 j)
      (add_nonneg (Finset.sum_nonneg fun j _ => hC0 j _) zero_le_two), fun x hx ξ => ?_⟩
  obtain ⟨L, hNL, hL⟩ := borelSum_eventuallyEq χ ht a (x, ξ) N
  have hsm : ∀ j, ContDiff ℝ ∞ (cutoff χ (ht1 j) (a j)).coefficient :=
    fun j => (cutoff χ (ht1 j) (a j)).contDiff_coefficient
  -- Near `(x, ξ)` the remainder is
  -- `∑_{j < N} (χ(ξ / t j) a j - a j) + ∑_{N ≤ j < L} χ(ξ / t j) a j`.
  rw [(hL.sub (EventuallyEq.refl _ _)).mixedDeriv_eq,
    mixedDeriv_sub (contDiff_sum_coefficient _ _) (contDiff_sum_coefficient _ _),
    mixedDeriv_sum _ (fun j _ => hsm j), mixedDeriv_sum _ (fun j _ => (a j).contDiff_coefficient),
    ← Finset.sum_range_add_sum_Ico _ hNL, add_sub_right_comm, ← Finset.sum_sub_distrib]
  have hfirst : ∀ j, mixedDeriv α β (cutoff χ (ht1 j) (a j)).coefficient x ξ -
      mixedDeriv α β (a j).coefficient x ξ = mixedDeriv α β (s j).coefficient x ξ := fun j => by
    rw [hs, mixedDeriv_sub (hsm j) (a j).contDiff_coefficient]
  simp only [hfirst]
  -- The terms with `N ≤ j`, estimated with the gain `t j ^ (orders j - orders N)`.
  have htail : ∀ j ∈ Finset.Ico N L, ‖mixedDeriv α β (cutoff χ (ht1 j) (a j)).coefficient x ξ‖ ≤
      C j (e i₀) * t j ^ (orders j - orders N) * (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2) :=
    fun j hj => by
      have h := hC j (e i₀) (t j) (ht1 j) (orders N) (hmono (Finset.mem_Ico.1 hj).1) x
        (hi₀K hx) ξ
      rwa [hi₀α, hi₀β] at h
  have hγC : ∀ j ∈ Finset.Ico N L, C j (e i₀) * t j ^ (orders j - orders N) ≤ C j (e i₀) :=
    fun j hj => mul_le_of_le_one_right (hC0 j _) (Real.rpow_le_one_of_one_le_of_nonpos (ht1 j)
      (by linarith [hmono (Finset.mem_Ico.1 hj).1]))
  have hγ : ∀ j ∈ Finset.Ico N L, M ≤ j →
      C j (e i₀) * t j ^ (orders j - orders N) ≤ (1 / 2) ^ j := fun j hj hMj =>
    hsmall j i₀ ((le_max_right _ _).trans hMj) N (Finset.mem_Ico.1 hj).1
      (hJ j ((le_max_left _ _).trans hMj))
  calc ‖∑ j ∈ Finset.range N, mixedDeriv α β (s j).coefficient x ξ +
        ∑ j ∈ Finset.Ico N L, mixedDeriv α β (cutoff χ (ht1 j) (a j)).coefficient x ξ‖
      ≤ ∑ j ∈ Finset.range N, D j * (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2) +
          ∑ j ∈ Finset.Ico N L, C j (e i₀) * t j ^ (orders j - orders N) *
            (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2) :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hD j x hx ξ))
          ((norm_sum_le _ _).trans (Finset.sum_le_sum htail)))
    _ ≤ (∑ j ∈ Finset.range N, D j + (∑ j ∈ Finset.range M, C j (e i₀) + 2)) *
          (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, add_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (sum_Ico_le_sum_range_add_two (fun j => hC0 j _) hγC hγ) (by positivity))

end AsymptoticSum

variable {orders : ℕ → ℝ}

/-- **Borel's theorem**: every sequence of symbols `a j ∈ S^(orders j)` whose orders decrease to
`-∞` has an asymptotic sum `b ∈ S^(orders 0)`, a symbol such that `b - ∑_{j < N} a j` is a symbol
of order `orders N` for every `N`. -/
theorem exists_isAsymptoticSum (hmono : Antitone orders) (hlim : Tendsto orders atTop atBot)
    (a : (j : ℕ) → Symbol n V W (orders j)) :
    ∃ b : Symbol n V W (orders 0), IsAsymptoticSum a b := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  -- Uniform estimates of the cut-off terms, one constant for each term and estimate index.
  choose C hC0 hC using fun j (q : EstimateIndex n) =>
    exists_bound_mixedDeriv_cutoff (χ := χ) (a j) (isCompact_closedBall 0 (q.1 : ℝ)) q.2.1 q.2.2
  obtain ⟨e, he⟩ := exists_surjective_nat (EstimateIndex n)
  -- Radii large enough to make the relevant estimates at most `2⁻ʲ`.
  have hrad : ∀ j : ℕ, ∃ s : ℝ, (j : ℝ) + 1 ≤ s ∧ ∀ i ∈ Finset.range (j + 1),
      ∀ N ∈ Finset.range (j + 1), orders j < orders N →
        C j (e i) * s ^ (orders j - orders N) ≤ (1 / 2) ^ j := fun j => by
    refine ((eventually_ge_atTop _).and ((eventually_all_finset _).2 fun i _ =>
      (eventually_all_finset _).2 fun N _ => ?_)).exists
    by_cases hN : orders j < orders N
    · have h := (tendsto_rpow_neg_atTop (sub_pos.2 hN)).const_mul (C j (e i))
      rw [mul_zero] at h
      filter_upwards [h.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < (1 / 2) ^ j))]
        with s hs _
      rwa [neg_sub] at hs
    · exact Eventually.of_forall fun s h => absurd h hN
  choose t ht hsmall using hrad
  have hbound := exists_bound_borelSum_sub χ ht a hmono hlim he hC0 hC fun j i hi N hN =>
    hsmall j i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) N
      (Finset.mem_range.2 (Nat.lt_succ_of_le hN))
  have hB := contDiff_borelSum χ ht a
  refine ⟨⟨borelSum χ (one_le_radius ht) a, hB, fun K hK α β => ?_⟩, fun N =>
    ⟨⟨borelSum χ (one_le_radius ht) a - ∑ j ∈ Finset.range N, (a j).coefficient,
      hB.sub (contDiff_sum_coefficient _ _), fun K hK α β => hbound N hK α β⟩, rfl⟩⟩
  have h := hbound 0 hK α β
  rwa [Finset.sum_range_zero, sub_zero] at h

end Symbol

end TauCeti
