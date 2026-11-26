/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Homotopy.Lifting

/-!
# The distinguished logarithm

A continuous function `φ : ℝ → ℂ` with no zeros and `φ 0 = 1` has exactly one continuous
logarithm vanishing at `0`: a continuous `ψ` with `ψ 0 = 0` and `exp (ψ t) = φ t` for all `t`.
This is the **distinguished logarithm** `TauCeti.distLog φ`. It is the logarithm of a
characteristic function used throughout the theory of infinitely divisible laws: the principal
branch `Complex.log ∘ φ` jumps whenever `φ` crosses the negative real axis, while `distLog φ` does
not, and so it lets one take `n`-th roots and logarithms of characteristic functions continuously.

Existence lifts `φ` through the covering map `exp : ℂ → ℂ ∖ {0}`
(`Complex.isCoveringMapOn_exp`) from the simply connected line, by Mathlib's
`IsCoveringMapOn.existsUnique_continuousMap_lifts`; uniqueness, also on any preconnected set
containing `0`, is uniqueness of lifts (`IsCoveringMap.eqOn_of_comp_eqOn`).

## Main definitions and results

* `TauCeti.distLog`: the distinguished logarithm, `0` when `φ` has no continuous logarithm
  vanishing at `0` (`TauCeti.distLog_of_not_exists`, with the special cases
  `TauCeti.distLog_of_not_continuous`, `TauCeti.distLog_of_apply_zero_ne_one` and
  `TauCeti.distLog_of_apply_eq_zero`).
* `TauCeti.existsUnique_distLog`: existence and uniqueness of that logarithm, with
  `TauCeti.distLog_eq_iff` characterizing `distLog φ` among all functions.
* `TauCeti.eqOn_distLog`: a continuous logarithm on a preconnected set containing `0`, vanishing
  at `0`, is `distLog φ` there.
* `TauCeti.distLog_mul`, `TauCeti.distLog_inv`, `TauCeti.distLog_div`, `TauCeti.distLog_pow`:
  the distinguished logarithm turns products, inverses, quotients and powers into sums,
  negatives, differences and multiples.
* `TauCeti.existsUnique_continuous_pow_eq` and `TauCeti.eq_cexp_distLog_div`: for `n ≠ 0`,
  `exp (distLog φ / n)` is the only continuous `n`-th root of `φ` equal to `1` at `0`.
* `TauCeti.norm_distLog_sub_distLog_le`: `‖distLog φ - distLog χ‖ ≤ 3/2 ‖φ / χ - 1‖` on a
  preconnected set containing `0` where `φ / χ` stays within `1/2` of `1`.
* `TauCeti.tendstoUniformlyOn_distLog` and `TauCeti.tendstoLocallyUniformly_distLog`: uniform
  convergence of such functions on a compact preconnected set containing `0`, or on compact sets,
  gives the same convergence of their distinguished logarithms.

## References

* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge Studies in
  Advanced Mathematics 68, Cambridge University Press, 1999, §7 (the distinguished logarithm).
* A. Klenke, *Probability Theory: A Comprehensive Course*, 3rd ed., Universitext, Springer,
  2020, §16.1.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter Set Topology

variable {φ χ ψ : ℝ → ℂ}

/-- The **distinguished logarithm** of `φ : ℝ → ℂ`: the unique continuous `ψ` with `ψ 0 = 0` and
`exp (ψ t) = φ t` for every `t`. Such a `ψ` exists exactly when `φ` is continuous, has no zeros and
satisfies `φ 0 = 1` (`TauCeti.existsUnique_distLog`); otherwise `distLog φ` is `0`. -/
def distLog (φ : ℝ → ℂ) : ℝ → ℂ :=
  open Classical in
  if h : ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ t, cexp (ψ t) = φ t then h.choose else 0

/-- **Existence and uniqueness of the distinguished logarithm.** A continuous function with no
zeros and value `1` at `0` has exactly one continuous logarithm vanishing at `0`. -/
theorem existsUnique_distLog (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) :
    ∃! ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ t, cexp (ψ t) = φ t := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := isCoveringMapOn_exp.existsUnique_continuousMap_lifts ⟨φ, hφ⟩
    (a₀ := 0) (e₀ := 0) (by simp [h0]) hne
  refine ⟨F, ⟨F.continuous, hF0, fun t ↦ congrFun hF t⟩, ?_⟩
  rintro ψ ⟨hψ, hψ0, hψφ⟩
  refine isCoveringMap_exp.eq_of_comp_eq hψ F.continuous ?_ 0 (by simp [hψ0, hF0])
  ext1 t
  exact Subtype.ext ((hψφ t).trans (congrFun hF t).symm)

/-- The defining properties of `distLog φ`, for continuous `φ` without zeros and with `φ 0 = 1`. -/
private theorem distLog_spec (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) :
    Continuous (distLog φ) ∧ distLog φ 0 = 0 ∧ ∀ t, cexp (distLog φ t) = φ t := by
  have h := (existsUnique_distLog hφ h0 hne).exists
  simp only [distLog, h, ↓reduceDIte]
  exact h.choose_spec

/-- The distinguished logarithm vanishes at `0`; this holds also for the junk value `0`. -/
@[simp]
theorem distLog_apply_zero (φ : ℝ → ℂ) : distLog φ 0 = 0 := by
  rw [distLog]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rfl

/-- The junk value: when `φ` has no continuous logarithm vanishing at `0`, `distLog φ` is `0`. -/
theorem distLog_of_not_exists (h : ¬ ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ t, cexp (ψ t) = φ t) :
    distLog φ = 0 := by
  simp only [distLog, h, ↓reduceDIte]

/-- The distinguished logarithm of a discontinuous function is `0`. -/
theorem distLog_of_not_continuous (hφ : ¬ Continuous φ) : distLog φ = 0 :=
  distLog_of_not_exists fun ⟨_, hψ, _, hψφ⟩ ↦ hφ <| funext hψφ ▸ continuous_exp.comp' hψ

/-- The distinguished logarithm of a function with `φ 0 ≠ 1` is `0`. -/
theorem distLog_of_apply_zero_ne_one (h0 : φ 0 ≠ 1) : distLog φ = 0 :=
  distLog_of_not_exists fun ⟨_, _, hψ0, hψφ⟩ ↦ h0 <| by rw [← hψφ, hψ0, exp_zero]

/-- The distinguished logarithm of a function with a zero is `0`. -/
theorem distLog_of_apply_eq_zero {t : ℝ} (ht : φ t = 0) : distLog φ = 0 :=
  distLog_of_not_exists fun ⟨_, _, _, hψφ⟩ ↦ exp_ne_zero _ <| (hψφ t).trans ht

/-- The distinguished logarithm is continuous. -/
theorem continuous_distLog (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) :
    Continuous (distLog φ) :=
  (distLog_spec hφ h0 hne).1

/-- The distinguished logarithm is a logarithm. -/
theorem cexp_distLog (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) (t : ℝ) :
    cexp (distLog φ t) = φ t :=
  (distLog_spec hφ h0 hne).2.2 t

/-- **Characterization of the distinguished logarithm**: `distLog φ` is the continuous logarithm of
`φ` vanishing at `0`. -/
theorem distLog_eq_iff (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) :
    distLog φ = ψ ↔ Continuous ψ ∧ ψ 0 = 0 ∧ ∀ t, cexp (ψ t) = φ t :=
  ⟨by rintro rfl; exact distLog_spec hφ h0 hne,
    fun h ↦ (existsUnique_distLog hφ h0 hne).unique (distLog_spec hφ h0 hne) h⟩

/-- The distinguished logarithm of `exp ∘ ψ`, for continuous `ψ` vanishing at `0`, is `ψ`. -/
theorem distLog_cexp (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) : distLog (fun t ↦ cexp (ψ t)) = ψ :=
  (distLog_eq_iff (by fun_prop) (by simp [hψ0]) fun _ ↦ exp_ne_zero _).2
    ⟨hψ, hψ0, fun _ ↦ rfl⟩

/-- The distinguished logarithm of the constant function `1` is `0`. -/
@[simp]
theorem distLog_one : distLog 1 = 0 :=
  (distLog_eq_iff continuous_const rfl fun _ ↦ one_ne_zero).2
    ⟨continuous_const, rfl, fun _ ↦ by simp⟩

/-- **Local uniqueness.** On a preconnected set `s` containing `0`, a logarithm of `φ` continuous on
`s` and vanishing at `0` agrees with the distinguished logarithm. -/
theorem eqOn_distLog (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0) {s : Set ℝ}
    (hs : IsPreconnected s) (h0s : 0 ∈ s) (hψ : ContinuousOn ψ s) (hψ0 : ψ 0 = 0)
    (hψφ : ∀ t ∈ s, cexp (ψ t) = φ t) : EqOn (distLog φ) ψ s :=
  isCoveringMap_exp.eqOn_of_comp_eqOn hs (continuous_distLog hφ h0 hne).continuousOn hψ
    (fun t ht ↦ Subtype.ext ((cexp_distLog hφ h0 hne t).trans (hψφ t ht).symm)) h0s
    (by simp [hψ0])

/-! ### Products, quotients and powers -/

section Algebra

variable (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0)
include hφ h0 hne

/-- The distinguished logarithm of a product is the sum of the distinguished logarithms. -/
theorem distLog_mul (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχne : ∀ t, χ t ≠ 0) :
    distLog (φ * χ) = distLog φ + distLog χ :=
  (distLog_eq_iff (hφ.mul hχ) (by simp [h0, hχ0]) fun t ↦ mul_ne_zero (hne t) (hχne t)).2
    ⟨(continuous_distLog hφ h0 hne).add (continuous_distLog hχ hχ0 hχne), by simp, fun t ↦ by
      simp [exp_add, cexp_distLog hφ h0 hne, cexp_distLog hχ hχ0 hχne]⟩

/-- The distinguished logarithm of an inverse is the negative of the distinguished logarithm. -/
theorem distLog_inv : distLog φ⁻¹ = -distLog φ :=
  (distLog_eq_iff (hφ.inv₀ hne) (by simp [h0]) fun t ↦ inv_ne_zero (hne t)).2
    ⟨(continuous_distLog hφ h0 hne).neg, by simp, fun t ↦ by
      simp [exp_neg, cexp_distLog hφ h0 hne]⟩

/-- The distinguished logarithm of a quotient is the difference of the distinguished logarithms. -/
theorem distLog_div (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχne : ∀ t, χ t ≠ 0) :
    distLog (φ / χ) = distLog φ - distLog χ := by
  rw [div_eq_mul_inv, distLog_mul hφ h0 hne (hχ.inv₀ hχne) (by simp [hχ0])
    (fun t ↦ inv_ne_zero (hχne t)), distLog_inv hχ hχ0 hχne, sub_eq_add_neg]

/-- The distinguished logarithm of a power is the corresponding multiple of the distinguished
logarithm. -/
theorem distLog_pow (n : ℕ) : distLog (φ ^ n) = n • distLog φ :=
  (distLog_eq_iff (hφ.pow n) (by simp [h0]) fun t ↦ pow_ne_zero n (hne t)).2
    ⟨(continuous_distLog hφ h0 hne).const_smul n, by simp, fun t ↦ by
      simp [nsmul_eq_mul, exp_natCast_mul, cexp_distLog hφ h0 hne]⟩

/-- `exp (distLog φ / n)` is an `n`-th root of `φ`. -/
theorem cexp_distLog_div_pow {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    cexp (distLog φ t / n) ^ n = φ t := by
  rw [← exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), cexp_distLog hφ h0 hne]

end Algebra

/-! ### Roots -/

/-- **Uniqueness of continuous roots.** A continuous `n`-th root `χ` of a function `φ` without
zeros, with `χ 0 = 1` and `n ≠ 0`, is `exp (distLog φ / n)`. -/
theorem eq_cexp_distLog_div (hne : ∀ t, φ t ≠ 0) (hχ : Continuous χ) (hχ0 : χ 0 = 1) {n : ℕ}
    (hn : n ≠ 0) (hχφ : ∀ t, χ t ^ n = φ t) : χ = fun t ↦ cexp (distLog φ t / n) := by
  have hχne (t : ℝ) : χ t ≠ 0 := fun h ↦ hne t (by rw [← hχφ, h, zero_pow hn])
  obtain rfl : φ = χ ^ n := funext fun t ↦ (hχφ t).symm
  ext t
  rw [distLog_pow hχ hχ0 hχne, Pi.smul_apply, nsmul_eq_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn), cexp_distLog hχ hχ0 hχne]

/-- **Existence and uniqueness of continuous roots.** For `n ≠ 0`, a continuous function without
zeros and with value `1` at `0` has exactly one continuous `n`-th root with value `1` at `0`,
namely `exp (distLog φ / n)` (`TauCeti.eq_cexp_distLog_div`). -/
theorem existsUnique_continuous_pow_eq (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0)
    {n : ℕ} (hn : n ≠ 0) : ∃! χ : ℝ → ℂ, Continuous χ ∧ χ 0 = 1 ∧ ∀ t, χ t ^ n = φ t :=
  ⟨fun t ↦ cexp (distLog φ t / n),
    ⟨((continuous_distLog hφ h0 hne).div_const _).cexp, by simp,
      cexp_distLog_div_pow hφ h0 hne hn⟩,
    fun _ ⟨hχ, hχ0, hχφ⟩ ↦ eq_cexp_distLog_div hne hχ hχ0 hn hχφ⟩

/-! ### Continuity -/

/-- **Stability of the distinguished logarithm.** On a preconnected set `s` containing `0` on which
`φ / χ` stays within `1/2` of `1`, the distinguished logarithms of `φ` and `χ` differ by at most
`3/2 ‖φ / χ - 1‖`. There `distLog φ - distLog χ` is the principal logarithm of `φ / χ`. -/
theorem norm_distLog_sub_distLog_le (hφ : Continuous φ) (h0 : φ 0 = 1) (hne : ∀ t, φ t ≠ 0)
    (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχne : ∀ t, χ t ≠ 0) {s : Set ℝ} (hs : IsPreconnected s)
    (h0s : 0 ∈ s) (hφχ : ∀ t ∈ s, ‖φ t / χ t - 1‖ ≤ 1 / 2) {t : ℝ} (ht : t ∈ s) :
    ‖distLog φ t - distLog χ t‖ ≤ 3 / 2 * ‖φ t / χ t - 1‖ := by
  have hslit (t : ℝ) (ht : t ∈ s) : φ t / χ t ∈ slitPlane := by
    simpa using mem_slitPlane_of_norm_lt_one ((hφχ t ht).trans_lt (by norm_num))
  have hlog : EqOn (distLog (φ / χ)) (fun t ↦ log (φ t / χ t)) s :=
    eqOn_distLog (hφ.div hχ hχne) (by simp [h0, hχ0]) (fun t ↦ div_ne_zero (hne t) (hχne t)) hs
      h0s ((hφ.div hχ hχne).continuousOn.clog hslit) (by simp [h0, hχ0])
      fun t ht ↦ exp_log (slitPlane_ne_zero (hslit t ht))
  have hdiv := congrFun (distLog_div hφ h0 hne hχ hχ0 hχne) t
  rw [Pi.sub_apply] at hdiv
  rw [← hdiv, hlog ht]
  simpa only [add_sub_cancel] using norm_log_one_add_half_le_self (hφχ t ht)

/-- **Continuity of the distinguished logarithm, on a compact set.** If continuous functions `φ i`
without zeros and with value `1` at `0` converge uniformly on a compact preconnected set `s`
containing `0` to a continuous function `φ₀` without zeros, then their distinguished logarithms
converge uniformly on `s` to that of `φ₀`. -/
theorem tendstoUniformlyOn_distLog {ι : Type*} {l : Filter ι} {φ : ι → ℝ → ℂ} {φ₀ : ℝ → ℂ}
    (hφ : ∀ i, Continuous (φ i)) (h0 : ∀ i, φ i 0 = 1) (hne : ∀ i t, φ i t ≠ 0)
    (hφ₀ : Continuous φ₀) (hne₀ : ∀ t, φ₀ t ≠ 0) {s : Set ℝ} (hs : IsCompact s)
    (hs' : IsPreconnected s) (h0s : 0 ∈ s) (h : TendstoUniformlyOn φ φ₀ l s) :
    TendstoUniformlyOn (fun i ↦ distLog (φ i)) (distLog φ₀) l s := by
  rcases l.eq_or_neBot with rfl | hl
  · exact Metric.tendstoUniformlyOn_iff.2 fun _ _ ↦ eventually_bot
  have h0₀ : φ₀ 0 = 1 := tendsto_nhds_unique (h.tendsto_at h0s) (by simp [h0])
  -- `‖φ₀‖` is bounded below on `s` by some `m > 0`
  obtain ⟨t₀, -, hmin⟩ := hs.exists_isMinOn ⟨0, h0s⟩ hφ₀.norm.continuousOn
  set m := ‖φ₀ t₀‖
  have hm : 0 < m := norm_pos_iff.2 (hne₀ t₀)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  -- once `‖φ i - φ₀‖ < δ` on `s`, the ratio `φ i / φ₀` is within `δ / m ≤ 1/2` of `1` there
  set δ := min (m / 2) (ε * m / 2)
  have hδm : δ / m ≤ 1 / 2 := by
    rw [div_le_iff₀ hm]
    linarith [min_le_left (m / 2) (ε * m / 2)]
  have hδε : 3 / 2 * (δ / m) < ε := by
    have : δ / m ≤ ε / 2 := by
      rw [div_le_iff₀ hm]
      linarith [min_le_right (m / 2) (ε * m / 2)]
    linarith
  filter_upwards [h δ (by positivity)] with i hi
  have hratio (t : ℝ) (ht : t ∈ s) : ‖φ i t / φ₀ t - 1‖ ≤ δ / m := by
    rw [div_sub_one (hne₀ t), norm_div, ← dist_eq_norm']
    exact div_le_div₀ (by positivity) (hi t ht).le hm (hmin ht)
  intro t ht
  rw [dist_eq_norm']
  calc ‖distLog (φ i) t - distLog φ₀ t‖ ≤ 3 / 2 * ‖φ i t / φ₀ t - 1‖ :=
        norm_distLog_sub_distLog_le (hφ i) (h0 i) (hne i) hφ₀ h0₀ hne₀ hs' h0s
          (fun t ht ↦ (hratio t ht).trans hδm) ht
    _ ≤ 3 / 2 * (δ / m) := by gcongr; exact hratio t ht
    _ < ε := hδε

/-- **Continuity of the distinguished logarithm.** If continuous functions `φ i` without zeros and
with value `1` at `0` converge locally uniformly to a function `φ₀` without zeros, then their
distinguished logarithms converge locally uniformly to that of `φ₀`. -/
theorem tendstoLocallyUniformly_distLog {ι : Type*} {l : Filter ι} {φ : ι → ℝ → ℂ}
    {φ₀ : ℝ → ℂ} (hφ : ∀ i, Continuous (φ i)) (h0 : ∀ i, φ i 0 = 1) (hne : ∀ i t, φ i t ≠ 0)
    (hne₀ : ∀ t, φ₀ t ≠ 0) (h : TendstoLocallyUniformly φ φ₀ l) :
    TendstoLocallyUniformly (fun i ↦ distLog (φ i)) (distLog φ₀) l := by
  rcases l.eq_or_neBot with rfl | hl
  · exact fun _ _ _ ↦ ⟨univ, univ_mem, eventually_bot⟩
  have hφ₀ : Continuous φ₀ := h.continuous (Frequently.of_forall hφ)
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  -- a compact set lies in some `[-T, T]`, which is compact, preconnected and contains `0`
  obtain ⟨T, hKT⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hKT
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (by linarith), subset_empty_iff] at hKT
    exact hKT ▸ tendstoUniformlyOn_empty
  exact (tendstoUniformlyOn_distLog hφ h0 hne hφ₀ hne₀ isCompact_Icc isPreconnected_Icc
    ⟨by linarith, hT⟩ (h _ isCompact_Icc)).mono hKT

end TauCeti
