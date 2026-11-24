/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Topology.LocallyFinsupp
public import TauCeti.Analysis.Complex.Runge.Operator
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.InfiniteProd
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Complex.Runge.ZeroFree

/-!
# Holomorphic functions with prescribed zeros on open subsets of the plane

This file proves the Weierstrass theorem on an arbitrary open set `Ω ⊆ ℂ`: for every
multiplicity function `m : Function.locallyFinsuppWithin Ω ℕ`, that is, natural multiplicities
supported on a subset of `Ω` that is closed and discrete in `Ω`, some function holomorphic on `Ω`
vanishes to order exactly `m z` at every `z ∈ Ω`, and in particular has no zeros in `Ω` off the
support of `m` (`TauCeti.exists_holomorphic_with_zero_orders`). No connectedness of `Ω` is
assumed, and `Ω` may be empty.

The construction patches finite products along the filled compact exhaustion
`TauCeti.filledExhaustion Ω`. The step that makes this possible is
`TauCeti.IsRungeCompactPair.exists_differentiableOn_analyticOrderAt_eq_norm_sub_one_lt`: for a
Runge compact pair `(Ω, K)` and finitely many points off `K` with multiplicities, some function
holomorphic on `Ω` has exactly these zeros in `Ω` and is uniformly as close to `1` on `K` as
desired. It multiplies the polynomial `∏ a ∈ s, (z - a) ^ m a` by a zero-free Runge approximant of
its reciprocal (`TauCeti.IsRungeCompactPair.exists_differentiableOn_ne_zero_norm_sub_lt`).
Applied to the points of the support of `m` in each shell
`filledExhaustion Ω (n + 1) \ filledExhaustion Ω n`, with distance `2⁻ⁿ` from `1` on
`filledExhaustion Ω n`, it produces factors whose infinite product converges locally uniformly on
`Ω`, and whose analytic orders add up to `m`
(`TauCeti.analyticOrderAt_tprod_one_add`).

Two consequences follow. Realizing the positive and negative parts of an integer divisor and
dividing gives a meromorphic function with that divisor and finite order everywhere
(`TauCeti.exists_meromorphic_with_divisor`). Multiplying a meromorphic function by a holomorphic
function vanishing to the order of each of its poles removes the poles, so every meromorphic
function on `Ω` is a quotient of holomorphic functions off a subset closed and discrete in `Ω`
(`TauCeti.exists_holomorphic_quotient`).

## Main results

* `TauCeti.IsRungeCompactPair.exists_differentiableOn_analyticOrderAt_eq_norm_sub_one_lt`: a
  finite divisor off `K` is realized by a function holomorphic on `Ω` that is uniformly close to
  `1` on `K`.
* `TauCeti.exists_holomorphic_with_zero_orders`: every natural multiplicity function on an open
  set `Ω ⊆ ℂ` is the zero-order function of some function holomorphic on `Ω`.
* `TauCeti.exists_meromorphic_with_divisor`: every integer divisor on `Ω` is the divisor of some
  function meromorphic on `Ω` with finite order at every point.
* `TauCeti.exists_holomorphic_quotient`: every function meromorphic on `Ω` is, off a subset closed
  and discrete in `Ω`, a quotient of two functions holomorphic on `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Proposition 15.2 and Theorems 15.3
  and 15.6.
-/

public section

open Complex Filter Metric Set
open scoped Topology

namespace TauCeti

variable {Ω K : Set ℂ}

/-- **Finite divisors off a Runge compact set, close to `1` on it.** Let `(Ω, K)` be a Runge compact
pair and `s` a finite set of points off `K`, with multiplicities `m`. For every `ε > 0` some
function holomorphic on `Ω` vanishes to order exactly `m a` at every `a ∈ s ∩ Ω`, has no other zeros
in `Ω`, and is uniformly within `ε` of `1` on `K`. -/
theorem IsRungeCompactPair.exists_differentiableOn_analyticOrderAt_eq_norm_sub_one_lt
    (hRunge : IsRungeCompactPair Ω K) (s : Finset ℂ) (hsK : ∀ a ∈ s, a ∉ K) (m : ℂ → ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧
      (∀ z ∈ Ω, analyticOrderAt h z = if z ∈ s then (m z : ℕ∞) else 0) ∧
      ∀ z ∈ K, ‖h z - 1‖ < ε := by
  -- Multiply the polynomial `q` with these zeros by a zero-free approximant of `q⁻¹` on `K`.
  set q : ℂ → ℂ := ∏ a ∈ s, (· - a) ^ m a with hq
  have hqd : Differentiable ℂ q := by
    rw [hq]
    fun_prop
  have hq0 (z : ℂ) (hz : z ∉ (s : Set ℂ)) : q z ≠ 0 := by
    simp only [hq, Finset.prod_apply, Pi.pow_apply]
    exact Finset.prod_ne_zero_iff.mpr fun a ha ↦
      pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ hz (h ▸ ha))
  have hKs : K ⊆ (s : Set ℂ)ᶜ := fun z hz hzs ↦ hsK z hzs hz
  obtain ⟨M, hM⟩ := hRunge.isCompact.exists_bound_of_continuousOn hqd.continuous.continuousOn
  obtain ⟨g, hg, hg0, hgq⟩ := hRunge.exists_differentiableOn_ne_zero_norm_sub_lt
    s.finite_toSet.isClosed.isOpen_compl hKs (u := fun z ↦ (q z)⁻¹)
    (hqd.differentiableOn.inv hq0) (fun z hz ↦ inv_ne_zero (hq0 z (hKs hz)))
    (ε := ε / (|M| + 1)) (by positivity)
  refine ⟨q * g, hqd.differentiableOn.mul hg, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hga : AnalyticAt ℂ g z := hg.analyticAt (hRunge.isOpen.mem_nhds hz)
    rw [analyticOrderAt_mul (hqd.analyticAt z) hga, hga.analyticOrderAt_eq_zero.mpr (hg0 z hz),
      add_zero, hq, analyticOrderAt_prod_sub_pow]
  · have hqz := hq0 z (hKs hz)
    have hsplit : (q * g) z - 1 = q z * ((q z)⁻¹ - g z) * -1 := by
      rw [Pi.mul_apply]
      field_simp
      ring
    calc ‖(q * g) z - 1‖ = ‖q z‖ * ‖(q z)⁻¹ - g z‖ := by
          rw [hsplit, norm_mul, norm_mul, norm_neg, norm_one, mul_one]
      _ ≤ (|M| + 1) * ‖(q z)⁻¹ - g z‖ := by
          gcongr
          exact (hM z hz).trans ((le_abs_self M).trans (by linarith))
      _ < (|M| + 1) * (ε / (|M| + 1)) := by
          gcongr
          exact hgq z hz
      _ = ε := by field_simp

/-- Splitting the support of `m` into its part in the stage `filledExhaustion Ω 0` and its parts in
the shells between consecutive stages, the multiplicities of the pieces at `z ∈ Ω` add up to
`m z`. -/
private theorem ite_add_tsum_ite_sdiff_eq (hΩ : IsOpen Ω) (m : Function.locallyFinsuppWithin Ω ℕ)
    {T : ℕ → Finset ℂ} (hT : ∀ n z, z ∈ T n ↔ z ∈ filledExhaustion Ω n ∧ m z ≠ 0) {z : ℂ}
    (hz : z ∈ Ω) :
    ((if z ∈ T 0 then (m z : ℕ∞) else 0) +
      ∑' n, if z ∈ T (n + 1) \ T n then (m z : ℕ∞) else 0) = m z := by
  classical
  by_cases hmz : m z = 0
  · simp [hmz]
  -- Count the zeros at `z` by the first exhaustion stage that contains `z`.
  have hex : ∃ n, z ∈ filledExhaustion Ω n :=
    mem_iUnion.mp (hΩ.iUnion_filledExhaustion.symm ▸ hz)
  have hstage (n : ℕ) : z ∈ T n ↔ Nat.find hex ≤ n := by
    rw [hT, and_iff_left hmz]
    exact ⟨fun h ↦ Nat.find_min' hex h, fun h ↦ filledExhaustion_mono h (Nat.find_spec hex)⟩
  simp_rw [Finset.mem_sdiff, hstage]
  rcases Nat.find hex with _ | N
  · simp
  · have hiff (n : ℕ) : (N + 1 ≤ n + 1 ∧ ¬N + 1 ≤ n) ↔ n = N := by omega
    simp only [hiff, tsum_ite_eq, Nat.le_zero, Nat.add_one_ne_zero, ite_false, zero_add]

/-- **Weierstrass theorem on open subsets of the plane.** For every natural multiplicity function
`m` on an open set `Ω ⊆ ℂ`, supported on a subset closed and discrete in `Ω`, some function
holomorphic on `Ω` vanishes to order exactly `m z` at every `z ∈ Ω`. In particular it has no zeros
in `Ω` off the support of `m`, and it vanishes identically near no point of `Ω`. -/
theorem exists_holomorphic_with_zero_orders (hΩ : IsOpen Ω)
    (m : Function.locallyFinsuppWithin Ω ℕ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ ∀ z ∈ Ω, analyticOrderAt f z = (m z : ℕ∞) := by
  classical
  -- `T n` is the part of the support of `m` in the `n`th exhaustion stage.
  set T : ℕ → Finset ℂ := fun n ↦ ((m.restrict (filledExhaustion_subset Ω n)).finiteSupport
    (isCompact_filledExhaustion Ω n)).toFinset with hT
  have hmemT (n : ℕ) (z : ℂ) : z ∈ T n ↔ z ∈ filledExhaustion Ω n ∧ m z ≠ 0 := by
    simp [hT, Function.locallyFinsuppWithin.restrict_apply]
  -- The head factor carries the zeros in stage `0`; the `n`th factor carries those in the shell
  -- between stages `n` and `n + 1`, and is within `2⁻ⁿ` of `1` on stage `n`.
  obtain ⟨h₀, hh₀, hord₀, -⟩ := (isRungeCompactPair_empty_right.mpr
    hΩ).exists_differentiableOn_analyticOrderAt_eq_norm_sub_one_lt (T 0) (fun _ _ h ↦ h) m one_pos
  have hshell (n : ℕ) : ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧
      (∀ z ∈ Ω, analyticOrderAt h z = if z ∈ T (n + 1) \ T n then (m z : ℕ∞) else 0) ∧
      ∀ z ∈ filledExhaustion Ω n, ‖h z - 1‖ < (1 / 2 : ℝ) ^ n :=
    (hΩ.isRungeCompactPair_filledExhaustion
      n).exists_differentiableOn_analyticOrderAt_eq_norm_sub_one_lt _
      (fun a ha haK ↦ (Finset.mem_sdiff.mp ha).2 ((hmemT _ _).mpr ⟨haK, ((hmemT _ _).mp
        (Finset.mem_sdiff.mp ha).1).2⟩)) m (pow_pos (by norm_num) n)
  choose h hh hord hclose using hshell
  -- The infinite product of the shell factors converges locally uniformly on `Ω`.
  set u : ℕ → ℂ → ℂ := fun n z ↦ h n z - 1 with hu
  have hud (n : ℕ) : DifferentiableOn ℂ (u n) Ω := (hh n).sub_const 1
  have hone (n : ℕ) : (fun w ↦ 1 + u n w) = h n := by
    ext w
    simp [hu]
  have htail (L : Set ℂ) (hLΩ : L ⊆ Ω) (hL : IsCompact L) :
      SummableUniformlyOn (fun n z ↦ ‖u n z‖) L := by
    obtain ⟨N₀, hN₀⟩ := hΩ.exists_subset_filledExhaustion hL hLΩ
    refine (HasSumUniformlyOn.of_norm_le_summable_eventually summable_geometric_two
      (Nat.cofinite_eq_atTop ▸ eventually_atTop.2 ⟨N₀, fun n hn z hz ↦ ?_⟩)).summableUniformlyOn
    simpa using (hclose n z (filledExhaustion_mono hn (hN₀ hz))).le
  have hprod := differentiableOn_tprod_one_add hΩ hud htail
  refine ⟨h₀ * fun w ↦ ∏' n, (1 + u n w), hh₀.mul hprod, fun z hz ↦ ?_⟩
  rw [analyticOrderAt_mul (hh₀.analyticAt (hΩ.mem_nhds hz)) (hprod.analyticAt (hΩ.mem_nhds hz)),
    analyticOrderAt_tprod_one_add hΩ hud htail hz, hord₀ z hz]
  simp_rw [hone, fun n ↦ hord n z hz]
  exact ite_add_tsum_ite_sdiff_eq hΩ m hmemT hz

/-- The positive part of an integer divisor on an open set `Ω ⊆ ℂ` is the zero-order function of
some function analytic on `Ω`. -/
private theorem exists_analyticOnNhd_analyticOrderAt_eq_toNat (hΩ : IsOpen Ω)
    (D : Function.locallyFinsuppWithin Ω ℤ) : ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧
      ∀ z ∈ Ω, analyticOrderAt g z = ((D z).toNat : ℕ∞) := by
  obtain ⟨g, hg, hord⟩ := exists_holomorphic_with_zero_orders hΩ (D.mapRange Int.toNat rfl)
  exact ⟨g, hg.analyticOnNhd hΩ, fun z hz ↦ by
    rw [hord z hz, Function.locallyFinsuppWithin.mapRange_apply]⟩

/-- **Meromorphic functions with a prescribed divisor.** For every integer divisor `ν` on an open
set `Ω ⊆ ℂ`, that is, integer multiplicities supported on a subset closed and discrete in `Ω`,
some function meromorphic on `Ω` has divisor exactly `ν`, and its meromorphic order is finite at
every point of `Ω`, so it vanishes identically on no component of `Ω`. -/
theorem exists_meromorphic_with_divisor (hΩ : IsOpen Ω) (ν : Function.locallyFinsuppWithin Ω ℤ) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧ MeromorphicOn.divisor f Ω = ν ∧
      ∀ z ∈ Ω, meromorphicOrderAt f z ≠ ⊤ := by
  obtain ⟨g₁, hg₁, hord₁⟩ := exists_analyticOnNhd_analyticOrderAt_eq_toNat hΩ ν
  obtain ⟨g₂, hg₂, hord₂⟩ := exists_analyticOnNhd_analyticOrderAt_eq_toNat hΩ (-ν)
  have hne (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g Ω) (D : Function.locallyFinsuppWithin Ω ℤ)
      (hord : ∀ z ∈ Ω, analyticOrderAt g z = ((D z).toNat : ℕ∞)) :
      ∀ z ∈ Ω, meromorphicOrderAt g z ≠ ⊤ := fun z hz ↦ by
    simp [(hg z hz).meromorphicOrderAt_eq, hord z hz]
  have hne₁ := hne g₁ hg₁ ν hord₁
  have hne₂ := hne g₂ hg₂ (-ν) hord₂
  have hdiv (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g Ω) (D : Function.locallyFinsuppWithin Ω ℤ)
      (hord : ∀ z ∈ Ω, analyticOrderAt g z = ((D z).toNat : ℕ∞)) {z : ℂ} (hz : z ∈ Ω) :
      MeromorphicOn.divisor g Ω z = (D z).toNat := by
    rw [hg.meromorphicOn.divisor_eq_analyticOrderNatAt (hg z hz) hz, analyticOrderNatAt, hord z hz,
      ENat.toNat_natCast]
  refine ⟨g₁ * g₂⁻¹, hg₁.meromorphicOn.mul hg₂.meromorphicOn.inv, ?_, fun z hz ↦ ?_⟩
  · rw [MeromorphicOn.divisor_mul hg₁.meromorphicOn hg₂.meromorphicOn.inv hne₁
      (fun z hz ↦ by simpa [meromorphicOrderAt_inv] using hne₂ z hz), MeromorphicOn.divisor_inv]
    ext z
    by_cases hz : z ∈ Ω
    · simp [hdiv g₁ hg₁ ν hord₁ hz, hdiv g₂ hg₂ (-ν) hord₂ hz, ← sub_eq_add_neg]
    · simp [ν.apply_eq_zero_of_notMem hz, hz]
  · rw [meromorphicOrderAt_mul (hg₁ z hz).meromorphicAt (hg₂ z hz).meromorphicAt.inv,
      meromorphicOrderAt_inv]
    simpa using ⟨hne₁ z hz, hne₂ z hz⟩

/-- **Meromorphic functions are quotients of holomorphic functions.** Every function `F`
meromorphic on an open set `Ω ⊆ ℂ` agrees, off a subset closed and discrete in `Ω`, with a
quotient `f / g` of functions holomorphic on `Ω`. The denominator `g` has finite analytic order at
every point of `Ω`, so it vanishes identically on no component of `Ω`, even on components where
`F` vanishes identically. -/
theorem exists_holomorphic_quotient (hΩ : IsOpen Ω) {F : ℂ → ℂ} (hF : MeromorphicOn F Ω) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ DifferentiableOn ℂ g Ω ∧
      (∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤) ∧
      ∀ᶠ z in codiscreteWithin Ω, g z ≠ 0 ∧ F z = f z / g z := by
  -- The denominator `g` vanishes exactly at the poles of `F`, to the order of the pole.
  obtain ⟨g, hg, hord⟩ :=
    exists_analyticOnNhd_analyticOrderAt_eq_toNat hΩ (-MeromorphicOn.divisor F Ω)
  have hFg : MeromorphicOn (F * g) Ω := hF.mul hg.meromorphicOn
  have hnonneg (z : ℂ) (hz : z ∈ Ω) : 0 ≤ meromorphicOrderAt (F * g) z := by
    rw [meromorphicOrderAt_mul (hF z hz) (hg z hz).meromorphicAt,
      (hg z hz).meromorphicOrderAt_eq, hord z hz]
    cases h : meromorphicOrderAt F z with
    | top => simp
    | coe n =>
      have hn : MeromorphicOn.divisor F Ω z = n := by simp [hF, hz, h]
      simp only [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, hn, ENat.map_natCast]
      exact_mod_cast (by omega : 0 ≤ n + ((-n).toNat : ℤ))
  -- The product `F * g` has no poles, so its normal form on `Ω` is the analytic numerator.
  have hf : AnalyticOnNhd ℂ (toMeromorphicNFOn (F * g) Ω) Ω := fun z hz ↦
    (meromorphicNFOn_toMeromorphicNFOn (F * g) Ω hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [meromorphicOrderAt_toMeromorphicNFOn hFg hz]; exact hnonneg z hz)
  refine ⟨toMeromorphicNFOn (F * g) Ω, g, hf.differentiableOn, hg.differentiableOn,
    fun z hz ↦ by simp [hord z hz], ?_⟩
  have hΩmem : Ω ∈ codiscreteWithin Ω := by simp
  filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hFg,
    (MeromorphicOn.divisor F Ω).eq_zero_codiscreteWithin, hΩmem] with z hfz hDz hz
  have hgz : g z ≠ 0 := (hg z hz).analyticOrderAt_eq_zero.mp (by simp [hord z hz, hDz])
  refine ⟨hgz, ?_⟩
  rw [← hfz, Pi.mul_apply, mul_div_cancel_right₀ _ hgz]

end TauCeti
