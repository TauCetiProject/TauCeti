/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.List

/-!
# Asymptotic summation of weakly parameter-dependent symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aₖ` be weakly parameter-dependent
symbols of frequency orders `mₖ` and a common anisotropy `d` on an open set `R` of reciprocal
spectral parameters (`TauCeti.WeakParameterSymbol`). This file constructs an *asymptotic sum*: a
weakly parameter-dependent symbol `b` of order `m₀` such that for every `N` the remainder
`b - ∑_{k < N} aₖ` is a weakly parameter-dependent symbol of order `m_N`
(`TauCeti.WeakParameterSymbol.IsAsymptoticSum`, `TauCeti.WeakParameterSymbol.exists_asymptoticSum`).
So the `j`-th derivative of the remainder in the parameter `r` is a symbol of order `m_N + d j`,
with estimates uniform in `r ∈ R`. In particular, at each `r ∈ R` the parameter derivatives
`∂_r^j b(·, ·, r)` are asymptotic sums of the ordinary symbols `∂_r^j aₖ(·, ·, r)`
(`TauCeti.WeakParameterSymbol.IsAsymptoticSum.iteratedDerivSymbol`).

Asymptotic sums are what turns the formal parametrices of the weakly parametric calculus of Grubb
and Seeley, which are sequences of symbols of decreasing orders, into actual symbols, as
`TauCeti.Symbol.exists_asymptoticSum` does for ordinary symbols and
`TauCeti.ParameterSymbol.exists_asymptoticSum` for strongly parameter-dependent ones.

## The construction

As in Borel's theorem, the sum is `b = ∑ₖ χ(ξ / tₖ) aₖ` for a frequency cutoff `χ`
(`TauCeti.FrequencyCutoff`) and radii `tₖ → ∞`. The cutoffs depend on the frequency alone, so for
each `(x, ξ)` only finitely many terms are nonzero, whatever the parameter `r`: the sum is
holomorphic in `r` on `R`, and its derivatives in `r` are the sums of the cut-off derivatives
`χ(ξ / tₖ) ∂_r^j aₖ`. The radius `tₖ` is chosen so that for every `j ≤ k` these are at most `2^{-k}`
in the estimates of order `mₖ + d j + 1` for the derivatives of length at most `k` on the ball of
radius `k`, uniformly in `r ∈ R`. This is possible since the cut-off symbols satisfy the estimates
of order `mₖ + d j + 1` with constants `C / tₖ`, where `C` depends only on the uniform bounds for
`∂_r^j aₖ`. Since `mₖ + 1 ≤ m_N` for large `k`, the tail of the series is summable in the estimates
of order `m_N + d j`, uniformly in `r`. This adapts the construction of
`TauCeti.Symbol.exists_asymptoticSum`, run for all parameter derivatives at once with constants
uniform in the parameter.

## Main declarations

* `TauCeti.WeakParameterSymbol.IsAsymptoticSum`: `b` is an asymptotic sum of the symbols `aₖ`.
* `TauCeti.WeakParameterSymbol.exists_asymptoticSum`: every sequence of weakly parameter-dependent
  symbols of orders decreasing to `-∞` has an asymptotic sum.
* `WeakParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_forall_exists_coefficient_sub_eq`:
  asymptotic sums are unique up to weakly parameter-dependent symbols of every order.
* `TauCeti.WeakParameterSymbol.IsAsymptoticSum.iteratedDerivSymbol`: an asymptotic sum gives, at
  each parameter `r ∈ R` and for each `j`, an asymptotic sum of the `j`-th parameter derivatives.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
* G. Grubb and L. Hansen, *Complex powers of resolvents of pseudodifferential operators*,
  Comm. Partial Differential Equations 27 (2002), §2.
-/

public section

noncomputable section

open Set Filter Finset Metric
open scoped ContDiff Topology

namespace TauCeti

namespace WeakParameterSymbol

variable {n : ℕ} {R : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {d : ℝ}

/-! ### Families of symbols with uniform estimates -/

/-- **Cut-off families.** Let `F τ` be smooth functions satisfying the estimates of order `μ` on
`K`, uniformly in `τ`. Then the products `χ(ξ / t) F τ`, `t ≥ 1`, satisfy the estimates of every
order `μ + e`, `e ≥ 0`, with constants `C t^(-e)`, where `C` depends neither on `τ` nor on `t`. -/
private theorem exists_uniform_norm_mixedDeriv_cutoff_smul_le
    (χ : FrequencyCutoff (CoordinateSpace n)) {T : Type*} {μ e : ℝ} (he : 0 ≤ e)
    {F : T → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hF : ∀ τ, ContDiff ℝ ∞ (F τ))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hD : ∀ s s' : List (Fin n), ∃ D, 0 ≤ D ∧ ∀ τ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv s s' (F τ) x ξ‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ ((μ - s'.length) / 2))
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ τ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • F τ p) x ξ‖ ≤
        C * t ^ (-e) * (1 + ‖ξ‖ ^ 2) ^ ((e + μ - β.length) / 2) := by
  choose D _ hD using hD
  -- The dilated cutoffs satisfy the estimates of order `e` with constants `C t^(-e)`.
  choose Cc _ hCc using fun s s' : List (Fin n) =>
    (Symbol.const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0)
      |>.exists_norm_mixedDeriv_cutoff_smul_le χ hK s s'
  set S := (β.sublists'.revzip.map fun s' =>
    (α.sublists'.revzip.map fun s => Cc s.1 s'.1 * D s.2 s'.2).sum).sum
  refine ⟨max S 0, le_max_right _ _, fun t ht τ x hx ξ => ?_⟩
  have hfun : (fun p => χ (t⁻¹ • p.2) • F τ p) = fun p =>
      (χ (t⁻¹ • p.2) •
        (Symbol.const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).coefficient p).comp (F τ p) :=
    funext fun p => by simp
  have h := Symbol.norm_mixedDeriv_comp_le (m' := e) (m := μ)
    ((Symbol.const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).contDiff_cutoff_smul_coefficient
      χ t) (hF τ) (C := fun s s' => t ^ (-e) * Cc s s') (D := D)
    (fun s s' => by
      have h := hCc s s' t ht e he x hx ξ
      rwa [zero_sub, mul_comm (Cc s s')] at h)
    (fun s s' => hD s s' τ x hx ξ) α β
  have hsum : (β.sublists'.revzip.map fun s' => (α.sublists'.revzip.map fun s =>
      t ^ (-e) * Cc s.1 s'.1 * D s.2 s'.2).sum).sum = t ^ (-e) * S := by
    simp only [S, mul_assoc, List.sum_map_mul_left]
  rw [hfun]
  refine h.trans (le_of_eq_of_le (by rw [hsum]) ?_)
  calc t ^ (-e) * S * (1 + ‖ξ‖ ^ 2) ^ ((e + μ - β.length) / 2)
      ≤ t ^ (-e) * max S 0 * (1 + ‖ξ‖ ^ 2) ^ ((e + μ - β.length) / 2) := by
        gcongr
        exact le_max_left _ _
    _ = _ := by ring

/-- **Composed families.** Let `F τ` be smooth functions satisfying the estimates of order `μ` on
the compact set `K`, uniformly in `τ`, and let `b` be a symbol of order `e`. Then the compositions
`b ∘ F τ` satisfy the estimates of order `e + μ` on `K`, uniformly in `τ`. -/
private theorem exists_uniform_norm_mixedDeriv_comp_le {T : Type*} {μ e : ℝ}
    (b : Symbol n W W e) {F : T → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hF : ∀ τ, ContDiff ℝ ∞ (F τ)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hD : ∀ s s' : List (Fin n), ∃ D, 0 ≤ D ∧ ∀ τ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv s s' (F τ) x ξ‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ ((μ - s'.length) / 2))
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ τ, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => (b.coefficient p).comp (F τ p)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((e + μ - β.length) / 2) := by
  choose D _ hD using hD
  choose Cb _ hCb using b.exists_bound K hK
  set S := (β.sublists'.revzip.map fun s' =>
    (α.sublists'.revzip.map fun s => Cb s.1 s'.1 * D s.2 s'.2).sum).sum
  refine ⟨max S 0, le_max_right _ _, fun τ x hx ξ => ?_⟩
  refine (Symbol.norm_mixedDeriv_comp_le b.contDiff_coefficient (hF τ) (C := Cb) (D := D)
    (fun s s' => hCb s s' x hx ξ) (fun s s' => hD s s' τ x hx ξ) α β).trans ?_
  gcongr
  exact le_max_left _ _

/-- The `i`-th parameter derivatives of `a` satisfy the estimates of order `m₀ + d i` on the
compact set `K`, uniformly in `r ∈ R`. -/
private theorem exists_uniform_bound_iteratedDeriv {m₀ : ℝ} (a : WeakParameterSymbol n R V W d m₀)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (i : ℕ) (s s' : List (Fin n)) :
    ∃ D, 0 ≤ D ∧ ∀ r : R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv s s' (fun p => iteratedDeriv i (a.coefficient p) r) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((m₀ + d * i - s'.length) / 2) := by
  obtain ⟨D, hD0, hD⟩ := a.exists_bound K hK i s s'
  exact ⟨D, hD0, fun r x hx ξ => hD x hx ξ r r.property⟩

/-! ### The Borel sum -/

variable {m : ℕ → ℝ}

/-- The Borel sum `∑ₖ χ(ξ / tₖ) aₖ(x, ξ, r)` of a sequence of weakly parameter-dependent symbols
with cutoff radii `tₖ`, minus its first `N` terms `∑_{k < N} aₖ(x, ξ, r)`. -/
private def borelRemainder (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℕ → ℝ)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) : V →L[ℂ] W :=
  (∑ᶠ k, χ ((t k)⁻¹ • p.2) • (a k).coefficient p r) - ∑ k ∈ range N, (a k).coefficient p r

/-- With radii `tₖ ≥ k + 1`, only the terms with `k < J` of the Borel sum can be nonzero at
frequencies `‖ξ‖ < J`, whatever the parameter. -/
private theorem borelRemainder_eq_sum (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ}
    (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k) (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (N : ℕ)
    {J : ℕ} {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖p.2‖ < J) :
    borelRemainder χ t a N p = fun r =>
      ∑ k ∈ range J, χ ((t k)⁻¹ • p.2) • (a k).coefficient p r -
        ∑ k ∈ range N, (a k).coefficient p r := by
  funext r
  rw [borelRemainder]
  congr 1
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  rw [coe_range, Set.mem_Iio]
  by_contra hkJ
  have hJk : (J : ℝ) ≤ k := by exact_mod_cast not_lt.1 hkJ
  have htk : 0 < t k := by linarith [ht k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact hk (by simp only [χ.apply_inv_smul_eq_zero htk (by linarith [ht k]), zero_smul])

/-- The `i`-th parameter derivative of the Borel remainder at `r ∈ R` is the Borel remainder of
the `i`-th parameter derivatives. -/
private theorem iteratedDeriv_borelRemainder (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k) (a : ∀ k, WeakParameterSymbol n R V W d (m k))
    (N : ℕ) {J : ℕ} {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖p.2‖ < J) (i : ℕ)
    {r : ℂ} (hr : r ∈ R) :
    iteratedDeriv i (borelRemainder χ t a N p) r =
      ∑ k ∈ range J, χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r -
        ∑ k ∈ range N, iteratedDeriv i ((a k).coefficient p) r := by
  rw [borelRemainder_eq_sum χ ht a N hp,
    iteratedDeriv_fun_sub
      (ContDiffAt.sum fun k _ => ((a k).contDiffAt_coefficient p hr).const_smul _)
      (ContDiffAt.sum fun k _ => (a k).contDiffAt_coefficient p hr),
    iteratedDeriv_fun_sum fun k _ => ((a k).contDiffAt_coefficient p hr).const_smul _,
    iteratedDeriv_fun_sum fun k _ => (a k).contDiffAt_coefficient p hr]
  congr 1
  exact Finset.sum_congr rfl fun k _ =>
    iteratedDeriv_fun_const_smul ((a k).contDiffAt_coefficient p hr) _

/-- The Borel remainder is holomorphic in the parameter on `R`. -/
private theorem contDiffOn_borelRemainder (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k) (a : ∀ k, WeakParameterSymbol n R V W d (m k))
    (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    ContDiffOn ℂ ∞ (borelRemainder χ t a N p) R := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖p.2‖
  rw [borelRemainder_eq_sum χ ht a N hJ]
  exact (ContDiffOn.sum fun k _ => ((a k).contDiffOn_coefficient p).const_smul _).sub
    (ContDiffOn.sum fun k _ => (a k).contDiffOn_coefficient p)

/-- The Borel remainder vanishes for parameters outside `R`. -/
private theorem borelRemainder_of_notMem (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℕ → ℝ)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∉ R) :
    borelRemainder χ t a N p r = 0 := by
  simp [borelRemainder, (a _).coefficient_of_notMem p r hr]

/-- The parameter derivatives of the Borel remainder are smooth in the position and the frequency,
since near each point they are finite sums of smooth terms. -/
private theorem contDiff_iteratedDeriv_borelRemainder (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k) (a : ∀ k, WeakParameterSymbol n R V W d (m k))
    (N i : ℕ) {r : ℂ} (hr : r ∈ R) :
    ContDiff ℝ ∞ fun p => iteratedDeriv i (borelRemainder χ t a N p) r := by
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖p₀.2‖
  have hs : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n =>
      ∑ k ∈ range J, χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r -
        ∑ k ∈ range N, iteratedDeriv i ((a k).coefficient p) r :=
    (ContDiff.sum fun k _ => ((χ.contDiff (n := ⊤)).comp
      (contDiff_snd.const_smul (t k)⁻¹)).smul ((a k).contDiff_iteratedDeriv i r hr)).sub
      (ContDiff.sum fun k _ => (a k).contDiff_iteratedDeriv i r hr)
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hJ] with p hp
  exact iteratedDeriv_borelRemainder χ ht a N hp i hr

/-- For each `k` there is a radius `t ≥ k + 1` making the cut-off parameter derivatives
`χ(ξ / t) ∂_r^i aₖ`, `i ≤ k`, at most `2^{-k}` in the estimates of order `mₖ + d i + 1` for the
derivatives of length at most `k` on the ball of radius `k`, uniformly in `r ∈ R`. -/
private theorem exists_radius (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (k : ℕ) :
    ∃ t : ℝ, (k : ℝ) + 1 ≤ t ∧ ∀ i ≤ k, ∀ α β : List (Fin n), α.length ≤ k → β.length ≤ k →
      ∀ r ∈ R, ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ‖ ≤
          (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2) := by
  have key (i : ℕ) (α β : List (Fin n)) : ∀ᶠ t : ℝ in atTop, ∀ r ∈ R,
      ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ‖ ≤
          (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2) := by
    obtain ⟨C, -, hC⟩ := exists_uniform_norm_mixedDeriv_cutoff_smul_le χ zero_le_one
      (fun r : R => (a k).contDiff_iteratedDeriv i r r.property) (isCompact_closedBall 0 k)
      ((a k).exists_uniform_bound_iteratedDeriv (isCompact_closedBall 0 k) i) α β
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (C * 2 ^ k)]
      with t ht1 htC r hr x hx ξ
    have ht0 : 0 < t := one_pos.trans_le ht1
    have h := hC t ht1 ⟨r, hr⟩ x hx ξ
    rw [add_comm (1 : ℝ) (m k + d * i)] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ ht0]
    calc C = (1 / 2) ^ k * (C * 2 ^ k) := by
          rw [one_div, inv_pow]
          field_simp
      _ ≤ (1 / 2) ^ k * t := by gcongr
  have hfin : ∀ᶠ t : ℝ in atTop, ∀ i ∈ range (k + 1), ∀ α ∈ {l : List (Fin n) | l.length ≤ k},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ k}, ∀ r ∈ R,
        ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
          ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r)
            x ξ‖ ≤ (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2) := by
    rw [eventually_all_finset]
    intro i _
    rw [eventually_all_finite (List.finite_length_le _ k)]
    intro α _
    rw [eventually_all_finite (List.finite_length_le _ k)]
    intro β _
    exact key i α β
  obtain ⟨t, ht, ht'⟩ := ((eventually_ge_atTop ((k : ℝ) + 1)).and hfin).exists
  exact ⟨t, ht, fun i hi α β hα hβ => ht' i (mem_range.2 (Nat.lt_succ_of_le hi)) α hα β hβ⟩

/-- Radii `tₖ` for which the cut-off parameter derivatives `χ(ξ / tₖ) ∂_r^i aₖ`, `i ≤ k`, are at
most `2^{-k}` in the estimates of order `mₖ + d i + 1` for the derivatives of length at most `k` on
the ball of radius `k`, uniformly in `r ∈ R`. Such radii exist for every sequence `aₖ`. -/
private abbrev IsSmallCutoff (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (t : ℕ → ℝ) : Prop :=
  ∀ k, ∀ i ≤ k, ∀ α β : List (Fin n), α.length ≤ k → β.length ≤ k →
    ∀ r ∈ R, ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r)
        x ξ‖ ≤ (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2)

/-- Near `(x, ξ)` with `‖ξ‖ < J`, the `i`-th parameter derivative of the Borel remainder
`b - ∑_{k < N} aₖ` splits into the removed cutoffs `(χ(ξ / tₖ) - 1) ∂_r^i aₖ`, `k < N`, and the
cut-off terms `χ(ξ / tₖ) ∂_r^i aₖ` with `N ≤ k < j₁` and with `j₁ ≤ k < J`; so do its mixed
derivatives at `(x, ξ)`. -/
private theorem mixedDeriv_iteratedDeriv_borelRemainder (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k) (a : ∀ k, WeakParameterSymbol n R V W d (m k))
    {N j₁ J : ℕ} (hNj₁ : N ≤ j₁) (hj₁J : j₁ ≤ J) (i : ℕ) {r : ℂ} (hr : r ∈ R)
    (α β : List (Fin n)) (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ‖ξ‖ < J) :
    mixedDeriv α β (fun p => iteratedDeriv i (borelRemainder χ t a N p) r) x ξ =
      ∑ k ∈ range N, mixedDeriv α β
          ((fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) -
            fun p => iteratedDeriv i ((a k).coefficient p) r) x ξ +
        (∑ k ∈ Ico N j₁, mixedDeriv α β
            (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ +
          ∑ k ∈ Ico j₁ J, mixedDeriv α β
            (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ) := by
  set g : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun k p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r
  set h : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun k p => iteratedDeriv i ((a k).coefficient p) r
  have hg : ∀ k, ContDiff ℝ ∞ (g k) := fun k => ((χ.contDiff (n := ⊤)).comp
    (contDiff_snd.const_smul (t k)⁻¹)).smul ((a k).contDiff_iteratedDeriv i r hr)
  have hh : ∀ k, ContDiff ℝ ∞ (h k) := fun k => (a k).contDiff_iteratedDeriv i r hr
  have heq : (fun p => iteratedDeriv i (borelRemainder χ t a N p) r) =ᶠ[𝓝 (x, ξ)]
      ∑ k ∈ range N, (g k - h k) + (∑ k ∈ Ico N j₁, g k + ∑ k ∈ Ico j₁ J, g k) := by
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds
      (hξ : ‖(x, ξ).2‖ < J)] with p hp
    rw [iteratedDeriv_borelRemainder χ ht a N hp i hr, sum_Ico_consecutive _ hNj₁ hj₁J,
      ← sum_range_add_sum_Ico _ (hNj₁.trans hj₁J), sum_sub_distrib]
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, g, h]
    abel
  have hs₁ : ContDiff ℝ ∞ (∑ k ∈ range N, (g k - h k)) := by
    simpa only [Finset.sum_fn, Pi.sub_apply] using ContDiff.sum fun k _ => (hg k).sub (hh k)
  have hs₂ : ContDiff ℝ ∞ (∑ k ∈ Ico N j₁, g k) := by
    simpa only [Finset.sum_fn] using ContDiff.sum fun k _ => hg k
  have hs₃ : ContDiff ℝ ∞ (∑ k ∈ Ico j₁ J, g k) := by
    simpa only [Finset.sum_fn] using ContDiff.sum fun k _ => hg k
  have hs₂₃ : ContDiff ℝ ∞ (∑ k ∈ Ico N j₁, g k + ∑ k ∈ Ico j₁ J, g k) := hs₂.add hs₃
  rw [heq.mixedDeriv_eq, mixedDeriv_add hs₁ hs₂₃, mixedDeriv_add hs₂ hs₃,
    mixedDeriv_sum (f := fun k => g k - h k) (fun k _ => (hg k).sub (hh k)),
    mixedDeriv_sum (fun k _ => hg k), mixedDeriv_sum (fun k _ => hg k)]

/-- The removed cutoffs `(χ(ξ / t) - 1) ∂_r^i a` vanish for `‖ξ‖ ≥ 2 t`, so they satisfy the
estimates of every order `μ`, uniformly in `r ∈ R`. -/
private theorem exists_norm_mixedDeriv_cutoff_smul_sub_le (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℝ} (ht : 1 ≤ t) {m₀ : ℝ} (a : WeakParameterSymbol n R V W d m₀) (i : ℕ) (μ : ℝ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ D, 0 ≤ D ∧ ∀ r ∈ R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β ((fun p => χ (t⁻¹ • p.2) • iteratedDeriv i (a.coefficient p) r) -
        fun p => iteratedDeriv i (a.coefficient p) r) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
  -- `(χ(ξ / t) - 1) ∂_r^i a` is the composition with a symbol of order `μ - (m₀ + d i)`.
  let e : Symbol n W W (μ - (m₀ + d * i)) := Symbol.ofBoundedFrequencySupport
    (fun p => (χ (t⁻¹ • p.2) - 1) • ContinuousLinearMap.id ℂ W)
    ((((χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)).sub contDiff_const).smul
      contDiff_const) (2 * t) fun x ξ hξ => by
        simp [χ.apply_inv_smul_eq_one (one_pos.trans_le ht) hξ]
  obtain ⟨D, hD0, hD⟩ := exists_uniform_norm_mixedDeriv_comp_le e
    (fun r : R => a.contDiff_iteratedDeriv i r r.property) hK
    (a.exists_uniform_bound_iteratedDeriv hK i) α β
  refine ⟨D, hD0, fun r hr x hx ξ => ?_⟩
  have hfun : ((fun p => χ (t⁻¹ • p.2) • iteratedDeriv i (a.coefficient p) r) -
      fun p => iteratedDeriv i (a.coefficient p) r) =
        fun p => (e.coefficient p).comp (iteratedDeriv i (a.coefficient p) r) := by
    funext p
    simp [e, sub_smul]
  have h := hD ⟨r, hr⟩ x hx ξ
  rwa [sub_add_cancel, ← hfun] at h

/-- Given orders `mₖ → -∞`, `N`, `i`, a compact set `K` and words `α`, `β`, there is `j₁ ≥ N`
such that, for radii making the cut-off parameter derivatives small, the cut-off terms
`χ(ξ / tₖ) ∂_r^i aₖ` with `k ≥ j₁` are at most `2^{-k}` in the estimate of order `m_N + d i` for
`∂_x^α ∂_ξ^β` on `K`, uniformly in `r ∈ R`. -/
private theorem exists_forall_ge_norm_mixedDeriv_le (χ : FrequencyCutoff (CoordinateSpace n))
    (hm' : Tendsto m atTop atBot) (a : ∀ k, WeakParameterSymbol n R V W d (m k)) {t : ℕ → ℝ}
    (hsmall : IsSmallCutoff χ a t) (N i : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ j₁, N ≤ j₁ ∧ ∀ k, j₁ ≤ k → ∀ r ∈ R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r)
        x ξ‖ ≤ (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m N + d * i - β.length) / 2) := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hm'.eventually (eventually_le_atBot (m N - 1)))
  refine ⟨max (max N j₀) (max (max i ⌈ρ⌉₊) (max α.length β.length)),
    le_max_of_le_left (le_max_left _ _), fun k hk r hr x hx ξ => ?_⟩
  have hxk : x ∈ closedBall (0 : CoordinateSpace n) k := closedBall_subset_closedBall
    ((Nat.le_ceil ρ).trans (by exact_mod_cast (show ⌈ρ⌉₊ ≤ k by omega))) (hρ hx)
  refine (hsmall k i (by omega) α β (by omega) (by omega) r hr x hxk ξ).trans
    (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_) (by positivity))
  linarith [hj₀ k (by omega)]

/-- **The remainder estimates.** For radii making the cut-off parameter derivatives small, the
`i`-th parameter derivative of the Borel remainder `b - ∑_{k < N} aₖ` satisfies the estimates of
order `m_N + d i`, uniformly in `r ∈ R`. Near `(x, ξ)` it splits into the removed cutoffs
`(χ(ξ / tₖ) - 1) ∂_r^i aₖ`, `k < N`, which vanish at large frequencies, the finitely many cut-off
terms with `N ≤ k < j₁`, of orders `mₖ + d i ≤ m_N + d i`, and the cut-off terms with `k ≥ j₁`,
whose bounds `2^{-k}` sum to at most `2`. -/
private theorem exists_norm_mixedDeriv_iteratedDeriv_borelRemainder_le
    (χ : FrequencyCutoff (CoordinateSpace n)) (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k)
    (hsmall : IsSmallCutoff χ a t) (N i : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ r ∈ R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => iteratedDeriv i (borelRemainder χ t a N p) r) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m N + d * i - β.length) / 2) := by
  have ht1 : ∀ k, 1 ≤ t k := fun k => by linarith [ht k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  choose D₁ hD₁0 hD₁ using fun k => exists_norm_mixedDeriv_cutoff_smul_sub_le χ (ht1 k) (a k) i
    (m N + d * i) hK α β
  -- The cut-off terms satisfy the estimates of the orders `mₖ + d i`, uniformly in `r ∈ R`.
  choose D₂ hD₂0 hD₂ using fun k => exists_uniform_norm_mixedDeriv_cutoff_smul_le χ le_rfl
    (fun r : R => (a k).contDiff_iteratedDeriv i r r.property) hK
    ((a k).exists_uniform_bound_iteratedDeriv hK i) α β
  obtain ⟨j₁, hNj₁, htail⟩ := exists_forall_ge_norm_mixedDeriv_le χ hm' a hsmall N i hK α β
  refine ⟨∑ k ∈ range N, D₁ k + ∑ k ∈ range j₁, D₂ k + 2, by
    have := Finset.sum_nonneg fun k (_ : k ∈ range N) => hD₁0 k
    have := Finset.sum_nonneg fun k (_ : k ∈ range j₁) => hD₂0 k
    linarith, fun r hr x hx ξ => ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m N + d * i - β.length) / 2)
  have hw0 : 0 ≤ w := by positivity
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt ‖ξ‖
  rw [mixedDeriv_iteratedDeriv_borelRemainder χ ht a hNj₁ (le_max_right J₀ j₁) i hr α β x
    (hJ₀.trans_le (by exact_mod_cast le_max_left J₀ j₁))]
  -- The finitely many terms with `N ≤ k < j₁` have orders `mₖ + d i ≤ m_N + d i`.
  have h2 : ∑ k ∈ Ico N j₁, ‖mixedDeriv α β
      (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ‖ ≤
        ∑ k ∈ range j₁, D₂ k * w := by
    refine (Finset.sum_le_sum fun k hk => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => mem_range.2 (Finset.mem_Ico.1 hk).2) fun k _ _ => mul_nonneg (hD₂0 k) hw0)
    have hk' := hD₂ k (t k) (ht1 k) ⟨r, hr⟩ x hx ξ
    rw [neg_zero, Real.rpow_zero, mul_one, zero_add] at hk'
    refine hk'.trans (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_) (hD₂0 k))
    linarith [hm (Finset.mem_Ico.1 hk).1]
  -- The tail: the `k`-th term is at most `2^{-k}`, and these bounds sum to at most `2`.
  have h3 : ∑ k ∈ Ico j₁ (max J₀ j₁), ‖mixedDeriv α β
      (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ‖ ≤ 2 * w := by
    refine (Finset.sum_le_sum fun k hk => htail k (Finset.mem_Ico.1 hk).1 r hr x hx ξ).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => mem_range.2 (Finset.mem_Ico.1 hk).2) fun k _ _ => by positivity).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw0
  refine (norm_add_le _ _).trans ((add_le_add ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k _ => hD₁ k r hr x hx ξ))
    ((norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans h2)
      ((norm_sum_le _ _).trans h3)))).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The Borel remainder `b - ∑_{k < N} aₖ` as a weakly parameter-dependent symbol of order `m_N`,
for radii making the cut-off parameter derivatives small. -/
private def borelRemainderSymbol (χ : FrequencyCutoff (CoordinateSpace n)) (hm : Antitone m)
    (hm' : Tendsto m atTop atBot) (a : ∀ k, WeakParameterSymbol n R V W d (m k)) {t : ℕ → ℝ}
    (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k)
    (hsmall : IsSmallCutoff χ a t) (N : ℕ) : WeakParameterSymbol n R V W d (m N) :=
  ofIteratedDerivSymbol (borelRemainder χ t a N) (contDiffOn_borelRemainder χ ht a N)
    (fun p _ hr => borelRemainder_of_notMem χ t a N p hr)
    (fun i r hr =>
      { coefficient := fun p => iteratedDeriv i (borelRemainder χ t a N p) r
        contDiff_coefficient := contDiff_iteratedDeriv_borelRemainder χ ht a N i hr
        exists_bound := fun K hK α β =>
          (exists_norm_mixedDeriv_iteratedDeriv_borelRemainder_le χ hm hm' a ht hsmall N i hK α
            β).imp fun _ hC => ⟨hC.1, fun x hx ξ => hC.2 r hr x hx ξ⟩ })
    (fun _ _ _ _ => rfl)
    (fun i K α β => by
      obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_iteratedDeriv_borelRemainder_le χ hm hm' a ht
        hsmall N i K.isCompact α β
      exact ⟨C, fun r hr => Symbol.seminorm_le_bound K α β _ hC0 (hC r hr)⟩)

private theorem coefficient_borelRemainderSymbol (χ : FrequencyCutoff (CoordinateSpace n))
    (hm : Antitone m) (hm' : Tendsto m atTop atBot) (a : ∀ k, WeakParameterSymbol n R V W d (m k))
    {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k)
    (hsmall : IsSmallCutoff χ a t) (N : ℕ) :
    (borelRemainderSymbol χ hm hm' a ht hsmall N).coefficient = borelRemainder χ t a N := by
  rw [borelRemainderSymbol, coefficient_ofIteratedDerivSymbol]

/-! ### Asymptotic sums -/

/-- A weakly parameter-dependent symbol `b` of order `m₀` is an *asymptotic sum* `b ∼ ∑ₖ aₖ` of
weakly parameter-dependent symbols `aₖ` of orders `mₖ`, all of anisotropy `d`, if for every `N`
the remainder `b - ∑_{k < N} aₖ` is a weakly parameter-dependent symbol of order `m_N`. -/
def IsAsymptoticSum (b : WeakParameterSymbol n R V W d (m 0))
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) : Prop :=
  ∀ N, ∃ c : WeakParameterSymbol n R V W d (m N),
    b.coefficient - ∑ k ∈ range N, (a k).coefficient = c.coefficient

theorem isAsymptoticSum_iff {b : WeakParameterSymbol n R V W d (m 0)}
    {a : ∀ k, WeakParameterSymbol n R V W d (m k)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ c : WeakParameterSymbol n R V W d (m N),
      b.coefficient - ∑ k ∈ range N, (a k).coefficient = c.coefficient :=
  Iff.rfl

/-- **Uniqueness of asymptotic sums.** If `b` is an asymptotic sum of symbols `aₖ` whose orders
tend to `-∞`, then `b'` is one exactly when `b' - b` is a weakly parameter-dependent symbol of every
order `μ`. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_forall_exists_coefficient_sub_eq
    (hm' : Tendsto m atTop atBot) {a : ∀ k, WeakParameterSymbol n R V W d (m k)}
    {b b' : WeakParameterSymbol n R V W d (m 0)} (hb : b.IsAsymptoticSum a) :
    b'.IsAsymptoticSum a ↔ ∀ μ : ℝ, ∃ c : WeakParameterSymbol n R V W d μ,
      b'.coefficient - b.coefficient = c.coefficient := by
  refine ⟨fun hb' μ => ?_, fun h N => ?_⟩
  · obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot μ)).exists
    obtain ⟨c, hc⟩ := hb N
    obtain ⟨c', hc'⟩ := hb' N
    refine ⟨inclusion hN le_rfl (c' - c), ?_⟩
    rw [coefficient_inclusion, coefficient_sub, ← hc, ← hc']
    abel
  · obtain ⟨c, hc⟩ := hb N
    obtain ⟨e, he⟩ := h (m N)
    refine ⟨e + c, ?_⟩
    rw [coefficient_add, ← he, ← hc]
    abel

/-- **Asymptotic summation of weakly parameter-dependent symbols** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be
real orders tending to `-∞`, and let `aₖ` be weakly parameter-dependent symbols of orders `mₖ` and
anisotropy `d` on `R`. Then there is a weakly parameter-dependent symbol `b` of order `m₀` such
that for every `N` the remainder `b - ∑_{k < N} aₖ` is a weakly parameter-dependent symbol of
order `m_N`: its `j`-th derivative in the parameter satisfies the estimates of order `m_N + d j`,
uniformly in `r ∈ R`. -/
theorem exists_asymptoticSum (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) :
    ∃ b : WeakParameterSymbol n R V W d (m 0), b.IsAsymptoticSum a := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  choose t ht hsmall using exists_radius χ a
  refine ⟨borelRemainderSymbol χ hm hm' a ht hsmall 0, fun N =>
    ⟨borelRemainderSymbol χ hm hm' a ht hsmall N, ?_⟩⟩
  funext p r
  simp [coefficient_borelRemainderSymbol, borelRemainder]

/-- **Parameter derivatives of asymptotic sums.** If `b ∼ ∑ₖ aₖ`, then at every parameter `r ∈ R`
the `j`-th parameter derivative `∂_r^j b(·, ·, r)`, a symbol of order `m₀ + d j`, is an asymptotic
sum of the `j`-th parameter derivatives `∂_r^j aₖ(·, ·, r)`, of orders `mₖ + d j`. -/
theorem IsAsymptoticSum.iteratedDerivSymbol {b : WeakParameterSymbol n R V W d (m 0)}
    {a : ∀ k, WeakParameterSymbol n R V W d (m k)} (h : b.IsAsymptoticSum a) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) :
    Symbol.IsAsymptoticSum (m := fun k => m k + d * j) (b.iteratedDerivSymbol j hr)
      fun k => (a k).iteratedDerivSymbol j hr := by
  refine Symbol.isAsymptoticSum_iff.2 fun N => ?_
  obtain ⟨c, hc⟩ := h N
  refine ⟨c.iteratedDerivSymbol j hr, funext fun p => ?_⟩
  have hcp : c.coefficient p = fun r => b.coefficient p r - ∑ k ∈ range N, (a k).coefficient p r :=
    funext fun r => by simp [← hc]
  simp only [Pi.sub_apply, Finset.sum_apply, coefficient_iteratedDerivSymbol, hcp]
  rw [iteratedDeriv_fun_sub (b.contDiffAt_coefficient p hr)
      (ContDiffAt.sum fun k _ => (a k).contDiffAt_coefficient p hr),
    iteratedDeriv_fun_sum fun k _ => (a k).contDiffAt_coefficient p hr]

end WeakParameterSymbol

end TauCeti
