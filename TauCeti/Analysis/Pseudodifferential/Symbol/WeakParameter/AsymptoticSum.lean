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
of order `m_N + d j`, uniformly in `r`. At each `r ∈ R` the `j`-th parameter derivative of the
remainder is the remainder of the Borel sum `TauCeti.Symbol.borelSum` of the symbols
`∂_r^j aₖ(·, ·, r)`, so these estimates are those of the construction of
`TauCeti.Symbol.exists_asymptoticSum` for the families `r ↦ ∂_r^j aₖ(·, ·, r)` over `R`
(`TauCeti.Symbol.exists_norm_mixedDeriv_borelSum_sub_le_of_forall`).

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
        ∑ k ∈ range N, (a k).coefficient p r :=
  funext fun r => by rw [borelRemainder, Symbol.finsum_cutoff_smul_eq_sum χ ht _ hp]

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

/-- At `r ∈ R`, the `i`-th parameter derivative of the Borel remainder is the remainder after `N`
terms of the Borel sum (`TauCeti.Symbol.borelSum`) of the symbols `∂_r^i aₖ(·, ·, r)`. -/
private theorem iteratedDeriv_borelRemainder_eq_borelSum_sub
    (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (N i : ℕ) {r : ℂ} (hr : r ∈ R) :
    (fun p => iteratedDeriv i (borelRemainder χ t a N p) r) =
      Symbol.borelSum χ t (fun k => (a k).iteratedDerivSymbol i hr) -
        ∑ k ∈ range N, ((a k).iteratedDerivSymbol i hr).coefficient := by
  funext p
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖p.2‖
  rw [iteratedDeriv_borelRemainder χ ht a N hJ i hr, Pi.sub_apply,
    Symbol.borelSum_eq_sum χ ht _ hJ, Finset.sum_apply]
  simp only [coefficient_iteratedDerivSymbol]

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
  rw [iteratedDeriv_borelRemainder_eq_borelSum_sub χ ht a N i hr]
  exact (Symbol.contDiff_borelSum χ ht _).sub (Symbol.contDiff_sum_coefficient _ _)

/-- For each `k` there is a radius `t ≥ k + 1` making the cut-off parameter derivatives
`χ(ξ / t) ∂_r^i aₖ`, `i ≤ k`, at most `2^{-k}` in the estimates of order `mₖ + d i + 1` for the
derivatives of length at most `k` on the ball of radius `k`, uniformly in `r ∈ R`. -/
private theorem exists_radius (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (k : ℕ) :
    ∃ t : ℝ, (k : ℝ) + 1 ≤ t ∧ ∀ i ≤ k, ∀ α β : List (Fin n), α.length ≤ k → β.length ≤ k →
      ∀ r ∈ R, ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r) x ξ‖ ≤
          (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2) := by
  have hfin : ∀ᶠ t : ℝ in atTop, ∀ i ∈ range (k + 1), ∀ α ∈ {l : List (Fin n) | l.length ≤ k},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ k}, ∀ r : R,
        ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
          ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r)
            x ξ‖ ≤ (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2) := by
    rw [eventually_all_finset]
    intro i _
    simpa only [coefficient_iteratedDerivSymbol] using
      Symbol.eventually_norm_mixedDeriv_cutoff_smul_le_of_forall χ
        (fun r : R => (a k).iteratedDerivSymbol i r.property) k
        ((a k).exists_bound_iteratedDerivSymbol i (isCompact_closedBall 0 k))
  obtain ⟨t, ht, ht'⟩ := ((eventually_ge_atTop ((k : ℝ) + 1)).and hfin).exists
  exact ⟨t, ht, fun i hi α β hα hβ r hr =>
    ht' i (mem_range.2 (Nat.lt_succ_of_le hi)) α hα β hβ ⟨r, hr⟩⟩

/-- Radii `tₖ` for which the cut-off parameter derivatives `χ(ξ / tₖ) ∂_r^i aₖ`, `i ≤ k`, are at
most `2^{-k}` in the estimates of order `mₖ + d i + 1` for the derivatives of length at most `k` on
the ball of radius `k`, uniformly in `r ∈ R`. Such radii exist for every sequence `aₖ`. -/
private abbrev IsSmallCutoff (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) (t : ℕ → ℝ) : Prop :=
  ∀ k, ∀ i ≤ k, ∀ α β : List (Fin n), α.length ≤ k → β.length ≤ k →
    ∀ r ∈ R, ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ ((t k)⁻¹ • p.2) • iteratedDeriv i ((a k).coefficient p) r)
        x ξ‖ ≤ (1 / 2) ^ k * (1 + ‖ξ‖ ^ 2) ^ ((m k + d * i + 1 - β.length) / 2)

/-- **The remainder estimates.** For radii making the cut-off parameter derivatives small, the
`i`-th parameter derivative of the Borel remainder `b - ∑_{k < N} aₖ` satisfies the estimates of
order `m_N + d i`, uniformly in `r ∈ R`. At each `r` it is the remainder of the Borel sum of the
symbols `∂_r^i aₖ(·, ·, r)` of orders `mₖ + d i`, whose estimates hold uniformly in `r`; so this is
`TauCeti.Symbol.exists_norm_mixedDeriv_borelSum_sub_le_of_forall` for the family over `R`. The
cut-off terms are known to be small only on the balls of radius `k` with `k ≥ i`. -/
private theorem exists_norm_mixedDeriv_iteratedDeriv_borelRemainder_le
    (χ : FrequencyCutoff (CoordinateSpace n)) (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ k, WeakParameterSymbol n R V W d (m k)) {t : ℕ → ℝ} (ht : ∀ k : ℕ, (k : ℝ) + 1 ≤ t k)
    (hsmall : IsSmallCutoff χ a t) (N i : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ r ∈ R, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => iteratedDeriv i (borelRemainder χ t a N p) r) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m N + d * i - β.length) / 2) := by
  have ht1 : ∀ k, 1 ≤ t k := fun k => by linarith [ht k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨C, hC0, hC⟩ := Symbol.exists_norm_mixedDeriv_borelSum_sub_le_of_forall χ
    (m := fun k => m k + d * i) (hm.add_const _)
    (tendsto_atBot_add_const_right _ _ hm')
    (fun (r : R) k => (a k).iteratedDerivSymbol i r.property) ht
    (S := fun k => if i ≤ k then closedBall 0 k else ∅)
    (fun r k α hα β hβ x hx ξ => by
      split_ifs at hx with hik
      · simpa only [coefficient_iteratedDerivSymbol] using
          hsmall k i hik α β hα hβ r r.property x hx ξ
      · exact absurd hx (notMem_empty x))
    N (by
      filter_upwards [eventually_ge_atTop i, eventually_ge_atTop ⌈ρ⌉₊] with k hik hk
      simp only [hik, ↓reduceIte]
      exact hρ.trans (closedBall_subset_closedBall ((Nat.le_ceil ρ).trans (by exact_mod_cast hk))))
    α β
    (fun k => Symbol.exists_norm_mixedDeriv_cutoff_smul_sub_le_of_forall χ (ht1 k)
      (fun r : R => (a k).iteratedDerivSymbol i r.property) hK
      ((a k).exists_bound_iteratedDerivSymbol i hK) _ α β)
    (fun k => Symbol.exists_norm_mixedDeriv_cutoff_smul_le_of_forall χ
      (fun r : R => (a k).iteratedDerivSymbol i r.property) α β
      ((a k).exists_bound_iteratedDerivSymbol i hK α))
  refine ⟨C, hC0, fun r hr x hx ξ => ?_⟩
  rw [iteratedDeriv_borelRemainder_eq_borelSum_sub χ ht a N i hr]
  exact hC ⟨r, hr⟩ x hx ξ

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
