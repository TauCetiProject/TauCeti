/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.List

/-!
# Asymptotic summation of symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ ∈ S^{mⱼ}` be symbols. The series
`∑ⱼ aⱼ` need not converge, even pointwise, but it has an *asymptotic sum*: a symbol `b ∈ S^{m₀}`
such that, for every `N`, the remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N`
(`TauCeti.Symbol.IsAsymptoticSum`, `TauCeti.Symbol.exists_asymptoticSum`). This is the analogue
for symbols of Borel's theorem that every formal power series is the Taylor series of a smooth
function, and it is what turns formal expansions such as `∑ⱼ a_{m-j}` of classical symbols,
compositions and parametrices into actual symbols.

Following Borel, the sum is `b(x, ξ) = ∑ⱼ χ(ξ / tⱼ) aⱼ(x, ξ)` for a frequency cutoff `χ` and radii
`tⱼ → ∞`. For each `ξ` only the finitely many terms with `tⱼ < ‖ξ‖` are nonzero, so `b` is smooth.
The radii are chosen so large that the `j`-th term is at most `2^{-j}` in the estimates of order
`mⱼ + 1` for the derivatives of length at most `j` on the ball of radius `j`; since `mⱼ + 1 ≤ m_N`
for large `j`, the tail of the series is then summable in every estimate of order `m_N`. The
removed cutoffs `(χ(ξ / tⱼ) - 1) aⱼ` have bounded frequency support, so they are symbols of every
order (`TauCeti.Symbol.ofBoundedFrequencySupport`).

The radii can be chosen independently of the position because the dilated cutoffs `χ(ξ / t)`,
`t ≥ 1`, satisfy the order-zero symbol estimates uniformly in `t` and vanish for `‖ξ‖ ≤ t`. For a
symbol `a` of order `m`, the products `χ(ξ / t) a(x, ξ)` therefore satisfy the estimates of every
order `m' ≥ m` with constants `C t^{m - m'}`
(`TauCeti.Symbol.exists_norm_mixedDeriv_cutoff_smul_le`), which tend to zero as `t → ∞` when
`m' > m`.

The asymptotic sum is unique modulo smoothing symbols, and every symbol differing from it by a
smoothing symbol is again an asymptotic sum
(`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`).

The construction also works for continuous families `aⱼ : T → S^{mⱼ}` over a compact space `T`,
continuity being for the symbol topology of `TauCeti.Symbol.instTopologicalSpace`
(`TauCeti.Symbol.exists_continuous_asymptoticSum`). Since `T` is compact, the seminorms of each
`aⱼ(τ)` are bounded independently of `τ`, so one sequence of radii serves for every `τ`. The
remainders after `N` terms are then continuous in `τ`: up to the tail of the series, which is
uniformly small, they are finite sums of the families `aⱼ` composed with fixed symbols. Such
families arise, for instance, from continuous homotopies of symbols.

## Main declarations

* `TauCeti.Symbol.exists_norm_mixedDeriv_cutoff_smul_le`: the estimates of the cut-off symbols
  `χ(ξ / t) a(x, ξ)`, uniform in `t ≥ 1`.
* `TauCeti.Symbol.IsAsymptoticSum`: `b` is an asymptotic sum of the symbols `aⱼ`.
* `TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`: asymptotic sums are unique
  modulo smoothing symbols.
* `TauCeti.Symbol.exists_continuous_asymptoticSum`: continuous families of symbols over a compact
  space, of orders decreasing to `-∞`, have a continuous asymptotic sum with continuous
  remainders.
* `TauCeti.Symbol.exists_asymptoticSum`: every sequence of symbols of orders decreasing to `-∞`
  has an asymptotic sum.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
* R. Melrose, *Introduction to Microlocal Analysis*, Proposition 2.3 and (2.55)–(2.57).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I.
-/

public section

noncomputable section

open Filter Metric Set
open TopologicalSpace (Compacts)
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {A V W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

namespace Symbol

variable {m : ℝ}

/-- The product `χ(ξ / t) a(x, ξ)` of a symbol with a dilated frequency cutoff is smooth. -/
theorem contDiff_cutoff_smul_coefficient (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℝ)
    (a : Symbol n V W m) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) • a.coefficient p :=
  ((χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)).smul a.contDiff_coefficient

/-- The products `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `m` with the dilated frequency cutoffs,
`t ≥ 1`, satisfy the symbol estimates of every order `m' ≥ m` with constants `C t^(m - m')`, where
`C` depends neither on `t` nor on `m'`. This is because `χ(ξ / t)` vanishes for `‖ξ‖ ≤ t`, and
`⟨ξ⟩^(m - m') ≤ t^(m - m')` for `‖ξ‖ ≥ t`. -/
theorem exists_norm_mixedDeriv_cutoff_smul_le (χ : FrequencyCutoff (CoordinateSpace n))
    (a : Symbol n V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ m' : ℝ, m ≤ m' → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        C * t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  choose D hD0 hD using fun w => a.exists_bound K hK α w
  choose B hB0 hB using fun i : ℕ => χ.exists_norm_iteratedFDeriv_comp_inv_smul_le i
  set k := β.length
  set C := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i *
    ∑ w : Fin (k - i) → Fin n, D (List.ofFn w)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (Finset.sum_nonneg fun w _ => hD0 _)
  refine ⟨C, hC0, fun t ht m' hm' x hx ξ => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hχ : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
    (χ.contDiff (n := ⊤)).comp (contDiff_const_smul t⁻¹)
  by_cases hξ : ‖ξ‖ ≤ t
  · -- Below radius `t` the dilated cutoff vanishes to infinite order.
    refine (norm_mixedDeriv_comp_snd_smul_le hχ a.contDiff_coefficient α β x ξ).trans
      (le_of_eq_of_le (Finset.sum_eq_zero fun i _ => ?_) (by positivity))
    rw [χ.iteratedFDeriv_comp_inv_smul_eq_zero i ht0 hξ, norm_zero, mul_zero, zero_mul]
  -- `‖D^i χ(· / t) ξ‖ ≤ B i ⟨ξ⟩ ^ (-i)` is `‖D^i χ(· / t) ξ‖ ⟨ξ⟩ ^ i ≤ B i`
  have hB' (i : ℕ) : ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ *
      (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) ≤ B i := by
    calc ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2)
        ≤ B i * (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) := by
          gcongr
          exact hB i t ht ξ
      _ = B i := by
          rw [mul_assoc, ← Real.rpow_add (by positivity), neg_div, neg_add_cancel,
            Real.rpow_zero, mul_one]
  have hweight : (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) ≤
      t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) := by
    simpa only [sub_sub_sub_cancel_right] using
      rpow_weight_le_rpow_mul_rpow_weight ht0 (not_le.1 hξ).le (sub_le_sub_right hm' (k : ℝ))
  calc ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖
      ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) :=
        norm_mixedDeriv_comp_snd_smul_le_mul_rpow_weight hχ a.contDiff_coefficient hB'
          (fun w => hD w x hx ξ) β
    _ ≤ C * (t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2)) :=
        mul_le_mul_of_nonneg_left hweight hC0
    _ = _ := by ring

/-- The dilated cutoff `χ(ξ / t)`, `t ≥ 1`, as the scalar symbol `χ(ξ / t) id` of order `0`.
Composing with it cuts a symbol off below the frequency radius `t`. -/
private def dilatedCutoff (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℝ} (ht : 1 ≤ t) :
    Symbol n W W 0 where
  coefficient p :=
    χ (t⁻¹ • p.2) • (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).coefficient p
  contDiff_coefficient := (const _).contDiff_cutoff_smul_coefficient χ t
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ := (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0)
      |>.exists_norm_mixedDeriv_cutoff_smul_le χ hK α β
    exact ⟨C, hC0, fun x hx ξ => by simpa using hC t ht 0 le_rfl x hx ξ⟩

private theorem coefficient_dilatedCutoff_comp (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℝ}
    (ht : 1 ≤ t) {μ : ℝ} (a : Symbol n V W μ) :
    ((dilatedCutoff χ ht).comp a).coefficient = fun p => χ (t⁻¹ • p.2) • a.coefficient p :=
  funext fun p => by simp [dilatedCutoff]

/-- For large `t`, the cut-off terms `χ(ξ / t) a_τ(x, ξ)` of a continuous family `a` of symbols of
order `μ` over a compact space of parameters `τ` are at most `2^{-j}` in the estimates of order
`μ + 1` for the derivatives of length at most `j` on the ball of radius `j`, uniformly in `τ`. -/
private theorem eventually_norm_mixedDeriv_cutoff_smul_le
    (χ : FrequencyCutoff (CoordinateSpace n)) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {μ : ℝ} {a : T → Symbol n V W μ} (ha : Continuous a) (j : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ τ, ∀ x ∈ closedBall (0 : CoordinateSpace n) j,
        ∀ ξ, ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • (a τ).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((μ + 1 - β.length) / 2) := by
  rw [eventually_all_finite (List.finite_length_le _ j)]
  intro α _
  rw [eventually_all_finite (List.finite_length_le _ j)]
  intro β _
  let K : Compacts (CoordinateSpace n) := ⟨closedBall 0 j, isCompact_closedBall 0 j⟩
  -- The seminorms of the family are bounded, since the parameter space is compact.
  choose M hM using fun s s' : List (Fin n) => isCompact_univ.exists_bound_of_continuousOn
    ((withSeminorms.continuous_seminorm (K, s, s')).comp ha).continuousOn
  have hM' : ∀ s s' τ, Symbol.seminorm K s s' (a τ) ≤ M s s' := fun s s' τ => by
    have h := hM s s' τ (mem_univ τ)
    rw [Function.comp_apply, seminormFamily_apply] at h
    exact (Real.le_norm_self _).trans h
  -- The dilated cutoffs satisfy the estimates of order `1` with constants `C t⁻¹`.
  choose C hC0 hC using fun s s' : List (Fin n) =>
    (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).exists_norm_mixedDeriv_cutoff_smul_le χ
      (isCompact_closedBall (0 : CoordinateSpace n) j) s s'
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ((β.sublists'.revzip.map fun s' =>
    (α.sublists'.revzip.map fun s => C s.1 s'.1 * M s.2 s'.2).sum).sum * 2 ^ j)]
    with t ht1 htB τ x hx ξ
  have ht0 : 0 < t := one_pos.trans_le ht1
  have hcomp := norm_mixedDeriv_comp_le (m' := 1) (m := μ)
    ((const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).contDiff_cutoff_smul_coefficient χ t)
    (a τ).contDiff_coefficient (C := fun s s' => t⁻¹ * C s s') (D := M)
    (fun s s' => by
      have h := hC s s' t ht1 1 zero_le_one x hx ξ
      rwa [zero_sub, Real.rpow_neg_one, mul_comm (C s s')] at h)
    (fun s s' => (le_seminorm K s s' (a τ) hx ξ).trans (mul_le_mul_of_nonneg_right
      (hM' s s' τ) (rpow_weight_pos ξ _).le)) α β
  have hfun : (fun p => χ (t⁻¹ • p.2) • (a τ).coefficient p) = fun p =>
      (χ (t⁻¹ • p.2) • (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).coefficient p).comp
        ((a τ).coefficient p) :=
    funext fun p => by simp
  have hsum : (β.sublists'.revzip.map fun s' => (α.sublists'.revzip.map fun s =>
      t⁻¹ * C s.1 s'.1 * M s.2 s'.2).sum).sum = t⁻¹ * (β.sublists'.revzip.map fun s' =>
        (α.sublists'.revzip.map fun s => C s.1 s'.1 * M s.2 s'.2).sum).sum := by
    simp only [mul_assoc, List.sum_map_mul_left]
  rw [hfun]
  refine hcomp.trans (le_of_eq_of_le (by rw [hsum, add_comm (1 : ℝ) μ]) ?_)
  gcongr
  rw [inv_mul_le_iff₀ ht0, one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact htB

/-- The Borel sum `∑ⱼ χ(ξ / tⱼ) aⱼ(x, ξ)` of a sequence of symbols with cutoff radii `tⱼ`. -/
private def borelSum (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℕ → ℝ) {m : ℕ → ℝ}
    (a : ∀ j, Symbol n V W (m j)) (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∑ᶠ j, χ ((t j)⁻¹ • p.2) • (a j).coefficient p

/-- With radii `tⱼ ≥ j + 1`, only the terms with `j < J` of the Borel sum can be nonzero at
frequencies `‖ξ‖ < J`. -/
private theorem borelSum_eq_sum (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a : ∀ j, Symbol n V W (m j)) {J : ℕ}
    {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖p.2‖ < J) :
    borelSum χ t a p = ∑ j ∈ Finset.range J, χ ((t j)⁻¹ • p.2) • (a j).coefficient p := by
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjJ
  have hJj : (J : ℝ) ≤ j := by exact_mod_cast not_lt.1 hjJ
  have htj : 0 < t j := by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  exact hj (by simp only [χ.apply_inv_smul_eq_zero htj (by linarith [ht j]), zero_smul])

/-- Near a point with `‖ξ‖ < J`, the Borel sum is the finite sum of its first `J` terms. -/
private theorem borelSum_eventuallyEq (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a : ∀ j, Symbol n V W (m j)) {J : ℕ}
    {p₀ : CoordinateSpace n × CoordinateSpace n} (hJ : ‖p₀.2‖ < J) :
    borelSum χ t a =ᶠ[𝓝 p₀]
      ∑ j ∈ Finset.range J, fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p := by
  filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hJ] with p hp
  rw [borelSum_eq_sum χ ht a hp, Finset.sum_apply]

/-- The Borel sum is smooth, since near each point it is a finite sum of smooth terms. -/
private theorem contDiff_borelSum (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a : ∀ j, Symbol n V W (m j)) :
    ContDiff ℝ ∞ (borelSum χ t a) := by
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖p₀.2‖
  have hs : ContDiff ℝ ∞
      (∑ j ∈ Finset.range J, fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) := by
    simpa only [Finset.sum_fn] using
      ContDiff.sum fun j _ => (a j).contDiff_cutoff_smul_coefficient χ (t j)
  exact hs.contDiffAt.congr_of_eventuallyEq (borelSum_eventuallyEq χ ht a hJ)

/-- Given orders `mⱼ → -∞`, an index `N`, a compact set `K` and words `α`, `β`, there is
`j₁ ≥ N` such that for every `j ≥ j₁`, a function that is at most `2^{-j}` in the estimates of
order `mⱼ + 1` for the derivatives of length at most `j` on the ball of radius `j` is also at most
`2^{-j}` in the estimate of order `m_N` for `∂_x^α ∂_ξ^β` on `K`. -/
private theorem exists_forall_ge_norm_mixedDeriv_le {m : ℕ → ℝ} (hm' : Tendsto m atTop atBot)
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ j₁, N ≤ j₁ ∧ ∀ j, j₁ ≤ j → ∀ g : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W,
      (∀ α ∈ {l : List (Fin n) | l.length ≤ j}, ∀ β ∈ {l : List (Fin n) | l.length ≤ j},
        ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ,
          ‖mixedDeriv α β g x ξ‖ ≤ (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m j + 1 - β.length) / 2)) →
      ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β g x ξ‖ ≤ (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := by
  obtain ⟨JK, hJK⟩ : ∃ JK : ℕ, K ⊆ closedBall 0 JK := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨JK, hJK⟩ := exists_nat_ge r
    exact ⟨JK, hr.trans (closedBall_subset_closedBall hJK)⟩
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hm'.eventually (eventually_le_atBot (m N - 1)))
  refine ⟨max (max N j₀) (max JK (max α.length β.length)), le_max_of_le_left (le_max_left _ _),
    fun j hj g hg x hx ξ => ?_⟩
  have hαj : α.length ≤ j := by omega
  have hβj : β.length ≤ j := by omega
  have hxj : x ∈ closedBall (0 : CoordinateSpace n) j :=
    closedBall_subset_closedBall (by exact_mod_cast (show JK ≤ j by omega)) (hJK hx)
  refine (hg α hαj β hβj x hxj ξ).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [norm_nonneg ξ]) ?_) (by positivity))
  linarith [hj₀ j (by omega)]

/-- Near `(x, ξ)` with `‖ξ‖ < J`, the remainder `b - ∑_{j < N} aⱼ` of the Borel sum `b` splits into
the removed cutoffs `(χ(ξ / tⱼ) - 1) aⱼ`, `j < N`, and the cut-off terms with `N ≤ j < j₁` and with
`j₁ ≤ j < J`; so do its mixed derivatives at `(x, ξ)`. -/
private theorem mixedDeriv_borelSum_sub (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a : ∀ j, Symbol n V W (m j)) {N j₁ J : ℕ}
    (hNj₁ : N ≤ j₁) (hj₁J : j₁ ≤ J) (α β : List (Fin n)) (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : ‖ξ‖ < J) :
    mixedDeriv α β (borelSum χ t a - ∑ j ∈ Finset.range N, (a j).coefficient) x ξ =
      ∑ j ∈ Finset.range N,
          mixedDeriv α β ((fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) - (a j).coefficient)
            x ξ +
        (∑ j ∈ Finset.Ico N j₁,
            mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ +
          ∑ j ∈ Finset.Ico j₁ J,
            mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ) := by
  let g : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun j p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p
  have hg : ∀ j, ContDiff ℝ ∞ (g j) := fun j => (a j).contDiff_cutoff_smul_coefficient χ (t j)
  have hloc : borelSum χ t a =ᶠ[𝓝 (x, ξ)] ∑ j ∈ Finset.range J, g j :=
    borelSum_eventuallyEq χ ht a hξ
  have heq : borelSum χ t a - ∑ j ∈ Finset.range N, (a j).coefficient =ᶠ[𝓝 (x, ξ)]
      ∑ j ∈ Finset.range N, (g j - (a j).coefficient) +
        (∑ j ∈ Finset.Ico N j₁, g j + ∑ j ∈ Finset.Ico j₁ J, g j) := by
    filter_upwards [hloc] with p hp
    rw [Pi.sub_apply, hp, Finset.sum_Ico_consecutive _ hNj₁ hj₁J,
      ← Finset.sum_range_add_sum_Ico _ (hNj₁.trans hj₁J), Finset.sum_sub_distrib]
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hs₁ : ContDiff ℝ ∞ (∑ j ∈ Finset.range N, (g j - (a j).coefficient)) := by
    simpa only [Finset.sum_fn, Pi.sub_apply] using
      ContDiff.sum fun j _ => (hg j).sub (a j).contDiff_coefficient
  have hs₂ : ContDiff ℝ ∞ (∑ j ∈ Finset.Ico N j₁, g j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum fun j _ => hg j
  have hs₃ : ContDiff ℝ ∞ (∑ j ∈ Finset.Ico j₁ J, g j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum fun j _ => hg j
  have hs₂₃ : ContDiff ℝ ∞ (∑ j ∈ Finset.Ico N j₁, g j + ∑ j ∈ Finset.Ico j₁ J, g j) :=
    hs₂.add hs₃
  rw [heq.mixedDeriv_eq, mixedDeriv_add hs₁ hs₂₃, mixedDeriv_add hs₂ hs₃,
    mixedDeriv_sum (f := fun j => g j - (a j).coefficient)
      (fun j _ => (hg j).sub (a j).contDiff_coefficient),
    mixedDeriv_sum (fun j _ => hg j), mixedDeriv_sum (fun j _ => hg j)]

/-- If the radii `tⱼ ≥ j + 1` make the `j`-th term of the Borel sum `b` at most `2^{-j}` in the
estimates of order `mⱼ + 1` for the derivatives of length at most `j` on the ball of radius `j`,
then the remainder `b - ∑_{j < N} aⱼ` satisfies the estimates of order `m_N`. -/
private theorem exists_norm_mixedDeriv_borelSum_sub_le (χ : FrequencyCutoff (CoordinateSpace n))
    {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot) (a : ∀ j, Symbol n V W (m j))
    {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (hsmall : ∀ j, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m j + 1 - β.length) / 2))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (borelSum χ t a - ∑ j ∈ Finset.range N, (a j).coefficient) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := by
  have ht1 : ∀ j, 1 ≤ t j := fun j => by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨j₁, hNj₁, htail⟩ := exists_forall_ge_norm_mixedDeriv_le (V := V) (W := W) hm' N hK α β
  -- The removed cutoffs `(χ(ξ / tⱼ) - 1) aⱼ` have bounded frequency support.
  have hD1 : ∀ j, ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β
      ((fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) - (a j).coefficient) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := fun j => by
    have hR : ∀ x ξ, 2 * t j ≤ ‖ξ‖ →
        ((fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) - (a j).coefficient) (x, ξ) = 0 :=
      fun x ξ hξ => by
        simp only [Pi.sub_apply, χ.apply_inv_smul_eq_one (one_pos.trans_le (ht1 j)) hξ,
          one_smul, sub_self]
    simpa only [coefficient_ofBoundedFrequencySupport] using
      (ofBoundedFrequencySupport (m := m N)
        ((fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) - (a j).coefficient)
        (((a j).contDiff_cutoff_smul_coefficient χ (t j)).sub (a j).contDiff_coefficient)
        (2 * t j) hR).exists_bound K hK α β
  choose D₁ hD₁0 hD₁ using hD1
  choose D₂ hD₂0 hD₂ using fun j => (a j).exists_norm_mixedDeriv_cutoff_smul_le χ hK α β
  refine ⟨∑ j ∈ Finset.range N, D₁ j + ∑ j ∈ Finset.range j₁, D₂ j + 2,
    add_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => hD₁0 j)
      (Finset.sum_nonneg fun j _ => hD₂0 j)) zero_le_two, fun x hx ξ => ?_⟩
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2)
  have hw0 : 0 ≤ w := by positivity
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt ‖ξ‖
  rw [mixedDeriv_borelSum_sub χ ht a hNj₁ (le_max_right J₀ j₁) α β x
    (hJ₀.trans_le (by exact_mod_cast le_max_left _ _))]
  -- The first `N` terms: the removed cutoffs.
  have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.range N) =>
    hD₁ j x hx ξ)
  -- The finitely many terms with `N ≤ j < j₁` are symbols of order `mⱼ ≤ m_N`.
  have h2 : ∑ j ∈ Finset.Ico N j₁,
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
        ∑ j ∈ Finset.range j₁, D₂ j * w := by
    refine (Finset.sum_le_sum fun j hj => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2)
      fun j _ _ => mul_nonneg (hD₂0 j) hw0)
    have hNj : N ≤ j := (Finset.mem_Ico.1 hj).1
    refine (hD₂ j (t j) (ht1 j) (m N) (hm hNj) x hx ξ).trans ?_
    gcongr
    exact mul_le_of_le_one_right (hD₂0 j)
      (Real.rpow_le_one_of_one_le_of_nonpos (ht1 j) (by linarith [hm hNj]))
  -- The tail: the `j`-th term is at most `2^{-j}`, and these bounds sum to at most `2`.
  have h3 : ∑ j ∈ Finset.Ico j₁ (max J₀ j₁),
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤ 2 * w := by
    refine (Finset.sum_le_sum fun j hj =>
      htail j (Finset.mem_Ico.1 hj).1 _ (hsmall j) x hx ξ).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2) fun j _ _ => by positivity).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw0
  refine (norm_add_le _ _).trans ((add_le_add h1 ((norm_add_le _ _).trans (add_le_add
    ((norm_sum_le _ _).trans h2) ((norm_sum_le _ _).trans h3)))).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- With radii `tⱼ ≥ j + 1`, the remainders after `N` terms of the Borel sums of two sequences `a`,
`a'` of symbols differ at `(x, ξ)` by at most the differences of their first `j₂ ≥ N` terms (the
removed cutoffs `(χ(ξ / tⱼ) - 1) aⱼ` for `j < N`, the cut-off terms `χ(ξ / tⱼ) aⱼ` for
`N ≤ j < j₂`), plus `4 ⋅ 2^{-j₂}` in the estimate of order `m_N`, provided that from `j₂` on all
the cut-off terms are at most `2^{-j}` in that estimate. -/
private theorem norm_mixedDeriv_borelSum_sub_sub_le (χ : FrequencyCutoff (CoordinateSpace n))
    {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a a' : ∀ j, Symbol n V W (m j))
    {N j₂ : ℕ} (hNj₂ : N ≤ j₂) (α β : List (Fin n)) (x ξ : CoordinateSpace n)
    (htail : ∀ j, j₂ ≤ j →
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
        (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2))
    (htail' : ∀ j, j₂ ≤ j →
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a' j).coefficient p) x ξ‖ ≤
        (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2)) :
    ‖mixedDeriv α β (borelSum χ t a - ∑ j ∈ Finset.range N, (a j).coefficient) x ξ -
        mixedDeriv α β (borelSum χ t a' - ∑ j ∈ Finset.range N, (a' j).coefficient) x ξ‖ ≤
      ∑ j ∈ Finset.range N,
          ‖mixedDeriv α β ((fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) -
              (a j).coefficient) x ξ -
            mixedDeriv α β ((fun p => χ ((t j)⁻¹ • p.2) • (a' j).coefficient p) -
              (a' j).coefficient) x ξ‖ +
        ∑ j ∈ Finset.Ico N j₂,
          ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ -
            mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a' j).coefficient p) x ξ‖ +
        4 * (1 / 2) ^ j₂ * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := by
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt ‖ξ‖
  have hξ : ‖ξ‖ < (max J₀ j₂ : ℕ) := hJ₀.trans_le (by exact_mod_cast le_max_left _ _)
  rw [mixedDeriv_borelSum_sub χ ht a hNj₂ (le_max_right J₀ j₂) α β x hξ,
    mixedDeriv_borelSum_sub χ ht a' hNj₂ (le_max_right J₀ j₂) α β x hξ]
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2)
  have hw0 : 0 ≤ w := by positivity
  -- Each of the two tails from `j₂` on is at most `2 ⋅ 2^{-j₂}`.
  have hT : ∀ b : ∀ j, Symbol n V W (m j), (∀ j, j₂ ≤ j →
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (b j).coefficient p) x ξ‖ ≤ (1 / 2) ^ j * w) →
      ‖∑ j ∈ Finset.Ico j₂ (max J₀ j₂),
        mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (b j).coefficient p) x ξ‖ ≤
          2 * (1 / 2) ^ j₂ * w := fun b hb => by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj =>
      hb j (Finset.mem_Ico.1 hj).1).trans ?_)
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ((geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans
      (le_of_eq ?_)) hw0
    ring
  rw [show ∀ A A' B B' C C' : V →L[ℂ] W, A + (B + C) - (A' + (B' + C')) =
      (A - A') + (B - B') + (C - C') from fun _ _ _ _ _ _ => by abel,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))) ((norm_sub_le _ _).trans ?_))
  linarith [hT a htail, hT a' htail']

/-- Along a continuous family `F` of symbols of order `μ`, every mixed derivative converges
uniformly for positions in a compact set `K`, after division by the weight: near `τ₀` it is within
`ε ⟨ξ⟩^(μ - |β|)` of its value at `τ₀`. -/
private theorem eventually_norm_mixedDeriv_sub_le {T : Type*} [TopologicalSpace T] {μ : ℝ}
    {F : T → Symbol n V W μ} (hF : Continuous F) (τ₀ : T) (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (F τ).coefficient x ξ -
      mixedDeriv α β (F τ₀).coefficient x ξ‖ ≤ ε * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2) := by
  filter_upwards [(withSeminorms.tendsto_nhds F (F τ₀)).1 (hF.tendsto τ₀) (K, α, β) ε hε]
    with τ hτ x hx ξ
  have h := (mixedDerivCLM n V W μ α β x ξ).map_sub (F τ) (F τ₀)
  simp only [mixedDerivCLM_apply] at h
  rw [seminormFamily_apply] at hτ
  rw [← h]
  exact (le_seminorm K α β (F τ - F τ₀) hx ξ).trans
    (mul_le_mul_of_nonneg_right hτ.le (rpow_weight_pos ξ _).le)

/-- For `t ≥ 1`, the removed cutoffs `(χ(ξ / t) - 1) a_τ(x, ξ)` of a continuous family `a` of
symbols form a continuous family of symbols of every order `μ'`: they vanish for `‖ξ‖ ≥ 2t`. -/
private theorem exists_continuous_cutoff_smul_sub (χ : FrequencyCutoff (CoordinateSpace n))
    {T : Type*} [TopologicalSpace T] {t : ℝ} (ht : 1 ≤ t) {μ : ℝ} {a : T → Symbol n V W μ}
    (ha : Continuous a) (μ' : ℝ) :
    ∃ E : T → Symbol n V W μ', Continuous E ∧ ∀ τ, (E τ).coefficient =
      (fun p => χ (t⁻¹ • p.2) • (a τ).coefficient p) - (a τ).coefficient := by
  let e : Symbol n W W (μ' - μ) := ofBoundedFrequencySupport
    (fun p => (χ (t⁻¹ • p.2) - 1) • ContinuousLinearMap.id ℂ W)
    ((((χ.contDiff (n := ⊤)).comp (contDiff_snd.const_smul t⁻¹)).sub contDiff_const).smul
      contDiff_const) (2 * t) fun x ξ hξ => by
        simp [χ.apply_inv_smul_eq_one (one_pos.trans_le ht) hξ]
  refine ⟨fun τ => inclusion (sub_add_cancel μ' μ).le (e.comp (a τ)),
    (continuous_inclusion _).comp (continuous_const.symbol_comp ha), fun τ => ?_⟩
  funext p
  simp [e, sub_smul]

/-- For `t ≥ 1`, the cut-off terms `χ(ξ / t) a_τ(x, ξ)` of a continuous family `a` of symbols of
order `μ` form a continuous family of symbols of every order `μ' ≥ μ`. -/
private theorem exists_continuous_cutoff_smul (χ : FrequencyCutoff (CoordinateSpace n))
    {T : Type*} [TopologicalSpace T] {t : ℝ} (ht : 1 ≤ t) {μ μ' : ℝ} (h : μ ≤ μ')
    {a : T → Symbol n V W μ} (ha : Continuous a) :
    ∃ G : T → Symbol n V W μ', Continuous G ∧ ∀ τ,
      (G τ).coefficient = fun p => χ (t⁻¹ • p.2) • (a τ).coefficient p :=
  ⟨fun τ => inclusion ((zero_add μ).le.trans h) ((dilatedCutoff χ ht).comp (a τ)),
    (continuous_inclusion _).comp (continuous_const.symbol_comp ha), fun τ => by
      rw [coefficient_inclusion, coefficient_dilatedCutoff_comp]⟩

/-- If the radii `tⱼ ≥ j + 1` make the cut-off terms of continuous families `aⱼ` of symbols at most
`2^{-j}` in the estimates of order `mⱼ + 1` for the derivatives of length at most `j` on the ball
of radius `j`, uniformly in the parameter `τ`, then the remainders `b(τ) - ∑_{j < N} aⱼ(τ)` of the
Borel sums `b(τ)` form a continuous family of symbols of order `m_N`. -/
private theorem exists_continuous_borelSum_sub (χ : FrequencyCutoff (CoordinateSpace n))
    {T : Type*} [TopologicalSpace T] {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    {a : ∀ j, T → Symbol n V W (m j)} (ha : ∀ j, Continuous (a j)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (hsmall : ∀ j, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ τ, ∀ x ∈ closedBall (0 : CoordinateSpace n) j,
        ∀ ξ, ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j τ).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m j + 1 - β.length) / 2))
    (N : ℕ) :
    ∃ r : T → Symbol n V W (m N), Continuous r ∧ ∀ τ, (r τ).coefficient =
      borelSum χ t (fun j => a j τ) - ∑ j ∈ Finset.range N, (a j τ).coefficient := by
  have ht1 : ∀ j, 1 ≤ t j := fun j => by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hsum : ∀ τ, ContDiff ℝ ∞ (∑ j ∈ Finset.range N, (a j τ).coefficient) := fun τ => by
    simpa only [Finset.sum_fn] using ContDiff.sum fun j _ => (a j τ).contDiff_coefficient
  obtain ⟨r, hr⟩ : ∃ r : T → Symbol n V W (m N), ∀ τ, (r τ).coefficient =
      borelSum χ t (fun j => a j τ) - ∑ j ∈ Finset.range N, (a j τ).coefficient :=
    ⟨fun τ => ⟨_, (contDiff_borelSum χ ht _).sub (hsum τ),
      fun K hK α β => exists_norm_mixedDeriv_borelSum_sub_le χ hm hm' (fun j => a j τ) ht
        (fun j α hα β hβ => hsmall j α hα β hβ τ) N hK α β⟩, fun τ => rfl⟩
  -- Continuity at `τ₀` in the seminorm `p_{K,α,β}`: the remainder splits into its first `j₂`
  -- terms, which are continuous in `τ`, and a tail of size at most `4 ⋅ 2^{-j₂}` for every `τ`.
  refine ⟨r, continuous_iff_continuousAt.2 fun τ₀ => ?_, hr⟩
  rw [ContinuousAt, withSeminorms.tendsto_nhds]
  rintro ⟨K, α, β⟩ ε hε
  simp only [seminormFamily_apply]
  -- The removed cutoffs `(χ(ξ / tⱼ) - 1) aⱼ(τ)` and, for `j ≥ N`, the cut-off terms
  -- `χ(ξ / tⱼ) aⱼ(τ)` are continuous families of symbols of order `m_N`.
  choose E hEc hE using fun j => exists_continuous_cutoff_smul_sub χ (ht1 j) (ha j) (m N)
  -- From `j₂` on, the cut-off terms are at most `2^{-j}` in the estimate of order `m_N` on `K`,
  -- and `4 ⋅ 2^{-j₂} ≤ ε / 4`.
  obtain ⟨j₁, hNj₁, htail⟩ :=
    exists_forall_ge_norm_mixedDeriv_le (V := V) (W := W) hm' N K.isCompact α β
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / 16)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set j₂ := max j₁ L
  have hNj₂ : N ≤ j₂ := hNj₁.trans (le_max_left _ _)
  have hj₂ : (1 / 2 : ℝ) ^ j₂ ≤ ε / 16 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)).trans hL.le
  -- Near `τ₀`, each of the first `j₂` terms is within `ε'` of its value at `τ₀`.
  set ε' := ε / (4 * (j₂ + 1))
  have hε' : 0 < ε' := by positivity
  have hfinE : ∀ᶠ τ in 𝓝 τ₀, ∀ j ∈ Finset.range N, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (E j τ).coefficient x ξ - mixedDeriv α β (E j τ₀).coefficient x ξ‖ ≤
        ε' * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) :=
    (eventually_all_finset _).2 fun j _ => eventually_norm_mixedDeriv_sub_le (hEc j) τ₀ K α β hε'
  have hfinG : ∀ᶠ τ in 𝓝 τ₀, ∀ j ∈ Finset.Ico N j₂, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j τ).coefficient p) x ξ -
        mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j τ₀).coefficient p) x ξ‖ ≤
          ε' * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) :=
    (eventually_all_finset _).2 fun j hj => by
      obtain ⟨G, hGc, hG⟩ := exists_continuous_cutoff_smul χ (ht1 j) (hm (Finset.mem_Ico.1 hj).1)
        (ha j)
      simpa only [hG] using eventually_norm_mixedDeriv_sub_le hGc τ₀ K α β hε'
  filter_upwards [hfinE, hfinG] with τ hτE hτG
  refine (seminorm_le_bound K α β _ (by positivity : 0 ≤ ε / 2) fun x hx ξ => ?_).trans_lt
    (half_lt_self hε)
  set w := (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2)
  have hw0 : 0 ≤ w := by positivity
  have htail₂ : ∀ τ', ∀ j, j₂ ≤ j →
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j τ').coefficient p) x ξ‖ ≤
        (1 / 2) ^ j * w := fun τ' j hj =>
    htail j ((le_max_left _ _).trans hj) _ (fun α hα β hβ => hsmall j α hα β hβ τ') x hx ξ
  have hsub := (mixedDerivCLM n V W (m N) α β x ξ).map_sub (r τ) (r τ₀)
  simp only [mixedDerivCLM_apply, hr] at hsub
  rw [hsub]
  refine (norm_mixedDeriv_borelSum_sub_sub_le χ ht (fun j => a j τ) (fun j => a j τ₀) hNj₂ α β x ξ
    (htail₂ τ) (htail₂ τ₀)).trans ?_
  have hfin : ∑ j ∈ Finset.range N, ε' * w + ∑ j ∈ Finset.Ico N j₂, ε' * w ≤ ε / 4 * w := by
    have hj : (j₂ : ℝ) * ε' ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul,
      nsmul_eq_mul, Nat.cast_sub hNj₂]
    calc (N : ℝ) * (ε' * w) + ((j₂ : ℝ) - N) * (ε' * w) = j₂ * ε' * w := by ring
      _ ≤ ε / 4 * w := mul_le_mul_of_nonneg_right hj hw0
  calc _ ≤ ∑ j ∈ Finset.range N, ε' * w + ∑ j ∈ Finset.Ico N j₂, ε' * w + 4 * (ε / 16) * w := by
        gcongr with j hj j hj
        · rw [← hE j τ, ← hE j τ₀]
          exact hτE j hj x hx ξ
        · exact hτG j hj x hx ξ
    _ ≤ ε / 2 * w := by linarith

/-- A symbol `b` of order `m₀` is an *asymptotic sum* `b ∼ ∑ⱼ aⱼ` of symbols `aⱼ` of orders `mⱼ` if
for every `N` the remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N`. -/
def IsAsymptoticSum {m : ℕ → ℝ} (b : Symbol n V W (m 0)) (a : ∀ j, Symbol n V W (m j)) : Prop :=
  ∀ N, ∃ r : Symbol n V W (m N),
    b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient

theorem isAsymptoticSum_iff {m : ℕ → ℝ} {b : Symbol n V W (m 0)} {a : ∀ j, Symbol n V W (m j)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ r : Symbol n V W (m N),
      b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient :=
  Iff.rfl

/-- Asymptotic sums are unique modulo smoothing symbols: if `b` is an asymptotic sum of symbols
`aⱼ` whose orders tend to `-∞`, then `b'` is one exactly when `b' - b` is smoothing. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub {m : ℕ → ℝ}
    (hm' : Tendsto m atTop atBot) {a : ∀ j, Symbol n V W (m j)} {b b' : Symbol n V W (m 0)}
    (hb : b.IsAsymptoticSum a) : b'.IsAsymptoticSum a ↔ (b' - b).IsSmoothing := by
  refine ⟨fun hb' => isSmoothing_iff.2 fun m'' => ?_, fun h N => ?_⟩
  · obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot m'')).exists
    obtain ⟨r, hr⟩ := hb N
    obtain ⟨r', hr'⟩ := hb' N
    refine ⟨inclusion hN (r' - r), ?_⟩
    rw [coefficient_inclusion, coefficient_sub, ← hr, ← hr', coefficient_sub]
    abel
  · obtain ⟨r, hr⟩ := hb N
    obtain ⟨s, hs⟩ := isSmoothing_iff.1 h (m N)
    refine ⟨s + r, ?_⟩
    rw [coefficient_add, hs, ← hr, coefficient_sub]
    abel

/-- **Asymptotic summation with parameters** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to
`-∞`, let `T` be a compact space, and let `aⱼ : T → S^{mⱼ}` be continuous families of symbols.
Then there is a continuous family `b : T → S^{m₀}` such that for every `N` the remainders
`b(τ) - ∑_{j < N} aⱼ(τ)` form a continuous family of symbols of order `m_N`. -/
theorem exists_continuous_asymptoticSum {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    {a : ∀ j, T → Symbol n V W (m j)} (ha : ∀ j, Continuous (a j)) :
    ∃ b : T → Symbol n V W (m 0), Continuous b ∧ ∀ N, ∃ r : T → Symbol n V W (m N),
      Continuous r ∧ ∀ τ, (b τ).coefficient - ∑ j ∈ Finset.range N, (a j τ).coefficient =
        (r τ).coefficient := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  choose t ht using fun j : ℕ => ((eventually_ge_atTop ((j : ℝ) + 1)).and
    (eventually_norm_mixedDeriv_cutoff_smul_le χ (ha j) j)).exists
  choose r hrc hr using exists_continuous_borelSum_sub χ hm hm' ha (fun j => (ht j).1)
    fun j => (ht j).2
  refine ⟨r 0, hrc 0, fun N => ⟨r N, hrc N, fun τ => ?_⟩⟩
  rw [hr 0 τ, hr N τ, Finset.sum_range_zero, sub_zero]

/-- **Asymptotic summation** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞`, and let
`aⱼ` be symbols of order `mⱼ`. Then there is a symbol `b` of order `m₀` such that for every `N` the
remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, Symbol n V W (m j)) : ∃ b : Symbol n V W (m 0), b.IsAsymptoticSum a := by
  obtain ⟨b, -, hb⟩ := exists_continuous_asymptoticSum (T := Unit) hm hm' (a := fun j _ => a j)
    fun _ => continuous_const
  refine ⟨b (), fun N => ?_⟩
  obtain ⟨r, -, hr⟩ := hb N
  exact ⟨r (), hr ()⟩

end Symbol

end TauCeti
