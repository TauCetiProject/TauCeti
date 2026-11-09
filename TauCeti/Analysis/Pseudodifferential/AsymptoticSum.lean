/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
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
(`TauCeti.Symbol.exists_asymptoticSum`). This is the analogue for symbols of Borel's theorem that
every formal power series is the Taylor series of a smooth function, and it is what turns formal
expansions such as `∑ⱼ a_{m-j}` of classical symbols, compositions and parametrices into actual
symbols.

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

## Main declarations

* `TauCeti.Symbol.exists_norm_mixedDeriv_cutoff_smul_le`: the estimates of the cut-off symbols
  `χ(ξ / t) a(x, ξ)`, uniform in `t ≥ 1`.
* `TauCeti.Symbol.exists_asymptoticSum`: every sequence of symbols of orders decreasing to `-∞`
  has an asymptotic sum.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
* R. Melrose, *Introduction to Microlocal Analysis*, Proposition 2.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I.
-/

public section

noncomputable section

open Filter Metric Set
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

/-- Leibniz's rule bounds the mixed derivatives of `χ(ξ / t) a(x, ξ)` by the derivatives of the
dilated cutoff and those of `∂_x^α a(x, ·)`. -/
private theorem norm_mixedDeriv_cutoff_smul_le_sum (χ : FrequencyCutoff (CoordinateSpace n))
    (t : ℝ) (a : Symbol n V W m) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
      ∑ i ∈ Finset.range (β.length + 1), (β.length.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ *
        ‖iteratedFDeriv ℝ (β.length - i)
          (fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x) ξ‖ := by
  have hg : ContDiff ℝ ∞ fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x :=
    (a.contDiff_coefficient.coordinateDeriv_fst α).comp (contDiff_prodMk_right x)
  have hχ : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
    (χ.contDiff (n := ⊤)).comp (contDiff_const_smul t⁻¹)
  rw [mixedDeriv_eq_coordinateDeriv_snd (a.contDiff_cutoff_smul_coefficient χ t)]
  have hcomm : (fun η => coordinateDeriv α (fun y => χ (t⁻¹ • (y, η).2) • a.coefficient (y, η))
      x) = fun η => χ (t⁻¹ • η) • coordinateDeriv α (fun y => a.coefficient (y, η)) x := by
    funext η
    exact congrFun (coordinateDeriv_const_smul α
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_left η)) _)
      (χ (t⁻¹ • η))) x
  rw [hcomm]
  exact (norm_coordinateDeriv_le β (contDiff_infty.1 (hχ.smul hg) _) ξ).trans
    (norm_iteratedFDeriv_smul_le hχ hg ξ (mod_cast le_top))

/-- The products `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `m` with the dilated frequency cutoffs,
`t ≥ 1`, satisfy the symbol estimates of every order `m' ≥ m` with constants `C t^(m - m')`, where
`C` depends neither on `t` nor on `m'`. This is because `χ(ξ / t)` vanishes for `‖ξ‖ ≤ t`, and
`⟨ξ⟩^(m - m') ≤ t^(m - m')` for `‖ξ‖ ≥ t`. -/
theorem exists_norm_mixedDeriv_cutoff_smul_le (χ : FrequencyCutoff (CoordinateSpace n))
    (a : Symbol n V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ m' : ℝ, m ≤ m' → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        C * t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  choose G hG0 hG using fun i : ℕ => a.exists_norm_iteratedFDeriv_coordinateDeriv_le hK α i
  choose B hB0 hB using fun i : ℕ => χ.exists_norm_iteratedFDeriv_comp_inv_smul_le i
  set k := β.length
  have hC0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * G (k - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hG0 _)
  refine ⟨_, hC0, fun t ht m' hm' x hx ξ => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hleib := norm_mixedDeriv_cutoff_smul_le_sum χ t a α β x ξ
  by_cases hξ : ‖ξ‖ ≤ t
  · -- Below radius `t` the dilated cutoff vanishes to infinite order.
    refine hleib.trans (le_of_eq_of_le (Finset.sum_eq_zero fun i _ => ?_) (by positivity))
    rw [χ.iteratedFDeriv_comp_inv_smul_eq_zero i ht0 hξ, norm_zero, mul_zero, zero_mul]
  have hweight : (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) ≤
      t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) := by
    simpa only [sub_sub_sub_cancel_right] using
      rpow_weight_le_rpow_mul_rpow_weight ht0 (not_le.1 hξ).le (sub_le_sub_right hm' (k : ℝ))
  calc ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (B i * (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2)) *
          (G (k - i) * (1 + ‖ξ‖ ^ 2) ^ ((m - (k - i : ℕ)) / 2)) := by
        refine hleib.trans (Finset.sum_le_sum fun i _ => ?_)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hB i t ht ξ) (Nat.cast_nonneg _))
          (hG (k - i) x hx ξ) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by
            have := hB0 i
            positivity))
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * G (k - i)) *
          (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(i : ℝ) / 2) *
            (1 + ‖ξ‖ ^ 2) ^ ((m - (k - i : ℕ)) / 2) = (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) := by
          rw [← Real.rpow_add hw, Nat.cast_sub hik]
          ring_nf
        rw [← hexp]
        ring
    _ ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * G (k - i)) *
          (t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2)) :=
        mul_le_mul_of_nonneg_left hweight hC0
    _ = _ := by ring

/-- For large `t`, the cut-off term `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `μ` is at most
`2^{-j}` in the estimates of order `μ + 1` for the derivatives of length at most `j` on the ball of
radius `j`. -/
private theorem eventually_norm_mixedDeriv_cutoff_smul_le
    (χ : FrequencyCutoff (CoordinateSpace n)) {μ : ℝ} (a : Symbol n V W μ) (j : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((μ + 1 - β.length) / 2) := by
  rw [eventually_all_finite (List.finite_length_le _ j)]
  intro α _
  rw [eventually_all_finite (List.finite_length_le _ j)]
  intro β _
  obtain ⟨C, hC0, hC⟩ := a.exists_norm_mixedDeriv_cutoff_smul_le χ (isCompact_closedBall 0 j) α β
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (C * 2 ^ j)] with t ht1 htC x hx ξ
  refine (hC t ht1 (μ + 1) (by linarith) x hx ξ).trans ?_
  have ht0 : 0 < t := one_pos.trans_le ht1
  gcongr
  rw [show μ - (μ + 1) = -1 by ring, Real.rpow_neg_one, ← div_eq_mul_inv,
    div_le_iff₀ ht0, one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact htC

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

/-- If the radii `tⱼ` make the `j`-th term of the Borel sum at most `2^{-j}` in the estimates of
order `mⱼ + 1` for the derivatives of length at most `j` on the ball of radius `j`, then from some
index `j₁ ≥ N` on, the `j`-th term is at most `2^{-j}` in the estimates of order `m_N` for given
derivatives on a given compact set. -/
private theorem exists_forall_ge_norm_mixedDeriv_cutoff_smul_le
    (χ : FrequencyCutoff (CoordinateSpace n)) {m : ℕ → ℝ} (hm' : Tendsto m atTop atBot)
    (a : ∀ j, Symbol n V W (m j)) {t : ℕ → ℝ}
    (hsmall : ∀ j, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m j + 1 - β.length) / 2))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ j₁, N ≤ j₁ ∧ ∀ j, j₁ ≤ j → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
        (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := by
  obtain ⟨JK, hJK⟩ : ∃ JK : ℕ, K ⊆ closedBall 0 JK := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨JK, hJK⟩ := exists_nat_ge r
    exact ⟨JK, hr.trans (closedBall_subset_closedBall hJK)⟩
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hm'.eventually (eventually_le_atBot (m N - 1)))
  refine ⟨max (max N j₀) (max JK (max α.length β.length)), le_max_of_le_left (le_max_left _ _),
    fun j hj x hx ξ => ?_⟩
  have hαj : α.length ≤ j := by omega
  have hβj : β.length ≤ j := by omega
  have hxj : x ∈ closedBall (0 : CoordinateSpace n) j :=
    closedBall_subset_closedBall (by exact_mod_cast (show JK ≤ j by omega)) (hJK hx)
  refine (hsmall j α hαj β hβj x hxj ξ).trans (mul_le_mul_of_nonneg_left
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
  obtain ⟨j₁, hNj₁, htail⟩ :=
    exists_forall_ge_norm_mixedDeriv_cutoff_smul_le χ hm' a hsmall N hK α β
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
    refine (Finset.sum_le_sum fun j hj => htail j (Finset.mem_Ico.1 hj).1 x hx ξ).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2) fun j _ _ => by positivity).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw0
  refine (norm_add_le _ _).trans ((add_le_add h1 ((norm_add_le _ _).trans (add_le_add
    ((norm_sum_le _ _).trans h2) ((norm_sum_le _ _).trans h3)))).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Asymptotic summation** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞`, and let
`aⱼ` be symbols of order `mⱼ`. Then there is a symbol `b` of order `m₀` such that for every `N` the
remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, Symbol n V W (m j)) :
    ∃ b : Symbol n V W (m 0), ∀ N, ∃ r : Symbol n V W (m N),
      b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  choose t ht using fun j : ℕ => ((eventually_ge_atTop ((j : ℝ) + 1)).and
    (eventually_norm_mixedDeriv_cutoff_smul_le χ (a j) j)).exists
  have hb := contDiff_borelSum χ (fun j => (ht j).1) a
  have hrem := exists_norm_mixedDeriv_borelSum_sub_le χ hm hm' a (fun j => (ht j).1)
    fun j => (ht j).2
  refine ⟨⟨borelSum χ t a, hb, fun K hK α β => ?_⟩, fun N =>
    ⟨⟨borelSum χ t a - ∑ j ∈ Finset.range N, (a j).coefficient,
      hb.sub (by simpa only [Finset.sum_fn] using
        ContDiff.sum fun j _ => (a j).contDiff_coefficient),
      fun K hK α β => hrem N hK α β⟩, rfl⟩⟩
  simpa only [Finset.range_zero, Finset.sum_empty, sub_zero] using hrem 0 hK α β

end Symbol

end TauCeti
