/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Algebra.Order.Floor.Digits
import TauCeti.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.MeasureTheory.Integral.Lebesgue.Cumulative
import TauCeti.MeasureTheory.Integral.Lebesgue.OrdConnected

/-!
# The Christ–Kiselev lemma

Let `β : ℝ × ℝ → G` be integrable on the region `{(s, t) | s < t}`, and think of `β (s, t)` as
the pairing of an operator kernel `K(t, s)` applied to `f(s)` with `g(t)`, for instance
`⟪S(t - s) F(s), G(t)⟫` for a propagator `S`. Suppose that integrating `β` over a rectangle
`I × J` of intervals with `I` to the left of `J` costs at most

`‖∫_{I × J} β‖ ≤ A ‖1_I f‖_p ‖1_J g‖_r`,

which holds whenever the untruncated operator `f ↦ ∫ K(·, s) f(s) ds` is bounded from `Lᵖ` to
`L^{r'}`, by testing it on `1_I f` against `1_J g`. The **Christ–Kiselev lemma** says that if
`1 ≤ r` and `1 / p + 1 / r > 1`, that is `p < r'`, then the truncation to `s < t` is bounded too:

`‖∫_{s < t} β‖ ≤ (1 - 2^{-δ})⁻¹ A ‖f‖_p ‖g‖_r`, where `δ = 1 / p + 1 / r - 1`
(`TauCeti.eNorm_setIntegral_fst_lt_snd_le`).

This is how retarded (Duhamel) estimates `‖∫_{s < t} K(t, s) F(s) ds‖_{L^q_t} ≲ ‖F‖_{L^{p}_t}` are
deduced from bounds on the corresponding untruncated operators, for instance the inhomogeneous
Strichartz estimates with two different admissible pairs from the homogeneous ones. The functions
`f` and `g` take values in arbitrary normed groups, so mixed norms `L^p_t L^a_x` are covered by
taking `f : ℝ → Lᵃ`. The hypothesis `p < r'` cannot be dropped: the Hilbert transform, with kernel
`1 / (π (t - s))`, is bounded on `L²(ℝ)`, while its truncation `∫_{s < t} f(s) / (π (t - s)) ds`
diverges at every `t ∈ (0, 1)` for `f = 1_{[0, 1]}`.

## The argument

The cumulative mass `s ↦ ∫_{-∞}^s ‖f‖^p`, made strictly increasing by adding `ε σ(s)` for the
logistic sigmoid `σ` and divided by `M = ‖f‖_p^p + ε`, is a strictly increasing map
`φ : ℝ → [0, 1)`. Pulling back the dyadic intervals of `[0, 1)` along `φ` cuts `ℝ` into
intervals `I_{m, j} = {s | ⌊2^m φ(s)⌋ = j}` with `∫_{I_{m, j}} ‖f‖^p ≤ M 2^{-m}`. The region
`s < t` is the disjoint union of the dyadic Whitney rectangles
`I_{n + 1, 2k} × I_{n + 1, 2k + 1}`, `n ≥ 0`, `k < 2ⁿ`: for `φ(s) < φ(t)`, the level `n + 1` is
the first one at which their binary expansions differ. The hypothesis bounds the integral over
each rectangle at level `n` by `A (M 2^{-(n + 1)})^{1/p} ‖1_{J_k} g‖_r`, and Hölder's inequality
for the `2ⁿ` disjoint pieces `J_k` gives `∑_k ‖1_{J_k} g‖_r ≤ 2^{n (1 - 1/r)} ‖g‖_r`. The level
`n` therefore contributes at most `A M^{1/p} ‖g‖_r 2^{-n δ}`, a geometric series, and letting
`ε → 0` gives the claim.

## Main declarations

* `TauCeti.eNorm_setIntegral_fst_lt_snd_le`: the Christ–Kiselev lemma, in bilinear form.

## References

* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. **179**
  (2001), 409–425.
* H. F. Smith and C. D. Sogge, *Global Strichartz estimates for nontrapping perturbations of the
  Laplacian*, Comm. Partial Differential Equations **25** (2000), 2171–2183.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Lemma 2.4.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The dyadic Whitney decomposition of `{s < t}` -/

/-- The points whose image under `φ` lies in the `j`-th dyadic interval of length `2^{-m}`. -/
private def level (φ : ℝ → ℝ) (m j : ℕ) : Set ℝ := {s | ⌊2 ^ m * φ s⌋₊ = j}

/-- The Whitney rectangle with index `(n, k)`: the left and right children, at level `n + 1`, of
the `k`-th dyadic interval at level `n`. -/
private def box (φ : ℝ → ℝ) (i : ℕ × ℕ) : Set (ℝ × ℝ) :=
  level φ (i.1 + 1) (2 * i.2) ×ˢ level φ (i.1 + 1) (2 * i.2 + 1)

variable {φ : ℝ → ℝ}

private theorem ordConnected_level (hφ : Monotone φ) (m j : ℕ) : (level φ m j).OrdConnected :=
  ⟨fun _ hs _ ht _ hu => le_antisymm
    (ht ▸ Nat.floor_mono (mul_le_mul_of_nonneg_left (hφ hu.2) (by positivity)))
    (hs ▸ Nat.floor_mono (mul_le_mul_of_nonneg_left (hφ hu.1) (by positivity)))⟩

private theorem measurableSet_level (hφ : Monotone φ) (m j : ℕ) : MeasurableSet (level φ m j) :=
  (ordConnected_level hφ m j).measurableSet

private theorem lt_of_mem_level (hφ : StrictMono φ) {m j j' : ℕ} (hjj' : j < j') {s t : ℝ}
    (hs : s ∈ level φ m j) (ht : t ∈ level φ m j') : s < t := by
  refine hφ.lt_iff_lt.1 (lt_of_not_ge fun h => ?_)
  have := Nat.floor_mono (mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 ^ m))
  simp only [level, mem_ofPred_eq] at hs ht
  omega

private theorem level_eq_empty (h0 : ∀ s, 0 ≤ φ s) (h1 : ∀ s, φ s < 1) {m j : ℕ} (hj : 2 ^ m ≤ j) :
    level φ m j = ∅ := by
  refine eq_empty_of_forall_notMem fun s hs => ?_
  have : ⌊2 ^ m * φ s⌋₊ < 2 ^ m := by
    rw [Nat.floor_lt (by have := h0 s; positivity)]
    push_cast
    nlinarith [h1 s, h0 s, (by positivity : (0 : ℝ) < 2 ^ m)]
  simp only [level, mem_ofPred_eq] at hs
  omega

private theorem iUnion_box (hφ : StrictMono φ) (h0 : ∀ s, 0 ≤ φ s) (h1 : ∀ s, φ s < 1) :
    ⋃ i, box φ i = {z : ℝ × ℝ | z.1 < z.2} := by
  ext ⟨s, t⟩
  simp only [mem_iUnion, box, mem_prod, level, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hs, ht⟩
    exact lt_of_mem_level hφ (Nat.lt_succ_self _) hs ht
  · intro hst
    obtain ⟨n, k, hs, ht⟩ := exists_floor_two_pow_mul_eq (h0 s) (hφ hst) (h1 t)
    exact ⟨(n, k), hs, ht⟩

private theorem pairwise_disjoint_box : Pairwise (Function.onFun Disjoint (box φ)) := by
  rintro ⟨n, k⟩ ⟨n', k'⟩ hne
  refine disjoint_left.2 fun ⟨s, t⟩ h h' => hne ?_
  simp only [box, mem_prod, level, mem_ofPred_eq] at h h'
  obtain ⟨rfl, rfl⟩ := eq_of_floor_two_pow_mul_eq h.1 h.2 h'.1 h'.2
  rfl

/-- The integral over `{s < t}` is the sum of the integrals over the Whitney rectangles. -/
private theorem hasSum_setIntegral_box {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hφ : StrictMono φ) (h0 : ∀ s, 0 ≤ φ s) (h1 : ∀ s, φ s < 1) {β : ℝ × ℝ → G}
    (hβ : IntegrableOn β {z : ℝ × ℝ | z.1 < z.2}) :
    HasSum (fun i => ∫ z in box φ i, β z) (∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z) := by
  rw [← iUnion_box hφ h0 h1]
  refine hasSum_integral_iUnion (fun i => ?_) pairwise_disjoint_box ?_
  · exact (measurableSet_level hφ.monotone _ _).prod (measurableSet_level hφ.monotone _ _)
  · rwa [iUnion_box hφ h0 h1]

/-- **The Whitney bound.** The rectangle bounds of the Christ–Kiselev lemma, summed over the
Whitney rectangles of a strictly increasing `φ : ℝ → [0, 1)`. -/
private theorem eNorm_setIntegral_fst_lt_snd_le_tsum {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] {p r : ℝ≥0∞}
    (hφ : StrictMono φ) (h0 : ∀ s, 0 ≤ φ s) (h1 : ∀ s, φ s < 1) {β : ℝ × ℝ → G}
    (hβ : IntegrableOn β {z : ℝ × ℝ | z.1 < z.2}) (f : ℝ → E) (g : ℝ → F) {A : ℝ≥0∞}
    (hA : ∀ I J : Set ℝ, I.OrdConnected → J.OrdConnected → (∀ s ∈ I, ∀ t ∈ J, s < t) →
      ‖∫ z in I ×ˢ J, β z‖ₑ ≤ A * eLpNorm (I.indicator f) p * eLpNorm (J.indicator g) r) :
    ‖∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z‖ₑ ≤
      ∑' n : ℕ, ∑ k ∈ Finset.range (2 ^ n), A * eLpNorm ((level φ (n + 1) (2 * k)).indicator f) p *
        eLpNorm ((level φ (n + 1) (2 * k + 1)).indicator g) r := by
  rw [← (hasSum_setIntegral_box hφ h0 h1 hβ).tsum_eq]
  refine eNorm_tsum_le_tsum_eNorm.trans ?_
  rw [tsum_prod']
  refine tsum_le_tsum fun n => ?_
  rw [tsum_eq_sum (s := Finset.range (2 ^ n)) fun k hk => ?_]
  · refine Finset.sum_le_sum fun k _ => hA _ _ (ordConnected_level hφ.monotone _ _)
      (ordConnected_level hφ.monotone _ _) fun s hs t ht =>
      lt_of_mem_level hφ (Nat.lt_succ_self _) hs ht
  · have hk : 2 ^ (n + 1) ≤ 2 * k := by
      rw [Finset.mem_range, not_lt] at hk
      rw [pow_succ]
      omega
    simp [box, level_eq_empty h0 h1 hk]

/-! ### Measure bounds -/

/-- The geometric decay of the level-`n` contribution: `(X 2^{-(n + 1)})^a 2^{n(1 - b)}` is at most
`X^a (2^{1 - a - b})ⁿ`. -/
private theorem rpow_div_two_pow_mul_le {a b : ℝ} (ha : 0 ≤ a) (X : ℝ≥0∞) (n : ℕ) :
    (X / 2 ^ (n + 1)) ^ a * ((2 ^ n : ℕ) : ℝ≥0∞) ^ (1 - b) ≤
      X ^ a * ((2 : ℝ≥0∞) ^ (1 - a - b)) ^ n := by
  have hcomm (k : ℕ) (y : ℝ) (x : ℝ≥0∞) : (x ^ k) ^ y = (x ^ y) ^ k := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm, ENNReal.rpow_mul,
      ENNReal.rpow_natCast]
  have h2a : ((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) ^ a ≤ ((2 : ℝ≥0∞)⁻¹ ^ a) ^ n := by
    rw [hcomm]
    exact pow_le_pow_of_le_one bot_le (ENNReal.rpow_le_one (by norm_num) ha) (Nat.le_succ n)
  calc (X / 2 ^ (n + 1)) ^ a * ((2 ^ n : ℕ) : ℝ≥0∞) ^ (1 - b)
      = X ^ a * (((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) ^ a * ((2 : ℝ≥0∞) ^ (1 - b)) ^ n) := by
        rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.inv_pow, mul_assoc,
          Nat.cast_pow, Nat.cast_ofNat, hcomm]
    _ ≤ X ^ a * (((2 : ℝ≥0∞)⁻¹ ^ a) ^ n * ((2 : ℝ≥0∞) ^ (1 - b)) ^ n) := by gcongr
    _ = X ^ a * ((2 : ℝ≥0∞) ^ (1 - a - b)) ^ n := by
        rw [← mul_pow, ENNReal.inv_rpow, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
        ring_nf

/-- The dyadic pieces of `φ` carry little mass when `φ` grows at least as fast as the cumulative
integral of `h` divided by `M`. -/
private theorem setLIntegral_level_le {h : ℝ → ℝ≥0∞} (hm : ∫⁻ x, h x ≠ ∞) (hφ : Monotone φ)
    {M : ℝ} (hM : 0 < M) (hinc : ∀ s t, s ≤ t →
      (∫⁻ x in Iic t, h x).toReal - (∫⁻ x in Iic s, h x).toReal ≤ M * (φ t - φ s))
    (h0 : ∀ s, 0 ≤ φ s) (n j : ℕ) :
    ∫⁻ x in level φ n j, h x ≤ ENNReal.ofReal M / 2 ^ n := by
  refine setLIntegral_le_of_ordConnected (ordConnected_level hφ n j) fun s hs t ht hst => ?_
  -- The integral over `[s, t]` is the increment of the cumulative integral.
  have hfin (u : ℝ) : ∫⁻ x in Iic u, h x ≠ ∞ :=
    ne_top_of_le_ne_top hm (setLIntegral_le_lintegral _ _)
  rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, setLIntegral_Ioc_eq_sub (hfin s),
    ← ENNReal.ofReal_toReal (ENNReal.sub_ne_top (hfin t)),
    ENNReal.toReal_sub_of_le (lintegral_mono_set (Iic_subset_Iic.2 hst)) (hfin t)]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← ENNReal.ofReal_toReal (a := 2 ^ n) (by simp), ← ENNReal.ofReal_div_of_pos (by simp),
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [level, mem_ofPred_eq] at hs ht
  rw [Nat.floor_eq_iff (mul_nonneg h2.le (h0 s))] at hs
  rw [Nat.floor_eq_iff (mul_nonneg h2.le (h0 t))] at ht
  rw [le_div_iff₀ h2]
  have hwidth : 2 ^ n * φ t - 2 ^ n * φ s < 1 := by linarith [hs.1, ht.2]
  nlinarith [mul_le_mul_of_nonneg_right (hinc s t hst) h2.le, mul_lt_mul_of_pos_left hwidth hM]

/-- **The normalized mass function.** If `h` has finite integral `m`, then for every `ε > 0` there
is a strictly increasing `φ : ℝ → [0, 1)` whose dyadic pieces `I_{n, j}` each carry at most
`(m + ε) 2^{-n}` of the integral of `h`. -/
private theorem exists_strictMono_setLIntegral_level_le {h : ℝ → ℝ≥0∞} (hm : ∫⁻ x, h x ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ (∀ s, 0 ≤ φ s) ∧ (∀ s, φ s < 1) ∧
      ∀ n j, ∫⁻ x in level φ n j, h x ≤ ((∫⁻ x, h x) + ENNReal.ofReal ε) / 2 ^ n := by
  obtain ⟨σ, hσ, hσ01⟩ : ∃ σ : ℝ → ℝ, StrictMono σ ∧ ∀ s, 0 < σ s ∧ σ s < 1 :=
    ⟨Real.sigmoid, Real.sigmoid_strictMono, fun s => ⟨Real.sigmoid_pos s, Real.sigmoid_lt_one s⟩⟩
  -- The cumulative integral `Φ(s) = ∫_{-∞}^s h`, perturbed by `ε σ` and divided by `M = m + ε`.
  have hΦ (s : ℝ) : (∫⁻ x in Iic s, h x).toReal ≤ (∫⁻ x, h x).toReal :=
    ENNReal.toReal_mono hm (setLIntegral_le_lintegral _ _)
  have hΦmono : Monotone fun s => (∫⁻ x in Iic s, h x).toReal := fun s t hst =>
    ENNReal.toReal_mono (ne_top_of_le_ne_top hm (setLIntegral_le_lintegral _ _))
      (lintegral_mono_set (Iic_subset_Iic.2 hst))
  have hM : 0 < (∫⁻ x, h x).toReal + ε := by positivity
  have hφ : StrictMono fun s => ((∫⁻ x in Iic s, h x).toReal + ε * σ s) /
      ((∫⁻ x, h x).toReal + ε) :=
    StrictMono.div_const (hΦmono.add_strictMono (hσ.const_mul hε)) hM
  have h0 (s : ℝ) : 0 ≤ ((∫⁻ x in Iic s, h x).toReal + ε * σ s) / ((∫⁻ x, h x).toReal + ε) :=
    div_nonneg (add_nonneg ENNReal.toReal_nonneg (mul_pos hε (hσ01 s).1).le) hM.le
  refine ⟨_, hφ, h0, fun s => (div_lt_one hM).2 (by nlinarith [hΦ s, hσ01 s]), fun n j => ?_⟩
  have hX : (∫⁻ x, h x) + ENNReal.ofReal ε = ENNReal.ofReal ((∫⁻ x, h x).toReal + ε) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le, ENNReal.ofReal_toReal hm]
  rw [hX]
  refine setLIntegral_level_le hm hφ.monotone hM (fun s t hst => ?_) h0 n j
  have := hσ.monotone hst
  rw [mul_sub, mul_div_cancel₀ _ hM.ne', mul_div_cancel₀ _ hM.ne']
  nlinarith

/-- **The level-`n` bound.** If the dyadic pieces of `φ` carry at most `X 2^{-n}` of `‖f‖^p`, the
Whitney rectangles at level `n` contribute at most `A X^{1/p} ‖g‖_r (2^{1 - 1/p - 1/r})ⁿ`. -/
private theorem sum_mul_eLpNorm_level_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p r : ℝ≥0∞} (hp : p ≠ 0) (hp_top : p ≠ ∞) (hr : 1 ≤ r) (hφ : Monotone φ) {f : ℝ → E}
    (hf : AEStronglyMeasurable f) {X : ℝ≥0∞}
    (hX : ∀ n j, ∫⁻ x in level φ n j, ‖f x‖ₑ ^ p.toReal ≤ X / 2 ^ n) (g : ℝ → F) (A : ℝ≥0∞)
    (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n), A * eLpNorm ((level φ (n + 1) (2 * k)).indicator f) p *
        eLpNorm ((level φ (n + 1) (2 * k + 1)).indicator g) r ≤
      A * X ^ p.toReal⁻¹ * eLpNorm g r * ((2 : ℝ≥0∞) ^ (1 - p.toReal⁻¹ - r.toReal⁻¹)) ^ n := by
  -- The restrictions of `f` to the pieces at level `n + 1` have small `Lᵖ` norms.
  have hpiece (k : ℕ) : eLpNorm ((level φ (n + 1) k).indicator f) p ≤
      (X / 2 ^ (n + 1)) ^ p.toReal⁻¹ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_level hφ _ _).nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp hp_top hf.restrict, one_div]
    gcongr
    exact hX _ _
  -- The pieces of `g` are disjoint, so Hölder's inequality sums their norms.
  have hg : ∑ k ∈ Finset.range (2 ^ n), eLpNorm ((level φ (n + 1) (2 * k + 1)).indicator g) r ≤
      ((2 ^ n : ℕ) : ℝ≥0∞) ^ (1 - r.toReal⁻¹) * eLpNorm g r := by
    refine (sum_eLpNorm_indicator_le hr _ (fun k _ => measurableSet_level hφ _ _)
      (fun k _ k' _ hkk' => disjoint_left.2 fun s hs hs' => hkk' ?_) g).trans_eq (by
        rw [Finset.card_range])
    simp only [level, mem_ofPred_eq] at hs hs'
    omega
  refine (Finset.sum_le_sum fun k _ => mul_le_mul_left (mul_le_mul_right (hpiece _) A) _).trans ?_
  rw [← Finset.mul_sum]
  refine (mul_le_mul_right hg _).trans ?_
  have key := rpow_div_two_pow_mul_le (b := r.toReal⁻¹) (by positivity : 0 ≤ p.toReal⁻¹) X n
  have hrw : A * (X / 2 ^ (n + 1)) ^ p.toReal⁻¹ *
      (((2 ^ n : ℕ) : ℝ≥0∞) ^ (1 - r.toReal⁻¹) * eLpNorm g r) = A * eLpNorm g r *
        ((X / 2 ^ (n + 1)) ^ p.toReal⁻¹ * ((2 ^ n : ℕ) : ℝ≥0∞) ^ (1 - r.toReal⁻¹)) := by ring
  rw [hrw]
  refine (mul_le_mul_right key _).trans_eq ?_
  ring

/-! ### The Christ–Kiselev lemma -/

/-- The Christ–Kiselev bound with `‖f‖_p^p` replaced by `‖f‖_p^p + ε`, from the Whitney
decomposition along the cumulative mass of `f`. -/
private theorem eNorm_setIntegral_fst_lt_snd_le_add {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] {p r : ℝ≥0∞}
    (hp : p ≠ 0) (hp_top : p ≠ ∞) (hr : 1 ≤ r) {β : ℝ × ℝ → G}
    (hβ : IntegrableOn β {z : ℝ × ℝ | z.1 < z.2}) {f : ℝ → E} (hf : AEStronglyMeasurable f)
    (hm : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ≠ ∞) (g : ℝ → F) {A : ℝ≥0∞}
    (hA : ∀ I J : Set ℝ, I.OrdConnected → J.OrdConnected → (∀ s ∈ I, ∀ t ∈ J, s < t) →
      ‖∫ z in I ×ˢ J, β z‖ₑ ≤ A * eLpNorm (I.indicator f) p * eLpNorm (J.indicator g) r)
    {ε : ℝ} (hε : 0 < ε) :
    ‖∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z‖ₑ ≤
      (1 - 2 ^ (1 - p.toReal⁻¹ - r.toReal⁻¹))⁻¹ * A *
        ((∫⁻ x, ‖f x‖ₑ ^ p.toReal) + ENNReal.ofReal ε) ^ p.toReal⁻¹ * eLpNorm g r := by
  obtain ⟨φ, hφ, hφ0, hφ1, hmass⟩ := exists_strictMono_setLIntegral_level_le hm hε
  refine (eNorm_setIntegral_fst_lt_snd_le_tsum hφ hφ0 hφ1 hβ f g hA).trans ?_
  refine (tsum_le_tsum fun n =>
    sum_mul_eLpNorm_level_le hp hp_top hr hφ.monotone hf hmass g A n).trans_eq ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  ring

/-- The exponent bookkeeping of the Christ–Kiselev lemma: for `1 / p + 1 / r > 1` with `p ≠ 0`
and `1 ≤ r`, the exponent `p` is finite and `δ = 1 / p + 1 / r - 1` is positive. -/
private theorem ne_top_and_toReal_inv_add_inv_sub_one {p r : ℝ≥0∞} (hp : p ≠ 0) (hr : 1 ≤ r)
    (hpr : 1 < p⁻¹ + r⁻¹) :
    p ≠ ∞ ∧ -(p⁻¹ + r⁻¹ - 1).toReal = 1 - p.toReal⁻¹ - r.toReal⁻¹ ∧
      1 - p.toReal⁻¹ - r.toReal⁻¹ < 0 := by
  have hr_inv : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hr
  have hr_ne : r⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hr_inv
  have hsum_ne : p⁻¹ + r⁻¹ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hp, hr_ne⟩
  have hδ : -(p⁻¹ + r⁻¹ - 1).toReal = 1 - p.toReal⁻¹ - r.toReal⁻¹ := by
    rw [ENNReal.toReal_sub_of_le hpr.le hsum_ne, ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp) hr_ne,
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one]
    ring
  refine ⟨?_, hδ, ?_⟩
  · rintro rfl
    simp only [ENNReal.inv_top, zero_add] at hpr
    exact hr_inv.not_gt hpr
  · rw [← hδ]
    exact neg_neg_of_pos (ENNReal.toReal_pos (tsub_pos_of_lt hpr).ne' (ENNReal.sub_ne_top hsum_ne))

/-- If the bound of the Christ–Kiselev lemma vanishes, so does the integral over `{s < t}`: the
integral over every Whitney rectangle vanishes. -/
private theorem eNorm_setIntegral_fst_lt_snd_eq_zero {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] {p r : ℝ≥0∞} {β : ℝ × ℝ → G}
    (hβ : IntegrableOn β {z : ℝ × ℝ | z.1 < z.2}) (f : ℝ → E) (g : ℝ → F) {A : ℝ≥0∞}
    (hA : ∀ I J : Set ℝ, I.OrdConnected → J.OrdConnected → (∀ s ∈ I, ∀ t ∈ J, s < t) →
      ‖∫ z in I ×ˢ J, β z‖ₑ ≤ A * eLpNorm (I.indicator f) p * eLpNorm (J.indicator g) r)
    (h0 : A * eLpNorm f p * eLpNorm g r = 0) :
    ‖∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z‖ₑ = 0 := by
  obtain ⟨σ, hσ, hσ01⟩ : ∃ σ : ℝ → ℝ, StrictMono σ ∧ ∀ s, 0 < σ s ∧ σ s < 1 :=
    ⟨Real.sigmoid, Real.sigmoid_strictMono, fun s => ⟨Real.sigmoid_pos s, Real.sigmoid_lt_one s⟩⟩
  have hterm (I J : Set ℝ) (hI : MeasurableSet I) (hJ : MeasurableSet J) :
      A * eLpNorm (I.indicator f) p * eLpNorm (J.indicator g) r = 0 := by
    refine le_antisymm (le_trans ?_ h0.le) bot_le
    gcongr
    exacts [eLpNorm_indicator_le f hI.nullMeasurableSet,
      eLpNorm_indicator_le g hJ.nullMeasurableSet]
  refine le_antisymm ((eNorm_setIntegral_fst_lt_snd_le_tsum hσ (fun s => (hσ01 s).1.le)
    (fun s => (hσ01 s).2) hβ f g hA).trans_eq ?_) bot_le
  exact tsum_eq_zero_iff.2 fun n => Finset.sum_eq_zero fun k _ =>
    hterm _ _ (measurableSet_level hσ.monotone _ _) (measurableSet_level hσ.monotone _ _)

/-- **The Christ–Kiselev lemma**, in bilinear form. Let `1 / p + 1 / r > 1` with `1 ≤ r`, and let
`β : ℝ × ℝ → G` be integrable on `{(s, t) | s < t}`. Suppose that for intervals `I` and `J` with
`I` to the left of `J`,

`‖∫_{I × J} β‖ ≤ A ‖1_I f‖_p ‖1_J g‖_r`.

Then `‖∫_{s < t} β‖ ≤ (1 - 2^{-δ})⁻¹ A ‖f‖_p ‖g‖_r`, where `δ = 1 / p + 1 / r - 1 > 0`.

For `β (s, t) = ⟪K(t, s) f(s), g(t)⟫`, the hypothesis follows from boundedness of the operator
`f ↦ ∫ K(·, s) f(s) ds` from `Lᵖ` to `L^{r'}`, and the conclusion is the boundedness of its
truncation `f ↦ ∫_{s < ·} K(·, s) f(s) ds` in weak form. -/
theorem eNorm_setIntegral_fst_lt_snd_le {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] {p r : ℝ≥0∞}
    (hr : 1 ≤ r) (hpr : 1 < p⁻¹ + r⁻¹) {β : ℝ × ℝ → G}
    (hβ : IntegrableOn β {z : ℝ × ℝ | z.1 < z.2}) (f : ℝ → E) (g : ℝ → F) {A : ℝ≥0∞}
    (hA : ∀ I J : Set ℝ, I.OrdConnected → J.OrdConnected → (∀ s ∈ I, ∀ t ∈ J, s < t) →
      ‖∫ z in I ×ˢ J, β z‖ₑ ≤ A * eLpNorm (I.indicator f) p * eLpNorm (J.indicator g) r) :
    ‖∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z‖ₑ ≤
      (1 - 2 ^ (-(p⁻¹ + r⁻¹ - 1).toReal))⁻¹ * A * eLpNorm f p * eLpNorm g r := by
  -- If the right side vanishes, so does the integral. This includes the degenerate case `p = 0`.
  rcases eq_or_ne (A * eLpNorm f p * eLpNorm g r) 0 with h0 | h0
  · rw [eNorm_setIntegral_fst_lt_snd_eq_zero hβ f g hA h0]
    exact bot_le
  -- If the right side is infinite there is nothing to prove.
  set C : ℝ≥0∞ := (1 - 2 ^ (-(p⁻¹ + r⁻¹ - 1).toReal))⁻¹
  have hC : C ≠ 0 := ENNReal.inv_ne_zero.2 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hassoc : C * A * eLpNorm f p * eLpNorm g r = C * (A * eLpNorm f p * eLpNorm g r) := by ring
  rcases eq_or_ne (A * eLpNorm f p * eLpNorm g r) ∞ with htop | htop
  · rw [hassoc, htop, ENNReal.mul_top hC]
    exact le_top
  -- Otherwise every factor is finite and positive; let `ε → 0` in the bound with mass
  -- `‖f‖_p^p + ε`.
  have hA0 : A ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h0)
  have hf0 : eLpNorm f p ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h0)
  have hg0 : eLpNorm g r ≠ 0 := right_ne_zero_of_mul h0
  have hAtop : A ≠ ∞ := fun h => htop (by rw [h, ENNReal.top_mul hf0, ENNReal.top_mul hg0])
  have hftop : eLpNorm f p ≠ ∞ := fun h => htop (by
    rw [h, ENNReal.mul_top hA0, ENNReal.top_mul hg0])
  have hgtop : eLpNorm g r ≠ ∞ := fun h => htop (by
    rw [h, ENNReal.mul_top (left_ne_zero_of_mul h0)])
  have hfm := aestronglyMeasurable_of_eLpNorm_ne_top hftop
  have hp : p ≠ 0 := fun h => hf0 (h ▸ eLpNorm_exponent_zero hfm)
  obtain ⟨hp_top, hδ, hδ0⟩ := ne_top_and_toReal_inv_add_inv_sub_one hp hr hpr
  have hCtop : C ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt
    (ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (hδ ▸ hδ0))).ne'
  have hf_eq : eLpNorm f p = (∫⁻ x, ‖f x‖ₑ ^ p.toReal) ^ p.toReal⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp hp_top hfm, one_div]
  have hp₀ : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  have hm : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ≠ ∞ := by
    intro h
    rw [hf_eq, h, ENNReal.top_rpow_of_pos (inv_pos.2 hp₀)] at hftop
    exact hftop rfl
  have hlim : Tendsto (fun ε : ℝ => C * A * eLpNorm g r *
      ((∫⁻ x, ‖f x‖ₑ ^ p.toReal) + ENNReal.ofReal ε) ^ p.toReal⁻¹) (𝓝[>] 0)
      (𝓝 (C * A * eLpNorm g r * eLpNorm f p)) := by
    refine ENNReal.Tendsto.const_mul ?_
      (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top hCtop hAtop) hgtop))
    have hcont : Continuous fun ε : ℝ =>
        ((∫⁻ x, ‖f x‖ₑ ^ p.toReal) + ENNReal.ofReal ε) ^ p.toReal⁻¹ :=
      ENNReal.continuous_rpow_const.comp (continuous_const.add ENNReal.continuous_ofReal)
    have := hcont.tendsto 0
    rw [ENNReal.ofReal_zero, add_zero, ← hf_eq] at this
    exact this.mono_left nhdsWithin_le_nhds
  calc ‖∫ z in {z : ℝ × ℝ | z.1 < z.2}, β z‖ₑ ≤ C * A * eLpNorm g r * eLpNorm f p := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        refine (eNorm_setIntegral_fst_lt_snd_le_add hp hp_top hr hβ hfm hm g hA hε).trans_eq ?_
        rw [← hδ]
        ring
    _ = _ := by ring

end TauCeti
