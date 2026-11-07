/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd
import TauCeti.Analysis.Polynomial.EvalRpow
import TauCeti.Analysis.Polynomial.Integral
import TauCeti.Analysis.Polynomial.OneSidedApproximation
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The logarithmic Tauberian theorem for zeta residues

Let `μ₀ ≥ μ₁ ≥ ⋯ ≥ 0` be a nonincreasing sequence, for instance the singular values of a compact
operator, and write `ζ(s) = ∑ⱼ μⱼ ^ s` for its zeta function. This file proves that the residue
of `ζ` at `s = 1` and the limit of the logarithmic means of `μ` determine each other:

`lim_(s ↓ 1) (s - 1) ζ(s) = L  ↔  lim_(N → ∞) (log (N + 2))⁻¹ ∑_(j ≤ N) μⱼ = L`,

provided `ζ(s)` converges for every `s > 1`. This is the analytic input that identifies the
Dixmier trace of a positive operator in the logarithmic ideal `L^(1,∞)` with the residue of its
zeta function. Convergence of `ζ` holds in particular when the logarithmic means are bounded,
which is the membership condition for `L^(1,∞)`.

## Main declarations

* `TauCeti.summable_rpow_of_sum_le_mul_log`: bounded logarithmic means make `∑ⱼ μⱼ ^ s` converge
  for every `s > 1`.
* `TauCeti.tendsto_sub_one_mul_tsum_rpow_of_tendsto_sum_div_log`: convergent logarithmic means
  give the same residue of the zeta function (the Abelian direction).
* `TauCeti.tendsto_sum_div_log_of_tendsto_sub_one_mul_tsum_rpow`: a residue of the zeta function
  forces the logarithmic means to converge to it (the Tauberian direction).
* `TauCeti.tendsto_sub_one_mul_tsum_rpow_iff_tendsto_sum_div_log`: the equivalence.

## Implementation notes

Both directions pass through the *level sums* `M(x) = ∑_(μⱼ ≥ exp (-x)) μⱼ`, which grow like
`L x` exactly when the logarithmic means tend to `L`; monotonicity of `μ` is what makes the two
normalizations comparable. In the level variable the zeta function is a Laplace–Stieltjes
transform, `ζ(1 + ε) = ∑ⱼ μⱼ exp (-ε (-log μⱼ))`, so:

* the *Abelian* direction (means to residue) sums `M` against the weights `(1 - q) q ^ k` with
  `q = exp (-ε)`, after bracketing each `μⱼ ^ ε` between consecutive powers of `q`;
* the *Tauberian* direction (residue to means) is Karamata's argument: the hypothesis evaluates
  `ε ∑ⱼ μⱼ ^ (1 + ε) P(μⱼ ^ ε)` in the limit for every polynomial `P`, and the Weierstrass
  approximation theorem squeezes the indicator of `[exp (-t), 1]` between polynomials of nearly
  equal integral, which gives the asymptotics of `M`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
* J. Karamata, *Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes*,
  Math. Z. **32** (1930), 319–320.
* J. Korevaar, *Tauberian Theory: A Century of Developments*, Springer, 2004, Chapter I.
-/

public section

open Filter Topology Finset Real Polynomial

namespace TauCeti

variable {μ : ℕ → ℝ}

/-! ### Level sums -/

/-- The sum of the entries of `μ` that are at least `exp (-x)`. -/
private noncomputable def levelSum (μ : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j, if exp (-x) ≤ μ j then μ j else 0

private lemma levelSum_nonneg (hμ0 : ∀ j, 0 ≤ μ j) (x : ℝ) : 0 ≤ levelSum μ x :=
  tsum_nonneg fun j ↦ ite_nonneg (hμ0 j) le_rfl

/-- Beyond an index `n` with `μ n < exp (-x)`, an antitone `μ` has no entries at level `x`. -/
private lemma levelTerm_eq_zero (hμ : Antitone μ) {n j : ℕ} {x : ℝ} (hn : μ n < exp (-x))
    (hj : j ∉ range n) : (if exp (-x) ≤ μ j then μ j else 0) = 0 :=
  ite_eq_right (not_le.2 ((hμ (not_lt.1 (mem_range.not.1 hj))).trans_lt hn))

private lemma summable_levelTerm (hμ : Antitone μ) (hμt : Tendsto μ atTop (𝓝 0)) (x : ℝ) :
    Summable fun j ↦ if exp (-x) ≤ μ j then μ j else 0 := by
  obtain ⟨n, hn⟩ := (hμt.eventually (gt_mem_nhds (exp_pos (-x)))).exists
  exact summable_of_ne_finset_zero (s := range n) fun j hj ↦ levelTerm_eq_zero hμ hn hj

private lemma levelSum_le_sum_range (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ) {n : ℕ} {x : ℝ}
    (hn : μ n < exp (-x)) : levelSum μ x ≤ ∑ j ∈ range n, μ j := by
  rw [levelSum, tsum_eq_sum fun j hj ↦ levelTerm_eq_zero hμ hn hj]
  exact sum_le_sum fun j _ ↦ by split_ifs <;> simp [hμ0 j]

private lemma sum_range_le_levelSum_add (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ)
    (hμt : Tendsto μ atTop (𝓝 0)) (n : ℕ) (x : ℝ) :
    ∑ j ∈ range n, μ j ≤ levelSum μ x + n * exp (-x) := by
  calc ∑ j ∈ range n, μ j
      ≤ ∑ j ∈ range n, ((if exp (-x) ≤ μ j then μ j else 0) + exp (-x)) := by
        refine sum_le_sum fun j _ ↦ ?_
        split_ifs with h
        · linarith [exp_pos (-x)]
        · linarith [not_le.1 h]
    _ = ∑ j ∈ range n, (if exp (-x) ≤ μ j then μ j else 0) + n * exp (-x) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    _ ≤ levelSum μ x + n * exp (-x) := by
        gcongr
        exact (summable_levelTerm hμ hμt x).sum_le_tsum _ fun j _ ↦ ite_nonneg (hμ0 j) le_rfl

private lemma sum_div_log_nonneg (hμ0 : ∀ j, 0 ≤ μ j) (N : ℕ) :
    0 ≤ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2) :=
  div_nonneg (sum_nonneg fun j _ ↦ hμ0 j) (log_nonneg (by linarith [N.cast_nonneg (α := ℝ)]))

/-- If the logarithmic means converge, then `μ` tends to `0`. -/
private lemma tendsto_zero_of_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ) {L : ℝ}
    (h : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L)) :
    Tendsto μ atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ log ((N : ℝ) + 2) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul 2).comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    rw [mul_zero] at h1
    refine squeeze_zero (fun N ↦ div_nonneg (log_nonneg (by linarith [N.cast_nonneg (α := ℝ)]))
      (by positivity)) (fun N ↦ ?_) h1
    have hlogN : 0 ≤ log ((N : ℝ) + 2) := log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
    simp only [Function.comp_apply, id]
    rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    nlinarith [N.cast_nonneg (α := ℝ)]
  have := h.mul hlog
  rw [mul_zero] at this
  refine squeeze_zero hμ0 (fun N ↦ ?_) this
  have hS : ((N : ℝ) + 1) * μ N ≤ ∑ j ∈ range (N + 1), μ j := by
    simpa using card_nsmul_le_sum (range (N + 1)) μ (μ N) fun j hj ↦
      hμ (Nat.lt_succ_iff.1 (mem_range.1 hj))
  have hlog0 : 0 < log ((N : ℝ) + 2) := log_pos (by linarith [N.cast_nonneg (α := ℝ)])
  calc μ N ≤ (∑ j ∈ range (N + 1), μ j) / ((N : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
    _ = _ := by field_simp

/-! ### Level sums against logarithmic means -/

/-- Lower half of `tendsto_sum_div_log_of_tendsto_levelSum`. -/
private lemma lt_sum_div_log_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ) {L : ℝ}
    (h : Tendsto (fun x : ℝ ↦ levelSum μ x / x) atTop (𝓝 L))
    {a : ℝ} (ha : a < L) :
    ∀ᶠ N : ℕ in atTop, a < (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2) := by
  rcases lt_or_ge a 0 with ha0 | ha0
  · exact Eventually.of_forall fun N ↦ ha0.trans_le (sum_div_log_nonneg hμ0 N)
  obtain ⟨c, hac, hcL⟩ := exists_between ha
  obtain ⟨c', hac', hc'c⟩ := exists_between hac
  have hc : 0 < c := ha0.trans_lt hac
  set r := c' / c with hr
  have hr0 : 0 < r := div_pos (ha0.trans_lt hac') hc
  have hr1 : r < 1 := (div_lt_one hc).2 hc'c
  have hcr : c * r = c' := by rw [hr]; field_simp
  -- The level sum at `y = r log (N + 2)` is eventually above `c y`.
  have h1 : ∀ᶠ N : ℕ in atTop,
      c * (r * log ((N : ℝ) + 2)) < levelSum μ (r * log ((N : ℝ) + 2)) := by
    refine ((tendsto_log_natCast_add_atTop 2).const_mul_atTop hr0).eventually
      (p := fun y ↦ c * y < levelSum μ y) ?_
    filter_upwards [h.eventually (lt_mem_nhds hcL), eventually_gt_atTop 0] with y hy hy0
    rwa [lt_div_iff₀ hy0] at hy
  have h2 : ∀ᶠ N : ℕ in atTop,
      2 * c' * log ((N : ℝ) + 2) + 0 < exp ((1 - r) * log ((N : ℝ) + 2)) :=
    (tendsto_log_natCast_add_atTop 2).eventually (eventually_mul_add_lt_exp_mul (by linarith) _ _)
  filter_upwards [h1, h2, (tendsto_log_natCast_add_atTop 2).eventually_gt_atTop 0] with N h1 h2 hpos
  rw [lt_div_iff₀ hpos]
  set z := log ((N : ℝ) + 2)
  have haz : a * z < c' * z := by nlinarith
  have hcrz : c * (r * z) = c' * z := by rw [← mul_assoc, hcr]
  by_cases hN : μ (N + 1) < exp (-(r * z))
  · have := levelSum_le_sum_range hμ0 hμ hN
    linarith
  · -- Otherwise all of the first `N + 1` entries are large.
    have hS : ((N : ℝ) + 1) * exp (-(r * z)) ≤ ∑ j ∈ range (N + 1), μ j := by
      simpa using card_nsmul_le_sum (range (N + 1)) μ (exp (-(r * z))) fun j hj ↦
        ((not_lt.1 hN).trans (hμ (Nat.le_succ N))).trans (hμ (Nat.lt_succ_iff.1 (mem_range.1 hj)))
    have hez : exp z = N + 2 := exp_log (by positivity)
    have hsplit : exp ((1 - r) * z) = exp z * exp (-(r * z)) := by
      rw [← exp_add]; ring_nf
    have he : 0 < exp (-(r * z)) := exp_pos _
    have : exp ((1 - r) * z) ≤ 2 * ((N + 1) * exp (-(r * z))) := by
      rw [hsplit, hez]; nlinarith
    linarith

/-- Upper half of `tendsto_sum_div_log_of_tendsto_levelSum`. -/
private lemma sum_div_log_lt_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ)
    (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun x : ℝ ↦ levelSum μ x / x) atTop (𝓝 L))
    {b : ℝ} (hb : L < b) :
    ∀ᶠ N : ℕ in atTop, (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2) < b := by
  have hL : 0 ≤ L := ge_of_tendsto h (by
    filter_upwards [eventually_gt_atTop 0] with x hx using div_nonneg (levelSum_nonneg hμ0 x) hx.le)
  obtain ⟨c, hLc, hcb⟩ := exists_between hb
  obtain ⟨c', hcc', hc'b⟩ := exists_between hcb
  have hc : 0 < c := hL.trans_lt hLc
  set r := c' / c with hr
  have hr1 : 1 < r := (one_lt_div hc).2 hcc'
  have hcr : c * r = c' := by rw [hr]; field_simp
  have h1 : ∀ᶠ N : ℕ in atTop,
      levelSum μ (r * log ((N : ℝ) + 2)) < c * (r * log ((N : ℝ) + 2)) := by
    refine ((tendsto_log_natCast_add_atTop 2).const_mul_atTop (by linarith)).eventually
      (p := fun y ↦ levelSum μ y < c * y) ?_
    filter_upwards [h.eventually (gt_mem_nhds hLc), eventually_gt_atTop 0] with y hy hy0
    rwa [div_lt_iff₀ hy0] at hy
  have h3 : ∀ᶠ N : ℕ in atTop, 1 < (b - c') * log ((N : ℝ) + 2) :=
    ((tendsto_log_natCast_add_atTop 2).const_mul_atTop (sub_pos.2 hc'b)).eventually_gt_atTop 1
  filter_upwards [h1, h3, (tendsto_log_natCast_add_atTop 2).eventually_gt_atTop 0] with N h1 h3 hpos
  rw [div_lt_iff₀ hpos]
  set z := log ((N : ℝ) + 2)
  have hS := sum_range_le_levelSum_add hμ0 hμ hμt (N + 1) (r * z)
  -- The entries below the level contribute at most `(N + 1) exp (-r z) ≤ 1`.
  have he : ((N + 1 : ℕ) : ℝ) * exp (-(r * z)) ≤ 1 := by
    have h1' : exp (-(r * z)) ≤ exp (-z) := exp_le_exp.2 (by nlinarith)
    have h2' : exp (-z) = ((N : ℝ) + 2)⁻¹ := by rw [exp_neg, exp_log (by positivity)]
    rw [h2'] at h1'
    have : ((N + 1 : ℕ) : ℝ) * ((N : ℝ) + 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; push_cast; linarith
    calc _ ≤ ((N + 1 : ℕ) : ℝ) * ((N : ℝ) + 2)⁻¹ := by gcongr
      _ ≤ 1 := this
  nlinarith

/-- If the level sums grow like `L x`, the logarithmic means tend to `L`. -/
private lemma tendsto_sum_div_log_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ)
    (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun x : ℝ ↦ levelSum μ x / x) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L) :=
  tendsto_order.2 ⟨fun _ ha ↦ lt_sum_div_log_of_tendsto_levelSum hμ0 hμ h ha,
    fun _ hb ↦ sum_div_log_lt_of_tendsto_levelSum hμ0 hμ hμt h hb⟩

/-- Lower half of `tendsto_levelSum_of_tendsto_sum_div_log`. -/
private lemma lt_levelSum_div_of_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ)
    (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L))
    {a : ℝ} (ha : a < L) :
    ∀ᶠ x : ℝ in atTop, a < levelSum μ x / x := by
  rcases lt_or_ge a 0 with ha0 | ha0
  · filter_upwards [eventually_gt_atTop 0] with x hx using
      ha0.trans_le (div_nonneg (levelSum_nonneg hμ0 x) hx.le)
  obtain ⟨c, hac, hcL⟩ := exists_between ha
  obtain ⟨c', hac', hc'c⟩ := exists_between hac
  have hc : 0 < c := ha0.trans_lt hac
  set r := c' / c with hr
  have hr0 : 0 < r := div_pos (ha0.trans_lt hac') hc
  have hr1 : r < 1 := (div_lt_one hc).2 hc'c
  have hcr : c * r = c' := by rw [hr]; field_simp
  have hN : Tendsto (fun x : ℝ ↦ ⌊exp (r * x)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  have h1 : ∀ᶠ x in atTop, c * log ((⌊exp (r * x)⌋₊ : ℝ) + 2) <
      ∑ j ∈ range (⌊exp (r * x)⌋₊ + 1), μ j :=
    hN.eventually ((h.eventually (lt_mem_nhds hcL)).mono fun N hN ↦ by
      rwa [lt_div_iff₀ (log_pos (by linarith [N.cast_nonneg (α := ℝ)]))] at hN)
  have h2 : ∀ᶠ x in atTop, 2 < (c' - a) * x :=
    (tendsto_id.const_mul_atTop (sub_pos.2 hac')).eventually_gt_atTop 2
  filter_upwards [h1, h2, eventually_gt_atTop 0] with x h1 h2 hx
  rw [lt_div_iff₀ hx]
  set N := ⌊exp (r * x)⌋₊
  have hS := sum_range_le_levelSum_add hμ0 hμ hμt (N + 1) x
  have hfloor : (N : ℝ) ≤ exp (r * x) := Nat.floor_le (exp_pos _).le
  have hlt : exp (r * x) < N + 1 := Nat.lt_floor_add_one _
  -- The entries below the level contribute at most `(N + 1) exp (-x) ≤ 2`.
  have he : ((N + 1 : ℕ) : ℝ) * exp (-x) ≤ 2 := by
    have h1' : exp (r * x) * exp (-x) ≤ 1 := by
      rw [← exp_add, exp_le_one_iff]; nlinarith
    have h2' : exp (-x) ≤ 1 := exp_le_one_iff.2 (by linarith)
    push_cast
    nlinarith [exp_pos (-x)]
  have hlog : r * x ≤ log ((N : ℝ) + 2) := by
    rw [le_log_iff_exp_le (by positivity)]; linarith
  nlinarith

/-- Upper half of `tendsto_levelSum_of_tendsto_sum_div_log`. -/
private lemma levelSum_div_lt_of_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ) {L : ℝ}
    (h : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L))
    {b : ℝ} (hb : L < b) :
    ∀ᶠ x : ℝ in atTop, levelSum μ x / x < b := by
  have hL : 0 ≤ L := ge_of_tendsto' h (sum_div_log_nonneg hμ0)
  obtain ⟨c, hLc, hcb⟩ := exists_between hb
  obtain ⟨c', hcc', hc'b⟩ := exists_between hcb
  have hc : 0 < c := hL.trans_lt hLc
  set r := c' / c with hr
  have hr1 : 1 < r := (one_lt_div hc).2 hcc'
  have hcr : c * r = c' := by rw [hr]; field_simp
  have hN : Tendsto (fun x : ℝ ↦ ⌈exp (r * x)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp
      (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith)))
  have h1 : ∀ᶠ x in atTop, ∑ j ∈ range (⌈exp (r * x)⌉₊ + 1), μ j <
      c * log ((⌈exp (r * x)⌉₊ : ℝ) + 2) :=
    hN.eventually ((h.eventually (gt_mem_nhds hLc)).mono fun N hN ↦ by
      rwa [div_lt_iff₀ (log_pos (by linarith [N.cast_nonneg (α := ℝ)]))] at hN)
  have hgrow : ∀ᶠ x in atTop, c * r * x + c * log 4 < exp ((r - 1) * x) :=
    eventually_mul_add_lt_exp_mul (by linarith) _ _
  have h3 : ∀ᶠ x in atTop, c * log 4 < (b - c') * x :=
    (tendsto_id.const_mul_atTop (sub_pos.2 hc'b)).eventually_gt_atTop _
  filter_upwards [h1, hgrow, h3, eventually_gt_atTop 0] with x h1 hg h3 hx
  rw [div_lt_iff₀ hx]
  set N := ⌈exp (r * x)⌉₊
  have hceil : exp (r * x) ≤ N := Nat.le_ceil _
  have hceil' : (N : ℝ) < exp (r * x) + 1 := Nat.ceil_lt_add_one (exp_pos _).le
  have hone : 1 ≤ exp (r * x) := one_le_exp (by nlinarith)
  have hlog : log ((N : ℝ) + 2) ≤ r * x + log 4 := by
    rw [← log_exp (r * x), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) (by linarith)
  -- No entry beyond `N` reaches the level `x`.
  have hμN : μ N < exp (-x) := by
    by_contra hcon
    have hS : ((N : ℝ) + 1) * exp (-x) ≤ ∑ j ∈ range (N + 1), μ j := by
      simpa using card_nsmul_le_sum (range (N + 1)) μ (exp (-x)) fun j hj ↦
        (not_lt.1 hcon).trans (hμ (Nat.lt_succ_iff.1 (mem_range.1 hj)))
    have : exp ((r - 1) * x) ≤ (N + 1) * exp (-x) := by
      rw [sub_mul, one_mul, sub_eq_add_neg, exp_add]
      nlinarith [exp_pos (-x)]
    nlinarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hNN : ∑ j ∈ range N, μ j ≤ ∑ j ∈ range (N + 1), μ j := by
    rw [sum_range_succ]; linarith [hμ0 N]
  have := levelSum_le_sum_range hμ0 hμ hμN
  nlinarith

/-- If the logarithmic means tend to `L`, the level sums grow like `L x`. -/
private lemma tendsto_levelSum_of_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ)
    (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ ↦ levelSum μ x / x) atTop (𝓝 L) :=
  tendsto_order.2 ⟨fun _ ha ↦ lt_levelSum_div_of_tendsto_sum_div_log hμ0 hμ hμt h ha,
    fun _ hb ↦ levelSum_div_lt_of_tendsto_sum_div_log hμ0 hμ h hb⟩

/-! ### The Abelian direction -/

/-- Bracketing `u ^ ε` between consecutive powers of `q = exp (-ε)`, written as a geometric series
over the levels `exp (-k)` that `u` reaches. -/
private lemma tsum_geometric_level_le_rpow {ε u : ℝ} (hε : 0 < ε) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * (if exp (-(k : ℝ)) ≤ u then u else 0) ≤
        u ^ (1 + ε) ∧
      u ^ (1 + ε) ≤
        exp ε *
          ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * (if exp (-(k : ℝ)) ≤ u then u else 0) := by
  rcases hu0.eq_or_lt with rfl | hu
  · simp [zero_rpow (by linarith : (1 + ε) ≠ 0)]
  set q := exp (-ε) with hq
  set m := ⌈-log u⌉₊
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hcond : ∀ k : ℕ, exp (-(k : ℝ)) ≤ u ↔ m ≤ k := fun k ↦ by
    rw [← le_log_iff_exp_le hu, neg_le, Nat.ceil_le]
  have hsum : ∑' k : ℕ, (1 - q) * q ^ k * (if exp (-(k : ℝ)) ≤ u then u else 0) = q ^ m * u := by
    refine HasSum.tsum_eq ((hasSum_nat_add_iff' m).1 ?_)
    simp_rw [hcond]
    rw [sum_eq_zero fun i hi ↦ by simp [not_le.2 (mem_range.1 hi)], sub_zero]
    simp only [le_add_iff_nonneg_left, zero_le, ite_true, pow_add]
    convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - q) * q ^ m * u) using 1
    · ext k; ring
    · field_simp [(sub_pos.2 hq1).ne']
  rw [hsum]
  have hpow : u ^ (1 + ε) = u * exp (ε * log u) := by
    rw [rpow_add hu, rpow_one, rpow_def_of_pos hu, mul_comm (log u)]
  have hqm : q ^ m = exp (-(ε * m)) := by
    rw [hq, ← exp_nat_mul]; congr 1; ring
  have hm1 : -log u ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < -log u + 1 := Nat.ceil_lt_add_one (neg_nonneg.2 (log_nonpos hu0 hu1))
  rw [hpow, hqm]
  constructor
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) hu.le
  · rw [← mul_assoc, ← exp_add, mul_comm _ u]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) hu.le

/-- An affine bound on the level sums makes the weighted level series converge. -/
private lemma summable_geometric_mul_levelSum (hμ0 : ∀ j, 0 ≤ μ j) {A B : ℝ}
    (hbound : ∀ k : ℕ, levelSum μ k ≤ A * k + B) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℕ ↦ (1 - q) * q ^ k * levelSum μ k :=
  Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (mul_nonneg (sub_nonneg.2 hq1.le) (pow_nonneg hq0 _))
      (levelSum_nonneg hμ0 k))
    (fun k ↦ mul_le_mul_of_nonneg_left (hbound k)
      (mul_nonneg (sub_nonneg.2 hq1.le) (pow_nonneg hq0 _)))
    (hasSum_one_sub_mul_geometric_mul_affine (by rwa [norm_of_nonneg hq0]) A B).summable

/-- Comparison of the zeta function with the weighted level series. -/
private lemma summable_rpow_and_le_of_levelSum_le (hμ0 : ∀ j, 0 ≤ μ j) (hμ1 : ∀ j, μ j ≤ 1)
    (hμ : Antitone μ) (hμt : Tendsto μ atTop (𝓝 0)) {A B : ℝ}
    (hbound : ∀ k : ℕ, levelSum μ k ≤ A * k + B) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j ↦ μ j ^ (1 + ε)) ∧
      ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * levelSum μ k ≤ ∑' j, μ j ^ (1 + ε) ∧
      ∑' j, μ j ^ (1 + ε) ≤ exp ε * ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * levelSum μ k := by
  set q := exp (-ε) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set F : ℕ → ℕ → ℝ := fun k j ↦ (1 - q) * q ^ k * (if exp (-(k : ℝ)) ≤ μ j then μ j else 0)
    with hF
  have hF0 : 0 ≤ Function.uncurry F := fun p ↦
    mul_nonneg (mul_nonneg (sub_nonneg.2 hq1.le) (pow_nonneg hq0 _)) (ite_nonneg (hμ0 _) le_rfl)
  have hrow : ∀ k, Summable (F k) := fun k ↦ (summable_levelTerm hμ hμt k).mul_left _
  have hrow_eq : ∀ k, ∑' j, F k j = (1 - q) * q ^ k * levelSum μ k := fun k ↦
    (summable_levelTerm hμ hμt k).tsum_mul_left _
  have hlevel := summable_geometric_mul_levelSum hμ0 hbound hq0 hq1
  have hFs : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg hF0).2 ⟨hrow, by simpa only [Function.uncurry_apply_pair, hrow_eq]⟩
  have hcol : ∀ j, Summable fun k ↦ F k j := fun j ↦
    hFs.comp_injective (i := fun k ↦ (k, j)) fun _ _ h ↦ (Prod.mk.inj h).1
  have hcols : Summable fun j ↦ ∑' k, F k j := by
    simpa only [Prod.swap_prod_mk, Function.uncurry_apply_pair] using hFs.prod_symm.prod
  have hbr : ∀ j, ∑' k, F k j ≤ μ j ^ (1 + ε) ∧ μ j ^ (1 + ε) ≤ exp ε * ∑' k, F k j := fun j ↦
    tsum_geometric_level_le_rpow hε (hμ0 j) (hμ1 j)
  have hsumm : Summable fun j ↦ μ j ^ (1 + ε) :=
    Summable.of_nonneg_of_le (fun j ↦ rpow_nonneg (hμ0 j) _) (fun j ↦ (hbr j).2)
      (hcols.mul_left _)
  have hcomm : ∑' k : ℕ, (1 - q) * q ^ k * levelSum μ k = ∑' j, ∑' k, F k j := by
    rw [← (hFs.tsum_comm' hrow hcol).symm.trans rfl]
    exact tsum_congr fun k ↦ (hrow_eq k).symm
  refine ⟨hsumm, ?_, ?_⟩
  · rw [hcomm]
    exact hcols.tsum_le_tsum (fun j ↦ (hbr j).1) hsumm
  · rw [hcomm, ← hcols.tsum_mul_left]
    exact hsumm.tsum_le_tsum (fun j ↦ (hbr j).2) (hcols.mul_left _)

private lemma geometric_weight_nonneg {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    0 ≤ (1 - exp (-ε)) * exp (-ε) ^ k :=
  mul_nonneg (sub_nonneg.2 (Real.exp_lt_one_iff.2 (by linarith)).le) (pow_nonneg (exp_pos _).le _)

/-- A level-sum asymptotic with an eventual linear bound gives a global affine bound. -/
private lemma exists_levelSum_le (hμ0 : ∀ j, 0 ≤ μ j) {L c : ℝ} (hc : 0 ≤ c) (hLc : L < c)
    (h : Tendsto (fun k : ℕ ↦ levelSum μ k / k) atTop (𝓝 L)) :
    ∃ B, ∀ k : ℕ, levelSum μ k ≤ c * k + B := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((h.eventually (gt_mem_nhds hLc)).and (eventually_gt_atTop 0))
  refine ⟨∑ i ∈ range K, levelSum μ i, fun k ↦ ?_⟩
  have hB : 0 ≤ ∑ i ∈ range K, levelSum μ i := sum_nonneg fun i _ ↦ levelSum_nonneg hμ0 i
  rcases lt_or_ge k K with hk | hk
  · have := Finset.single_le_sum (s := range K) (f := fun i : ℕ ↦ levelSum μ i)
      (fun i _ ↦ levelSum_nonneg hμ0 i)
      (mem_range.2 hk)
    nlinarith [k.cast_nonneg (α := ℝ)]
  · obtain ⟨h1, h2⟩ := hK k hk
    rw [div_lt_iff₀ (by exact_mod_cast h2)] at h1
    linarith

private lemma exists_le_levelSum (hμ0 : ∀ j, 0 ≤ μ j) {L c : ℝ} (hc : 0 ≤ c) (hcL : c < L)
    (h : Tendsto (fun k : ℕ ↦ levelSum μ k / k) atTop (𝓝 L)) :
    ∃ B, ∀ k : ℕ, c * k - B ≤ levelSum μ k := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((h.eventually (lt_mem_nhds hcL)).and (eventually_gt_atTop 0))
  refine ⟨c * K, fun k ↦ ?_⟩
  rcases lt_or_ge k K with hk | hk
  · have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
    nlinarith [levelSum_nonneg hμ0 k]
  · obtain ⟨h1, h2⟩ := hK k hk
    rw [lt_div_iff₀ (by exact_mod_cast h2)] at h1
    nlinarith [K.cast_nonneg (α := ℝ)]

/-- Lower half of `tendsto_mul_tsum_rpow_of_tendsto_levelSum`. -/
private lemma lt_mul_tsum_rpow_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun k : ℕ ↦ levelSum μ k / k) atTop (𝓝 L))
    {a : ℝ} (ha : a < L) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, a < ε * ∑' j, μ j ^ (1 + ε) := by
  have hL : 0 ≤ L := ge_of_tendsto' h fun k ↦ div_nonneg (levelSum_nonneg hμ0 k) k.cast_nonneg
  obtain ⟨A, hA⟩ := exists_levelSum_le hμ0 (hL.trans (lt_add_one L).le) (lt_add_one L) h
  rcases lt_or_ge a 0 with ha0 | ha0
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact ha0.trans_le (mul_nonneg hε.le (tsum_nonneg fun j ↦ rpow_nonneg (hμ0 j) _))
  obtain ⟨c, hac, hcL⟩ := exists_between ha
  have hc0 : 0 ≤ c := ha0.trans hac.le
  obtain ⟨B, hB⟩ := exists_le_levelSum hμ0 hc0 hcL h
  have hlim : Tendsto (fun ε : ℝ ↦ c * exp (-ε) - ε * B) (𝓝[>] 0) (𝓝 (c * exp (-0) - 0 * B)) :=
    ((continuous_const.mul (continuous_exp.comp continuous_neg)).sub
      (continuous_id.mul continuous_const)).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  rw [neg_zero, exp_zero, mul_one, zero_mul, sub_zero] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hac), self_mem_nhdsWithin] with ε h1 (hε : 0 < ε)
  obtain ⟨-, hle, -⟩ := summable_rpow_and_le_of_levelSum_le hμ0 hμ1 hμ hμt hA hε
  have hq0 : 0 ≤ exp (-ε) := (exp_pos _).le
  have hq1 : exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hgeom := hasSum_one_sub_mul_geometric_mul_affine (by rwa [norm_of_nonneg hq0]) c (-B)
  have hlow : c * exp (-ε) / (1 - exp (-ε)) - B ≤
      ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * levelSum μ k := by
    rw [sub_eq_add_neg, ← hgeom.tsum_eq]
    exact hgeom.summable.tsum_le_tsum
      (fun k ↦ mul_le_mul_of_nonneg_left (by linarith [hB k]) (geometric_weight_nonneg hε k))
      (summable_geometric_mul_levelSum hμ0 hA hq0 hq1)
  have hr : ε * (exp (-ε) / (1 - exp (-ε))) = ε / (exp ε - 1) := by
    have : exp ε - 1 ≠ 0 := (sub_pos.2 (one_lt_exp_iff.2 hε)).ne'
    rw [exp_neg]
    field_simp
  have : exp (-ε) ≤ ε * (exp (-ε) / (1 - exp (-ε))) := hr ▸ exp_neg_le_div_exp_sub_one hε
  calc a < c * exp (-ε) - ε * B := h1
    _ ≤ c * (ε * (exp (-ε) / (1 - exp (-ε)))) - ε * B := by gcongr
    _ = ε * (c * exp (-ε) / (1 - exp (-ε)) - B) := by ring
    _ ≤ ε * ∑' j, μ j ^ (1 + ε) := by gcongr; exact hlow.trans hle

/-- Upper half of `tendsto_mul_tsum_rpow_of_tendsto_levelSum`. -/
private lemma mul_tsum_rpow_lt_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun k : ℕ ↦ levelSum μ k / k) atTop (𝓝 L))
    {b : ℝ} (hb : L < b) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * ∑' j, μ j ^ (1 + ε) < b := by
  have hL : 0 ≤ L := ge_of_tendsto' h fun k ↦ div_nonneg (levelSum_nonneg hμ0 k) k.cast_nonneg
  obtain ⟨c, hLc, hcb⟩ := exists_between hb
  have hc0 : 0 ≤ c := hL.trans hLc.le
  obtain ⟨B, hB⟩ := exists_levelSum_le hμ0 hc0 hLc h
  have hlim : Tendsto (fun ε : ℝ ↦ exp ε * (c + ε * B)) (𝓝[>] 0) (𝓝 (exp 0 * (c + 0 * B))) :=
    (continuous_exp.mul (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0
      |>.mono_left nhdsWithin_le_nhds
  rw [exp_zero, zero_mul, add_zero, one_mul] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hcb), self_mem_nhdsWithin] with ε h1 (hε : 0 < ε)
  obtain ⟨-, -, hle⟩ := summable_rpow_and_le_of_levelSum_le hμ0 hμ1 hμ hμt hB hε
  have hq0 : 0 ≤ exp (-ε) := (exp_pos _).le
  have hq1 : exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hgeom := hasSum_one_sub_mul_geometric_mul_affine (by rwa [norm_of_nonneg hq0]) c B
  have hup : ∑' k : ℕ, (1 - exp (-ε)) * exp (-ε) ^ k * levelSum μ k ≤
      c * exp (-ε) / (1 - exp (-ε)) + B := by
    rw [← hgeom.tsum_eq]
    exact (summable_geometric_mul_levelSum hμ0 hB hq0 hq1).tsum_le_tsum
      (fun k ↦ mul_le_mul_of_nonneg_left (hB k) (geometric_weight_nonneg hε k)) hgeom.summable
  have hr : ε * (exp (-ε) / (1 - exp (-ε))) = ε / (exp ε - 1) := by
    have : exp ε - 1 ≠ 0 := (sub_pos.2 (one_lt_exp_iff.2 hε)).ne'
    rw [exp_neg]
    field_simp
  have : ε * (exp (-ε) / (1 - exp (-ε))) ≤ 1 := hr ▸ div_exp_sub_one_le_one hε.le
  calc ε * ∑' j, μ j ^ (1 + ε)
      ≤ ε * (exp ε * (c * exp (-ε) / (1 - exp (-ε)) + B)) := by
        gcongr; exact hle.trans (by gcongr)
    _ = exp ε * (c * (ε * (exp (-ε) / (1 - exp (-ε)))) + ε * B) := by ring
    _ ≤ exp ε * (c * 1 + ε * B) := by gcongr
    _ = exp ε * (c + ε * B) := by ring
    _ < b := h1

/-- The Abelian direction for sequences bounded by `1`, in the level variable. -/
private lemma tendsto_mul_tsum_rpow_of_tendsto_levelSum (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hμt : Tendsto μ atTop (𝓝 0)) {L : ℝ}
    (h : Tendsto (fun k : ℕ ↦ levelSum μ k / k) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ ↦ ε * ∑' j, μ j ^ (1 + ε)) (𝓝[>] 0) (𝓝 L) :=
  tendsto_order.2 ⟨fun _ ha ↦ lt_mul_tsum_rpow_of_tendsto_levelSum hμ0 hμ1 hμ hμt h ha,
    fun _ hb ↦ mul_tsum_rpow_lt_of_tendsto_levelSum hμ0 hμ1 hμ hμt h hb⟩

/-! ### The Tauberian direction -/

/-- The residue hypothesis, evaluated at `s = 1 + (i + 1) ε`. -/
private lemma tendsto_mul_tsum_rpow_one_add_mul {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) (i : ℕ) :
    Tendsto (fun ε : ℝ ↦ ε * ∑' j, μ j ^ (1 + (i + 1) * ε)) (𝓝[>] 0) (𝓝 (L / (i + 1))) := by
  have hg : Tendsto (fun ε : ℝ ↦ 1 + (i + 1) * ε) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul ((i : ℝ) + 1)).const_add (1 : ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have : 0 < ((i : ℝ) + 1) * ε := by positivity
      exact lt_add_of_pos_right 1 this
  convert (hζ.comp hg).div_const ((i : ℝ) + 1) using 1
  ext ε
  simp only [Function.comp_apply, add_sub_cancel_left]
  field_simp

/-- The residue hypothesis evaluates `ε ∑ⱼ μⱼ ^ (1 + ε) Q(μⱼ ^ ε)` in the limit for every
polynomial `Q`. -/
private lemma tendsto_mul_tsum_rpow_mul_eval (hμ0 : ∀ j, 0 ≤ μ j)
    (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s) {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) (Q : ℝ[X]) :
    Tendsto (fun ε : ℝ ↦ ε * ∑' j, μ j ^ (1 + ε) * Q.eval (μ j ^ ε)) (𝓝[>] 0)
      (𝓝 (L * ∫ u in (0 : ℝ)..1, Q.eval u)) := by
  have hval : L * ∫ u in (0 : ℝ)..1, Q.eval u =
      ∑ i ∈ range (Q.natDegree + 1), Q.coeff i * (L / (i + 1)) := by
    rw [Q.integral_eval_eq_sum, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [one_pow, zero_pow (Nat.succ_ne_zero i)]; ring
  rw [hval]
  refine (tendsto_finsetSum (range (Q.natDegree + 1)) fun i _ ↦
    (tendsto_mul_tsum_rpow_one_add_mul hζ i).const_mul (Q.coeff i)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [tsum_rpow_mul_eval_rpow_eq_sum (a := 1 + ε) hμ0 (by linarith) hε.le Q
    fun i _ ↦ hsum _ (by nlinarith [mul_nonneg i.cast_nonneg hε.le]), mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [show 1 + ε + (i : ℝ) * ε = 1 + (i + 1) * ε by ring]
  ring

private lemma nonneg_of_tendsto_sub_one_mul_tsum_rpow (hμ0 : ∀ j, 0 ≤ μ j) {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) : 0 ≤ L :=
  ge_of_tendsto hζ (eventually_nhdsWithin_of_forall fun s (hs : 1 < s) ↦
    mul_nonneg (sub_nonneg.2 hs.le) (tsum_nonneg fun j ↦ rpow_nonneg (hμ0 j) _))

/-- Karamata's step: the residue hypothesis evaluates the truncated sums
`ε ∑_(μⱼ ^ ε ≥ a) μⱼ ^ (1 + ε)` in the limit. -/
private lemma tendsto_mul_tsum_rpow_mul_indicator (hμ0 : ∀ j, 0 ≤ μ j) (hμ1 : ∀ j, μ j ≤ 1)
    (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s) {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    Tendsto (fun ε : ℝ ↦ ε * ∑' j, μ j ^ (1 + ε) * (if a ≤ μ j ^ ε then (1 : ℝ) else 0)) (𝓝[>] 0)
      (𝓝 (L * (1 - a))) := by
  have hL := nonneg_of_tendsto_sub_one_mul_tsum_rpow hμ0 hζ
  have hmem : ∀ ε : ℝ, 0 < ε → ∀ j, μ j ^ ε ∈ Set.Icc (0 : ℝ) 1 := fun ε hε j ↦
    ⟨rpow_nonneg (hμ0 j) _, rpow_le_one (hμ0 j) (hμ1 j) hε.le⟩
  have hind : ∀ ε : ℝ, 0 < ε →
      Summable fun j ↦ μ j ^ (1 + ε) * (if a ≤ μ j ^ ε then (1 : ℝ) else 0) := fun ε hε ↦
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (rpow_nonneg (hμ0 j) _) (ite_nonneg
      zero_le_one le_rfl)) (fun j ↦ mul_le_of_le_one_right (rpow_nonneg (hμ0 j) _)
      (ite_le_one le_rfl zero_le_one)) (hsum _ (by linarith))
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun b hb ↦ ?_⟩
  · set η := (L * (1 - a) - c) / (L + 1)
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hLη : L * η < L * (1 - a) - c := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    obtain ⟨Q, hQ, hQint⟩ := exists_polynomial_le_indicator ha0.le ha1 hη
    have hlt : c < L * ∫ u in (0 : ℝ)..1, Q.eval u := by nlinarith
    filter_upwards [(tendsto_mul_tsum_rpow_mul_eval hμ0 hsum hζ Q).eventually (lt_mem_nhds hlt),
      self_mem_nhdsWithin] with ε h1 (hε : 0 < ε)
    refine h1.trans_le (mul_le_mul_of_nonneg_left ?_ hε.le)
    have hQs := summable_rpow_mul_eval_rpow (a := 1 + ε) hμ0 (by linarith) hε.le Q
      fun i _ ↦ hsum _ (by nlinarith [mul_nonneg i.cast_nonneg hε.le])
    exact hQs.tsum_le_tsum (fun j ↦
      mul_le_mul_of_nonneg_left (hQ _ (hmem ε hε j)) (rpow_nonneg (hμ0 j) _)) (hind ε hε)
  · set η := (b - L * (1 - a)) / (L + 1)
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hLη : L * η < b - L * (1 - a) := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    obtain ⟨Q, hQ, hQint⟩ := exists_polynomial_ge_indicator ha0 ha1.le hη
    have hlt : L * ∫ u in (0 : ℝ)..1, Q.eval u < b := by nlinarith
    filter_upwards [(tendsto_mul_tsum_rpow_mul_eval hμ0 hsum hζ Q).eventually (gt_mem_nhds hlt),
      self_mem_nhdsWithin] with ε h1 (hε : 0 < ε)
    refine (mul_le_mul_of_nonneg_left ?_ hε.le).trans_lt h1
    exact (hind ε hε).tsum_le_tsum (fun j ↦
      mul_le_mul_of_nonneg_left (hQ _ (hmem ε hε j)) (rpow_nonneg (hμ0 j) _))
      (summable_rpow_mul_eval_rpow (a := 1 + ε) hμ0 (by linarith) hε.le Q
        fun i _ ↦ hsum _ (by nlinarith [mul_nonneg i.cast_nonneg hε.le]))

/-- The truncated sums of Karamata's step are comparable with the level sums. -/
private lemma levelSum_le_tsum_rpow_mul_indicator (hμ0 : ∀ j, 0 ≤ μ j) (hμ1 : ∀ j, μ j ≤ 1)
    (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s) {t x : ℝ} (ht : 0 < t)
    (hx : 0 < x) :
    exp (-t) * levelSum μ x ≤
        ∑' j, μ j ^ (1 + t / x) * (if exp (-t) ≤ μ j ^ (t / x) then (1 : ℝ) else 0) ∧
      ∑' j, μ j ^ (1 + t / x) * (if exp (-t) ≤ μ j ^ (t / x) then (1 : ℝ) else 0) ≤
        levelSum μ x := by
  have hε : 0 < t / x := div_pos ht hx
  have hμt : Tendsto μ atTop (𝓝 0) := Nat.cofinite_eq_atTop ▸
    tendsto_cofinite_zero_of_summable_rpow two_pos hμ0 (hsum 2 one_lt_two)
  have htx : t / (t / x) = x := by field_simp
  have hS1 : Summable fun j ↦ μ j ^ (1 + t / x) *
      (if exp (-t) ≤ μ j ^ (t / x) then (1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (rpow_nonneg (hμ0 j) _) (ite_nonneg
      zero_le_one le_rfl)) (fun j ↦ mul_le_of_le_one_right (rpow_nonneg (hμ0 j) _)
      (ite_le_one le_rfl zero_le_one)) (hsum _ (by linarith))
  -- On the level set, `μⱼ ^ (1 + ε) = μⱼ μⱼ ^ ε` with `exp (-t) ≤ μⱼ ^ ε ≤ 1`.
  have hterm : ∀ j, exp (-t) * (if exp (-x) ≤ μ j then μ j else 0) ≤
        μ j ^ (1 + t / x) * (if exp (-t) ≤ μ j ^ (t / x) then (1 : ℝ) else 0) ∧
      μ j ^ (1 + t / x) * (if exp (-t) ≤ μ j ^ (t / x) then (1 : ℝ) else 0) ≤
        if exp (-x) ≤ μ j then μ j else 0 := fun j ↦ by
    have hiff := exp_neg_le_rpow_iff (t := t) (hμ0 j) hε
    rw [htx] at hiff
    by_cases hj : exp (-x) ≤ μ j
    · have hj' := hiff.2 hj
      rw [ite_eq_left hj, ite_eq_left hj', mul_one, rpow_add' (hμ0 j) (by positivity), rpow_one]
      exact ⟨by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hj' (hμ0 j),
        mul_le_of_le_one_right (hμ0 j) (rpow_le_one (hμ0 j) (hμ1 j) hε.le)⟩
    · rw [ite_eq_right hj, ite_eq_right (hiff.not.2 hj)]
      simp
  rw [levelSum, ← (summable_levelTerm hμ hμt x).tsum_mul_left]
  exact ⟨((summable_levelTerm hμ hμt x).mul_left _).tsum_le_tsum (fun j ↦ (hterm j).1) hS1,
    hS1.tsum_le_tsum (fun j ↦ (hterm j).2) (summable_levelTerm hμ hμt x)⟩

/-- Lower half of `tendsto_levelSum_of_tendsto_sub_one_mul_tsum_rpow`. -/
private lemma lt_levelSum_div_of_tendsto_sub_one_mul_tsum_rpow (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s)
    {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L))
    {a : ℝ} (ha : a < L) :
    ∀ᶠ x : ℝ in atTop, a < levelSum μ x / x := by
  have hL := nonneg_of_tendsto_sub_one_mul_tsum_rpow hμ0 hζ
  have hmap : ∀ t : ℝ, 0 < t → Tendsto (fun x : ℝ ↦ t / x) atTop (𝓝[>] 0) := fun t ht ↦
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.div_atTop tendsto_id)
      (by filter_upwards [eventually_gt_atTop 0] with x hx using div_pos ht hx)
  have hexp : Tendsto (fun t : ℝ ↦ exp t) (𝓝[>] 0) (𝓝 1) := by
    simpa using (continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds
  rcases lt_or_ge a 0 with ha0 | ha0
  · filter_upwards [eventually_gt_atTop 0] with x hx using
      ha0.trans_le (div_nonneg (levelSum_nonneg hμ0 x) hx.le)
  -- Choose `t > 0` with `a < L exp (-t)`; then `a t < L t exp (-t) ≤ L (1 - exp (-t))`.
  obtain ⟨t, h1, ht⟩ := ((((hexp.inv₀ one_ne_zero).const_mul L).eventually
    (lt_mem_nhds (by simpa using ha))).and self_mem_nhdsWithin).exists
  rw [← exp_neg] at h1
  have hgt : a * t < L * (1 - exp (-t)) := by
    have h2 : t * exp (-t) ≤ 1 - exp (-t) := by
      have := add_one_le_exp t
      have h3 : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
      nlinarith [exp_pos (-t)]
    nlinarith
  have hA := tendsto_mul_tsum_rpow_mul_indicator hμ0 hμ1 hsum hζ (exp_pos (-t))
    (Real.exp_lt_one_iff.2 (by linarith))
  filter_upwards [(hmap t ht).eventually (hA.eventually (lt_mem_nhds hgt)),
    eventually_gt_atTop 0] with x h1 hx
  have hb := (levelSum_le_tsum_rpow_mul_indicator hμ0 hμ1 hμ hsum ht hx).2
  rw [lt_div_iff₀ hx]
  have : a * t < t / x * levelSum μ x := h1.trans_le (by gcongr)
  rw [div_mul_eq_mul_div, lt_div_iff₀ hx] at this
  nlinarith

/-- Upper half of `tendsto_levelSum_of_tendsto_sub_one_mul_tsum_rpow`. -/
private lemma levelSum_div_lt_of_tendsto_sub_one_mul_tsum_rpow (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s)
    {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L))
    {b : ℝ} (hb : L < b) :
    ∀ᶠ x : ℝ in atTop, levelSum μ x / x < b := by
  have hL := nonneg_of_tendsto_sub_one_mul_tsum_rpow hμ0 hζ
  have hmap : ∀ t : ℝ, 0 < t → Tendsto (fun x : ℝ ↦ t / x) atTop (𝓝[>] 0) := fun t ht ↦
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.div_atTop tendsto_id)
      (by filter_upwards [eventually_gt_atTop 0] with x hx using div_pos ht hx)
  have hexp : Tendsto (fun t : ℝ ↦ exp t) (𝓝[>] 0) (𝓝 1) := by
    simpa using (continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Choose `t > 0` with `L exp t < b`; then `L (1 - exp (-t)) ≤ L t < b t exp (-t)`.
  obtain ⟨t, h1, ht⟩ := (((hexp.const_mul L).eventually
    (gt_mem_nhds (by simpa using hb))).and self_mem_nhdsWithin).exists
  have hlt : L * (1 - exp (-t)) < b * t * exp (-t) := by
    have h2 : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
    have h3 : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    have h4 : L * t * (exp t * exp (-t)) < b * t * exp (-t) := by
      rw [show L * t * (exp t * exp (-t)) = (L * exp t) * (t * exp (-t)) by ring]
      rw [mul_assoc b]
      exact mul_lt_mul_of_pos_right h1 (by positivity)
    rw [h3, mul_one] at h4
    nlinarith
  have hA := tendsto_mul_tsum_rpow_mul_indicator hμ0 hμ1 hsum hζ (exp_pos (-t))
    (Real.exp_lt_one_iff.2 (by linarith))
  filter_upwards [(hmap t ht).eventually (hA.eventually (gt_mem_nhds hlt)),
    eventually_gt_atTop 0] with x h1 hx
  have hb := (levelSum_le_tsum_rpow_mul_indicator hμ0 hμ1 hμ hsum ht hx).1
  rw [div_lt_iff₀ hx]
  have : t / x * (exp (-t) * levelSum μ x) < b * t * exp (-t) :=
    (mul_le_mul_of_nonneg_left hb (div_pos ht hx).le).trans_lt h1
  rw [div_mul_eq_mul_div, div_lt_iff₀ hx] at this
  have : 0 < t * exp (-t) := by positivity
  nlinarith

/-- The Tauberian direction for sequences bounded by `1`, in the level variable. -/
private lemma tendsto_levelSum_of_tendsto_sub_one_mul_tsum_rpow (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ1 : ∀ j, μ j ≤ 1) (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s)
    {L : ℝ}
    (hζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) :
    Tendsto (fun x : ℝ ↦ levelSum μ x / x) atTop (𝓝 L) :=
  tendsto_order.2
    ⟨fun _ ha ↦ lt_levelSum_div_of_tendsto_sub_one_mul_tsum_rpow hμ0 hμ1 hμ hsum hζ ha,
      fun _ hb ↦ levelSum_div_lt_of_tendsto_sub_one_mul_tsum_rpow hμ0 hμ1 hμ hsum hζ hb⟩

/-! ### Bounded logarithmic means -/

/-- If the logarithmic means `(log (N + 2))⁻¹ ∑_(j ≤ N) μⱼ` of an antitone nonnegative sequence are
bounded, then `∑ⱼ μⱼ ^ s` converges for every `s > 1`. -/
theorem summable_rpow_of_sum_le_mul_log (hμ0 : ∀ j, 0 ≤ μ j) (hμ : Antitone μ) {C : ℝ}
    (hC : ∀ N : ℕ, ∑ j ∈ range (N + 1), μ j ≤ C * log ((N : ℝ) + 2)) {s : ℝ} (hs : 1 < s) :
    Summable fun j ↦ μ j ^ s := by
  set η := (s - 1) / (2 * s) with hη_def
  have hs0 : 0 < s := by linarith
  have hη : 0 < η := div_pos (by linarith) (by linarith)
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero] at h
    by_contra hneg
    nlinarith [hμ0 0, log_pos (by norm_num : (1 : ℝ) < 2)]
  -- `μ_N ≤ K (N + 1) ^ (η - 1)`, from `(N + 1) μ_N ≤ C log (N + 2)` and `log x ≤ x ^ η / η`.
  have hbound : ∀ N : ℕ, μ N ≤ C * 2 ^ η / η * ((N : ℝ) + 1) ^ (η - 1) := by
    intro N
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    have h3 : ((N : ℝ) + 2) ^ η ≤ 2 ^ η * ((N : ℝ) + 1) ^ η := by
      rw [← mul_rpow (by norm_num) hN1.le]
      exact rpow_le_rpow (by positivity) (by linarith) hη.le
    have key : ((N : ℝ) + 1) * μ N ≤ C * 2 ^ η / η * ((N : ℝ) + 1) ^ η := by
      calc ((N : ℝ) + 1) * μ N ≤ C * log ((N : ℝ) + 2) := by
            refine le_trans ?_ (hC N)
            simpa using card_nsmul_le_sum (range (N + 1)) μ (μ N) fun j hj ↦
              hμ (Nat.lt_succ_iff.1 (mem_range.1 hj))
        _ ≤ C * (((N : ℝ) + 2) ^ η / η) := by gcongr; exact log_le_rpow_div (by positivity) hη
        _ ≤ C * (2 ^ η * ((N : ℝ) + 1) ^ η / η) := by gcongr
        _ = C * 2 ^ η / η * ((N : ℝ) + 1) ^ η := by ring
    rw [rpow_sub hN1, rpow_one, mul_div_assoc', le_div_iff₀ hN1]
    linarith
  have hp : (η - 1) * s < -1 := by
    have : (η - 1) * s = -(s + 1) / 2 := by rw [hη_def]; field_simp; ring
    linarith
  have hsumm : Summable fun N : ℕ ↦ ((N : ℝ) + 1) ^ ((η - 1) * s) := by
    simpa using (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)
  refine Summable.of_nonneg_of_le (fun j ↦ rpow_nonneg (hμ0 j) s) (fun N ↦ ?_)
    (hsumm.mul_left ((C * 2 ^ η / η) ^ s))
  calc μ N ^ s ≤ (C * 2 ^ η / η * ((N : ℝ) + 1) ^ (η - 1)) ^ s :=
        rpow_le_rpow (hμ0 N) (hbound N) hs0.le
    _ = (C * 2 ^ η / η) ^ s * ((N : ℝ) + 1) ^ ((η - 1) * s) := by
        rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity)]

/-! ### The logarithmic Tauberian theorem -/

private lemma tendsto_sub_one_mul_tsum_rpow_of_tendsto_mul {ν : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun ε : ℝ ↦ ε * ∑' j, ν j ^ (1 + ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, ν j ^ s) (𝓝[>] 1) (𝓝 L) := by
  have hg : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) using sub_pos.2 hs
  refine (h.comp hg).congr fun s ↦ ?_
  simp only [Function.comp_apply, add_sub_cancel]

private lemma tendsto_rpow_nhdsGT_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ ↦ c ^ s) (𝓝[>] 1) (𝓝 c) := by
  simpa using (continuousAt_const_rpow hc.ne' (b := 1)).tendsto.mono_left nhdsWithin_le_nhds

/-- **Abelian direction of the logarithmic Tauberian theorem.** If the logarithmic means
`(log (N + 2))⁻¹ ∑_(j ≤ N) μⱼ` of an antitone nonnegative sequence tend to `L`, then so does
`(s - 1) ∑ⱼ μⱼ ^ s` as `s ↓ 1`. The series converges for `s > 1` by
`summable_rpow_of_sum_le_mul_log`. -/
theorem tendsto_sub_one_mul_tsum_rpow_of_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ : Antitone μ) {L : ℝ}
    (h : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L)) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L) := by
  -- Normalize to a sequence bounded by `1`.
  set c := max (μ 0) 1
  have hc : 0 < c := one_pos.trans_le (le_max_right _ _)
  have hν0 : ∀ j, 0 ≤ μ j / c := fun j ↦ div_nonneg (hμ0 j) hc.le
  have hν1 : ∀ j, μ j / c ≤ 1 := fun j ↦
    (div_le_one hc).2 ((hμ (Nat.zero_le j)).trans (le_max_left _ _))
  have hνa : Antitone fun j ↦ μ j / c := fun i j hij ↦ div_le_div_of_nonneg_right (hμ hij) hc.le
  have hνh : Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j / c) / log ((N : ℝ) + 2)) atTop
      (𝓝 (L / c)) := by
    refine (h.div_const c).congr fun N ↦ ?_
    rw [← sum_div, div_div, div_div, mul_comm]
  have hνt := tendsto_zero_of_tendsto_sum_div_log hν0 hνa hνh
  have hlev := (tendsto_levelSum_of_tendsto_sum_div_log hν0 hνa hνt hνh).comp
    tendsto_natCast_atTop_atTop
  have hs := tendsto_sub_one_mul_tsum_rpow_of_tendsto_mul
    (tendsto_mul_tsum_rpow_of_tendsto_levelSum hν0 hν1 hνa hνt hlev)
  have hlim := (tendsto_rpow_nhdsGT_one hc).mul hs
  rw [show c * (L / c) = L by field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [tsum_congr fun j ↦ div_rpow (hμ0 j) hc.le s, tsum_div_const]
  field_simp [(rpow_pos_of_pos hc s).ne']

/-- **Tauberian direction of the logarithmic Tauberian theorem.** If `∑ⱼ μⱼ ^ s` converges for
every `s > 1` and `(s - 1) ∑ⱼ μⱼ ^ s` tends to `L` as `s ↓ 1`, then the logarithmic means
`(log (N + 2))⁻¹ ∑_(j ≤ N) μⱼ` of the antitone nonnegative sequence `μ` tend to `L`. -/
theorem tendsto_sum_div_log_of_tendsto_sub_one_mul_tsum_rpow (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s) {L : ℝ}
    (h : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L)) :
    Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L) := by
  -- Normalize to a sequence bounded by `1`.
  set c := max (μ 0) 1
  have hc : 0 < c := one_pos.trans_le (le_max_right _ _)
  have hν0 : ∀ j, 0 ≤ μ j / c := fun j ↦ div_nonneg (hμ0 j) hc.le
  have hν1 : ∀ j, μ j / c ≤ 1 := fun j ↦
    (div_le_one hc).2 ((hμ (Nat.zero_le j)).trans (le_max_left _ _))
  have hνa : Antitone fun j ↦ μ j / c := fun i j hij ↦ div_le_div_of_nonneg_right (hμ hij) hc.le
  have hνsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ (μ j / c) ^ s := fun s hs ↦
    ((hsum s hs).div_const (c ^ s)).congr fun j ↦ (div_rpow (hμ0 j) hc.le s).symm
  have hνζ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, (μ j / c) ^ s) (𝓝[>] 1) (𝓝 (L / c)) := by
    refine (h.div (tendsto_rpow_nhdsGT_one hc) hc.ne').congr fun s ↦ ?_
    rw [Pi.div_apply, tsum_congr fun j ↦ div_rpow (hμ0 j) hc.le s, tsum_div_const, mul_div_assoc]
  have hlev := tendsto_levelSum_of_tendsto_sub_one_mul_tsum_rpow hν0 hν1 hνa hνsum hνζ
  have hmean := (tendsto_sum_div_log_of_tendsto_levelSum hν0 hνa
    (Nat.cofinite_eq_atTop ▸ tendsto_cofinite_zero_of_summable_rpow two_pos hν0
      (hνsum 2 one_lt_two)) hlev).const_mul c
  rw [show c * (L / c) = L by field_simp] at hmean
  refine hmean.congr fun N ↦ ?_
  rw [← sum_div]
  field_simp

/-- **The logarithmic Tauberian theorem.** For an antitone nonnegative sequence `μ` whose zeta
function `∑ⱼ μⱼ ^ s` converges for every `s > 1`, the residue `lim_(s ↓ 1) (s - 1) ∑ⱼ μⱼ ^ s`
equals `L` exactly when the logarithmic means `(log (N + 2))⁻¹ ∑_(j ≤ N) μⱼ` tend to `L`. -/
theorem tendsto_sub_one_mul_tsum_rpow_iff_tendsto_sum_div_log (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ : Antitone μ) (hsum : ∀ s : ℝ, 1 < s → Summable fun j ↦ μ j ^ s) {L : ℝ} :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' j, μ j ^ s) (𝓝[>] 1) (𝓝 L) ↔
      Tendsto (fun N : ℕ ↦ (∑ j ∈ range (N + 1), μ j) / log ((N : ℝ) + 2)) atTop (𝓝 L) :=
  ⟨tendsto_sum_div_log_of_tendsto_sub_one_mul_tsum_rpow hμ0 hμ hsum,
    tendsto_sub_one_mul_tsum_rpow_of_tendsto_sum_div_log hμ0 hμ⟩

end TauCeti
