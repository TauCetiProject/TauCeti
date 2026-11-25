/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Summable
import TauCeti.MeasureTheory.Integral.Bochner.Markov
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.IdentDistrib
import TauCeti.Probability.Independence.Basic

/-!
# Large entries of random arrays

Let `x` be an array, indexed by `ℕ × ℕ`, of entries with a common law `ν`, and consider its
top-left corners. Cut off the entries at the unnormalized level `n^a`. If `ν` has a finite
absolute moment of order `m`, the entries are independent within each row and
`2 < q (m a - 1)`, then almost surely every row of the `r(n) × ℓ(n)` corners eventually has fewer
than `q` entries above the cutoff, as long as `r(n), ℓ(n) ≤ K n` eventually. The proof is the
union bound `TauCeti.Probability.measure_exists_le_card_filter_lt_norm_le` over `q`-element sets
of positions, followed by Borel–Cantelli; distinct rows may be dependent. If the entries are also
independent within each column, the same holds for the rows and the columns of the `p(n) × n`
corners with `p(n) ≤ K n`.

If `ν` has a finite fourth moment, the largest entry of the `p(n) × n` corners is almost surely
`o(√n)`, without any independence; if `ν` has a finite second moment, it is almost surely `o(n)`.
The array is enumerated along `Nat.pair`, which reduces these bounds to the prefix maxima of
`TauCeti.Probability.ae_eventually_forall_lt_norm_le_mul_of_identDistrib`.

## Main results

* `TauCeti.Probability.ae_eventually_forall_card_filter_lt_norm_lt`: almost surely, every row of
  the `r(n) × ℓ(n)` corners eventually has fewer than `q` entries above `n^a`.
* `TauCeti.Probability.ae_eventually_card_filter_lt_norm_lt`: almost surely, every row and every
  column of the `p(n) × n` corners eventually has fewer than `q` entries above `n^a`.
* `TauCeti.Probability.ae_eventually_norm_le_mul_sqrt`: almost surely, the largest entry of the
  corners is eventually below `ε √n` for every `ε > 0`.
* `TauCeti.Probability.ae_eventually_norm_le_mul`: under a second moment, almost surely the
  largest entry of the corners is eventually below `ε n` for every `ε > 0`.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988).
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddGroup E] [MeasurableSpace E]
  {P : Measure Ω} {x : ℕ × ℕ → Ω → E} {ν : Measure E} {p : ℕ → ℕ}

section Count

/-- **Row counts of large entries.** Let the array have entries with a common law `ν` of finite
`m`-th absolute moment, independent within each row, and let `r(n), ℓ(n) ≤ K n` eventually. If
`2 < q * (m * a - 1)`, then almost surely, eventually every row of the `r(n) × ℓ(n)` corner has
fewer than `q` entries of norm above `n ^ a`. Distinct rows may be dependent. -/
theorem ae_eventually_forall_card_filter_lt_norm_lt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) {m : ℕ} (hm : Integrable (fun z ↦ ‖z‖ ^ m) ν)
    {r ℓ : ℕ → ℕ} {K : ℝ} (hr : ∀ᶠ n in atTop, (r n : ℝ) ≤ K * n)
    (hℓ : ∀ᶠ n in atTop, (ℓ n : ℝ) ≤ K * n) {a : ℝ} {q : ℕ} (hq : 2 < q * (m * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i : Fin (r n),
      (Finset.univ.filter fun j : Fin (ℓ n) ↦ (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q := by
  -- Count in the real array of norms; the norm is a.e. measurable as the `m`-th root of `‖·‖ ^ m`.
  have hm₀ : m ≠ 0 := by
    rintro rfl
    push_cast at hq
    nlinarith [(q.cast_nonneg : (0 : ℝ) ≤ q)]
  have hnorm : AEMeasurable (fun z : E ↦ ‖z‖) ν :=
    (hm.aemeasurable.pow_const (m⁻¹ : ℝ)).congr
      (.of_forall fun z ↦ Real.pow_rpow_inv_natCast (norm_nonneg z) hm₀)
  have hm' : Integrable (fun t : ℝ ↦ ‖t‖ ^ m) (ν.map fun z ↦ ‖z‖) := by
    rw [integrable_map_measure (by fun_prop) hnorm]
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_norm] using hm
  have hrow' (i : ℕ) : iIndepFun (fun j ω ↦ ‖x (i, j) ω‖) P :=
    (hrow i).comp₀ (fun _ z ↦ ‖z‖) (fun _ ↦ (hx _).aemeasurable) fun _ ↦ by rwa [(hx _).map_eq]
  let C := ∫ t, ‖t‖ ^ m ∂(ν.map fun z ↦ ‖z‖)
  have hb : ∑' n : ℕ, ENNReal.ofReal (K ^ (q + 1) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q))
      < ∞ :=
    ((Real.summable_nat_rpow.2 (by nlinarith)).mul_left _).tsum_ofReal_lt_top
  -- Each entry exceeds a positive cutoff `R` with probability at most the Markov bound for the
  -- law of its norm.
  have htail (ij : ℕ × ℕ) {R : ℝ} (hR : 0 < R) :
      P {ω | R < ‖‖x ij ω‖‖} ≤ ENNReal.ofReal (C / R ^ m) := by
    rw [((hasLaw_map hnorm).fun_comp (hx ij)).measure_eq (p := fun t ↦ R < ‖t‖)
      (measurableSet_lt measurable_const continuous_norm.measurable)]
    exact meas_norm_gt_le_integral_norm_pow_div_pow (Z := fun t ↦ t) m hm' hR
  have hbound : ∀ᶠ n in atTop,
      P {ω | ∃ i : Fin (r n), q ≤ (Finset.univ.filter fun j : Fin (ℓ n) ↦
          (n : ℝ) ^ a < ‖x (i, j) ω‖).card} ≤
        ENNReal.ofReal (K ^ (q + 1) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q)) := by
    filter_upwards [hr, hℓ, eventually_gt_atTop 0] with n hrn hℓn hn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hcount := measure_exists_le_card_filter_lt_norm_le
      (Y := fun (i : Fin (r n)) (j : Fin (ℓ n)) ω ↦ ‖x (i, j) ω‖)
      (fun i ↦ (hrow' i).precomp Fin.val_injective) _
      (fun _ _ ↦ htail _ (Real.rpow_pos_of_pos hN a)) (fun _ ↦ (Fintype.card_fin (ℓ n)).le) q
    simp only [Fintype.card_fin, Real.norm_eq_abs, abs_norm] at hcount
    refine hcount.trans ?_
    calc
      _ = ENNReal.ofReal (r n * ℓ n ^ q * (C / ((n : ℝ) ^ a) ^ m) ^ q) := by
        -- Move `ENNReal.ofReal` through the nonnegative products and powers.
        simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
          ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal <| by
        -- Write `C ^ q * n ^ (q + 1 - a m q)` as `n ^ (q + 1) * (C / (n ^ a) ^ m) ^ q`.
        have hK : 0 ≤ K * n := (Nat.cast_nonneg _).trans hrn
        rw [mul_assoc _ (C ^ q), ← pow_add_one_mul_div_rpow_pow_pow hN, ← mul_assoc, ← mul_pow,
          pow_succ']
        gcongr
  filter_upwards [TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le hb hbound]
    with ω hω
  exact hω.mono fun n hn ↦ by simpa only [mem_ofPred_eq, not_exists, not_le] using hn

/-- **Row and column counts of large entries.** Let the array have entries with a common law `ν`
of finite `m`-th absolute moment, independent within each row and within each column, and let
`p(n) ≤ K n` eventually. If
`2 < q * (m * a - 1)`, then almost surely, eventually every row and every column of the
`p(n) × n` corner has fewer than `q` entries of norm above `n ^ a`. -/
theorem ae_eventually_card_filter_lt_norm_lt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) {m : ℕ} (hm : Integrable (fun z ↦ ‖z‖ ^ m) ν)
    {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} {q : ℕ} (hq : 2 < q * (m * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ i : Fin (p n), (Finset.univ.filter fun j : Fin n ↦
        (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q) ∧
      ∀ j : Fin n, (Finset.univ.filter fun i : Fin (p n) ↦
        (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q := by
  -- Both dimensions are at most `max K 1 * n`; the columns are the rows of the transpose.
  have hp' : ∀ᶠ n in atTop, (p n : ℝ) ≤ max K 1 * n :=
    hp.mono fun n hn ↦ hn.trans (by gcongr; exact le_max_left _ _)
  have hn : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ max K 1 * n :=
    .of_forall fun n ↦ le_mul_of_one_le_left n.cast_nonneg (le_max_right _ _)
  filter_upwards [ae_eventually_forall_card_filter_lt_norm_lt (ℓ := fun n ↦ n) hx hrow hm hp' hn hq,
    ae_eventually_forall_card_filter_lt_norm_lt (x := fun ij ↦ x ij.swap) (r := fun n ↦ n)
      (fun _ ↦ hx _) hcol hm hn hp' hq] with ω hω₁ hω₂
  filter_upwards [hω₁, hω₂] with n h₁ h₂ using ⟨h₁, h₂⟩

end Count

section Maximum

/-- **Largest entry of the corners.** If the entries of the array share a law `ν` with finite
fourth moment and `p(n) ≤ K n` eventually, then almost surely, for every `ε > 0`, every entry of
the `p(n) × n` corner eventually has norm at most `ε √n`. Independence is unnecessary. -/
theorem ae_eventually_norm_le_mul_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν) {K : ℝ} (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (i : Fin (p n)) (j : Fin n),
      ‖x (i, j) ω‖ ≤ ε * √n := by
  -- The norm is a.e. measurable as the fourth root of `‖·‖ ^ 4`, with a finite fourth moment.
  have hnorm : AEMeasurable (fun z : E ↦ ‖z‖) ν :=
    (h4.aemeasurable.pow_const ((4 : ℕ) : ℝ)⁻¹).congr
      (.of_forall fun z ↦ Real.pow_rpow_inv_natCast (norm_nonneg z) four_ne_zero)
  have h4' : MemLp (fun z : E ↦ ‖z‖) 4 ν := by
    refine (integrable_norm_rpow_iff hnorm.aestronglyMeasurable (by norm_num) (by norm_num)).1 ?_
    simpa only [Real.norm_eq_abs, abs_norm, ENNReal.toReal_ofNat, Real.rpow_ofNat] using h4
  let L : ℝ := |K| + 1
  have hL : 0 < L := by positivity
  have hs : Tendsto (fun n : ℕ ↦ √(L * n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop hL)
  -- Enumerate the array along `Nat.pair`; the corner lies in the first `max (p n) n ^ 2` terms.
  have hm : ∀ᶠ n in atTop, ((max (p n) n ^ 2 : ℕ) : ℝ) ≤ √(L * n) ^ 4 := by
    filter_upwards [hp] with n hn
    have hmax : (max (p n) n : ℝ) ≤ L * n := by
      refine max_le (hn.trans ?_) ?_ <;> nlinarith [le_abs_self K, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    push_cast
    exact pow_le_pow_left₀ (by positivity) hmax 2
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib (p := 4)
    (X := fun k ω ↦ ‖x (Nat.unpair k) ω‖)
    (fun k ↦ ((hx _).identDistrib HasLaw.id).comp_of_aemeasurable (by rwa [(hx _).map_eq])) h4' hs
    (by simpa only [NNReal.coe_ofNat, ← Real.rpow_natCast, Nat.cast_ofNat] using hm)]
    with ω hω ε hε
  filter_upwards [hω (ε / √L) (by positivity)] with n hn i j
  have hk : Nat.pair i j < max (p n) n ^ 2 :=
    (Nat.pair_lt_max_add_one_sq i j).trans_le (Nat.pow_le_pow_left (by omega) 2)
  have h := hn _ hk
  rw [Nat.unpair_pair, Real.norm_eq_abs, abs_norm] at h
  refine h.trans_eq ?_
  have : 0 < √L := Real.sqrt_pos.2 hL
  rw [Real.sqrt_mul hL.le]
  field_simp

/-- **Largest entry of the corners under a second moment.** If the entries of the array share a
law `ν` with finite second moment and `p(n) ≤ K n` eventually, then almost surely, for every
`ε > 0`, every entry of the `p(n) × n` corner eventually has norm at most `ε n`. Independence is
unnecessary. -/
theorem ae_eventually_norm_le_mul (hx : ∀ ij, HasLaw (x ij) ν P)
    (h2 : Integrable (fun z ↦ ‖z‖ ^ 2) ν) {K : ℝ} (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (i : Fin (p n)) (j : Fin n),
      ‖x (i, j) ω‖ ≤ ε * n := by
  -- The square roots `‖x‖ ^ (1 / 2)` of the norms have a finite fourth moment.
  let f : E → ℝ := fun z ↦ ‖z‖ ^ (2⁻¹ : ℝ)
  have hf : AEMeasurable f ν :=
    (h2.aemeasurable.sqrt.congr (.of_forall fun z ↦ Real.sqrt_sq (norm_nonneg z))).pow_const _
  have h4 : Integrable (fun t : ℝ ↦ ‖t‖ ^ 4) (ν.map f) := by
    rw [integrable_map_measure (by fun_prop) hf]
    refine h2.congr (.of_forall fun z ↦ ?_)
    simp only [Function.comp_apply, f, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg z)]
    norm_num
  filter_upwards [ae_eventually_norm_le_mul_sqrt
    (fun ij ↦ (hasLaw_map hf).fun_comp (hx ij)) h4 hp] with ω hω ε hε
  filter_upwards [hω (√ε) (Real.sqrt_pos.2 hε)] with n hn i j
  have hle : ‖x (i, j) ω‖ ^ (2⁻¹ : ℝ) ≤ √ε * √n := by
    simpa [f, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hn i j
  calc
    ‖x (i, j) ω‖ = (‖x (i, j) ω‖ ^ (2⁻¹ : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    _ ≤ (√ε * √n) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    _ = ε * n := by rw [mul_pow, Real.sq_sqrt hε.le, Real.sq_sqrt n.cast_nonneg]

end Maximum

end TauCeti.Probability
