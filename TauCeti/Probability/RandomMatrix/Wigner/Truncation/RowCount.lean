/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Probability.Independence.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Markov
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# Row counts of large entries in Wigner corners

If the off-diagonal entries within each row of a zero-diagonal Wigner corner are independent, the
chance that some row has at least `q` entries above a normalized cutoff is controlled by the
`q`-th power of a uniform entry tail bound. These events need not be measurable, so the bounds
are stated for the measure, which is an outer measure on nonmeasurable sets.

For a common upper-entry law with finite fourth moment and the cutoff `(n+1)^a / √(n+1)`, Markov's
inequality bounds this by a constant times `(n+1)^(q+1-4*a*q)`. When `2 < q * (4*a - 1)` these
bounds are summable, so by Borel–Cantelli every row eventually has fewer than `q` entries above
the cutoff almost surely.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), Theorems 2.3.23–2.3.24.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {ξ : StrictUpper → Ω → ℂ} {X : Ω' → ℂ}

/-- The measure of the set where some row has at least `q` entries above the normalized cutoff
is at most `n^(q+1)` times the `q`-th power of a uniform bound on the unnormalized tail
measures. The entries need not be measurable, so this is an outer-measure bound in general and a
probability bound when the events are measurable. For zero-diagonal corners, independence is
needed only among the off-diagonal entries within each row. -/
theorem measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_le {n q : ℕ}
    (hind : ∀ i : Fin n, iIndepFun (fun (j : {j : Fin n // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) n ω i j) P)
    {R : ℝ} (hR : 0 ≤ R) {p : ℝ≥0∞}
    (htail : ∀ ij : StrictUpper, ij.val.2 < n → P {ω | R < ‖ξ ij ω‖} ≤ p) :
    P {ω | ∃ i : Fin n, q ≤ (Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card} ≤
        (n : ℝ≥0∞) ^ (q + 1) * p ^ q := by
  classical
  let E (i : Fin n) (j : {j : Fin n // i ≠ j}) :=
    {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖}
  -- Each exceedance event is the preimage of a Borel set under its entry, so it is measurable in
  -- the σ-algebra pulled back by that entry and inherits the entries' independence.
  have hE (i : Fin n) : iIndepSet (E i) P := by
    rw [iIndepSet_iff_iIndep]
    exact iIndep_of_iIndep_of_le (hind i).iIndep fun j ↦
      MeasurableSpace.generateFrom_singleton_le <| MeasurableSpace.measurableSet_comap.2
        ⟨{z : ℂ | R / Real.sqrt n < ‖z‖}, measurableSet_lt measurable_const measurable_norm, rfl⟩
  have hp (i : Fin n) (j : {j : Fin n // i ≠ j}) : P (E i j) ≤ p := by
    simp only [E, div_lt_norm_wignerMatrix_apply_iff _ _ _ j.property]
    exact htail _ (max_lt i.isLt j.val.isLt)
  have hcount (ω : Ω) (i : Fin n) :
      (Finset.univ.filter fun j ↦ ω ∈ E i j).card =
        (Finset.univ.filter fun j ↦ R / Real.sqrt n <
          ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card := by
    let S := Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖
    have hsub : S.subtype (i ≠ ·) = Finset.univ.filter (fun j ↦ ω ∈ E i j) := by
      ext j
      simp [S, E]
    rw [← hsub, Finset.card_subtype, Finset.filter_eq_self.2]
    intro j hj hij
    subst j
    have hlt := (Finset.mem_filter.1 hj).2
    simp only [wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero] at hlt
    exact (not_lt_of_ge (div_nonneg hR (Real.sqrt_nonneg _))) hlt
  calc
    _ ≤ ∑ i : Fin n, ((Fintype.card {j : Fin n // i ≠ j}).choose q : ℝ≥0∞) * p ^ q := by
      simpa only [hcount] using measure_exists_le_card_filter_mem_le E hE hp q
    _ ≤ ∑ _i : Fin n, (n : ℝ≥0∞) ^ q * p ^ q := by
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hc : Fintype.card {j : Fin n // i ≠ j} ≤ n := by
        simpa only [Fintype.card_fin] using Fintype.card_subtype_le (i ≠ ·)
      exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hc q)
    _ = _ := by simp [nsmul_eq_mul, pow_succ', mul_assoc]

/-- In a zero-diagonal Wigner corner with a common upper-entry law of finite fourth moment
and independence within each row, the measure of the set where some row has at least `q` entries
above `(n+1)^a / √(n+1)` is bounded by the `q`-th power of that moment times
`(n+1)^(q+1-4*a*q)`. The set need not be measurable, so this is an outer-measure bound in
general and a probability bound when the set is measurable. -/
theorem measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_le_ofReal_rpow
    (a : ℝ) (n q : ℕ)
    (hind : ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P)
    (hid : ∀ ij : StrictUpper, ij.val.2 < n + 1 → IdentDistrib (ξ ij) X P Q)
    (hX : MemLp X 4 Q) :
    P {ω | ∃ i : Fin (n + 1), q ≤ (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card} ≤
      ENNReal.ofReal ((∫ ω, ‖X ω‖ ^ 4 ∂Q) ^ q *
        ((n + 1 : ℕ) : ℝ) ^ ((q : ℝ) + 1 - a * (4 * q))) := by
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂Q
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  let N : ℝ := (n + 1 : ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hr : 0 < N ^ a := Real.rpow_pos_of_pos hN _
  have htail : Q {ω | N ^ a < ‖X ω‖} ≤ ENNReal.ofReal (C / (N ^ a) ^ 4) := by
    have hsub : {ω | N ^ a < ‖X ω‖} ⊆ {ω | N ^ a ≤ ‖X ω‖} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      exact hω.le
    refine (measure_mono hsub).trans ?_
    exact meas_ge_le_integral_pow_div_pow 4 (hX.integrable_norm_pow (by decide))
      (.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _) hr
  have hpow : N ^ (q + 1) * (C / (N ^ a) ^ 4) ^ q =
      C ^ q * N ^ ((q : ℝ) + 1 - a * (4 * q)) := by
    rw [div_pow, ← pow_mul, ← Real.rpow_natCast N (q + 1), ← Real.rpow_mul_natCast hN.le,
      mul_div_left_comm, ← Real.rpow_sub hN]
    push_cast
    ring
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ (q + 1) * Q {ω | N ^ a < ‖X ω‖} ^ q :=
      measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_le hind
        hr.le fun ij hij ↦ ((hid ij hij).comp measurable_norm).measure_mem_eq
          measurableSet_Ioi |>.le
    _ ≤ ENNReal.ofReal (N ^ (q + 1) * (C / (N ^ a) ^ 4) ^ q) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (div_nonneg hC (by positivity))]
      gcongr
    _ = _ := congrArg ENNReal.ofReal hpow

/-- The measures of the events that some row of the zero-diagonal Wigner corner has at
least `q` entries above cutoff `(n+1)^a / √(n+1)` have finite sum when `2 < q * (4*a - 1)`.
The upper entries are identically distributed with finite fourth moment, and the off-diagonal
entries of each row are independent. -/
theorem tsum_measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_lt_top
    (hind : ∀ n : ℕ, ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hX : MemLp X 4 Q) {a : ℝ} {q : ℕ} (hq : 2 < q * (4 * a - 1)) :
    (∑' n : ℕ, P {ω | ∃ i : Fin (n + 1), q ≤ (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card}) < ∞ := by
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂Q
  let E (n : ℕ) := {ω | ∃ i : Fin (n + 1), q ≤ (Finset.univ.filter fun j ↦
    ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
      ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card}
  have hbound (n : ℕ) : P (E n) ≤
      ENNReal.ofReal (C ^ q * ((n : ℝ) + 1) ^ ((q : ℝ) + 1 - a * (4 * q))) := by
    refine (measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_le_ofReal_rpow a n q
      (hind n) (fun ij _ ↦ hid ij) hX).trans_eq ?_
    rw [Nat.cast_add_one]
  exact (tsum_le_tsum hbound).trans_lt
    (tsum_ofReal_mul_natCast_add_one_rpow_lt_top _ (by linarith))

/-- For zero-diagonal Wigner corners with a common upper-entry law of finite fourth moment and
independence within each row, almost surely every row eventually has fewer than `q` entries above
the cutoff `(n+1)^a / √(n+1)` when `2 < q * (4*a - 1)`. -/
theorem ae_eventually_card_filter_lt_norm_wignerMatrix_zero_apply_lt
    (hind : ∀ n : ℕ, ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hX : MemLp X 4 Q) {a : ℝ} {q : ℕ} (hq : 2 < q * (4 * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (n + 1), (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card < q := by
  have hfinite :=
    tsum_measure_exists_le_card_filter_lt_norm_wignerMatrix_zero_apply_lt_top hind hid hX hq
  exact (ae_eventually_notMem hfinite.ne).mono fun ω hω ↦
    hω.mono fun n hn i ↦ lt_of_not_ge fun hi ↦ hn ⟨i, hi⟩

end TauCeti.Probability
