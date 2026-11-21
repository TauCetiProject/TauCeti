/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Probability.RandomMatrix.Wigner.EntryMax
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Probability.Independence.Basic
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal.OperatorNorm
import TauCeti.Probability.Moments.Chebyshev
import TauCeti.Probability.RandomMatrix.Wigner.Centering.Basic
import TauCeti.Probability.RandomMatrix.Wigner.Truncation.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# Operator-norm truncation of Wigner corners

A finite fourth moment makes the largest normalized off-diagonal entry tend to zero
almost surely. Above a cutoff of order `n^a` in the unnormalized matrix, with
`1/4 < a`, the number of discarded entries per row is eventually bounded uniformly.
Thus their operator norm vanishes. The mean subtracted in recentering also contributes
a vanishing operator norm, and the real diagonal can be removed under its finite
second moment. For `a < 1/2` the retained normalized entries are polynomially small,
as needed for growing trace moments.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), Theorems 2.3.23–2.3.24.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.12.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix ProbabilityTheory Set
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {X : Ω' → ℂ}

/-- The probability that some row has at least `q` entries above the normalized cutoff
is at most `n^(q+1)` times the `q`-th power of a uniform bound on the unnormalized tail
probabilities. For zero-diagonal corners, independence is needed only among the off-diagonal entries
within each row. -/
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
  have hE (i : Fin n) : iIndepSet (E i) P := by
    apply iIndep_comap_mem_iff.1
    have hind' := (hind i).comp (fun _ (z : ℂ) ↦ R / Real.sqrt n < ‖z‖) fun _ ↦
      measurableSet_setOfPred.mp (measurableSet_lt measurable_const measurable_norm)
    simpa only [E, mem_ofPred_eq, Function.comp_def, Prop.instMeasurableSpace]
      using hind'.iIndep
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
and independence within each row, the probability of at least `q` entries in some row above
`(n+1)^a / √(n+1)` is bounded by the `q`-th power of that moment times
`(n+1)^(q+1-4*a*q)`. -/
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
    exact meas_ge_le_integral_norm_pow_div_pow 4 (hX.integrable_norm_pow (by decide))
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

private theorem ae_eventually_card_filter_lt_norm_wignerMatrix_zero_apply_lt
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

/-- For zero-diagonal Wigner corners with a common upper-entry law of finite fourth moment
and independence within each row, the part discarded above cutoff `(n+1)^a / √(n+1)`
has operator norm tending to zero almost surely when `a > 1/4`. -/
theorem ae_tendsto_l2_opNorm_wignerMatrix_zero_hardThreshold
    (hind : ∀ n : ℕ, ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hX : MemLp X 4 Q) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).hardThreshold
      (((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ))‖) atTop (𝓝 0) := by
  have hgap : 0 < 4 * a - 1 := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / (4 * a - 1))
  have hq' := (div_lt_iff₀ hgap).1 hq
  filter_upwards [ae_eventually_card_filter_lt_norm_wignerMatrix_zero_apply_lt hind hid hX hq',
    ae_eventually_norm_wignerMatrix_zero_apply_le hid hX] with ω hsparse hmax
  apply tendsto_order.2
  refine ⟨fun r hr ↦ .of_forall fun n ↦ hr.trans_le (norm_nonneg _), fun r hr ↦ ?_⟩
  have hε : 0 < r / (q + 1 : ℝ) := by positivity
  filter_upwards [hsparse, hmax _ hε] with n hn hentry
  refine ((wignerMatrix_isHermitian _ _ ω _).l2_opNorm_hardThreshold_le _ hε.le
    (fun i ↦ (hn i).le) (fun i j _ ↦ hentry i j)).trans_lt ?_
  rw [mul_comm]
  calc
    _ < (r / (q + 1 : ℝ)) * (q + 1) := mul_lt_mul_of_pos_left (by linarith) hε
    _ = r := div_mul_cancel₀ _ (by positivity)

/-- The original Wigner corners and their zero-diagonal centered truncations at radius
`(n+1)^a`, with `a > 1/4`, differ by a vanishing operator norm almost surely. The upper
entries have a common centered law with finite fourth moment, and the diagonal entries have
a common law with finite second moment. Independence is required only among the off-diagonal
entries within each row. -/
theorem ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation_zero
    (hind : ∀ n : ℕ, ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P)
    (hid : ∀ ij, IdentDistrib (ξ ij) X P Q) (hX : MemLp X 4 Q)
    (hmean : ∫ ω, X ω ∂Q = 0) {Ω'' : Type*} [MeasurableSpace Ω'']
    {S : Measure Ω''} {Y : Ω'' → ℝ}
    (hd : ∀ i, IdentDistrib (η i) Y P S) (hη : MemLp Y 2 S)
    {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_l2_opNorm_wignerMatrix_zero_hardThreshold hind hid hX ha,
    ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero (ξ := ξ) hd hη] with ω htail hdiag
  have hquot : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ) / ((((n + 1 : ℕ) : ℝ) ^ a) ^ 3))
      atTop (𝓝 0) := by
    refine ((tendsto_rpow_neg_atTop (by linarith : 0 < 3 * a - 1 / 2)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).congr fun n ↦ ?_
    have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Function.comp_apply, Function.comp_apply, Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast hN.le, ← Real.rpow_sub hN]
    congr 1
    push_cast
    ring
  have hcenterLimit := hX.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero
    (k := 3) hmean (fun _ ↦ Real.rpow_pos_of_pos (by positivity) _)
    (fun _ ↦ Real.sqrt_nonneg _) hquot
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using (hdiag.add htail).add hcenterLimit)
  let R : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let Z := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  let T := wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) (n + 1) ω
  let B := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) (fun _ _ ↦ 0) (n + 1) ω
  let c := ∫ ω', {ω'' | ‖X ω''‖ ≤ R}.indicator X ω' ∂Q
  have hcenter : (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c) =
      (fun ij ↦ centeredTruncation (ξ ij) P R) := by
    funext ij
    rw [centeredTruncation_def, (hid ij).integral_indicator_setOf_norm_le_eq]
  have hTB : ‖T - B‖ ≤ Real.sqrt (n + 1 : ℕ) * ‖c‖ := by
    simpa only [hcenter] using l2_opNorm_wignerMatrix_sub_center_le
      (fun ij ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) c (n + 1) ω
  have hZT := wignerMatrix_zero_sub_indicator_eq_hardThreshold (ξ := ξ) (n := n + 1) R ω
  calc
    _ ≤ ‖wignerMatrix ξ η (n + 1) ω - Z‖ + ‖Z - T‖ + ‖T - B‖ := by
      exact (norm_sub_le_norm_sub_add_norm_sub _ T _).trans
        (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ Z _) _)
    _ ≤ _ := by
      have h1 : ‖Z - T‖ = ‖Z.hardThreshold ((R : ℝ) / Real.sqrt (n + 1 : ℕ))‖ :=
        congrArg norm hZT
      exact add_le_add (add_le_add_right h1.le _) hTB

end TauCeti.Probability
