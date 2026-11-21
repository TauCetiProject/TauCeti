/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Probability.RandomMatrix.Wigner.CornerAverage
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Probability.RandomMatrix.Diagonal
import TauCeti.Probability.Moments.Chebyshev
import TauCeti.Probability.RandomMatrix.Centering
import TauCeti.Analysis.Matrix.HardThreshold
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Real

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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {X : Ω → ℂ}

omit [MeasurableSpace Ω] in
private theorem div_lt_norm_wignerMatrix_apply_iff {n : ℕ} (ω : Ω)
    {i j : Fin n} (hij : i ≠ j) (R : ℝ) :
    R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖ ↔
      R < ‖ξ ⟨(min i.val j.val, max i.val j.val), min_lt_max.mpr (Fin.val_ne_of_ne hij)⟩ ω‖ := by
  rw [norm_wignerMatrix_apply_of_ne _ _ _ hij, inv_mul_eq_div,
    div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.zero_lt_of_lt i.isLt)))]

private theorem measure_norm_wignerMatrix_zero_apply_gt {n : ℕ}
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    {i j : Fin n} (hij : i ≠ j) (R : ℝ) :
    P {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖} =
      P {ω | R < ‖X ω‖} := by
  simp_rw [div_lt_norm_wignerMatrix_apply_iff _ hij]
  exact ((hid _ (max_lt i.isLt j.isLt)).comp measurable_norm).measure_mem_eq measurableSet_Ioi

private theorem measure_row_large_wigner_entries {n q : ℕ}
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    (i : Fin n) (j : Fin q → Fin n) (hinj : Function.Injective j)
    (hne : ∀ k, i ≠ j k) (R : ℝ) :
    P (⋂ k, {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i (j k)‖}) =
      P {ω | R < ‖X ω‖} ^ q := by
  have hedge : Function.Injective (fun k ↦ s(i, j k)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hinj h.2
    · exact (hne b h.1).elim
  have hind' := iIndepFun_wignerMatrix_apply_of_ne (η := fun _ _ ↦ 0)
    (fun _ ↦ i) j hne hedge hind
  calc
    _ = ∏ k, P {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i (j k)‖} :=
      hind'.meas_iInter (fun _ ↦ ⟨{z : ℂ | R / Real.sqrt n < ‖z‖},
        measurableSet_lt measurable_const measurable_norm, rfl⟩)
    _ = _ := by
      simp only [measure_norm_wignerMatrix_zero_apply_gt hid (hne _), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

/-- The probability that some row has at least `q` entries above the normalized cutoff
is at most `n^(q+1)` times the `q`-th power of the common unnormalized tail probability. -/
theorem measure_exists_row_with_large_wigner_entries_le {n q : ℕ}
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    {R : ℝ} (hR : 0 ≤ R) :
    P {ω | ∃ i : Fin n, q ≤ (Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card} ≤
        (n : ℝ≥0∞) ^ (q + 1) * P {ω | R < ‖X ω‖} ^ q := by
  classical
  let E (p : Fin n × (Fin q → Fin n)) : Set Ω :=
    if Function.Injective p.2 ∧ ∀ k, p.1 ≠ p.2 k then
      ⋂ k, {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω p.1 (p.2 k)‖}
    else ∅
  have hcover : {ω | ∃ i : Fin n, q ≤ (Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card} ⊆ ⋃ p, E p := by
    rintro ω ⟨i, hi⟩
    obtain ⟨t, hsub, hcard⟩ := Finset.exists_subset_card_eq hi
    let e := (Fintype.equivFinOfCardEq (Fintype.card_coe t ▸ hcard)).symm
    let j : Fin q → Fin n := Subtype.val ∘ e
    have hj (k) := (Finset.mem_filter.1 (hsub (e k).property)).2
    have hne (k) : i ≠ j k := by
      intro h
      have hk := hj k
      dsimp only [j, Function.comp_apply] at h
      rw [← h] at hk
      simp only [wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero] at hk
      exact (not_lt_of_ge (div_nonneg hR (Real.sqrt_nonneg _))) hk
    have hv : Function.Injective j ∧ ∀ k, i ≠ j k := ⟨Subtype.val_injective.comp e.injective, hne⟩
    exact mem_iUnion.2 ⟨(i, j), by
      simpa only [E, ite_eq_left hv, mem_iInter, mem_ofPred_eq, j, Function.comp_apply] using hj⟩
  calc
    _ ≤ ∑ p, P (E p) := (measure_mono hcover).trans (measure_iUnion_fintype_le P E)
    _ ≤ ∑ _p : Fin n × (Fin q → Fin n), P {ω | R < ‖X ω‖} ^ q := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      dsimp only [E]
      split_ifs with h
      · exact (measure_row_large_wigner_entries hind hid p.1 p.2 h.1 h.2 _).le
      · rw [measure_empty]
        exact bot_le
    _ = _ := by simp [pow_succ, mul_comm, mul_assoc]

private theorem measure_exists_row_with_large_wigner_entries_rpow_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) (a : ℝ) (n q : ℕ) :
    P {ω | ∃ i : Fin (n + 1), q ≤ (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card} ≤
      ENNReal.ofReal ((∫ ω, ‖X ω‖ ^ 4 ∂P) ^ q *
        ((n + 1 : ℕ) : ℝ) ^ ((q : ℝ) + 1 - a * (4 * q))) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂P
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  let N : ℝ := (n + 1 : ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hr : 0 < N ^ a := Real.rpow_pos_of_pos hN _
  have htail : P {ω | N ^ a < ‖X ω‖} ≤ ENNReal.ofReal (C / (N ^ a) ^ 4) := by
    have hsq : Integrable (fun ω ↦ ‖(‖X ω‖ ^ 2 : ℝ)‖ ^ 2) P := by
      simpa only [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul] using
        (hX.integrable_norm_pow (by decide))
    have hsub : {ω | N ^ a < ‖X ω‖} ⊆ {ω | (N ^ a) ^ 2 ≤ ‖(‖X ω‖ ^ 2 : ℝ)‖} := by
      intro ω hω
      simp only [mem_ofPred_eq, Real.norm_of_nonneg (sq_nonneg _)] at hω ⊢
      exact pow_le_pow_left₀ hr.le hω.le _
    refine (measure_mono hsub).trans ?_
    simpa only [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul, C] using
      meas_ge_le_integral_norm_sq_div_sq hsq (sq_pos_of_pos hr)
  have hpow : N ^ (q + 1) * (C / (N ^ a) ^ 4) ^ q =
      C ^ q * N ^ ((q : ℝ) + 1 - a * (4 * q)) := by
    rw [div_pow, ← pow_mul, ← Real.rpow_natCast N (q + 1), Real.rpow_mul_div_rpow_pow hN]
    push_cast
    ring
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ (q + 1) * P {ω | N ^ a < ‖X ω‖} ^ q :=
      measure_exists_row_with_large_wigner_entries_le (hind.precomp Subtype.val_injective)
        (fun ij _ ↦ hid ij) hr.le
    _ ≤ ENNReal.ofReal (N ^ (q + 1) * (C / (N ^ a) ^ 4) ^ q) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (div_nonneg hC (by positivity))]
      gcongr
    _ = _ := congrArg ENNReal.ofReal hpow

private theorem ae_eventually_card_row_large_wigner_entries_lt
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) {a : ℝ} {q : ℕ} (hq : 2 < q * (4 * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (n + 1), (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card < q := by
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂P
  let E (n : ℕ) := {ω | ∃ i : Fin (n + 1), q ≤ (Finset.univ.filter fun j ↦
    ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
      ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card}
  let b (n : ℕ) := C ^ q * ((n + 1 : ℕ) : ℝ) ^ ((q : ℝ) + 1 - a * (4 * q))
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ ((q : ℝ) + 1 - a * (4 * q))) :=
    (Real.summable_nat_rpow (p := (q : ℝ) + 1 - a * (4 * q))).2 (by linarith)
  have hb : Summable b := ((summable_nat_add_iff 1).2 hsum).mul_left (C ^ q)
  have hbound (n : ℕ) : P (E n) ≤ ENNReal.ofReal (b n) := by
    exact measure_exists_row_with_large_wigner_entries_rpow_le hind hid hX a n q
  have hfinite : (∑' n, P (E n)) < ∞ := (tsum_le_tsum hbound).trans_lt hb.tsum_ofReal_lt_top
  exact (ae_eventually_notMem hfinite.ne).mono fun ω hω ↦
    hω.mono fun n hn i ↦ lt_of_not_ge fun hi ↦ hn ⟨i, hi⟩

omit [MeasurableSpace Ω] in
private theorem wignerMatrix_sub_indicator_eq_hardThreshold {n : ℕ}
    (r : ℝ≥0) (ω : Ω) :
    wignerMatrix ξ (fun _ _ ↦ 0) n ω -
      wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ r}.indicator (ξ ij)) (fun _ _ ↦ 0) n ω =
    (wignerMatrix ξ (fun _ _ ↦ 0) n ω).hardThreshold (r / Real.sqrt n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.hardThreshold_apply]
  simp only [wignerMatrix_sub, Matrix.hardThreshold_apply, div_lt_norm_wignerMatrix_apply_iff _ hij]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, min_eq_left h.le, max_eq_right h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, min_eq_right h.le, max_eq_left h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp

private theorem ae_tendsto_norm_wignerMatrix_hardThreshold
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).hardThreshold
      (((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ))‖) atTop (𝓝 0) := by
  have hgap : 0 < 4 * a - 1 := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / (4 * a - 1))
  have hq' := (div_lt_iff₀ hgap).1 hq
  filter_upwards [ae_eventually_card_row_large_wigner_entries_lt hind hid hX hq',
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
`n^a` differ by a vanishing operator norm almost surely. Only the upper coordinates
need to be independent, and no independence between the diagonal and upper coordinates
is needed. -/
theorem ae_tendsto_norm_wignerMatrix_sub_centeredTruncation
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P) (hX : MemLp X 4 P)
    (hmean : ∫ ω, X ω ∂P = 0) (hd : ∀ i, IdentDistrib (η i) (η 0) P P) (hη : MemLp (η 0) 2 P)
    {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  filter_upwards [ae_tendsto_norm_wignerMatrix_hardThreshold hind hid hX ha,
    ae_tendsto_norm_wignerMatrix_sub_zero_diagonal (ξ := ξ) hd hη] with ω htail hdiag
  have hExp : 1 / 6 < a := by linarith
  have hcenterLimit := hX.tendsto_sqrt_mul_norm_integral_indicator_norm_le hmean hExp
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using (hdiag.add htail).add hcenterLimit)
  let R : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let Z := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  let T := wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) (n + 1) ω
  let B := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) (fun _ _ ↦ 0) (n + 1) ω
  let c := ∫ ω', {ω'' | ‖X ω''‖ ≤ R}.indicator X ω' ∂P
  have hTB : T - B = hermitianOffDiagonal ((Real.sqrt (n + 1 : ℕ))⁻¹ • c) (n + 1) := by
    have hcenter : (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c) =
        (fun ij ↦ centeredTruncation (ξ ij) P R) := by
      funext ij
      rw [centeredTruncation_def, (hid ij).integral_indicator_setOf_norm_le_eq]
    have h : T = wignerMatrix (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c)
        (fun _ _ ↦ 0) (n + 1) ω + hermitianOffDiagonal ((Real.sqrt (n + 1 : ℕ))⁻¹ • c) (n + 1) :=
      wignerMatrix_eq_center_add_hermitianOffDiagonal
        (fun ij ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) c (n + 1) ω
    rw [hcenter] at h
    exact sub_eq_iff_eq_add.2 (h.trans (add_comm _ _))
  have hZT := wignerMatrix_sub_indicator_eq_hardThreshold (ξ := ξ) (n := n + 1) R ω
  calc
    _ ≤ ‖wignerMatrix ξ η (n + 1) ω - Z‖ + ‖Z - T‖ + ‖T - B‖ := by
      exact (norm_sub_le_norm_sub_add_norm_sub _ T _).trans
        (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ Z _) _)
    _ ≤ _ := by
      have h1 : ‖Z - T‖ = ‖Z.hardThreshold ((R : ℝ) / Real.sqrt (n + 1 : ℕ))‖ :=
        congrArg norm hZT
      have h2 : ‖T - B‖ ≤ Real.sqrt (n + 1 : ℕ) * ‖c‖ := by
        rw [hTB]
        refine (l2_opNorm_hermitianOffDiagonal_le _ _).trans_eq ?_
        have hs : 0 < Real.sqrt (n + 1 : ℕ) := by positivity
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc]
        congr 1
        exact (mul_inv_eq_iff_eq_mul₀ hs.ne').2
          (by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)])
      exact add_le_add (add_le_add_right h1.le _) h2

end TauCeti.Probability
