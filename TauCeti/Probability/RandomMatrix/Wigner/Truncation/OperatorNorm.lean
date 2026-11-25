/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Probability.RandomMatrix.Wigner.Corner.Maximum
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal.OperatorNorm
import TauCeti.Probability.RandomMatrix.Wigner.Centering.Basic
import TauCeti.Probability.RandomMatrix.Wigner.Truncation.HardThreshold
import TauCeti.Probability.RandomMatrix.Wigner.Truncation.RowCount
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Operator-norm truncation of Wigner corners

Let the upper entries share a common law with finite fourth moment. Then the largest normalized
off-diagonal entry tends to zero almost surely, without any independence. Above a cutoff of order
`n^a` in the unnormalized matrix, with `1/4 < a`, independence of the off-diagonal entries within
each row makes the number of discarded entries per row eventually bounded uniformly (see
`TauCeti.Probability.RandomMatrix.Wigner.Truncation.RowCount`). Thus their operator norm
vanishes. When the common upper law is centered, the mean subtracted in recentering
also contributes a vanishing operator norm. Hence the corners and their centered truncations with
the same diagonal differ by a vanishing operator norm, whatever the diagonal. When the diagonal
entries share a law with finite second moment, the diagonal can also be removed. The retained
normalized entries of the zero-diagonal truncations are bounded by
`TauCeti.norm_wignerMatrix_centeredTruncation_zero_apply_le` in
`TauCeti.Probability.RandomMatrix.Wigner.Truncation.Basic`. For the corner of size `n + 1` at
cutoff `(n+1)^a` that bound is `2 (n+1)^(a - 1/2)`, polynomially small for `a < 1/2`.

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
  filter_upwards [ae_eventually_card_filter_lt_norm_wignerMatrix_zero_apply_lt (m := 4) hind
      (fun ij ↦ ((hid ij).symm.memLp_snd hX).integrable_norm_pow (by decide))
      (fun ij ↦ ((hid ij).comp (measurable_norm.pow_const 4)).integral_eq.le)
      (by exact_mod_cast hq'),
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

/-- The original Wigner corners and their centered truncations at radius `(n+1)^a`, with
`a > 1/4` and the same diagonal, differ by a vanishing operator norm almost surely. The upper
entries have a common centered law with finite fourth moment, and independence is required only
among the off-diagonal entries within each row. The diagonal is arbitrary. -/
theorem ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation
    (hind : ∀ n : ℕ, ∀ i : Fin (n + 1), iIndepFun (fun (j : {j : Fin (n + 1) // i ≠ j}) ω ↦
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j) P)
    (hid : ∀ ij, IdentDistrib (ξ ij) X P Q) (hX : MemLp X 4 Q)
    (hmean : ∫ ω, X ω ∂Q = 0) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        η (n + 1) ω‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_l2_opNorm_wignerMatrix_zero_hardThreshold hind hid hX ha]
    with ω htail
  have hquot : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ) / ((((n + 1 : ℕ) : ℝ) ^ a) ^ 3))
      atTop (𝓝 0) :=
    (tendsto_sqrt_div_rpow_pow_atTop_nhds_zero (k := 3) (by push_cast; linarith)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hcenterLimit := hX.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero
    (k := 3) hmean hquot
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using htail.add hcenterLimit)
  let R : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let Z := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  let T := wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) (n + 1) ω
  let B := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) (fun _ _ ↦ 0) (n + 1) ω
  let c := ∫ ω', {ω'' | ‖X ω''‖ ≤ R}.indicator X ω' ∂Q
  -- The common diagonal cancels in the difference.
  have hdiag : wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η (n + 1) ω = Z - B := by
    simp only [Z, B, wignerMatrix_sub, sub_self]
  have hcenter : (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c) =
      (fun ij ↦ centeredTruncation (ξ ij) P R) := by
    funext ij
    rw [centeredTruncation_def, (hid ij).integral_indicator_setOf_norm_le_eq]
  have hTB : ‖T - B‖ ≤ Real.sqrt (n + 1 : ℕ) * ‖c‖ := by
    simpa only [hcenter] using l2_opNorm_wignerMatrix_sub_center_le
      (fun ij ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) c (n + 1) ω
  have hZT := wignerMatrix_zero_sub_indicator_eq_hardThreshold (ξ := ξ) (n := n + 1) R ω
  calc
    _ = ‖Z - B‖ := congrArg norm hdiag
    _ ≤ ‖Z - T‖ + ‖T - B‖ := norm_sub_le_norm_sub_add_norm_sub _ T _
    _ ≤ _ := add_le_add (congrArg norm hZT).le hTB

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
  filter_upwards [ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero (ξ := ξ) hd hη,
    ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation (η := fun _ _ ↦ 0)
      hind hid hX hmean ha] with ω hdiag htrunc
  refine squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ norm_sub_le_norm_sub_add_norm_sub _ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω) _) ?_
  simpa only [add_zero] using hdiag.add htrunc

end TauCeti.Probability
