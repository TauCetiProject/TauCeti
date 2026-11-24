/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecificLimits.DyadicSum

/-!
# Frequency envelopes

A frequency envelope for `u` records, at each dyadic frequency `2^k`, `k ∈ ℤ`, an upper bound
`c_k` for the size `a_k = ‖P_k u‖_X` of the Littlewood–Paley block of `u` in a translation-invariant
space `X`, chosen to vary slowly with `k`: `2^{-δ(j-k)} c_j ≲ c_k ≲ 2^{δ(j-k)} c_j` for `j > k`.
Everything here is a statement about real sequences indexed by `ℤ`; it is applied to the weighted
block sizes of elements of homogeneous Besov spaces in
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.FrequencyEnvelope`.

Following Oh–Tataru, Definitions 3.2–3.4 and Lemma 3.5:

* `TauCeti.IsSlowlyVarying σ₁ σ₂ c`: `2^{-σ₁(j-k)} c_j ≲ c_k ≲ 2^{σ₂(j-k)} c_j` for `j > k`.
* `TauCeti.IsFrequencyEnvelope δ a c`: `c` is positive, or identically zero, majorizes `a`, and is
  slowly varying with both rates `δ`. The zero sequence is an envelope of `a` exactly when
  `a ≤ 0`.
* `TauCeti.IsAdmissibleEnvelope σ₁ σ₂ ε c`: `c` is `(-σ₁, σ₂)`-admissible, that is slowly varying
  with the rates `σ₁(1 - ε)` and `σ₂(1 - ε)`.
* `TauCeti.dyadicLowSum r d k = ∑_{j < k} 2^{r(j-k)} d_j` and `TauCeti.dyadicLowSup r c k =
  sup_{j < k} 2^{r(j-k)} c_j`, so that the sequence `c^{[σ]}` of Oh–Tataru is
  `dyadicLowSup ((1 - ε) σ) c`.
* `TauCeti.IsFrequencyCompatible σ ε c d`: `d` is `σ`-compatible with `c`, that is the sums
  `∑_{j < k} 2^{σ(1-ε)(j-k)} d_j` converge and `c_k ∑_{j < k} 2^{σ(1-ε)(j-k)} d_j ≲ d_k`.

## Main results

* `TauCeti.exists_isFrequencyEnvelope_of_summable_sq`: every square-summable sequence has a
  frequency envelope that is `(-σ₁, σ₂)`-admissible, with `‖c‖_{ℓ²} ≲ ‖a‖_{ℓ²}`, the constant
  depending only on the rates. The envelope is `TauCeti.frequencyEnvelopeOf r a`, with
  `c_k² = ∑_j 2^{-2r|j-k|} a_j²`.
* `TauCeti.IsSlowlyVarying.of_le_two_rpow_mul_abs`: a nonnegative sequence with
  `c_k ≤ 2^{r|k-k'|} c_{k'}` is slowly varying with all rates at least `r`.
* `TauCeti.mul_dyadicLowSum_add_mul_dyadicLowSum_le` and
  `TauCeti.isFrequencyCompatible_add_mul_dyadicLowSum` (Lemma 3.5): if `0 ≤ c ≤ M`, `0 ≤ d`,
  `σ' < σ(1 - ε)` and the sums `∑_{j < k} 2^{σ'(j-k)} d_j` are finite, then
  `e_k = d_k + c_k ∑_{j < k} 2^{σ'(j-k)} d_j` is `σ`-compatible with `c`, with constant
  `1 + M / (2^{σ(1-ε) - σ'} - 1)`; the sums for `e` converge by
  `TauCeti.summable_dyadicLowSum_add_mul_dyadicLowSum`. No slow variation of `c` or `d` is needed.

Examples and counterexamples: `TauCeti.isFrequencyEnvelope_single` (a single nonzero block),
`TauCeti.not_isAdmissibleEnvelope_two_rpow` (a sequence growing too fast to be admissible),
`TauCeti.isFrequencyEnvelope_zero` (the zero envelope of zero data) and
`TauCeti.not_summable_dyadicLowSum_one` (a lower sum that is infinite).

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 3, Definitions 3.2–3.4 (frequency envelopes, admissibility
  and compatibility) and Lemma 3.5.
-/

public section

noncomputable section

namespace TauCeti

/-- A sequence `c : ℤ → ℝ` is **slowly varying with rates `σ₁` and `σ₂`** if, up to a constant,
it grows by at most `2^{σ₁ m}` and decays by at most `2^{-σ₂ m}` over `m` steps to the right:
`2^{-σ₁(j-k)} c_j ≲ c_k ≲ 2^{σ₂(j-k)} c_j` for `j > k`. -/
def IsSlowlyVarying (σ₁ σ₂ : ℝ) (c : ℤ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ k j : ℤ, k < j →
    (2 : ℝ) ^ (-σ₁ * (j - k : ℝ)) * c j ≤ C * c k ∧ c k ≤ C * (2 : ℝ) ^ (σ₂ * (j - k : ℝ)) * c j

/-- A **frequency envelope** with rate `δ` for the block sizes `a_k = ‖P_k u‖_X`, `k ∈ ℤ`: a
sequence `c` that is positive or identically zero, majorizes `a`, and is slowly varying with both
rates `δ`, `2^{-δ(j-k)} c_j ≲ c_k ≲ 2^{δ(j-k)} c_j` for `j > k`. -/
structure IsFrequencyEnvelope (δ : ℝ) (a c : ℤ → ℝ) : Prop where
  /-- The envelope is positive, or identically zero. -/
  pos_or_eq_zero : (∀ k, 0 < c k) ∨ c = 0
  /-- The envelope majorizes the block sizes. -/
  le : ∀ k, a k ≤ c k
  /-- The envelope is slowly varying with both rates `δ`. -/
  isSlowlyVarying : IsSlowlyVarying δ δ c

/-- A frequency envelope is nonnegative. -/
theorem IsFrequencyEnvelope.nonneg {δ : ℝ} {a c : ℤ → ℝ} (h : IsFrequencyEnvelope δ a c) (k : ℤ) :
    0 ≤ c k := by
  rcases h.pos_or_eq_zero with hc | rfl
  · exact (hc k).le
  · exact le_rfl

/-- A sequence is **`(-σ₁, σ₂)`-admissible** (with the loss `ε`) if it is slowly varying with the
rates `σ₁(1 - ε)` and `σ₂(1 - ε)`:
`2^{-σ₁(1-ε)(j-k)} c_j ≲ c_k ≲ 2^{σ₂(1-ε)(j-k)} c_j` for `j > k`. -/
def IsAdmissibleEnvelope (σ₁ σ₂ ε : ℝ) (c : ℤ → ℝ) : Prop :=
  IsSlowlyVarying (σ₁ * (1 - ε)) (σ₂ * (1 - ε)) c

/-- The weighted lower sum `∑_{j < k} 2^{r(j-k)} d_j`. It is `0` when the series does not
converge. -/
def dyadicLowSum (r : ℝ) (d : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑' j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * d j

/-- The weighted lower supremum `sup_{j < k} 2^{r(j-k)} c_j`; the sequence `c^{[σ]}` of Oh–Tataru
is `dyadicLowSup ((1 - ε) * σ) c`. It is `0` when the family is not bounded above. -/
def dyadicLowSup (r : ℝ) (c : ℤ → ℝ) (k : ℤ) : ℝ :=
  ⨆ j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * c j

/-- `d` is **`σ`-compatible** with `c` (with the loss `ε`) if the sums
`∑_{j < k} 2^{σ(1-ε)(j-k)} d_j` converge and `c_k ∑_{j < k} 2^{σ(1-ε)(j-k)} d_j ≲ d_k`. -/
def IsFrequencyCompatible (σ ε : ℝ) (c d : ℤ → ℝ) : Prop :=
  (∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (σ * (1 - ε) * ((j : ℤ) - k : ℝ)) * d (j : ℤ)) ∧
    ∃ C : ℝ, ∀ k, c k * dyadicLowSum (σ * (1 - ε)) d k ≤ C * d k

theorem isSlowlyVarying_iff {σ₁ σ₂ : ℝ} {c : ℤ → ℝ} :
    IsSlowlyVarying σ₁ σ₂ c ↔ ∃ C : ℝ, ∀ k j : ℤ, k < j →
      (2 : ℝ) ^ (-σ₁ * (j - k : ℝ)) * c j ≤ C * c k ∧
        c k ≤ C * (2 : ℝ) ^ (σ₂ * (j - k : ℝ)) * c j :=
  Iff.rfl

theorem isAdmissibleEnvelope_iff {σ₁ σ₂ ε : ℝ} {c : ℤ → ℝ} :
    IsAdmissibleEnvelope σ₁ σ₂ ε c ↔ IsSlowlyVarying (σ₁ * (1 - ε)) (σ₂ * (1 - ε)) c :=
  Iff.rfl

theorem dyadicLowSum_def (r : ℝ) (d : ℤ → ℝ) (k : ℤ) :
    dyadicLowSum r d k = ∑' j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * d j :=
  (rfl)

theorem dyadicLowSup_def (r : ℝ) (c : ℤ → ℝ) (k : ℤ) :
    dyadicLowSup r c k = ⨆ j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * c j :=
  (rfl)

theorem isFrequencyCompatible_iff {σ ε : ℝ} {c d : ℤ → ℝ} :
    IsFrequencyCompatible σ ε c d ↔
      (∀ k : ℤ, Summable fun j : Set.Iio k ↦
        (2 : ℝ) ^ (σ * (1 - ε) * ((j : ℤ) - k : ℝ)) * d (j : ℤ)) ∧
      ∃ C : ℝ, ∀ k, c k * dyadicLowSum (σ * (1 - ε)) d k ≤ C * d k :=
  Iff.rfl

/-- The lower sums of a sequence compatible with `c` converge. -/
theorem IsFrequencyCompatible.summable {σ ε : ℝ} {c d : ℤ → ℝ} (h : IsFrequencyCompatible σ ε c d)
    (k : ℤ) :
    Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (σ * (1 - ε) * ((j : ℤ) - k : ℝ)) * d (j : ℤ) :=
  h.1 k

/-- The compatibility bound `c_k ∑_{j < k} 2^{σ(1-ε)(j-k)} d_j ≤ C d_k`. -/
theorem IsFrequencyCompatible.exists_le {σ ε : ℝ} {c d : ℤ → ℝ}
    (h : IsFrequencyCompatible σ ε c d) :
    ∃ C : ℝ, ∀ k, c k * dyadicLowSum (σ * (1 - ε)) d k ≤ C * d k :=
  h.2

/-! ### Slow variation -/

/-- Slow variation with smaller rates implies slow variation with larger ones, for nonnegative
sequences. -/
theorem IsSlowlyVarying.mono {σ₁ σ₂ τ₁ τ₂ : ℝ} {c : ℤ → ℝ} (h : IsSlowlyVarying σ₁ σ₂ c)
    (hc : 0 ≤ c) (h₁ : σ₁ ≤ τ₁) (h₂ : σ₂ ≤ τ₂) : IsSlowlyVarying τ₁ τ₂ c := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun k j hkj ↦ ?_⟩
  have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
  have hCk : C * c k ≤ max C 0 * c k := mul_le_mul_of_nonneg_right (le_max_left _ _) (hc k)
  have hCj : C * (2 : ℝ) ^ (σ₂ * (j - k : ℝ)) * c j ≤ max C 0 * 2 ^ (τ₂ * (j - k : ℝ)) * c j :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)) (by positivity)
      (le_max_right _ _)) (hc j)
  refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ (hc j)) ((hC k j hkj).1.trans hCk),
    (hC k j hkj).2.trans hCj⟩
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)

/-- A nonnegative sequence with `c_k ≤ 2^{r|k-k'|} c_{k'}` for all `k, k'` is slowly varying with
all rates `σ₁, σ₂ ≥ r`, with constant `1`. -/
theorem IsSlowlyVarying.of_le_two_rpow_mul_abs {r σ₁ σ₂ : ℝ} {c : ℤ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (h₁ : r ≤ σ₁) (h₂ : r ≤ σ₂) (h : ∀ k k' : ℤ, c k ≤ 2 ^ (r * |(k - k' : ℝ)|) * c k') :
    IsSlowlyVarying σ₁ σ₂ c := by
  refine ⟨1, fun k j hkj ↦ ?_⟩
  have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
  have hj := h j k
  have hk := h k j
  rw [abs_of_nonneg hjk] at hj
  rw [abs_sub_comm, abs_of_nonneg hjk] at hk
  refine ⟨?_, ?_⟩
  · calc (2 : ℝ) ^ (-σ₁ * (j - k : ℝ)) * c j
        ≤ 2 ^ (-σ₁ * (j - k : ℝ)) * (2 ^ (r * (j - k : ℝ)) * c k) :=
          mul_le_mul_of_nonneg_left hj (by positivity)
      _ = 2 ^ ((r - σ₁) * (j - k : ℝ)) * c k := by
          rw [← mul_assoc, ← Real.rpow_add two_pos]
          ring_nf
      _ ≤ 1 * c k :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hjk)) (hc k)
  · rw [one_mul]
    exact hk.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)) (hc j))

/-! ### Weighted lower sums and suprema -/

/-- The lower sum as a sum over `ℤ` of the terms with `j < k`. -/
theorem dyadicLowSum_eq_tsum (r : ℝ) (d : ℤ → ℝ) (k : ℤ) :
    dyadicLowSum r d k = ∑' j, if j < k then (2 : ℝ) ^ (r * (j - k : ℝ)) * d j else 0 := by
  rw [dyadicLowSum, tsum_subtype (Set.Iio k) fun j : ℤ ↦ (2 : ℝ) ^ (r * (j - k : ℝ)) * d j]
  simp only [Set.indicator_apply, Set.mem_Iio]

/-- The lower sum converges exactly when the sum over `ℤ` of the terms with `j < k` does. -/
theorem summable_dyadicLowSum_iff {r : ℝ} {d : ℤ → ℝ} {k : ℤ} :
    (Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * d (j : ℤ)) ↔
      Summable fun j ↦ if j < k then (2 : ℝ) ^ (r * (j - k : ℝ)) * d j else 0 := by
  have h : (fun j : ℤ ↦ if j < k then (2 : ℝ) ^ (r * (j - k : ℝ)) * d j else 0) =
      (Set.Iio k).indicator fun j : ℤ ↦ (2 : ℝ) ^ (r * (j - k : ℝ)) * d j := by
    funext j
    simp only [Set.indicator_apply, Set.mem_Iio]
  rw [h]
  exact summable_subtype_iff_indicator (f := fun j : ℤ ↦ (2 : ℝ) ^ (r * (j - k : ℝ)) * d j)

/-- The lower sum of a nonnegative sequence is nonnegative. -/
theorem dyadicLowSum_nonneg {r : ℝ} {d : ℤ → ℝ} (hd : ∀ k, 0 ≤ d k) (k : ℤ) :
    0 ≤ dyadicLowSum r d k :=
  tsum_nonneg fun j ↦ mul_nonneg (by positivity) (hd j)

/-- Every weighted term `2^{r(j-k)} c_j`, `j < k`, is at most `dyadicLowSup r c k`, when these
terms are bounded above. -/
theorem le_dyadicLowSup {r : ℝ} {c : ℤ → ℝ} {k j : ℤ}
    (h : BddAbove (Set.range fun j : Set.Iio k ↦ (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * c j))
    (hj : j < k) : (2 : ℝ) ^ (r * (j - k : ℝ)) * c j ≤ dyadicLowSup r c k :=
  le_ciSup h (⟨j, hj⟩ : Set.Iio k)

/-- A common bound for the weighted terms `2^{r(j-k)} c_j`, `j < k`, bounds
`dyadicLowSup r c k`. -/
theorem dyadicLowSup_le {r M : ℝ} {c : ℤ → ℝ} {k : ℤ}
    (h : ∀ j < k, (2 : ℝ) ^ (r * (j - k : ℝ)) * c j ≤ M) : dyadicLowSup r c k ≤ M :=
  have : Nonempty (Set.Iio k) := ⟨⟨k - 1, by simp⟩⟩
  ciSup_le fun j ↦ h j j.property

/-! ### Compatibility: Lemma 3.5 -/

/-- The `d` part of Lemma 3.5: `∑_{j ∈ F, j < k} 2^{s(j-k)} d_j ≤ ∑_{j < k} 2^{t(j-k)} d_j` for
`t ≤ s`. -/
private theorem sum_ite_two_rpow_mul_le {d : ℤ → ℝ} {s t : ℝ} (hd : ∀ k, 0 ≤ d k) (hts : t ≤ s)
    {k : ℤ} (hsum : Summable fun j ↦ if j < k then (2 : ℝ) ^ (t * (j - k : ℝ)) * d j else 0)
    (F : Finset ℤ) :
    ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * d j else 0) ≤ dyadicLowSum t d k := by
  rw [dyadicLowSum_eq_tsum]
  refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) (Summable.sum_le_tsum F (fun j _ ↦ by
    split_ifs
    exacts [mul_nonneg (by positivity) (hd j), le_rfl]) hsum)
  split_ifs with hjk
  · refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (hd j)
    have : (j - k : ℝ) < 0 := sub_neg.2 (by exact_mod_cast hjk)
    nlinarith
  · rfl

/-- The `c L` part of Lemma 3.5: for `t < s`,
`∑_{j ∈ F, j < k} 2^{s(j-k)} L_j ≤ (2^{s-t} - 1)⁻¹ L_k`, where `L_j = ∑_{i < j} 2^{t(i-j)} d_i`. -/
private theorem sum_ite_two_rpow_mul_dyadicLowSum_le {d : ℤ → ℝ} {s t : ℝ}
    (hd : ∀ k, 0 ≤ d k) (hts : t < s)
    (hsum : ∀ k : ℤ, Summable fun j : ℤ ↦ if j < k then (2 : ℝ) ^ (t * (j - k : ℝ)) * d j else 0)
    (k : ℤ) (F : Finset ℤ) :
    ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * dyadicLowSum t d j else 0) ≤
      1 / (2 ^ (s - t) - 1) * dyadicLowSum t d k := by
  set g : ℤ → ℤ → ℝ := fun j i ↦ if i < j then (2 : ℝ) ^ (t * (i - j : ℝ)) * d i else 0
  have hg : ∀ j, Summable fun i ↦ if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * g j i else 0 :=
    fun j ↦ by
      split_ifs
      · exact (hsum j).mul_left _
      · exact summable_zero
  have hrw : ∀ j, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * dyadicLowSum t d j else 0) =
      ∑' i, if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * g j i else 0 := by
    intro j
    split_ifs
    · rw [dyadicLowSum_eq_tsum, ← tsum_mul_left]
    · simp
  simp_rw [hrw]
  rw [← Summable.tsum_finsetSum fun j _ ↦ hg j, dyadicLowSum_eq_tsum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i ↦ ?_) (summable_sum fun j _ ↦ hg j)
    ((hsum k).mul_left _)
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    calc ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * g j i else 0)
        ≤ ∑ j ∈ F, (if j < k then (2 : ℝ) ^ ((s - t) * (j - k : ℝ)) else 0) *
            ((2 : ℝ) ^ (t * (i - k : ℝ)) * d i) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          simp only [g]
          split_ifs with hjk hij
          · rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
            exact le_of_eq (by congr 2; ring)
          · simp only [mul_zero]
            exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hd i))
          · simp
      _ ≤ 1 / (2 ^ (s - t) - 1) * ((2 : ℝ) ^ (t * (i - k : ℝ)) * d i) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (sum_ite_two_rpow_le (by linarith) F k)
            (mul_nonneg (by positivity) (hd i))
  · simp only [hik, ↓reduceIte, mul_zero]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).le
    simp only [g]
    split_ifs with hjk hij
    · exact absurd (hij.trans hjk) hik
    · rw [mul_zero]
    · rfl

/-- The partial sums in Lemma 3.5: for `0 ≤ c ≤ M`, `0 ≤ d` and `t < s`, the finite sums of
`2^{s(j-k)} e_j`, `j < k`, are at most `(1 + M / (2^{s-t} - 1)) L_k`, where
`e = d + c L` and `L_j = ∑_{i < j} 2^{t(i-j)} d_i`. -/
private theorem sum_ite_two_rpow_mul_add_mul_dyadicLowSum_le {c d : ℤ → ℝ} {M s t : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hts : t < s)
    (hsum : ∀ k : ℤ, Summable fun j : ℤ ↦ if j < k then (2 : ℝ) ^ (t * (j - k : ℝ)) * d j else 0)
    (k : ℤ) (F : Finset ℤ) :
    ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * (d + c * dyadicLowSum t d) j else 0) ≤
      (1 + M / (2 ^ (s - t) - 1)) * dyadicLowSum t d k := by
  set L := dyadicLowSum t d
  have hM : 0 ≤ M := (hc k).trans (hcM k)
  have hL : ∀ j, 0 ≤ L j := dyadicLowSum_nonneg hd
  calc ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * (d + c * L) j else 0)
      ≤ ∑ j ∈ F, ((if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * d j else 0) +
          M * (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * L j else 0)) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        simp only [Pi.add_apply, Pi.mul_apply]
        split_ifs
        · have := mul_le_mul_of_nonneg_right (hcM j) (hL j)
          have h2 : 0 ≤ (2 : ℝ) ^ (s * (j - k : ℝ)) := by positivity
          nlinarith
        · simp
    _ = ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * d j else 0) +
          M * ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * L j else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ L k + M * (1 / (2 ^ (s - t) - 1) * L k) :=
        add_le_add (sum_ite_two_rpow_mul_le hd hts.le (hsum k) F)
          (mul_le_mul_of_nonneg_left (sum_ite_two_rpow_mul_dyadicLowSum_le hd hts hsum k F) hM)
    _ = (1 + M / (2 ^ (s - t) - 1)) * L k := by ring

/-- The terms of `e = d + c L`, `L_j = ∑_{i < j} 2^{t(i-j)} d_i`, in a weighted lower sum with
rate `s`, are nonnegative for `0 ≤ c` and `0 ≤ d`. -/
private theorem ite_two_rpow_mul_add_mul_dyadicLowSum_nonneg {c d : ℤ → ℝ} {s t : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k) (k j : ℤ) :
    0 ≤ if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * (d + c * dyadicLowSum t d) j else 0 := by
  split_ifs
  · exact mul_nonneg (by positivity) (add_nonneg (hd j) (mul_nonneg (hc j)
      (dyadicLowSum_nonneg hd j)))
  · exact le_rfl

/-- In Lemma 3.5 the sums for `e`, `∑_{j < k} 2^{s(j-k)} e_j` with
`e_j = d_j + c_j ∑_{i < j} 2^{t(i-j)} d_i`, converge: let `0 ≤ c ≤ M`, `0 ≤ d`, `t < s`, and let the
sums `∑_{j < k} 2^{t(j-k)} d_j` converge. -/
theorem summable_dyadicLowSum_add_mul_dyadicLowSum {c d : ℤ → ℝ} {M s t : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hts : t < s)
    (hsum : ∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (t * ((j : ℤ) - k : ℝ)) * d (j : ℤ))
    (k : ℤ) :
    Summable fun j : Set.Iio k ↦
      (2 : ℝ) ^ (s * ((j : ℤ) - k : ℝ)) * (d + c * dyadicLowSum t d) (j : ℤ) :=
  summable_dyadicLowSum_iff.2 (summable_of_sum_le
    (ite_two_rpow_mul_add_mul_dyadicLowSum_nonneg hc hd k)
    (sum_ite_two_rpow_mul_add_mul_dyadicLowSum_le hc hcM hd hts
      (fun k ↦ summable_dyadicLowSum_iff.1 (hsum k)) k))

/-- **Lemma 3.5 of Oh–Tataru**, quantitative form. Let `0 ≤ c ≤ M`, `0 ≤ d`, `t < s`, and
let the sums `∑_{j < k} 2^{t(j-k)} d_j` converge. Then `e_k = d_k + c_k ∑_{j < k} 2^{t(j-k)} d_j`
satisfies `c_k ∑_{j < k} 2^{s(j-k)} e_j ≤ (1 + M / (2^{s-t} - 1)) e_k`, where these sums converge
by `TauCeti.summable_dyadicLowSum_add_mul_dyadicLowSum`. -/
theorem mul_dyadicLowSum_add_mul_dyadicLowSum_le {c d : ℤ → ℝ} {M s t : ℝ} (hc : ∀ k, 0 ≤ c k)
    (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hts : t < s)
    (hsum : ∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (t * ((j : ℤ) - k : ℝ)) * d (j : ℤ))
    (k : ℤ) :
    c k * dyadicLowSum s (d + c * dyadicLowSum t d) k ≤
      (1 + M / (2 ^ (s - t) - 1)) * (d + c * dyadicLowSum t d) k := by
  have hG : 0 ≤ M / (2 ^ (s - t) - 1) := by
    have : (1 : ℝ) < 2 ^ (s - t) := Real.one_lt_rpow one_lt_two (by linarith)
    exact div_nonneg ((hc k).trans (hcM k)) (by linarith)
  have h : dyadicLowSum s (d + c * dyadicLowSum t d) k ≤
      (1 + M / (2 ^ (s - t) - 1)) * dyadicLowSum t d k := by
    rw [dyadicLowSum_eq_tsum]
    exact Real.tsum_le_of_sum_le (ite_two_rpow_mul_add_mul_dyadicLowSum_nonneg hc hd k)
      (sum_ite_two_rpow_mul_add_mul_dyadicLowSum_le hc hcM hd hts
        (fun k ↦ summable_dyadicLowSum_iff.1 (hsum k)) k)
  refine (mul_le_mul_of_nonneg_left h (hc k)).trans ?_
  simp only [Pi.add_apply, Pi.mul_apply]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + M / (2 ^ (s - t) - 1)) (hd k)]

/-- **Lemma 3.5 of Oh–Tataru.** If `0 ≤ c ≤ M`, `0 ≤ d`, `σ' < σ(1 - ε)` and the sums
`∑_{j < k} 2^{σ'(j-k)} d_j` converge, then `e_k = d_k + c_k ∑_{j < k} 2^{σ'(j-k)} d_j` is
`σ`-compatible with `c`. -/
theorem isFrequencyCompatible_add_mul_dyadicLowSum {c d : ℤ → ℝ} {M σ ε σ' : ℝ} (hc : ∀ k, 0 ≤ c k)
    (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hσ' : σ' < σ * (1 - ε))
    (hsum : ∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (σ' * ((j : ℤ) - k : ℝ)) * d (j : ℤ)) :
    IsFrequencyCompatible σ ε c (d + c * dyadicLowSum σ' d) :=
  ⟨summable_dyadicLowSum_add_mul_dyadicLowSum hc hcM hd hσ' hsum,
    _, mul_dyadicLowSum_add_mul_dyadicLowSum_le hc hcM hd hσ' hsum⟩

/-! ### The envelope of a square-summable sequence -/

/-- The frequency envelope of `a` with rate `r`: `c_k = (∑_j 2^{-2r|j-k|} a_j²)^{1/2}`. For
`r > 0` and `a ∈ ℓ²` it majorizes `a`, satisfies `c_k ≤ 2^{r|k-k'|} c_{k'}`, and
`‖c‖_{ℓ²}² = (∑_m 2^{-2r|m|}) ‖a‖_{ℓ²}²`. -/
def frequencyEnvelopeOf (r : ℝ) (a : ℤ → ℝ) (k : ℤ) : ℝ :=
  √(∑' j : ℤ, (2 : ℝ) ^ (-(2 * r) * |(j - k : ℝ)|) * a j ^ 2)

theorem frequencyEnvelopeOf_def (r : ℝ) (a : ℤ → ℝ) (k : ℤ) :
    frequencyEnvelopeOf r a k = √(∑' j : ℤ, (2 : ℝ) ^ (-(2 * r) * |(j - k : ℝ)|) * a j ^ 2) :=
  (rfl)

/-- The envelope is nonnegative. -/
theorem frequencyEnvelopeOf_nonneg (r : ℝ) (a : ℤ → ℝ) (k : ℤ) : 0 ≤ frequencyEnvelopeOf r a k :=
  Real.sqrt_nonneg _

/-- The square of the envelope: `c_k² = ∑_j 2^{-2r|j-k|} a_j²`. -/
theorem sq_frequencyEnvelopeOf (r : ℝ) (a : ℤ → ℝ) (k : ℤ) :
    frequencyEnvelopeOf r a k ^ 2 = ∑' j : ℤ, (2 : ℝ) ^ (-(2 * r) * |(j - k : ℝ)|) * a j ^ 2 :=
  Real.sq_sqrt (tsum_nonneg fun j ↦ mul_nonneg (by positivity) (sq_nonneg _))

private theorem two_rpow_neg_mul_abs_le_one {r x : ℝ} (hr : 0 ≤ r) :
    (2 : ℝ) ^ (-r * |x|) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg x))

private theorem summable_weight_mul_sq {r : ℝ} (hr : 0 ≤ r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) (k : ℤ) :
    Summable fun j : ℤ ↦ (2 : ℝ) ^ (-(2 * r) * |(j - k : ℝ)|) * a j ^ 2 :=
  ha.of_nonneg_of_le (fun j ↦ by positivity) fun j ↦
    mul_le_of_le_one_left (sq_nonneg _) (two_rpow_neg_mul_abs_le_one (by linarith))

/-- The envelope of a square-summable sequence majorizes it. -/
theorem le_frequencyEnvelopeOf {r : ℝ} (hr : 0 ≤ r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) (k : ℤ) : a k ≤ frequencyEnvelopeOf r a k := by
  refine (le_abs_self _).trans ?_
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ((le_of_eq ?_).trans
    ((summable_weight_mul_sq hr ha k).le_tsum k fun j _ ↦ by positivity))
  simp

/-- The envelope of `a` with rate `r ≥ 0` varies by at most `2^{r|k-k'|}`. -/
theorem frequencyEnvelopeOf_le {r : ℝ} (hr : 0 ≤ r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) (k k' : ℤ) :
    frequencyEnvelopeOf r a k ≤ 2 ^ (r * |(k - k' : ℝ)|) * frequencyEnvelopeOf r a k' := by
  have hsq : (2 : ℝ) ^ (2 * r * |(k - k' : ℝ)|) =
      ((2 : ℝ) ^ (r * |(k - k' : ℝ)|)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 1
    push_cast
    ring
  rw [frequencyEnvelopeOf, frequencyEnvelopeOf, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤
    2 ^ (r * |(k - k' : ℝ)|)), ← Real.sqrt_mul (by positivity), ← hsq, ← tsum_mul_left]
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun j ↦ ?_) (summable_weight_mul_sq hr ha k)
    ((summable_weight_mul_sq hr ha k').mul_left _))
  rw [← mul_assoc, ← Real.rpow_add two_pos]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    (sq_nonneg _)
  nlinarith [abs_sub_le (j : ℝ) k k', abs_nonneg ((j : ℝ) - k), abs_nonneg ((k : ℝ) - k')]

/-- The envelope of `a` with rate `r ≥ 0` is slowly varying with all rates `σ₁, σ₂ ≥ r`, with
constant `1`. -/
theorem isSlowlyVarying_frequencyEnvelopeOf {r σ₁ σ₂ : ℝ} (hr : 0 ≤ r) (h₁ : r ≤ σ₁)
    (h₂ : r ≤ σ₂) {a : ℤ → ℝ} (ha : Summable fun k ↦ a k ^ 2) :
    IsSlowlyVarying σ₁ σ₂ (frequencyEnvelopeOf r a) :=
  .of_le_two_rpow_mul_abs (frequencyEnvelopeOf_nonneg r a) h₁ h₂ (frequencyEnvelopeOf_le hr ha)

/-- The envelope of `a` is positive unless `a = 0`, in which case it is `0`. -/
theorem frequencyEnvelopeOf_pos_or_eq_zero {r : ℝ} (hr : 0 ≤ r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) :
    (∀ k, 0 < frequencyEnvelopeOf r a k) ∨ frequencyEnvelopeOf r a = 0 := by
  by_cases h : ∀ j, a j = 0
  · right
    funext k
    simp [frequencyEnvelopeOf, h]
  · left
    push Not at h
    obtain ⟨j, hj⟩ := h
    intro k
    refine Real.sqrt_pos.2 (lt_of_lt_of_le ?_
      ((summable_weight_mul_sq hr ha k).le_tsum j fun i _ ↦ by positivity))
    exact mul_pos (by positivity) (by positivity)

/-- `‖c‖_{ℓ²}² = (∑_m 2^{-2r|m|}) ‖a‖_{ℓ²}²` for the envelope `c` of `a` with rate `r > 0`. -/
theorem hasSum_sq_frequencyEnvelopeOf {r : ℝ} (hr : 0 < r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) :
    HasSum (fun k ↦ frequencyEnvelopeOf r a k ^ 2)
      ((∑' m : ℤ, (2 : ℝ) ^ (-(2 * r) * |(m : ℝ)|)) * ∑' k, a k ^ 2) := by
  set w : ℤ → ℝ := fun m ↦ (2 : ℝ) ^ (-(2 * r) * |(m : ℝ)|)
  have hw : Summable w := summable_two_rpow_neg_mul_abs (by linarith)
  have hw0 : ∀ m, 0 ≤ w m := fun m ↦ by positivity
  have hprod : Summable fun p : ℤ × ℤ ↦ w p.1 * a p.2 ^ 2 := by
    refine summable_mul_of_summable_norm (f := w) (g := fun j ↦ a j ^ 2) ?_ ?_
    · exact hw.congr fun m ↦ (Real.norm_of_nonneg (hw0 m)).symm
    · exact ha.congr fun j ↦ (Real.norm_of_nonneg (sq_nonneg _)).symm
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p ↦ (p.2 - p.1, p.2)
      invFun := fun p ↦ (p.2 - p.1, p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp }
  have hf : Summable (Function.uncurry fun k j : ℤ ↦ w (j - k) * a j ^ 2) :=
    (e.summable_iff (f := fun p : ℤ × ℤ ↦ w p.1 * a p.2 ^ 2)).2 hprod
  have hsq : ∀ k, frequencyEnvelopeOf r a k ^ 2 = ∑' j, w (j - k) * a j ^ 2 := fun k ↦ by
    simp only [sq_frequencyEnvelopeOf, w, Int.cast_sub]
  simp only [hsq]
  refine hf.prod.hasSum_iff.2 ?_
  simp only [Function.uncurry_apply_pair]
  rw [← hf.tsum_comm, ← tsum_mul_left]
  refine tsum_congr fun j ↦ ?_
  rw [tsum_mul_right]
  congr 1
  exact (Equiv.subLeft j).tsum_eq w

/-- **Existence of admissible envelopes in `ℓ²`.** For rates `δ > 0`, `σ₁(1 - ε) > 0` and
`σ₂(1 - ε) > 0` there is a constant `C` such that every square-summable `a` has a frequency envelope
`c` with rate `δ` that is `(-σ₁, σ₂)`-admissible and has `‖c‖_{ℓ²}² ≤ C ‖a‖_{ℓ²}²`. -/
theorem exists_isFrequencyEnvelope_of_summable_sq {δ σ₁ σ₂ ε : ℝ} (hδ : 0 < δ)
    (h₁ : 0 < σ₁ * (1 - ε)) (h₂ : 0 < σ₂ * (1 - ε)) :
    ∃ C, ∀ a : ℤ → ℝ, Summable (fun k ↦ a k ^ 2) → ∃ c, IsFrequencyEnvelope δ a c ∧
      IsAdmissibleEnvelope σ₁ σ₂ ε c ∧ Summable (fun k ↦ c k ^ 2) ∧
        ∑' k, c k ^ 2 ≤ C * ∑' k, a k ^ 2 := by
  set r := min δ (min (σ₁ * (1 - ε)) (σ₂ * (1 - ε)))
  have hr : 0 < r := lt_min hδ (lt_min h₁ h₂)
  refine ⟨∑' m : ℤ, (2 : ℝ) ^ (-(2 * r) * |(m : ℝ)|), fun a ha ↦
    ⟨frequencyEnvelopeOf r a, ⟨frequencyEnvelopeOf_pos_or_eq_zero hr.le ha,
      le_frequencyEnvelopeOf hr.le ha,
      isSlowlyVarying_frequencyEnvelopeOf hr.le (min_le_left _ _) (min_le_left _ _) ha⟩,
      isSlowlyVarying_frequencyEnvelopeOf hr.le ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_right _ _)) ha,
      (hasSum_sq_frequencyEnvelopeOf hr ha).summable,
      (hasSum_sq_frequencyEnvelopeOf hr ha).tsum_eq.le⟩⟩

/-! ### Checks -/

/-- Zero data admit the zero envelope, whose `ℓ²` norm is `0`. -/
theorem isFrequencyEnvelope_zero (δ : ℝ) : IsFrequencyEnvelope δ 0 0 :=
  ⟨Or.inr rfl, fun _ ↦ le_rfl, ⟨0, fun _ _ _ ↦ by simp⟩⟩

/-- **A single nonzero block.** If only the block `k₀` is nonzero, with size `b ≥ 0`, then
`c_k = 2^{-δ|k-k₀|} b` is a frequency envelope with rate `δ ≥ 0`. Every envelope `c` of these
block sizes has `c_{k₀} ≥ b`, by `TauCeti.IsFrequencyEnvelope.le`. -/
theorem isFrequencyEnvelope_single {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (k₀ : ℤ) :
    IsFrequencyEnvelope δ (Pi.single k₀ b) fun k ↦ (2 : ℝ) ^ (-δ * |(k - k₀ : ℝ)|) * b := by
  refine ⟨?_, fun k ↦ ?_, .of_le_two_rpow_mul_abs (fun k ↦ mul_nonneg (by positivity) hb)
    le_rfl le_rfl fun k k' ↦ ?_⟩
  · rcases hb.lt_or_eq with hb | rfl
    · exact Or.inl fun k ↦ by positivity
    · exact Or.inr (funext fun k ↦ by simp)
  · rcases eq_or_ne k k₀ with rfl | hk
    · simp
    · rw [Pi.single_eq_of_ne hk]
      positivity
  · rw [← mul_assoc, ← Real.rpow_add two_pos]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hb
    nlinarith [abs_sub_le (k' : ℝ) k k₀, abs_sub_comm (k : ℝ) k']

/-- The sequence `c_k = 2^k` for `k ≤ 0` and `c_k = 1` for `k > 0` grows at the rate `1 > 1 - ε`
to the right on `k ≤ 0`, so it is not `(-1, S)`-admissible for any `S`. -/
theorem not_isAdmissibleEnvelope_two_rpow {ε : ℝ} (hε : 0 < ε) (S : ℝ) :
    ¬ IsAdmissibleEnvelope 1 S ε fun k : ℤ ↦ if k ≤ 0 then (2 : ℝ) ^ (k : ℝ) else 1 := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (Real.one_lt_rpow one_lt_two hε)
  set n := m + 1
  have hn : C < ((2 : ℝ) ^ ε) ^ n :=
    hm.trans_le (pow_le_pow_right₀ (Real.one_lt_rpow one_lt_two hε).le (Nat.le_succ m))
  have h := (hC (-n) 0 (by omega)).1
  have hn0 : -(n : ℤ) ≤ 0 := by omega
  simp only [le_refl, ↓reduceIte, hn0, Int.cast_zero, Int.cast_neg, Int.cast_natCast,
    Real.rpow_zero, mul_one] at h
  have h2 : ((2 : ℝ) ^ ε) ^ n * 2 ^ (-(n : ℝ)) = 2 ^ (-(1 * (1 - ε)) * (0 - -(n : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    ring_nf
  have h3 : C * 2 ^ (-(n : ℝ)) < ((2 : ℝ) ^ ε) ^ n * 2 ^ (-(n : ℝ)) :=
    mul_lt_mul_of_pos_right hn (by positivity)
  linarith

/-- With `d_j = 1` and `σ' = 0`, the lower sum `∑_{j < 0} 2^{σ' j} d_j = ∑_{j < 0} 1` diverges, so
`TauCeti.isFrequencyCompatible_add_mul_dyadicLowSum` does not apply. -/
theorem not_summable_dyadicLowSum_one :
    ¬ Summable fun j : Set.Iio (0 : ℤ) ↦ (2 : ℝ) ^ (0 * ((j : ℤ) - 0 : ℝ)) * (1 : ℤ → ℝ) j := by
  have : Infinite (Set.Iio (0 : ℤ)) := (Set.Iio_infinite 0).to_subtype
  simp only [zero_mul, Real.rpow_zero, Pi.one_apply, mul_one]
  rw [summable_const_iff]
  exact one_ne_zero

end TauCeti
