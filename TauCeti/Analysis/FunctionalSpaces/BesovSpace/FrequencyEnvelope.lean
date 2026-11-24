/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Frequency envelopes

A frequency envelope for `u` records, at each dyadic frequency `2^k`, `k ∈ ℤ`, an upper bound
`c_k` for the size `a_k = ‖P_k u‖_X` of the Littlewood–Paley block of `u` in a translation-invariant
space `X`, chosen to vary slowly with `k`: `2^{-δ(j-k)} c_j ≲ c_k ≲ 2^{δ(j-k)} c_j` for `j > k`.
Everything here is a statement about real sequences indexed by `ℤ`, applied to the weighted block
sizes `a_k = 2^{kσ} ‖P_k u‖_{L²}` of an element `u` of the homogeneous space
`\dot H^σ = \dot B^σ_{2,2}`.

Following the definitions of the YangMillsConnectionsAndCaloricGauge roadmap, §8.1 (after
OhTataru-YMHF, Definitions 3.2–3.4 and Lemma 3.5, lines 884–954):

* `TauCeti.IsSlowlyVarying σ₁ σ₂ c`: `2^{-σ₁(j-k)} c_j ≲ c_k ≲ 2^{σ₂(j-k)} c_j` for `j > k`.
* `TauCeti.IsFrequencyEnvelope δ a c`: `c` is positive, or identically zero, majorizes `a`, and is
  slowly varying with both rates `δ`. The zero sequence is an envelope exactly of the `a ≤ 0`.
* `TauCeti.IsAdmissible σ₁ σ₂ ε c`: `c` is `(-σ₁, σ₂)`-admissible, that is slowly varying with the
  rates `σ₁(1 - ε)` and `σ₂(1 - ε)`.
* `TauCeti.dyadicLowSum r d k = ∑_{j < k} 2^{r(j-k)} d_j` and `TauCeti.dyadicLowSup r c k =
  sup_{j < k} 2^{r(j-k)} c_j`, so that the roadmap's `c^{[σ]}` is `dyadicLowSup ((1 - ε) σ) c`.
* `TauCeti.IsCompatible σ ε c d`: `d` is `σ`-compatible with `c`, that is
  `c_k ∑_{j < k} 2^{σ(1-ε)(j-k)} d_j ≲ d_k`.

## Main results

* `TauCeti.exists_isFrequencyEnvelope_of_summable_sq`: every square-summable sequence has a
  frequency envelope that is `(-σ₁, σ₂)`-admissible, with `‖c‖_{ℓ²} ≲ ‖a‖_{ℓ²}`, the constant
  depending only on the rates. The envelope is `TauCeti.frequencyEnvelopeOf r a`, with
  `c_k² = ∑_j 2^{-2r|j-k|} a_j²`.
* `TauCeti.HomogeneousBesovSpace.exists_isFrequencyEnvelope`: the same for the weighted block
  sizes `2^{kσ} ‖P_k u‖_{L²}` of every `u ∈ \dot H^σ`, with `‖c‖_{ℓ²} ≲ ‖u‖_{\dot H^σ}`.
* `TauCeti.mul_dyadicLowSum_add_mul_dyadicLowSum_le` and
  `TauCeti.isCompatible_add_mul_dyadicLowSum` (Lemma 3.5): if `0 ≤ c ≤ M`, `0 ≤ d`,
  `σ' < σ(1 - ε)` and the sums `∑_{j < k} 2^{σ'(j-k)} d_j` are finite, then
  `e_k = d_k + c_k ∑_{j < k} 2^{σ'(j-k)} d_j` is `σ`-compatible with `c`, with constant
  `1 + M / (2^{σ(1-ε) - σ'} - 1)`. No slow variation of `c` or `d` is needed.

The checks of the roadmap on sequences are `TauCeti.isFrequencyEnvelope_single` (a single
nonzero block), `TauCeti.not_isAdmissible_two_rpow` (a sequence growing too fast to be
admissible), `TauCeti.isFrequencyEnvelope_zero` (the zero envelope of zero data) and
`TauCeti.not_summable_dyadicLowSum_one` (a lower sum that is infinite).
-/

public section

noncomputable section

open scoped ENNReal


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

/-- A sequence is **`(-σ₁, σ₂)`-admissible** (with the loss `ε`) if it is slowly varying with the
rates `σ₁(1 - ε)` and `σ₂(1 - ε)`:
`2^{-σ₁(1-ε)(j-k)} c_j ≲ c_k ≲ 2^{σ₂(1-ε)(j-k)} c_j` for `j > k`. -/
def IsAdmissible (σ₁ σ₂ ε : ℝ) (c : ℤ → ℝ) : Prop :=
  IsSlowlyVarying (σ₁ * (1 - ε)) (σ₂ * (1 - ε)) c

/-- The weighted lower sum `∑_{j < k} 2^{r(j-k)} d_j`. It is `0` when the series does not
converge. -/
def dyadicLowSum (r : ℝ) (d : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑' j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * d j

/-- The weighted lower supremum `sup_{j < k} 2^{r(j-k)} c_j`; the sequence `c^{[σ]}` of the roadmap
is `dyadicLowSup ((1 - ε) * σ) c`. It is `0` when the family is not bounded above. -/
def dyadicLowSup (r : ℝ) (c : ℤ → ℝ) (k : ℤ) : ℝ :=
  ⨆ j : Set.Iio k, (2 : ℝ) ^ (r * ((j : ℤ) - k : ℝ)) * c j

/-- `d` is **`σ`-compatible** with `c` (with the loss `ε`) if
`c_k ∑_{j < k} 2^{σ(1-ε)(j-k)} d_j ≲ d_k`. -/
def IsCompatible (σ ε : ℝ) (c d : ℤ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ k, c k * dyadicLowSum (σ * (1 - ε)) d k ≤ C * d k

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

/-- `∑_{j ∈ F, j < k} 2^{u(j-k)} ≤ 1 / (2^u - 1)` for every finite set `F` and `u > 0`. -/
private theorem sum_ite_two_rpow_le {u : ℝ} (hu : 0 < u) (F : Finset ℤ) (k : ℤ) :
    ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (u * (j - k : ℝ)) else 0) ≤ 1 / (2 ^ u - 1) := by
  set q : ℝ := (2 : ℝ) ^ (-u)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have key : ∀ j ∈ F.filter (· < k), (2 : ℝ) ^ (u * (j - k : ℝ)) = q * q ^ (k - j - 1).toNat := by
    intro j hj
    have hjk : j < k := (Finset.mem_filter.1 hj).2
    have hcast : (((k - j - 1).toNat : ℕ) : ℝ) = k - j - 1 := by
      have : ((k - j - 1).toNat : ℤ) = k - j - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [← Real.rpow_natCast, hcast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    congr 1
    ring
  rw [← Finset.sum_filter, Finset.sum_congr rfl key, ← Finset.mul_sum,
    ← Finset.sum_image (g := fun j : ℤ ↦ (k - j - 1).toNat) (f := fun n : ℕ ↦ q ^ n)]
  · calc q * ∑ n ∈ (F.filter (· < k)).image fun j : ℤ ↦ (k - j - 1).toNat, q ^ n
        ≤ q * ∑' n : ℕ, q ^ n :=
          mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
            (summable_geometric_of_lt_one hq0 hq1)) hq0
      _ = 1 / (2 ^ u - 1) := by
          have h2 : (1 : ℝ) < 2 ^ u := Real.one_lt_rpow one_lt_two hu
          rw [tsum_geometric_of_lt_one hq0 hq1, show q = (2 ^ u)⁻¹ from Real.rpow_neg zero_le_two u]
          field_simp
  · intro x hx y hy hxy
    have := (Finset.mem_filter.1 hx).2
    have := (Finset.mem_filter.1 hy).2
    simp only at hxy
    omega

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
    split_ifs with hjk hij <;> first | rfl | (exfalso; omega) | simp

/-- **Lemma 3.5 of OhTataru-YMHF**, quantitative form. Let `0 ≤ c ≤ M`, `0 ≤ d`, `t < s`, and
let the sums `∑_{j < k} 2^{t(j-k)} d_j` converge. Then `e_k = d_k + c_k ∑_{j < k} 2^{t(j-k)} d_j`
satisfies `c_k ∑_{j < k} 2^{s(j-k)} e_j ≤ (1 + M / (2^{s-t} - 1)) e_k`. -/
theorem mul_dyadicLowSum_add_mul_dyadicLowSum_le {c d : ℤ → ℝ} {M s t : ℝ} (hc : ∀ k, 0 ≤ c k)
    (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hts : t < s)
    (hsum : ∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (t * ((j : ℤ) - k : ℝ)) * d (j : ℤ))
    (k : ℤ) :
    c k * dyadicLowSum s (d + c * dyadicLowSum t d) k ≤
      (1 + M / (2 ^ (s - t) - 1)) * (d + c * dyadicLowSum t d) k := by
  set L := dyadicLowSum t d
  set G : ℝ := 1 / (2 ^ (s - t) - 1)
  have hG : 0 ≤ G := by
    have : (1 : ℝ) < 2 ^ (s - t) := Real.one_lt_rpow one_lt_two (by linarith)
    exact div_nonneg zero_le_one (by linarith)
  have hM : 0 ≤ M := (hc k).trans (hcM k)
  have hL : 0 ≤ L := fun j ↦ dyadicLowSum_nonneg hd j
  have hsum' := fun k ↦ summable_dyadicLowSum_iff.1 (hsum k)
  suffices h : c k * dyadicLowSum s (d + c * L) k ≤ (1 + M * G) * (c k * L k) by
    rw [← mul_one_div M]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    simp only [Pi.add_apply, Pi.mul_apply]
    linarith [hd k]
  rw [dyadicLowSum_eq_tsum, ← tsum_mul_left]
  refine Real.tsum_le_of_sum_le (fun j ↦ ?_) fun F ↦ ?_
  · dsimp only
    split_ifs
    · exact mul_nonneg (hc k) (mul_nonneg (by positivity)
        (add_nonneg (hd j) (mul_nonneg (hc j) (hL j))))
    · simp
  calc ∑ j ∈ F, c k * (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * (d + c * L) j else 0)
      ≤ ∑ j ∈ F, (c k * (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * d j else 0) +
          c k * M * (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * L j else 0)) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        simp only [Pi.add_apply, Pi.mul_apply]
        split_ifs
        · have := mul_le_mul_of_nonneg_right (hcM j) (hL j)
          have h2 : 0 ≤ c k * (2 : ℝ) ^ (s * (j - k : ℝ)) := mul_nonneg (hc k) (by positivity)
          nlinarith
        · simp
    _ = c k * ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * d j else 0) +
          c k * M * ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (s * (j - k : ℝ)) * L j else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c k * L k + c k * M * (G * L k) :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_ite_two_rpow_mul_le hd hts.le (hsum' k) F)
          (hc k)) (mul_le_mul_of_nonneg_left
            (sum_ite_two_rpow_mul_dyadicLowSum_le hd hts hsum' k F) (mul_nonneg (hc k) hM))
    _ = (1 + M * G) * (c k * L k) := by ring

/-- **Lemma 3.5 of OhTataru-YMHF.** If `0 ≤ c ≤ M`, `0 ≤ d`, `σ' < σ(1 - ε)` and the sums
`∑_{j < k} 2^{σ'(j-k)} d_j` converge, then `e_k = d_k + c_k ∑_{j < k} 2^{σ'(j-k)} d_j` is
`σ`-compatible with `c`. -/
theorem isCompatible_add_mul_dyadicLowSum {c d : ℤ → ℝ} {M σ ε σ' : ℝ} (hc : ∀ k, 0 ≤ c k)
    (hcM : ∀ k, c k ≤ M) (hd : ∀ k, 0 ≤ d k) (hσ' : σ' < σ * (1 - ε))
    (hsum : ∀ k : ℤ, Summable fun j : Set.Iio k ↦ (2 : ℝ) ^ (σ' * ((j : ℤ) - k : ℝ)) * d (j : ℤ)) :
    IsCompatible σ ε c (d + c * dyadicLowSum σ' d) :=
  ⟨_, mul_dyadicLowSum_add_mul_dyadicLowSum_le hc hcM hd hσ' hsum⟩

/-! ### The envelope of a square-summable sequence -/

/-- The frequency envelope of `a` with rate `r`: `c_k = (∑_j 2^{-2r|j-k|} a_j²)^{1/2}`. For
`r > 0` and `a ∈ ℓ²` it majorizes `a`, satisfies `c_k ≤ 2^{r|k-k'|} c_{k'}`, and
`‖c‖_{ℓ²}² = (∑_m 2^{-2r|m|}) ‖a‖_{ℓ²}²`. -/
def frequencyEnvelopeOf (r : ℝ) (a : ℤ → ℝ) (k : ℤ) : ℝ :=
  √(∑' j, (2 : ℝ) ^ (-(2 * r) * |((j - k : ℤ) : ℝ)|) * a j ^ 2)

private theorem two_rpow_neg_mul_abs_le_one {r x : ℝ} (hr : 0 ≤ r) :
    (2 : ℝ) ^ (-r * |x|) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg x))

private theorem summable_weight_mul_sq {r : ℝ} (hr : 0 ≤ r) {a : ℤ → ℝ}
    (ha : Summable fun k ↦ a k ^ 2) (k : ℤ) :
    Summable fun j ↦ (2 : ℝ) ^ (-(2 * r) * |((j - k : ℤ) : ℝ)|) * a j ^ 2 :=
  ha.of_nonneg_of_le (fun j ↦ by positivity) fun j ↦
    mul_le_of_le_one_left (sq_nonneg _) (two_rpow_neg_mul_abs_le_one (by linarith))

/-- `m ↦ 2^{-r|m|}` is summable over `ℤ` for `r > 0`: it is the bilateral geometric series of ratio
`2^{-r}`. -/
private theorem summable_two_rpow_neg_mul_abs {r : ℝ} (hr : 0 < r) :
    Summable fun m : ℤ ↦ (2 : ℝ) ^ (-r * |(m : ℝ)|) := by
  refine (summable_pow_natAbs (r := (2 : ℝ) ^ (-r)) (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))).congr fun m ↦ ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs]

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
    frequencyEnvelopeOf r a k ≤ 2 ^ (r * |((k - k' : ℤ) : ℝ)|) * frequencyEnvelopeOf r a k' := by
  have hsq : (2 : ℝ) ^ (2 * r * |((k - k' : ℤ) : ℝ)|) =
      ((2 : ℝ) ^ (r * |((k - k' : ℤ) : ℝ)|)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 1
    push_cast
    ring
  rw [frequencyEnvelopeOf, frequencyEnvelopeOf, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤
    2 ^ (r * |((k - k' : ℤ) : ℝ)|)), ← Real.sqrt_mul (by positivity), ← hsq, ← tsum_mul_left]
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun j ↦ ?_) (summable_weight_mul_sq hr ha k)
    ((summable_weight_mul_sq hr ha k').mul_left _))
  rw [← mul_assoc, ← Real.rpow_add two_pos]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    (sq_nonneg _)
  push_cast
  nlinarith [abs_sub_le (j : ℝ) k k', abs_nonneg ((j : ℝ) - k), abs_nonneg ((k : ℝ) - k')]

/-- The envelope of `a` with rate `r ≥ 0` is slowly varying with all rates `σ₁, σ₂ ≥ r`, with
constant `1`. -/
theorem isSlowlyVarying_frequencyEnvelopeOf {r σ₁ σ₂ : ℝ} (hr : 0 ≤ r) (h₁ : r ≤ σ₁)
    (h₂ : r ≤ σ₂) {a : ℤ → ℝ} (ha : Summable fun k ↦ a k ^ 2) :
    IsSlowlyVarying σ₁ σ₂ (frequencyEnvelopeOf r a) := by
  refine ⟨1, fun k j hkj ↦ ⟨?_, ?_⟩⟩
  · have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
    have h := frequencyEnvelopeOf_le hr ha j k
    rw [Int.cast_sub, abs_of_nonneg hjk] at h
    calc (2 : ℝ) ^ (-σ₁ * (j - k : ℝ)) * frequencyEnvelopeOf r a j
        ≤ 2 ^ (-σ₁ * (j - k : ℝ)) * (2 ^ (r * (j - k : ℝ)) * frequencyEnvelopeOf r a k) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 ^ ((r - σ₁) * (j - k : ℝ)) * frequencyEnvelopeOf r a k := by
          rw [← mul_assoc, ← Real.rpow_add two_pos]
          ring_nf
      _ ≤ 1 * frequencyEnvelopeOf r a k :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hjk)) (Real.sqrt_nonneg _)
  · have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
    have h := frequencyEnvelopeOf_le hr ha k j
    rw [Int.cast_sub, abs_sub_comm, abs_of_nonneg hjk] at h
    rw [one_mul]
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)) (Real.sqrt_nonneg _))

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
  have hsq : ∀ k, frequencyEnvelopeOf r a k ^ 2 = ∑' j, w (j - k) * a j ^ 2 := fun k ↦
    Real.sq_sqrt (tsum_nonneg fun j ↦ mul_nonneg (hw0 _) (sq_nonneg _))
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
      IsAdmissible σ₁ σ₂ ε c ∧ Summable (fun k ↦ c k ^ 2) ∧
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
  refine ⟨?_, fun k ↦ ?_, ⟨1, fun k j hkj ↦ ⟨?_, ?_⟩⟩⟩
  · rcases hb.lt_or_eq with hb | rfl
    · exact Or.inl fun k ↦ by positivity
    · exact Or.inr (funext fun k ↦ by simp)
  · rcases eq_or_ne k k₀ with rfl | hk
    · simp
    · rw [Pi.single_eq_of_ne hk]
      positivity
  · have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
    rw [← mul_assoc, ← Real.rpow_add two_pos, one_mul]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hb
    nlinarith [abs_sub_le (k : ℝ) j k₀, abs_sub_comm (k : ℝ) j, abs_of_nonneg hjk]
  · have hjk : (0 : ℝ) ≤ j - k := sub_nonneg.2 (by exact_mod_cast hkj.le)
    rw [one_mul, ← mul_assoc, ← Real.rpow_add two_pos]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hb
    nlinarith [abs_sub_le (j : ℝ) k k₀, abs_sub_comm (j : ℝ) k, abs_of_nonneg hjk]

/-- The sequence `c_k = 2^k` for `k ≤ 0` and `c_k = 1` for `k > 0` grows at the rate `1 > 1 - ε`
to the right on `k ≤ 0`, so it is not `(-1, S)`-admissible for any `S`. -/
theorem not_isAdmissible_two_rpow {ε : ℝ} (hε : 0 < ε) (S : ℝ) :
    ¬ IsAdmissible 1 S ε fun k : ℤ ↦ if k ≤ 0 then (2 : ℝ) ^ (k : ℝ) else 1 := by
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
`TauCeti.isCompatible_add_mul_dyadicLowSum` does not apply. -/
theorem not_summable_dyadicLowSum_one :
    ¬ Summable fun j : Set.Iio (0 : ℤ) ↦ (2 : ℝ) ^ (0 * ((j : ℤ) - 0 : ℝ)) * (1 : ℤ → ℝ) j := by
  have : Infinite (Set.Iio (0 : ℤ)) := (Set.Iio_infinite 0).to_subtype
  simp only [zero_mul, Real.rpow_zero, Pi.one_apply, mul_one]
  rw [summable_const_iff]
  exact one_ne_zero

/-! ### Envelopes in `\dot H^σ` -/

section HomogeneousSobolev

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {s : ℝ}

/-- **Admissible envelopes in `\dot H^σ`.** For rates `δ > 0`, `σ₁(1 - ε) > 0` and
`σ₂(1 - ε) > 0` there is a constant `C` such that the weighted block sizes `2^{ks} ‖P_k u‖_{L²}`
of every `u ∈ \dot H^s = \dot B^s_{2,2}` have a frequency envelope `c` with rate `δ` that is
`(-σ₁, σ₂)`-admissible and has `‖c‖_{ℓ²}² ≤ C ‖u‖_{\dot H^s}²`. -/
theorem HomogeneousBesovSpace.exists_isFrequencyEnvelope {δ σ₁ σ₂ ε : ℝ} (hδ : 0 < δ)
    (h₁ : 0 < σ₁ * (1 - ε)) (h₂ : 0 < σ₂ * (1 - ε)) :
    ∃ C, ∀ u : HomogeneousBesovSpace F φ s 2 2, ∃ c,
      IsFrequencyEnvelope δ (fun k ↦ 2 ^ (s * k) * ‖u.block k‖) c ∧ IsAdmissible σ₁ σ₂ ε c ∧
        Summable (fun k ↦ c k ^ 2) ∧ ∑' k, c k ^ 2 ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_isFrequencyEnvelope_of_summable_sq hδ h₁ h₂
  refine ⟨C, fun u ↦ ?_⟩
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsq : ∀ k : ℤ, (2 : ℝ) ^ (s * k) * ‖u.block k‖ = ‖u.weightedBlocks k‖ := fun k ↦
    (u.norm_weightedBlocks_apply k).symm
  have hsum := (lp.memℓp u.weightedBlocks).summable h2
  have hnorm := lp.norm_rpow_eq_tsum h2 u.weightedBlocks
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedBlocks] at hsum hnorm
  simp only [hsq]
  rw [hnorm]
  exact hC _ hsum

end HomogeneousSobolev

end TauCeti
