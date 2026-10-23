/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import TauCeti.Algebra.Order.BigOperators.Fin
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.DeterminantIndex
public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.NumberTheory.Height.Polynomial.RootMultiplicity
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.DegreeBound
public import TauCeti.RingTheory.MvPolynomial.SeparateVariable

/-!
# Roth's lemma

**Roth's lemma** bounds the index of a polynomial of small height at a point of large height.
Let `P ≠ 0` be a polynomial in `n ≥ 1` variables over a number field `K`, with partial degrees
`deg_{Xᵢ} P ≤ rᵢ`, where the weights `rᵢ > 0` decrease quickly: `rᵢ₊₁ ≤ σ rᵢ` with
`0 < σ ≤ 1 / 2`. If every coordinate of `β ∈ Kⁿ` has relative logarithmic height
`rᵢ h(βᵢ) ≥ σ⁻¹ (h(P) + 4 n r₀ [K : ℚ])`, then the weighted index of `P` at `β` satisfies

`Ind_{β, r}(P) ≤ 2 n σ ^ (1 / 2 ^ (n - 1))`.

In the proof of Roth's theorem this is the upper bound for the index of the auxiliary polynomial
at a point of good rational approximations; it contradicts the large index of the auxiliary
polynomial on the diagonal.

The proof is by induction on `n`. In one variable it is
`MvPolynomial.weightedIndex_toMvPolynomial_le`. For `n + 1` variables, separate the last
variable, which has the smallest weight: `P = ∑_{k < m} fₖ gₖ(Xₙ)` with linearly independent
families `fₖ` and `gₖ` (`MvPolynomial.exists_sum_mul_linearIndependent`). The determinant of
the Hasse derivatives `∂^(μ k + l eₙ) P` is the product of a nonzero generalized Wronskian
`W_μ(f)` and the Hasse Wronskian of the `gₖ`, placed in `Xₙ`. Its height is bounded by
`MvPolynomial.logHeight_det_hasseDeriv_le`, so the induction hypothesis bounds the index of
`W_μ(f)` and the one-variable case bounds the index of the Hasse Wronskian. On the other hand,
`TauCeti.ofReal_mul_min_le_weightedIndex_genWronskian_add` bounds the sum of these indices from
below in terms of `Ind_{β, r}(P)`; the two bounds are incompatible with a large index of `P`.

## Main results

* `TauCeti.weightedIndex_le_of_logHeight_le`: Roth's lemma.

## Implementation notes

The induction is carried out with the parameter `θ = σ ^ (1 / 2 ^ (n - 1))`, so that
`σ = θ ^ 2 ^ (n - 1)`. Passing from `n + 1` to `n` variables replaces `θ` by `θ ^ 2` and keeps
`σ`, and no real powers occur inside the induction. If `θ ≥ 1 / 2`, the statement holds because
the index is at most the number of variables; so the inductive step may assume `θ < 1 / 2`.

Heights are relative: `h(P)` is `MvPolynomial.logHeight` and `h(βᵢ)` is `Height.logHeight₁`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.4, Theorem 3.4.1 and its proof.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Lemma 6.3.7.
* The induction in the parameter `θ` and the reduction to `θ < 1 / 2` follow
  `DiophantineApproximation/RothLemma.lean` in Ralf Stephan's `rwst/Subspace-Theorems`, snapshot
  `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

namespace TauCeti

open Finset Height Module MvPolynomial
open scoped ENNReal Nat

variable {K : Type*} [Field K] [NumberField K]

/-- The height of a determinant of Hasse derivatives in the form used by Roth's lemma: if the
weights `r` sum to at most `2 r₀` and `m ≤ r₀ + 1`, the height of an `m × m` determinant of
Hasse derivatives of `P` is at most `m (h(P) + 4 r₀ [K : ℚ])`. -/
private theorem logHeight_det_hasseDeriv_le_mul {n m : ℕ} {r : Fin (n + 1) → ℕ}
    {P : MvPolynomial (Fin (n + 1)) K} (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ r j)
    (hsum : ∑ j, (r j : ℝ) ≤ 2 * r 0) (hm : m ≤ r 0 + 1) (E : Fin m → Fin m → Fin (n + 1) →₀ ℕ) :
    (Matrix.of fun k l ↦ hasseDeriv (E k l) P).det.logHeight ≤
      m * (P.logHeight + 4 * r 0 * finrank ℚ K) := by
  have h := logHeight_det_hasseDeriv_le hP hdeg E
  rw [Fintype.card_fin, NumberField.totalWeight_eq_finrank, ← sum_mul] at h
  have hD : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
  have hm' : (m : ℝ) ≤ r 0 + 1 := by exact_mod_cast hm
  -- `log m! ≤ m log m ≤ m (m - 1) ≤ m r₀`.
  have hfact : Real.log (m ! : ℝ) ≤ m * r 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    calc Real.log (m ! : ℝ) ≤ Real.log ((m ^ m : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast m.factorial_pos)
            (by exact_mod_cast Nat.factorial_le_pow m)
      _ = m * Real.log m := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ m * r 0 := by
          gcongr
          linarith [Real.log_le_sub_one_of_pos hm0']
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r 0 := Nat.cast_nonneg _
  have hkey : Real.log (m ! : ℝ) + 2 * m * ((∑ j, (r j : ℝ)) * Real.log 2) ≤ 4 * m * r 0 := by
    have h1 : 2 * m * ((∑ j, (r j : ℝ)) * Real.log 2) ≤ 2 * m * (2 * r 0 * Real.log 2) := by
      gcongr
    nlinarith [mul_nonneg hm0 hr0]
  nlinarith [mul_le_mul_of_nonneg_left hkey hD]

/-- The closing inequality of the inductive step of Roth's lemma: if `θ < 1 / 2`, `σ ≤ θ ^ 2`
and `t > 2 (n + 2) θ`, then `2 (n + 1) θ ^ 2 + σ < min ((t - σ) / 2) ((t - σ) ^ 2 / 2)`. -/
private theorem lt_min_of_mul_lt {n : ℕ} {θ σ t : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 2)
    (hσθ : σ ≤ θ ^ 2) (ht : 2 * (n + 2) * θ < t) :
    2 * (n + 1) * θ ^ 2 + σ < min ((t - σ) / 2) ((t - σ) ^ 2 / 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hθ2 : θ ^ 2 < θ / 2 := by nlinarith
  have hδ : (2 * n + 7 / 2) * θ < t - σ := by nlinarith
  have hA : 2 * (n + 1) * θ ^ 2 + σ ≤ (2 * n + 3) * θ ^ 2 := by nlinarith
  refine lt_min ?_ ?_
  · nlinarith
  · have hδ0 : 0 < (2 * n + 7 / 2) * θ := by positivity
    have hsq : ((2 * n + 7 / 2) * θ) ^ 2 < (t - σ) ^ 2 := by
      exact pow_lt_pow_left₀ hδ hδ0.le two_ne_zero
    nlinarith [sq_nonneg θ]

/-- Roth's lemma for `n + 1` variables in terms of the parameter `θ`, where `σ = θ ^ 2 ^ n`. -/
private def IndexBound (K : Type*) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ {θ : ℝ}, 0 < θ → θ ^ 2 ^ n ≤ 1 / 2 → ∀ {r : Fin (n + 1) → ℕ}, (∀ i, 0 < r i) →
    (∀ i : Fin n, (r i.succ : ℝ) ≤ θ ^ 2 ^ n * r i.castSucc) →
    ∀ {P : MvPolynomial (Fin (n + 1)) K}, P ≠ 0 → (∀ i, P.degreeOf i ≤ r i) →
    ∀ β : Fin (n + 1) → K,
    (∀ i, P.logHeight + 4 * (n + 1) * r 0 * finrank ℚ K ≤
      θ ^ 2 ^ n * (r i * logHeight₁ (β i))) →
    weightedIndex r β P ≤ ENNReal.ofReal (2 * (n + 1) * θ)

/-- Roth's lemma in one variable, from `MvPolynomial.weightedIndex_toMvPolynomial_le`. -/
private theorem indexBound_zero : IndexBound K 0 := by
  intro θ hθ _ r _ _ P hP hdeg β hβ
  simp only [pow_zero, pow_one, CharP.cast_eq_zero, zero_add, mul_one] at hβ ⊢
  -- Write `P` as a univariate polynomial placed in its only variable.
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  obtain ⟨p, rfl⟩ : ∃ p : Polynomial K, p.toMvPolynomial 0 = P := by
    have h : (Polynomial.toMvPolynomial (0 : Fin (0 + 1))).comp
        (uniqueAlgEquiv K (Fin (0 + 1))).toAlgHom = AlgHom.id K _ :=
      algHom_ext fun i ↦ by simp [Subsingleton.elim i 0]
    exact ⟨_, congrArg (· P) h⟩
  have hp : p ≠ 0 := fun h ↦ hP (by rw [h, map_zero])
  have hpdeg : p.natDegree ≤ r 0 := by simpa using hdeg 0
  have hD : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r 0 := Nat.cast_nonneg _
  have hlog : Real.log 2 ≤ 4 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  refine (weightedIndex_toMvPolynomial_le r β 0 hp hpdeg hθ ?_).trans
    (ENNReal.ofReal_le_ofReal (by linarith))
  simp only [Polynomial.logHeight_toMvPolynomial] at hβ
  rw [inv_mul_le_iff₀ hθ]
  nlinarith [hβ 0, mul_nonneg (mul_nonneg hD hr0) (sub_nonneg.2 hlog)]

/-- The inductive step of Roth's lemma. -/
private theorem indexBound_succ {n : ℕ} (ih : IndexBound K n) : IndexBound K (n + 1) := by
  intro θ hθ hθσ r hr hratio P hP hdeg β hβ
  set σ := θ ^ 2 ^ (n + 1) with hσ
  have hσ0 : 0 < σ := by positivity
  have hD : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hanti : Antitone r := Fin.antitone_iff_succ_le.2 fun i ↦ by
    have h := hratio i
    have h' : (r i.succ : ℝ) ≤ r i.castSucc :=
      h.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (r i.castSucc)])
    exact_mod_cast h'
  -- If `θ ≥ 1 / 2`, the index is at most the number of variables.
  rcases le_or_gt (1 / 2) θ with hθ2 | hθ2
  · refine (weightedIndex_le_sum_degreeOf r β hP).trans ?_
    calc ∑ j, (P.degreeOf j : ℝ≥0∞) / r j ≤ ∑ _j : Fin (n + 2), (1 : ℝ≥0∞) :=
          sum_le_sum fun j _ ↦ ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast hdeg j)
      _ = ENNReal.ofReal (n + 2) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_one, ← ENNReal.ofReal_natCast]
          push_cast
          rfl
      _ ≤ ENNReal.ofReal (2 * ((n + 1 : ℕ) + 1) * θ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          push_cast
          nlinarith
  by_contra hcon
  rw [not_le] at hcon
  -- The index `t` of `P` is finite and larger than `2 (n + 2) θ`.
  set t := (weightedIndex r β P).toReal
  have hPt : weightedIndex r β P = ENNReal.ofReal t :=
    (ENNReal.ofReal_toReal (weightedIndex_ne_top (fun j ↦ (hr j).ne') β hP)).symm
  have ht : 2 * ((n : ℝ) + 2) * θ < t := by
    rw [hPt] at hcon
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hcon
    push_cast at this
    linarith
  -- Separate the last variable and choose a nonzero generalized Wronskian of the `fₖ`.
  obtain ⟨m, hm, f, g, hf, hg, hfv, hfdeg, hgdeg, hPfg⟩ :=
    exists_sum_mul_linearIndependent P (Fin.last (n + 1))
  have hm' : m ≤ r (Fin.last (n + 1)) + 1 := hm.trans (by have := hdeg (Fin.last (n + 1)); omega)
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ by
    subst h
    exact hP (by simpa using hPfg)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨μ, hμ, hWf⟩ := exists_genWronskian_ne_zero hf
  have hf0 (l : Fin m) : (f l).degreeOf (Fin.last (n + 1)) = 0 := by
    by_contra h
    exact hfv l (mem_vars_iff_degreeOf_ne_zero.2 h)
  -- The rows `μ k` do not differentiate in the last variable, as no `fₖ` involves it.
  have hμl (k : Fin m) : μ k (Fin.last (n + 1)) = 0 := by
    by_contra hk
    refine hWf ?_
    rw [genWronskian_def]
    exact Matrix.det_eq_zero_of_row_eq_zero k fun l ↦ by
      rw [Matrix.of_apply]
      exact hasseDeriv_eq_zero_of_degreeOf_lt (by rw [hf0]; omega)
  set Wf := genWronskian μ f
  set Wg := Polynomial.hasseWronskian g
  have hWfl : (Fin.last (n + 1)) ∉ Wf.vars := by
    rw [mem_vars_iff_degreeOf_ne_zero, not_not]
    simpa using degreeOf_genWronskian_le μ f (Fin.last (n + 1)) 0 fun l ↦ (hf0 l).le
  have hWg : Wg ≠ 0 := Polynomial.hasseWronskian_ne_zero_of_linearIndependent hg
  -- The heights of the two Wronskians add up to at most `m (h(P) + 4 r₀ [K : ℚ])`.
  have hsum : ∑ j, (r j : ℝ) ≤ 2 * r 0 :=
    Fin.sum_le_two_mul_of_two_mul_succ_le (fun _ ↦ Nat.cast_nonneg _) fun i ↦ by
      nlinarith [hratio i, Nat.cast_nonneg (α := ℝ) (r i.castSucc)]
  have hheight := logHeight_det_hasseDeriv_le_mul hP hdeg hsum
    (hm'.trans (by have := hanti (Fin.zero_le (Fin.last (n + 1))); omega))
    (fun k l ↦ μ k + Finsupp.single (Fin.last (n + 1)) (l : ℕ))
  have hdet : (Matrix.of fun k l : Fin m ↦
      hasseDeriv (μ k + Finsupp.single (Fin.last (n + 1)) (l : ℕ)) P).det =
      Wf * Wg.toMvPolynomial (Fin.last (n + 1)) := by
    conv_lhs => rw [hPfg]
    exact det_hasseDeriv_sum_mul_toMvPolynomial hμl hfv g
  rw [hdet, logHeight_mul_toMvPolynomial hWfl hWf hWg] at hheight
  have hWgh := Polynomial.logHeight_nonneg Wg
  have hWfh := MvPolynomial.logHeight_nonneg Wf
  -- Lower bound: the indices of the two Wronskians add up to at least `m min (δ / 2) (δ² / 2)`,
  -- where `δ = t - σ`.
  -- Each row `μ k` only differentiates in variables of weight `1 / rⱼ ≤ 1 / rₙ`, and
  -- `|μ k| ≤ r_{n+1} ≤ σ rₙ`, so `∑ⱼ (μ k)ⱼ / rⱼ ≤ σ`.
  have hwt (k : Fin m) : (μ k).weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) ≤ ENNReal.ofReal σ := by
    set c := (Fin.last n).castSucc
    have hc : (0 : ℝ) < r c := by exact_mod_cast hr c
    refine ((μ k).weight_le_degree_nsmul_of_monotone
      (fun a b h ↦ ENNReal.inv_le_inv.2 (by exact_mod_cast hanti h)) (i := c) fun j hj ↦
        Fin.le_castSucc_iff.2 (Fin.lt_last_iff_ne_last.2 fun h ↦
          Finsupp.mem_support_iff.1 hj (h ▸ hμl k))).trans ?_
    rw [nsmul_eq_mul]
    calc ((μ k).degree : ℝ≥0∞) * (r c : ℝ≥0∞)⁻¹ ≤
          (r (Fin.last (n + 1)) : ℝ≥0∞) * (r c : ℝ≥0∞)⁻¹ := by
          gcongr
          have := hμ k
          have := k.isLt
          omega
      _ = ENNReal.ofReal (r (Fin.last (n + 1)) / r c) := by
          rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
            div_eq_mul_inv]
      _ ≤ ENNReal.ofReal σ :=
          ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc).2 (by simpa using hratio (Fin.last n)))
  have hlow := ofReal_mul_min_le_weightedIndex_genWronskian_add hm' hμl hfv g hσ0.le
    (t := t) (by rw [← hPfg, hPt]) hwt
  -- Upper bound for `W_μ(f)`, by the induction hypothesis with weights `m rⱼ`.
  obtain ⟨W, hW⟩ := exists_rename_eq_of_vars_subset_range Wf Fin.castSucc
    (Fin.castSucc_injective _) fun j hj ↦
      Fin.exists_castSucc_eq.2 fun h ↦ hWfl (h ▸ Finset.mem_coe.1 hj)
  have hW0 : W ≠ 0 := fun h ↦ hWf (by rw [← hW, h, map_zero])
  have hpow : (θ ^ 2) ^ 2 ^ n = σ := by rw [← pow_mul, hσ, pow_succ, mul_comm]
  have hWind := ih (θ := θ ^ 2) (by positivity) (by rwa [hpow])
    (r := fun j ↦ m * r j.castSucc) (fun j ↦ Nat.mul_pos hm0 (hr _)) (fun i ↦ by
      rw [hpow]
      have h := hratio i.castSucc
      rw [Fin.succ_castSucc] at h
      push_cast
      nlinarith)
    hW0 (fun j ↦ by
      rw [← degreeOf_rename_of_injective (Fin.castSucc_injective _), hW]
      exact degreeOf_genWronskian_le μ f _ _ fun l ↦ (hfdeg l _).trans (hdeg _))
    (β ∘ Fin.castSucc) (fun j ↦ by
      rw [hpow, ← logHeight_rename W (Fin.castSucc_injective _), hW, Fin.castSucc_zero]
      have h := mul_le_mul_of_nonneg_left (hβ j.castSucc) hm0'.le
      simp only [Function.comp_apply]
      push_cast at h ⊢
      nlinarith)
  have hWf_le : weightedIndex r β Wf ≤ ENNReal.ofReal (2 * (n + 1) * θ ^ 2) * m := by
    have hsmul : (fun j ↦ m * r j.castSucc) = m • (r ∘ Fin.castSucc) := by
      ext j
      simp
    rw [hsmul, weightedIndex_smul_weight hm0.ne', ← weightedIndex_rename (Fin.castSucc_injective _),
      hW, ENNReal.div_le_iff (by simpa using hm0.ne') (ENNReal.natCast_ne_top m)] at hWind
    exact hWind
  -- Upper bound for the Hasse Wronskian of the `gₖ`, by the one-variable case.
  have hWgdeg : Wg.natDegree ≤ (m • r) (Fin.last (n + 1)) := by
    rw [← Polynomial.degreeOf_toMvPolynomial Wg (Fin.last (n + 1)),
      ← genWronskian_single_toMvPolynomial,
      Pi.smul_apply, smul_eq_mul]
    exact degreeOf_genWronskian_le _ _ _ _ fun l ↦ by
      rw [Polynomial.degreeOf_toMvPolynomial]
      exact (hgdeg l).trans (hdeg _)
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have hrl : (r (Fin.last (n + 1)) : ℝ) ≤ r 0 := by
    exact_mod_cast hanti (Fin.zero_le (Fin.last (n + 1)))
  have hWgind := weightedIndex_toMvPolynomial_le (m • r) β (Fin.last (n + 1)) hWg hWgdeg hσ0 (by
    rw [inv_mul_le_iff₀ hσ0, Pi.smul_apply, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (hβ (Fin.last (n + 1))) hm0'.le
    have h2 : (finrank ℚ K : ℝ) * (m * r (Fin.last (n + 1))) * Real.log 2 ≤
        finrank ℚ K * (m * r 0) :=
      calc _ ≤ (finrank ℚ K : ℝ) * (m * r (Fin.last (n + 1))) * 1 := by gcongr
        _ ≤ finrank ℚ K * (m * r 0) := by rw [mul_one]; gcongr
    have h3 : 0 ≤ (n : ℝ) * (m * r 0 * finrank ℚ K) := by positivity
    have h4 : 0 ≤ (m : ℝ) * r 0 * finrank ℚ K := by positivity
    push_cast at h ⊢
    linarith)
  have hWg_le :
      weightedIndex r β (Wg.toMvPolynomial (Fin.last (n + 1))) ≤ ENNReal.ofReal σ * m := by
    rw [weightedIndex_smul_weight hm0.ne',
      ENNReal.div_le_iff (by simpa using hm0.ne') (ENNReal.natCast_ne_top m)] at hWgind
    exact hWgind
  -- Combine the two bounds.
  have hA : 0 ≤ 2 * ((n : ℝ) + 1) * θ ^ 2 + σ := by positivity
  have hcomb : ENNReal.ofReal (m * min ((t - σ) / 2) ((t - σ) ^ 2 / 2)) ≤
      ENNReal.ofReal (m * (2 * ((n : ℝ) + 1) * θ ^ 2 + σ)) := by
    refine hlow.trans ((add_le_add hWf_le hWg_le).trans_eq ?_)
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) hσ0.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcomb
  have hσθ : σ ≤ θ ^ 2 := pow_le_pow_of_le_one hθ.le (by linarith)
    (by simpa using Nat.pow_le_pow_right two_pos (Nat.succ_pos n))
  have := lt_min_of_mul_lt hθ hθ2 hσθ ht
  nlinarith

private theorem indexBound (n : ℕ) : IndexBound K n := by
  induction n with
  | zero => exact indexBound_zero
  | succ n ih => exact indexBound_succ ih

/-- **Roth's lemma** (Pottmeyer, Theorem 3.4.1). Let `P ≠ 0` be a polynomial in `n ≥ 1`
variables over a number field `K`, with partial degrees `deg_{Xᵢ} P ≤ rᵢ` for positive weights
`rᵢ` satisfying `rᵢ₊₁ ≤ σ rᵢ`, where `0 < σ ≤ 1 / 2`. If
`σ⁻¹ (h(P) + 4 n r₀ [K : ℚ]) ≤ rᵢ h(βᵢ)` for every `i`, then the index of `P` at `β` with
weights `r` is at most `2 n σ ^ (1 / 2 ^ (n - 1))`. Heights are relative logarithmic heights. -/
theorem weightedIndex_le_of_logHeight_le {n : ℕ} [NeZero n] {P : MvPolynomial (Fin n) K}
    (hP : P ≠ 0) {r : Fin n → ℕ} (hr : ∀ i, 0 < r i) (hdeg : ∀ i, P.degreeOf i ≤ r i)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hratio : ∀ i j : Fin n, (j : ℕ) = i + 1 → (r j : ℝ) ≤ σ * r i) (β : Fin n → K)
    (hβ : ∀ i, σ⁻¹ * (P.logHeight + 4 * n * r 0 * finrank ℚ K) ≤ r i * logHeight₁ (β i)) :
    weightedIndex r β P ≤ ENNReal.ofReal (2 * n * σ ^ ((1 : ℝ) / 2 ^ (n - 1))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  set θ := σ ^ ((1 : ℝ) / 2 ^ k)
  have hθ : 0 < θ := Real.rpow_pos_of_pos hσ₀ _
  have hθσ : θ ^ 2 ^ k = σ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ₀.le, Nat.cast_pow, Nat.cast_ofNat,
      one_div_mul_cancel (by positivity), Real.rpow_one]
  have h := indexBound (K := K) k hθ (by rwa [hθσ]) hr (fun i ↦ by
      rw [hθσ]
      exact hratio i.castSucc i.succ (by simp)) hP hdeg β (fun i ↦ by
      rw [hθσ, ← inv_mul_le_iff₀ hσ₀]
      push_cast at hβ
      exact hβ i)
  rw [Nat.succ_sub_one, Nat.cast_succ]
  exact h

end TauCeti
