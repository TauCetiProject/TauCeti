/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Connected
public import TauCeti.Probability.RandomMatrix.MomentBounds
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Probability.RandomMatrix.Wigner.Trace.Integrability

/-!
# Connected two-trace expansion and covariance bounds for Wigner moments

Expanding `E[tr(Hₙ ^ k₁) tr(Hₙ ^ k₂)] - E[tr(Hₙ ^ k₁)] E[tr(Hₙ ^ k₂)]` into pairs of closed walks
`(w₁, w₂)` eliminates two classes of pairs under independent corner entries with centered
off-diagonal coordinates:

* pairs whose unordered cyclic edge sets are disjoint decouple by independence
  (`TauCeti.integral_prod_mul_prod_wignerMatrix_apply_of_disjoint`), so `E[P₁ P₂] = E[P₁] E[P₂]`;
* pairs whose combined unordered cyclic edge multiset on `Fin k₁ ⊕ Fin k₂` contains a nonloop edge
  traversed only once satisfy `E[P₁ P₂] = 0` and either `E[P₁] = 0` or `E[P₂] = 0`
  (`TauCeti.integral_prod_wignerMatrix_apply_eq_zero_of_ne`).

Every surviving pair shares at least one unordered cyclic edge and has no singleton nonloop
unordered cyclic edge across `Fin k₁ ⊕ Fin k₂`. By
`TauCeti.card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_nonloop_edge`, such a pair
visits at most `(k₁ + k₂) / 2` vertices in total, hence there are at most
`n^((k₁ + k₂) / 2) * ((k₁ + k₂) / 2)^(k₁ + k₂)` surviving pairs. Under a uniform `(k₁ + k₂)`-th
absolute moment bound `B` on the `n × n` corner, each surviving pair contributes at most
`2 * (√n)⁻¹ ^ (k₁ + k₂) * B`, yielding an `O(n⁻²)` bound for normalized two-trace covariances and
for the mean-square fluctuations of normalized Wigner traces of every order, without requiring
diagonal centering.

## Main results

* `TauCeti.integral_trace_pow_mul_trace_pow_sub_wignerMatrix`: the connected two-trace expansion
  for `E[tr(Hₙ ^ k₁) tr(Hₙ ^ k₂)] - E[tr(Hₙ ^ k₁)] E[tr(Hₙ ^ k₂)]` under off-diagonal centering.
* `TauCeti.norm_inv_mul_inv_mul_integral_trace_pow_mul_sub_wignerMatrix_le` and
  `TauCeti.norm_integral_inv_mul_trace_pow_wignerMatrix_sub_mul_le`: quantitative `O(n⁻²)` bounds on
  normalized two-trace covariances for all `k₁, k₂, n : ℕ`.
* `TauCeti.integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le` and
  `TauCeti.tendsto_integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq`: `O(n⁻²)` mean-square
  concentration of normalized Wigner traces, including on varying probability spaces.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.4, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

section ConnectedExpansion

private theorem integral_prod_mul_prod_sub_eq_zero_of_not_connected {k₁ k₂ n : ℕ}
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (w₁ : Fin k₁ → Fin n) (w₂ : Fin k₂ → Fin n)
    (hnot : ¬ ((∃ i j, s(w₁ i, w₁ (finRotate k₁ i)) = s(w₂ j, w₂ (finRotate k₂ j))) ∧
      ∀ t : Fin k₁ ⊕ Fin k₂,
        Sum.elim w₁ w₂ t ≠
          Sum.elim (fun i ↦ w₁ (finRotate k₁ i)) (fun j ↦ w₂ (finRotate k₂ j)) t →
          ∃ t' ≠ t,
            Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
              (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
            Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
              (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t)) :
    (∫ ω, (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i))) *
        (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j))) ∂P) -
      (∫ ω, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i)) ∂P) *
        ∫ ω, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j)) ∂P = 0 := by
  by_cases hshare : ∃ i j, s(w₁ i, w₁ (finRotate k₁ i)) = s(w₂ j, w₂ (finRotate k₂ j))
  · let u : Fin k₁ ⊕ Fin k₂ → Fin n := Sum.elim w₁ w₂
    let v : Fin k₁ ⊕ Fin k₂ → Fin n :=
      Sum.elim (fun i ↦ w₁ (finRotate k₁ i)) (fun j ↦ w₂ (finRotate k₂ j))
    have hsingle : ∃ t : Fin k₁ ⊕ Fin k₂, u t ≠ v t ∧ ∀ t',
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t → t' = t := by
      by_contra! h
      exact hnot ⟨hshare, fun t hne ↦ let ⟨t', heq, htne⟩ := h t hne; ⟨t', htne, heq⟩⟩
    obtain ⟨t, hne, ht⟩ := hsingle
    have huv (s : Fin k₁ ⊕ Fin k₂) : s(u s, v s) =
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) s := by cases s <;> rfl
    have hprod_zero : ∫ ω, (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i))) *
        (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j))) ∂P = 0 := by
      have hcomb (ω : Ω) : (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i))) *
          (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j))) =
          ∏ s, wignerMatrix ξ η n ω (u s) (v s) := by
        simp [Fintype.prod_sum_type, u, v]
      simp_rw [hcomb]
      exact integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero u v hne
        fun s hs ↦ ht s (by simpa only [huv] using hs)
    have hfac_zero : (∫ ω, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i)) ∂P) *
        ∫ ω, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j)) ∂P = 0 := by
      cases t with
      | inl i =>
        rw [integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero w₁
          (fun i ↦ w₁ (finRotate k₁ i)) (t := i) (by simpa [u, v] using hne)
          fun i' hi' ↦ Sum.inl.inj (ht (.inl i') hi'), zero_mul]
      | inr j =>
        rw [integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero w₂
          (fun j ↦ w₂ (finRotate k₂ j)) (t := j) (by simpa [u, v] using hne)
          fun j' hj' ↦ Sum.inr.inj (ht (.inr j') hj'), mul_zero]
    rw [hprod_zero, hfac_zero, sub_zero]
  · exact sub_eq_zero.mpr (integral_prod_mul_prod_wignerMatrix_apply_of_disjoint
      hξm hηm hindep w₁ (fun i ↦ w₁ (finRotate k₁ i)) w₂ (fun j ↦ w₂ (finRotate k₂ j))
      fun i j hij ↦ hshare ⟨i, j, hij⟩)

/-- **Connected two-trace expansion of Wigner moments.** For independent entries in the `n × n`
corner in `L^(k₁ + k₂)` with centered strictly upper coordinates, subtracting the product of
expected traces from the expected product of traces restricts the double walk sum to pairs
`(w₁, w₂)` that share at least one unordered cyclic edge and have no singleton nonloop unordered
cyclic edge across `Fin k₁ ⊕ Fin k₂`. -/
theorem integral_trace_pow_mul_trace_pow_sub_wignerMatrix {k₁ k₂ n : ℕ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (k₁ + k₂ : ℕ) P) :
    (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P) -
        (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace ∂P) *
          (∫ ω, (wignerMatrix ξ η n ω ^ k₂).trace ∂P) =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n) with
        (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
          ∀ t : Fin k₁ ⊕ Fin k₂,
            Sum.elim p.1 p.2 t ≠
              Sum.elim (fun i ↦ p.1 (finRotate k₁ i)) (fun j ↦ p.2 (finRotate k₂ j)) t →
              ∃ t' ≠ t,
                Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
                  (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
                Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
                  (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t,
        ((∫ ω, (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
            (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) ∂P) -
          (∫ ω, ∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i)) ∂P) *
            ∫ ω, ∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)) ∂P) := by
  have := hindep.isProbabilityMeasure
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp [integral_const_mul]
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp [integral_mul_const]
  have hξ₁ (ij : StrictUpper) (hij : ij.val.2 < n) : MemLp (ξ ij) k₁ P :=
    (hξp ij hij).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂)
  have hη₁ (i : ℕ) (hi : i < n) : MemLp (η i) k₁ P :=
    (hηp i hi).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂)
  have hξ₂ (ij : StrictUpper) (hij : ij.val.2 < n) : MemLp (ξ ij) k₂ P :=
    (hξp ij hij).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁)
  have hη₂ (i : ℕ) (hi : i < n) : MemLp (η i) k₂ P :=
    (hηp i hi).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁)
  have hint₁₂ (p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n)) :
      Integrable (fun ω ↦ (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
        (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)))) P := by
    have h := integrable_prod_wignerMatrix_apply
      (ι := Fin k₁ ⊕ Fin k₂)
      (fun ij hij ↦ by simpa [Fintype.card_sum] using hξp ij hij)
      (fun i hi ↦ by simpa [Fintype.card_sum] using hηp i hi)
      (Sum.elim p.1 p.2) (Sum.elim (p.1 ∘ finRotate k₁) (p.2 ∘ finRotate k₂))
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] using h
  simp_rw [trace_pow_eq_sum_prod _ hk₁, trace_pow_eq_sum_prod _ hk₂]
  have hmul_sum (ω : Ω) :
      (∑ w₁ : Fin k₁ → Fin n, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i))) *
        (∑ w₂ : Fin k₂ → Fin n, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j))) =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n),
        (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
          (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) := by
    rw [Fintype.sum_prod_type, sum_mul_sum]
  have hmul_int :
      (∑ w₁ : Fin k₁ → Fin n, ∫ ω, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i)) ∂P) *
        (∑ w₂ : Fin k₂ → Fin n, ∫ ω, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j)) ∂P) =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n),
        (∫ ω, ∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i)) ∂P) *
          ∫ ω, ∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)) ∂P := by
    rw [Fintype.sum_prod_type, sum_mul_sum]
  simp_rw [hmul_sum]
  rw [integral_finsetSum _ fun p _ ↦ hint₁₂ p,
    integral_finsetSum _ fun w₁ _ ↦ integrable_prod_wignerMatrix_apply
      (fun ij hij ↦ by simpa using hξ₁ ij hij) (fun i hi ↦ by simpa using hη₁ i hi) _ _,
    integral_finsetSum _ fun w₂ _ ↦ integrable_prod_wignerMatrix_apply
      (fun ij hij ↦ by simpa using hξ₂ ij hij) (fun i hi ↦ by simpa using hη₂ i hi) _ _,
    hmul_int, ← sum_sub_distrib]
  symm
  apply sum_filter_of_ne
  intro p _ hp
  by_contra hnot
  exact hp (integral_prod_mul_prod_sub_eq_zero_of_not_connected
    (fun ij hij ↦ (hξp ij hij).aestronglyMeasurable.aemeasurable)
    (fun i hi ↦ (hηp i hi).aestronglyMeasurable.aemeasurable)
    hindep hξzero p.1 p.2 hnot)

end ConnectedExpansion

section MomentBounds

/-- On a probability space, a uniform `(card ι₁ + card ι₂)`-th absolute moment bound `B` on the
`n × n` corner controls the product of two expected products of Wigner entries indexed by
`ι₁` and `ι₂` (`Nonempty (ι₁ ⊕ ι₂)`), without independence or centering. -/
theorem norm_integral_prod_wignerMatrix_apply_mul_integral_prod_le [IsProbabilityMeasure P]
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty (ι₁ ⊕ ι₂)] {n : ℕ} {B : ℝ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n →
      MemLp (ξ ij) (Fintype.card ι₁ + Fintype.card ι₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (Fintype.card ι₁ + Fintype.card ι₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n →
      ∫ ω, ‖ξ ij ω‖ ^ (Fintype.card ι₁ + Fintype.card ι₂) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (Fintype.card ι₁ + Fintype.card ι₂) ∂P ≤ B)
    (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n) :
    ‖(∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ (Fintype.card ι₁ + Fintype.card ι₂) * B := by
  set K := Fintype.card ι₁ + Fintype.card ι₂
  let F : ι₁ ⊕ ι₂ → Ω × Ω → ℂ := fun x z ↦
    match x with
    | .inl s => wignerMatrix ξ η n z.1 (u₁ s) (v₁ s)
    | .inr t => wignerMatrix ξ η n z.2 (u₂ t) (v₂ t)
  have hprod : (∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
      (∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P) =
      ∫ z, ∏ x, F x z ∂P.prod P := by
    rw [← integral_prod_mul]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    simp [F, Fintype.prod_sum_type]
  have hcard : Fintype.card (ι₁ ⊕ ι₂) = K := Fintype.card_sum
  have hK_ne : (K : ℝ) ≠ 0 := by
    rw [← hcard]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hint (x : ι₁ ⊕ ι₂) : Integrable (fun z ↦ ‖F x z‖ ^ K) (P.prod P) := by
    have hK0 : K ≠ 0 := by rw [← hcard]; exact Fintype.card_ne_zero
    cases x with
    | inl s =>
      exact ((memLp_wignerMatrix_apply hξp hηp (u₁ s) (v₁ s)).integrable_norm_pow hK0).comp_fst P
    | inr t =>
      exact ((memLp_wignerMatrix_apply hξp hηp (u₂ t) (v₂ t)).integrable_norm_pow hK0).comp_snd P
  have hmom (x : ι₁ ⊕ ι₂) : ∫ z, ‖F x z‖ ^ K ∂P.prod P ≤ (Real.sqrt n)⁻¹ ^ K * B := by
    cases x with
    | inl s =>
      simpa [F, integral_fun_fst (fun ω ↦ ‖wignerMatrix ξ η n ω (u₁ s) (v₁ s)‖ ^ K)] using
        integral_norm_wignerMatrix_apply_pow_le hξ hη (u₁ s) (v₁ s)
    | inr t =>
      simpa [F, integral_fun_snd (fun ω ↦ ‖wignerMatrix ξ η n ω (u₂ t) (v₂ t)‖ ^ K)] using
        integral_norm_wignerMatrix_apply_pow_le hξ hη (u₂ t) (v₂ t)
  rw [hprod]
  calc
    ‖∫ z, ∏ x, F x z ∂P.prod P‖ ≤
        (K : ℝ)⁻¹ * ∑ x, ∫ z, ‖F x z‖ ^ K ∂P.prod P := by
      simpa [hcard] using norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow F univ_nonempty
        (fun x _ ↦ by simpa [hcard] using hint x)
    _ ≤ (K : ℝ)⁻¹ * ∑ _x : ι₁ ⊕ ι₂, (Real.sqrt n)⁻¹ ^ K * B := by
      gcongr with x
      exact hmom x
    _ = (Real.sqrt n)⁻¹ ^ K * B := by simp [hcard, hK_ne]

private theorem norm_integral_prod_mul_prod_sub_wignerMatrix_le [IsProbabilityMeasure P]
    {k₁ k₂ n : ℕ} [Nonempty (Fin k₁ ⊕ Fin k₂)] {B : ℝ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n)) :
    ‖(∫ ω, (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
          (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) ∂P) -
        (∫ ω, ∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i)) ∂P) *
          ∫ ω, ∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)) ∂P‖ ≤
      2 * ((Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B) := by
  have h1 : ‖∫ ω, (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
      (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B := by
    have h := norm_integral_prod_wignerMatrix_apply_le (ι := Fin k₁ ⊕ Fin k₂)
      (fun ij hij ↦ by simpa [Fintype.card_sum] using hξp ij hij)
      (fun i hi ↦ by simpa [Fintype.card_sum] using hηp i hi)
      (fun ij hij ↦ by simpa [Fintype.card_sum] using hξ ij hij)
      (fun i hi ↦ by simpa [Fintype.card_sum] using hη i hi)
      (Sum.elim p.1 p.2) (Sum.elim (p.1 ∘ finRotate k₁) (p.2 ∘ finRotate k₂))
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Fintype.card_sum, Fintype.card_fin] using h
  have h2 : ‖(∫ ω, ∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i)) ∂P) *
      ∫ ω, ∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B := by
    simpa using norm_integral_prod_wignerMatrix_apply_mul_integral_prod_le
      (by simpa using hξp) (by simpa using hηp) (by simpa using hξ) (by simpa using hη)
      p.1 (fun i ↦ p.1 (finRotate k₁ i)) p.2 (fun j ↦ p.2 (finRotate k₂ j))
  exact (norm_sub_le _ _).trans (by linarith)

/-- **Normalized two-trace covariance bound (uncentered difference form).** Under independent
entries in the `n × n` corner in `L^(k₁ + k₂)` with centered strictly upper coordinates and
`(k₁ + k₂)`-th absolute moments bounded by `B`, the covariance of the normalized traces
`(n : ℂ)⁻¹ * tr(Hₙ ^ k₁)` and `(n : ℂ)⁻¹ * tr(Hₙ ^ k₂)` has norm at most
`2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / n²` for all `k₁, k₂, n : ℕ`. -/
theorem norm_inv_mul_inv_mul_integral_trace_pow_mul_sub_wignerMatrix_le {k₁ k₂ n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (n : ℂ)⁻¹ *
        ((∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P) -
          (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace ∂P) *
            ∫ ω, (wignerMatrix ξ η n ω ^ k₂).trace ∂P)‖ ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 := by
  have := hindep.isProbabilityMeasure
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans
      (hη 0 (Nat.pos_of_ne_zero hn))
  have hpow : (n : ℝ) ^ ((k₁ + k₂) / 2) * (Real.sqrt n)⁻¹ ^ (k₁ + k₂) ≤ 1 := by
    have hinv : (Real.sqrt n)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn))
    conv_lhs => enter [2, 2]; rw [← Nat.div_add_mod (k₁ + k₂) 2]
    rw [pow_add, ← mul_assoc, inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n),
      mul_inv_cancel₀ (pow_ne_zero _ (by positivity)), one_mul]
    rcases Nat.mod_two_eq_zero_or_one (k₁ + k₂) with h | h
    · simp [h]
    · simpa [h] using hinv
  set S : Finset ((Fin k₁ → Fin n) × (Fin k₂ → Fin n)) :=
    {p | (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
      ∀ t : Fin k₁ ⊕ Fin k₂,
        Sum.elim p.1 p.2 t ≠
          Sum.elim (fun i ↦ p.1 (finRotate k₁ i)) (fun j ↦ p.2 (finRotate k₂ j)) t →
          ∃ t' ≠ t,
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t}
  have hcard : #S ≤ n ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
    simpa [S] using
      card_filter_shared_edge_and_no_singleton_nonloop_edge_le (β := Fin n) k₁ k₂
  rw [integral_trace_pow_mul_trace_pow_sub_wignerMatrix hindep hξzero hξp hηp,
    norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ‖∑ p ∈ S, _‖
      ≤ (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * (#S * (2 * ((Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B))) := by
        gcongr
        exact (norm_sum_le S _).trans ((sum_le_sum fun p hp ↦ by
          obtain ⟨-, ⟨i₀, -⟩, -⟩ := mem_filter.mp hp
          have : Nonempty (Fin k₁ ⊕ Fin k₂) := ⟨.inl i₀⟩
          exact norm_integral_prod_mul_prod_sub_wignerMatrix_le hξp hηp hξ hη p).trans (by simp))
    _ ≤ (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
        ((n ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) : ℕ) *
          (2 * ((Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B))) := by gcongr
    _ = (2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2) *
        ((n : ℝ) ^ ((k₁ + k₂) / 2) * (Real.sqrt n)⁻¹ ^ (k₁ + k₂)) := by
        push_cast; have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn; field_simp
    _ ≤ 2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hpow

private theorem integrable_trace_pow_mul_trace_pow_wignerMatrix [IsFiniteMeasure P] {k₁ k₂ n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (k₁ + k₂ : ℕ) P) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k₁).trace *
      (wignerMatrix ξ η n ω ^ k₂).trace) P := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact (integrable_trace_pow_wignerMatrix (n := n) (fun _ ↦ inferInstance)
      (fun ij hij ↦ by simpa using hξp ij hij) (fun i hi ↦ by simpa using hηp i hi)).const_mul _
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact (integrable_trace_pow_wignerMatrix (n := n) (fun _ ↦ inferInstance)
      (fun ij hij ↦ by simpa using hξp ij hij) (fun i hi ↦ by simpa using hηp i hi)).mul_const _
  have hprod (ω : Ω) : (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n),
        (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
          (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) := by
    rw [trace_pow_eq_sum_prod _ hk₁, trace_pow_eq_sum_prod _ hk₂, sum_mul_sum,
      ← univ_product_univ, sum_product]
  simp_rw [hprod]
  refine integrable_finsetSum _ fun p _ ↦ ?_
  have h := integrable_prod_wignerMatrix_apply (ι := Fin k₁ ⊕ Fin k₂)
    (fun ij hij ↦ by simpa [Fintype.card_sum] using hξp ij hij)
    (fun i hi ↦ by simpa [Fintype.card_sum] using hηp i hi)
    (Sum.elim p.1 p.2) (Sum.elim (p.1 ∘ finRotate k₁) (p.2 ∘ finRotate k₂))
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] using h

/-- **Centered normalized two-trace covariance bound.** Under independent entries in the `n × n`
corner in `L^(k₁ + k₂)` with centered strictly upper coordinates and `(k₁ + k₂)`-th absolute
moments bounded by `B`, the expected product of centered normalized traces of `Hₙ ^ k₁` and
`Hₙ ^ k₂` has norm at most `2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / n²` for all `k₁, k₂, n : ℕ`. -/
theorem norm_integral_inv_mul_trace_pow_wignerMatrix_sub_mul_le {k₁ k₂ n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
    ‖∫ ω, (((n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₁).trace -
          ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k₁).trace ∂P) *
        ((n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₂).trace -
          ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k₂).trace ∂P)) ∂P‖ ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 := by
  have := hindep.isProbabilityMeasure
  set X₁ : Ω → ℂ := fun ω ↦ (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₁).trace
  set X₂ : Ω → ℂ := fun ω ↦ (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₂).trace
  have hint₁ : Integrable X₁ P :=
    (integrable_trace_pow_wignerMatrix (n := n) (fun _ ↦ inferInstance)
      (fun ij hij ↦ (hξp ij hij).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂))
      (fun i hi ↦ (hηp i hi).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂))).const_mul _
  have hint₂ : Integrable X₂ P :=
    (integrable_trace_pow_wignerMatrix (n := n) (fun _ ↦ inferInstance)
      (fun ij hij ↦ (hξp ij hij).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁))
      (fun i hi ↦ (hηp i hi).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁))).const_mul _
  have hint₁₂ : Integrable (fun ω ↦ X₁ ω * X₂ ω) P := by
    have h := (integrable_trace_pow_mul_trace_pow_wignerMatrix hξp hηp).const_mul
      ((n : ℂ)⁻¹ * (n : ℂ)⁻¹)
    exact h.congr (.of_forall fun ω ↦ by dsimp [X₁, X₂]; ring)
  set μ₁ := ∫ ω', X₁ ω' ∂P
  set μ₂ := ∫ ω', X₂ ω' ∂P
  have hsub₁ : Integrable (fun ω ↦ X₁ ω * X₂ ω - X₁ ω * μ₂) P := hint₁₂.sub (hint₁.mul_const μ₂)
  have hsub₂ : Integrable (fun ω ↦ μ₁ * X₂ ω - μ₁ * μ₂) P :=
    (hint₂.const_mul μ₁).sub (integrable_const (μ₁ * μ₂))
  have hexpand : ∫ ω, (X₁ ω - μ₁) * (X₂ ω - μ₂) ∂P =
      (n : ℂ)⁻¹ * (n : ℂ)⁻¹ *
        ((∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P) -
          (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace ∂P) *
            ∫ ω, (wignerMatrix ξ η n ω ^ k₂).trace ∂P) := by
    simp_rw [sub_mul, mul_sub]
    rw [integral_sub hsub₁ hsub₂, integral_sub hint₁₂ (hint₁.mul_const μ₂),
      integral_sub (hint₂.const_mul μ₁) (integrable_const (μ₁ * μ₂)),
      integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul]
    have h12 : ∫ ω, X₁ ω * X₂ ω ∂P =
        (n : ℂ)⁻¹ * (n : ℂ)⁻¹ *
          ∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun ω ↦ by dsimp [X₁, X₂]; ring)
    rw [h12]
    simp only [μ₁, μ₂, X₁, X₂, integral_const_mul]
    ring
  rw [hexpand]
  exact norm_inv_mul_inv_mul_integral_trace_pow_mul_sub_wignerMatrix_le
    hindep hξzero hξp hηp hξ hη

/-- **Mean-square concentration of normalized Wigner traces.** Under independent entries in the
`n × n` corner in `L^(2k)` with centered strictly upper coordinates and `2k`-th absolute moments
bounded by `B`, the mean-square deviation of the normalized `k`-th trace of `Hₙ` is at most
`2 * k^(2k) * B / n²` for every `k` and `n`. -/
theorem integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∫ ω, ‖(n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P‖ ^ 2 ∂P ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2 := by
  -- Every power of a Hermitian matrix has real trace, so `Z ω * Z ω = (‖Z ω‖ ^ 2 : ℂ)`.
  set r : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace.re
  have hreal (ω : Ω) : ((r ω : ℝ) : ℂ) = (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace := by
    have htr : (((wignerMatrix ξ η n ω ^ k).trace.re : ℝ) : ℂ) =
        (wignerMatrix ξ η n ω ^ k).trace :=
      Complex.conj_eq_iff_re.mp (by
        rw [← Complex.star_def, ← trace_conjTranspose,
          ((wignerMatrix_isHermitian ξ η ω n).pow k).eq])
    simp only [r, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, htr]
  set Z : Ω → ℂ := fun ω ↦ (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace -
    ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P
  have hZ (ω : Ω) : Z ω = ((r ω - ∫ ω', r ω' ∂P : ℝ) : ℂ) := by
    have hmean : ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P =
        ((∫ ω', r ω' ∂P : ℝ) : ℂ) := by
      conv_lhs => enter [2, ω']; rw [← hreal ω']
      exact integral_complex_ofReal
    simp only [Z, hmean, ← hreal ω, Complex.ofReal_sub]
  have hsq (ω : Ω) : Z ω * Z ω = ((‖Z ω‖ ^ 2 : ℝ) : ℂ) := by
    rw [hZ ω, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_mul, sq]
  have heq : ‖∫ ω, Z ω * Z ω ∂P‖ = ∫ ω, ‖Z ω‖ ^ 2 ∂P := by
    simp_rw [hsq, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (integral_nonneg fun ω ↦ sq_nonneg _)
  have h2k : k + k = 2 * k := (two_mul k).symm
  have hdiv : (k + k) / 2 = k := by omega
  have hcov := norm_integral_inv_mul_trace_pow_wignerMatrix_sub_mul_le
    hindep hξzero (k₁ := k) (k₂ := k)
    (by simpa only [h2k] using hξp) (by simpa only [h2k] using hηp)
    (by simpa only [h2k] using hξ) (by simpa only [h2k] using hη)
  rw [hdiv, h2k] at hcov
  rw [← heq]
  exact hcov

/-- The mean-square fluctuation of the normalized `k`-th trace of a Wigner matrix tends to zero as
`n → ∞` under independent corner entries in `L^(2k)` with centered strictly upper coordinates and
uniformly bounded `2k`-th absolute moments, including for triangular arrays on varying probability
spaces. -/
theorem tendsto_integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦ ∫ ω,
      ‖(n : ℂ)⁻¹ * (wignerMatrix (ξ n) (η n) n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix (ξ n) (η n) n ω' ^ k).trace ∂P n‖ ^ 2 ∂P n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ sq_nonneg _)
    (fun n ↦ integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le
      (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim

end MomentBounds

end TauCeti
