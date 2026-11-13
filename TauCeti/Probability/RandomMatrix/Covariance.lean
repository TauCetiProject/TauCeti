/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Connected
public import TauCeti.Probability.RandomMatrix.MomentBounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Connected two-trace expansion and covariance bounds for Wigner moments

Expanding `E[tr(Hₙ ^ k₁) tr(Hₙ ^ k₂)] - E[tr(Hₙ ^ k₁)] E[tr(Hₙ ^ k₂)]` into pairs of closed walks
`(w₁, w₂)` eliminates two classes of pairs under independent centered entries:

* pairs whose unordered cyclic edge sets are disjoint decouple by independence, so
  `E[P₁ P₂] = E[P₁] E[P₂]`;
* pairs whose combined unordered cyclic edge multiset on `Fin k₁ ⊕ Fin k₂` contains an edge
  traversed only once satisfy `E[P₁ P₂] = 0` and either `E[P₁] = 0` or `E[P₂] = 0`.

Every surviving pair shares at least one unordered cyclic edge and has no singleton unordered
cyclic edge across `Fin k₁ ⊕ Fin k₂`. By
`TauCeti.card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge`, such a pair visits
at most `(k₁ + k₂) / 2` vertices in total, hence there are at most
`n^((k₁ + k₂) / 2) * ((k₁ + k₂) / 2)^(k₁ + k₂)` surviving pairs. Under a uniform `(k₁ + k₂)`-th
absolute moment bound `B` on a probability space, each surviving pair contributes at most
`2 * (√n)⁻^(k₁ + k₂) * B`, yielding an `O(n⁻²)` bound for normalized two-trace covariances and for
the mean-square fluctuations of normalized Wigner traces of every order.

## Main results

* `TauCeti.indepFun_prod_wignerMatrix_apply_of_disjoint` and
  `TauCeti.integral_prod_mul_prod_wignerMatrix_apply_of_disjoint`: entry products reading disjoint
  unordered positions are independent and factor in expectation.
* `TauCeti.integral_trace_pow_mul_trace_pow_sub_wignerMatrix`: the connected singleton-free
  two-trace expansion for `E[tr(Hₙ ^ k₁) tr(Hₙ ^ k₂)] - E[tr(Hₙ ^ k₁)] E[tr(Hₙ ^ k₂)]`.
* `TauCeti.norm_integral_centered_trace_pow_mul_wignerMatrix_le`: quantitative `O(n⁻²)` bound on
  the centered normalized two-trace expectation for all `k₁, k₂, n : ℕ`.
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
open scoped Topology ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

section DisjointEdges

private def entryCoord {n : ℕ} (i j : Fin n) : StrictUpper ⊕ ℕ :=
  if h : i.val < j.val then .inl ⟨(i, j), h⟩
  else if h' : j.val < i.val then .inl ⟨(j, i), h'⟩ else .inr i

private theorem entryCoord_eq_entryCoord_iff {n : ℕ} {i j i' j' : Fin n} :
    entryCoord i j = entryCoord i' j' ↔ s(i, j) = s(i', j') := by
  unfold entryCoord
  split_ifs <;> simp [Fin.ext_iff] <;> omega

private def orientCoord {n : ℕ} (i j : Fin n) (z : ℂ) : ℂ :=
  if i.val < j.val then z else if j.val < i.val then star z else (z.re : ℂ)

private theorem measurable_orientCoord {n : ℕ} (i j : Fin n) : Measurable (orientCoord i j) := by
  unfold orientCoord
  split_ifs
  · exact measurable_id
  · exact continuous_star.measurable
  · exact Complex.measurable_ofReal.comp Complex.measurable_re

omit [MeasurableSpace Ω] in
private theorem wignerMatrix_apply_eq_orientCoord {n : ℕ} (ω : Ω) (i j : Fin n) :
    wignerMatrix ξ η n ω i j = (Real.sqrt n : ℂ)⁻¹ *
      orientCoord i j (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (entryCoord i j) ω) := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [orientCoord, entryCoord, h]
  · obtain rfl := Fin.ext h
    simp [orientCoord, entryCoord]
  · simp [orientCoord, entryCoord, h, h.not_gt]

private theorem aemeasurable_wignerMatrix_apply
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    {n : ℕ} (i j : Fin n) : AEMeasurable (fun ω ↦ wignerMatrix ξ η n ω i j) P := by
  simp_rw [wignerMatrix_apply_eq_orientCoord]
  exact measurable_const.aemeasurable.mul
    ((measurable_orientCoord i j).comp_aemeasurable
      (aemeasurable_sumElim_ofReal hξm hηm (entryCoord i j)))

/-- **Edge-disjoint Wigner products are independent.** For independent array coordinates, two
finite products of Wigner entries reading disjoint sets of unordered positions are independent. No
centering or finite-moment assumption is required. -/
theorem indepFun_prod_wignerMatrix_apply_of_disjoint {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    {n : ℕ} (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    IndepFun
      (fun ω ↦ ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s))
      (fun ω ↦ ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) P := by
  classical
  set X : StrictUpper ⊕ ℕ → Ω → ℂ := fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k
  set e₁ : ι₁ → StrictUpper ⊕ ℕ := fun s ↦ entryCoord (u₁ s) (v₁ s)
  set e₂ : ι₂ → StrictUpper ⊕ ℕ := fun t ↦ entryCoord (u₂ t) (v₂ t)
  set S₁ : Finset (StrictUpper ⊕ ℕ) := univ.image e₁
  set S₂ : Finset (StrictUpper ⊕ ℕ) := univ.image e₂
  have hS : Disjoint S₁ S₂ := by
    rw [disjoint_left]
    intro k hk₁ hk₂
    obtain ⟨s, -, rfl⟩ := mem_image.mp hk₁
    obtain ⟨t, -, htk⟩ := mem_image.mp hk₂
    exact hdisj s t (entryCoord_eq_entryCoord_iff.mp htk.symm)
  set φ₁ : (S₁ → ℂ) → ℂ := fun g ↦ ∏ s ∈ univ.attach,
    (Real.sqrt n : ℂ)⁻¹ * orientCoord (u₁ s.1) (v₁ s.1) (g ⟨e₁ s.1, Finset.mem_image_of_mem e₁ s.2⟩)
  set φ₂ : (S₂ → ℂ) → ℂ := fun g ↦ ∏ t ∈ univ.attach,
    (Real.sqrt n : ℂ)⁻¹ * orientCoord (u₂ t.1) (v₂ t.1) (g ⟨e₂ t.1, Finset.mem_image_of_mem e₂ t.2⟩)
  have hφ₁ : Measurable φ₁ := Finset.measurable_prod _ fun s _ ↦
    measurable_const.mul ((measurable_orientCoord _ _).comp (measurable_pi_apply _))
  have hφ₂ : Measurable φ₂ := Finset.measurable_prod _ fun t _ ↦
    measurable_const.mul ((measurable_orientCoord _ _).comp (measurable_pi_apply _))
  have hind := (hindep.indepFun_finset₀ S₁ S₂ hS (aemeasurable_sumElim_ofReal hξm hηm)).comp
    hφ₁ hφ₂
  refine hind.congr (.of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ ?_)
  · simp only [Function.comp_apply, φ₁, ← prod_attach univ, wignerMatrix_apply_eq_orientCoord,
      X, e₁]
  · simp only [Function.comp_apply, φ₂, ← prod_attach univ, wignerMatrix_apply_eq_orientCoord,
      X, e₂]

/-- **Factorization of edge-disjoint Wigner products.** When two finite products of Wigner entries
read disjoint sets of unordered positions and the array coordinates are independent, the integral
of their product equals the product of their integrals. -/
theorem integral_prod_mul_prod_wignerMatrix_apply_of_disjoint {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂]
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    {n : ℕ} (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    ∫ ω, (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) *
        (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) ∂P =
      (∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P :=
  (indepFun_prod_wignerMatrix_apply_of_disjoint hξm hηm hindep u₁ v₁ u₂ v₂
    hdisj).integral_fun_mul_eq_mul_integral
    (Finset.aestronglyMeasurable_fun_prod univ fun s _ ↦
      (aemeasurable_wignerMatrix_apply hξm hηm (u₁ s) (v₁ s)).aestronglyMeasurable)
    (Finset.aestronglyMeasurable_fun_prod univ fun t _ ↦
      (aemeasurable_wignerMatrix_apply hξm hηm (u₂ t) (v₂ t)).aestronglyMeasurable)

end DisjointEdges

section ConnectedExpansion

private theorem integral_prod_mul_prod_sub_eq_zero_of_not_connected
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k₁ k₂ n : ℕ} (w₁ : Fin k₁ → Fin n) (w₂ : Fin k₂ → Fin n)
    (hnot : ¬ ((∃ i j, s(w₁ i, w₁ (finRotate k₁ i)) = s(w₂ j, w₂ (finRotate k₂ j))) ∧
      ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t)) :
    (∫ ω, (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i))) *
        (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j))) ∂P) -
      (∫ ω, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i)) ∂P) *
        ∫ ω, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j)) ∂P = 0 := by
  by_cases hshare : ∃ i j, s(w₁ i, w₁ (finRotate k₁ i)) = s(w₂ j, w₂ (finRotate k₂ j))
  · have hsingle : ∃ t : Fin k₁ ⊕ Fin k₂, ∀ t',
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
        Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t → t' = t := by
      by_contra! h
      exact hnot ⟨hshare, fun t ↦ let ⟨t', heq, hne⟩ := h t; ⟨t', hne, heq⟩⟩
    obtain ⟨t, ht⟩ := hsingle
    let u : Fin k₁ ⊕ Fin k₂ → Fin n := Sum.elim w₁ w₂
    let v : Fin k₁ ⊕ Fin k₂ → Fin n :=
      Sum.elim (fun i ↦ w₁ (finRotate k₁ i)) (fun j ↦ w₂ (finRotate k₂ j))
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
      exact integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero u v
        fun s hs ↦ ht s (by simpa only [huv] using hs)
    have hfac_zero : (∫ ω, ∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k₁ i)) ∂P) *
        ∫ ω, ∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k₂ j)) ∂P = 0 := by
      cases t with
      | inl i =>
        rw [integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero w₁
          (fun i ↦ w₁ (finRotate k₁ i)) (t := i) fun i' hi' ↦ Sum.inl.inj (ht (.inl i') hi'),
          zero_mul]
      | inr j =>
        rw [integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero w₂
          (fun j ↦ w₂ (finRotate k₂ j)) (t := j) fun j' hj' ↦ Sum.inr.inj (ht (.inr j') hj'),
          mul_zero]
    rw [hprod_zero, hfac_zero, sub_zero]
  · exact sub_eq_zero.mpr (integral_prod_mul_prod_wignerMatrix_apply_of_disjoint
      hξm hηm hindep w₁ (fun i ↦ w₁ (finRotate k₁ i)) w₂ (fun j ↦ w₂ (finRotate k₂ j))
      fun i j hij ↦ hshare ⟨i, j, hij⟩)

/-- **Connected two-trace expansion of Wigner moments.** For independent centered entries in
`L^(k₁ + k₂)` on a finite measure space, with `k₁ ≠ 0` and `k₂ ≠ 0`, subtracting the product of
expected traces from the expected product of traces restricts the double walk sum to pairs
`(w₁, w₂)` that share at least one unordered cyclic edge and have no singleton unordered cyclic
edge across `Fin k₁ ⊕ Fin k₂`. -/
theorem integral_trace_pow_mul_trace_pow_sub_wignerMatrix [IsFiniteMeasure P]
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P) (n : ℕ) :
    (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P) -
        (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace ∂P) *
          (∫ ω, (wignerMatrix ξ η n ω ^ k₂).trace ∂P) =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n) with
        (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
          ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t,
        ((∫ ω, (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
            (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) ∂P) -
          (∫ ω, ∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i)) ∂P) *
            ∫ ω, ∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)) ∂P) := by
  have hξ₁ (ij : StrictUpper) : MemLp (ξ ij) k₁ P :=
    (hξp ij).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂)
  have hη₁ (i : ℕ) : MemLp (η i) k₁ P :=
    (hηp i).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂)
  have hξ₂ (ij : StrictUpper) : MemLp (ξ ij) k₂ P :=
    (hξp ij).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁)
  have hη₂ (i : ℕ) : MemLp (η i) k₂ P :=
    (hηp i).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁)
  have hint₁₂ (p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n)) :
      Integrable (fun ω ↦ (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
        (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j)))) P := by
    have h := integrable_prod_wignerMatrix_apply
      (ι := Fin k₁ ⊕ Fin k₂)
      (by simpa [Fintype.card_sum] using hξp) (by simpa [Fintype.card_sum] using hηp)
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
      (by simpa using hξ₁) (by simpa using hη₁) _ _,
    integral_finsetSum _ fun w₂ _ ↦ integrable_prod_wignerMatrix_apply
      (by simpa using hξ₂) (by simpa using hη₂) _ _,
    hmul_int, ← sum_sub_distrib]
  symm
  apply sum_filter_of_ne
  intro p _ hp
  by_contra hnot
  exact hp (integral_prod_mul_prod_sub_eq_zero_of_not_connected
    (fun ij ↦ (hξp ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηp i).aestronglyMeasurable.aemeasurable)
    hindep hξzero hηzero p.1 p.2 hnot)

end ConnectedExpansion

section MomentBounds

/-- On a probability space, a uniform `(card ι₁ + card ι₂)`-th absolute moment bound `B` controls
the product of two expected products of Wigner entries, without independence or centering. -/
theorem norm_integral_prod_wignerMatrix_apply_mul_integral_prod_le [IsProbabilityMeasure P]
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (Fintype.card ι₁ + Fintype.card ι₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (Fintype.card ι₁ + Fintype.card ι₂ : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (Fintype.card ι₁ + Fintype.card ι₂) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (Fintype.card ι₁ + Fintype.card ι₂) ∂P ≤ B)
    {n : ℕ} (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n) :
    ‖(∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ (Fintype.card ι₁ + Fintype.card ι₂) * B := by
  set K := Fintype.card ι₁ + Fintype.card ι₂
  cases isEmpty_or_nonempty (ι₁ ⊕ ι₂) with
  | inl hempty =>
    have : IsEmpty ι₁ := ⟨fun s ↦ hempty.false (.inl s)⟩
    have : IsEmpty ι₂ := ⟨fun t ↦ hempty.false (.inr t)⟩
    have hK : K = 0 := by simp [K]
    simpa [hK] using hη 0
  | inr hne =>
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

/-- If the entries of the Wigner array lie in `L^(2k)` on a finite measure space, the trace of
`Hₙ ^ k` lies in `L²` for every `k` and `n`, without independence or centering. -/
theorem memLp_two_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) 2 P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    refine memLp_finsetSum univ fun w _ ↦ ?_
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have h := MemLp.fun_prod (s := (univ : Finset (Fin k)))
      (p := fun _ ↦ ((2 * k : ℕ) : ℝ≥0∞))
      fun t _ ↦ memLp_wignerMatrix_apply hξp hηp (w t) (w (finRotate k t))
    have hexp : (∑ _t : Fin k, ((2 * k : ℕ) : ℝ≥0∞)⁻¹)⁻¹ = 2 := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_ofNat]
      rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_comm 2⁻¹,
        ← mul_assoc, ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k), one_mul, inv_inv]
    rwa [hexp] at h

private theorem pow_div_two_mul_inv_sqrt_pow_le {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (n : ℝ) ^ (K / 2) * (Real.sqrt n)⁻¹ ^ K ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt_ge : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hinv_le : (Real.sqrt n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt_ge
  have hsplit : (Real.sqrt n)⁻¹ ^ K =
      (Real.sqrt n)⁻¹ ^ (2 * (K / 2)) * (Real.sqrt n)⁻¹ ^ (K % 2) := by
    rw [← pow_add, Nat.div_add_mod]
  have hpow2 : (n : ℝ) ^ (K / 2) * (Real.sqrt n)⁻¹ ^ (2 * (K / 2)) = 1 := by
    rw [inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n),
      mul_inv_cancel₀ (pow_ne_zero _ (by positivity))]
  rw [hsplit, ← mul_assoc, hpow2, one_mul]
  rcases Nat.mod_two_eq_zero_or_one K with h0 | h1
  · simp [h0]
  · simp [h1, hinv_le]

private theorem norm_integral_prod_mul_prod_sub_wignerMatrix_le [IsProbabilityMeasure P]
    {k₁ k₂ n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B)
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
      (by simpa [Fintype.card_sum] using hξp) (by simpa [Fintype.card_sum] using hηp)
      (by simpa [Fintype.card_sum] using hξ) (by simpa [Fintype.card_sum] using hη)
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

/-- **Normalized two-trace covariance bound (uncentered difference form).** On a probability space,
under independent centered entries in `L^(k₁ + k₂)` with `(k₁ + k₂)`-th absolute moments bounded by
`B`, the covariance of the normalized traces `(n : ℂ)⁻¹ * tr(Hₙ ^ k₁)` and
`(n : ℂ)⁻¹ * tr(Hₙ ^ k₂)` has norm at most `2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / n²` for all
`k₁, k₂, n : ℕ`. -/
theorem norm_inv_mul_inv_mul_integral_trace_pow_mul_sub_wignerMatrix_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k₁ k₂ n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (n : ℂ)⁻¹ *
        ((∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace ∂P) -
          (∫ ω, (wignerMatrix ξ η n ω ^ k₁).trace ∂P) *
            ∫ ω, (wignerMatrix ξ η n ω ^ k₂).trace ∂P)‖ ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 := by
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp only [pow_zero, trace_one, Fintype.card_fin, integral_const_mul, integral_const,
      probReal_univ, one_smul, sub_self, mul_zero, norm_zero]
    positivity
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp only [pow_zero, trace_one, Fintype.card_fin, integral_mul_const, integral_const,
      probReal_univ, one_smul, sub_self, mul_zero, norm_zero]
    positivity
  have : NeZero n := ⟨hn⟩
  set S : Finset ((Fin k₁ → Fin n) × (Fin k₂ → Fin n)) :=
    {p | (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
      ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
        Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
          (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
        Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
          (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t}
  have hcard : #S ≤ n ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
    simpa [S] using card_filter_shared_edge_and_no_singleton_edge_le (β := Fin n) k₁ k₂
  rw [integral_trace_pow_mul_trace_pow_sub_wignerMatrix hindep hξzero hηzero hk₁ hk₂ hξp hηp n,
    norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ‖∑ p ∈ S, _‖
      ≤ (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * (#S * (2 * ((Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B))) := by
        gcongr
        exact (norm_sum_le S _).trans ((sum_le_sum fun p _ ↦
          norm_integral_prod_mul_prod_sub_wignerMatrix_le hξp hηp hξ hη p).trans (by simp))
    _ ≤ (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
        ((n ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) : ℕ) *
          (2 * ((Real.sqrt n)⁻¹ ^ (k₁ + k₂) * B))) := by gcongr
    _ = (2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2) *
        ((n : ℝ) ^ ((k₁ + k₂) / 2) * (Real.sqrt n)⁻¹ ^ (k₁ + k₂)) := by
        push_cast
        have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp
    _ ≤ 2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 :=
        mul_le_of_le_one_right (by positivity)
          (pow_div_two_mul_inv_sqrt_pow_le hn (k₁ + k₂))

private theorem integrable_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    exact integrable_finsetSum _ fun w _ ↦ integrable_prod_wignerMatrix_apply
      (by simpa using hξp) (by simpa using hηp) _ _

private theorem integrable_trace_pow_mul_trace_pow_wignerMatrix [IsFiniteMeasure P] {k₁ k₂ : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P) (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P) (n : ℕ) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k₁).trace *
      (wignerMatrix ξ η n ω ^ k₂).trace) P := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact (integrable_trace_pow_wignerMatrix
      (by simpa using hξp) (by simpa using hηp) n).const_mul _
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact (integrable_trace_pow_wignerMatrix
      (by simpa using hξp) (by simpa using hηp) n).mul_const _
  have hprod (ω : Ω) : (wignerMatrix ξ η n ω ^ k₁).trace * (wignerMatrix ξ η n ω ^ k₂).trace =
      ∑ p : (Fin k₁ → Fin n) × (Fin k₂ → Fin n),
        (∏ i, wignerMatrix ξ η n ω (p.1 i) (p.1 (finRotate k₁ i))) *
          (∏ j, wignerMatrix ξ η n ω (p.2 j) (p.2 (finRotate k₂ j))) := by
    rw [trace_pow_eq_sum_prod _ hk₁, trace_pow_eq_sum_prod _ hk₂, sum_mul_sum,
      ← univ_product_univ, sum_product]
  simp_rw [hprod]
  refine integrable_finsetSum _ fun p _ ↦ ?_
  have h := integrable_prod_wignerMatrix_apply (ι := Fin k₁ ⊕ Fin k₂)
    (by simpa [Fintype.card_sum] using hξp) (by simpa [Fintype.card_sum] using hηp)
    (Sum.elim p.1 p.2) (Sum.elim (p.1 ∘ finRotate k₁) (p.2 ∘ finRotate k₂))
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] using h

/-- **Centered normalized two-trace covariance bound.** On a probability space, under independent
centered entries in `L^(k₁ + k₂)` with `(k₁ + k₂)`-th absolute moments bounded by `B`, the expected
product of centered normalized traces of `Hₙ ^ k₁` and `Hₙ ^ k₂` has norm at most
`2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / n²` for all `k₁, k₂, n : ℕ`. -/
theorem norm_integral_centered_trace_pow_mul_wignerMatrix_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k₁ k₂ n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
    ‖∫ ω, (((n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₁).trace -
          ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k₁).trace ∂P) *
        ((n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₂).trace -
          ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k₂).trace ∂P)) ∂P‖ ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n : ℝ) ^ 2 := by
  set X₁ : Ω → ℂ := fun ω ↦ (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₁).trace
  set X₂ : Ω → ℂ := fun ω ↦ (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k₂).trace
  have hint₁ : Integrable X₁ P :=
    (integrable_trace_pow_wignerMatrix
      (fun ij ↦ (hξp ij).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂))
      (fun i ↦ (hηp i).mono_exponent (by exact_mod_cast Nat.le_add_right k₁ k₂)) n).const_mul _
  have hint₂ : Integrable X₂ P :=
    (integrable_trace_pow_wignerMatrix
      (fun ij ↦ (hξp ij).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁))
      (fun i ↦ (hηp i).mono_exponent (by exact_mod_cast Nat.le_add_left k₂ k₁)) n).const_mul _
  have hint₁₂ : Integrable (fun ω ↦ X₁ ω * X₂ ω) P := by
    have h := (integrable_trace_pow_mul_trace_pow_wignerMatrix hξp hηp n).const_mul
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
    hindep hξzero hηzero hξp hηp hξ hη

/-- **Mean-square concentration of normalized Wigner traces.** On a probability space, under
independent centered entries in `L^(2k)` with `2k`-th absolute moments bounded by `B`, the
mean-square deviation of the normalized `k`-th trace of `Hₙ` is at most `2 * k^(2k) * B / n²` for
every `k` and `n`. -/
theorem integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
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
  have hcov := norm_integral_centered_trace_pow_mul_wignerMatrix_le
    hindep hξzero hηzero (k₁ := k) (k₂ := k) (n := n)
    (by simpa only [h2k] using hξp) (by simpa only [h2k] using hηp)
    (by simpa only [h2k] using hξ) (by simpa only [h2k] using hη)
  rw [hdiv, h2k] at hcov
  rw [← heq]
  exact hcov

/-- The mean-square fluctuation of the normalized `k`-th trace of a Wigner matrix tends to zero as
`n → ∞` under uniformly bounded `2k`-th absolute moments, including for triangular arrays on
varying probability spaces. -/
theorem tendsto_integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦ ∫ ω,
      ‖(n : ℂ)⁻¹ * (wignerMatrix (ξ n) (η n) n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix (ξ n) (η n) n ω' ^ k).trace ∂P n‖ ^ 2 ∂P n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ sq_nonneg _)
    (fun n ↦ integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim

end MomentBounds

end TauCeti
