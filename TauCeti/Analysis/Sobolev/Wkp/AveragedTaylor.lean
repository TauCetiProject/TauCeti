/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.RankOne
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedGradient.Integral
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.Analysis.Calculus.Taylor.Pairing.Polynomial
import TauCeti.Analysis.Sobolev.WeakDeriv.TaylorPairing
import TauCeti.Analysis.Sobolev.Wkp.IntegrationByParts
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Integral.ClosedBall

/-!
# Averaged Taylor pairings, weak-derivative commutation, and diameter bounds on `W^{k,p}`

On `W^{k,p}(Ω)` (`1 ≤ p ≤ ∞`, without smooth-function density):
* `TauCeti.Wkp.iteratedFDeriv_sum_setIntegral_iteratedFDeriv`: Brenner–Scott Proposition 4.1.17
  weak-derivative commutation for averaged Taylor pairings along arbitrary direction tuples.
* `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq` and
  `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`: coordinate-free spatial derivative
  commutation for compactly supported weights continuous on `tsupport`.
* `TauCeti.Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE`,
  `TauCeti.Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall`, and
  `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`: membership in
  `TauCeti.polynomialsDegLE` and explicit `Lᵖ → L^∞` diameter and chunkiness bounds.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Proposition 4.1.17 and Lemma 4.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open _root_.MeasureTheory IteratedGradient Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def averagedTaylorTerm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (mu : Measure E) (Omega : Opens E) (φ w : E → ℝ) (r : ℕ) : E → ℝ := fun x =>
  ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι, ∫ y in Omega,
    iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem fderiv_averagedTaylorTerm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn mu Omega u u' h) (d : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (d + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x : E) :
    fderiv ℝ (averagedTaylorTerm b mu Omega φ u (d + 1)) x h =
      averagedTaylorTerm b mu Omega φ u' d x := by
  unfold averagedTaylorTerm
  rw [hu.fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b _ d hφ hφc hφs x,
    Nat.factorial_succ]
  have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
  push_cast; field_simp [hd1]; ring

private theorem iteratedFDerivAlong_ofFn_sum_eq_of_ge
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Omega) :
    ∀ (j d : ℕ) (u : Wkp mu Omega p (j + 1)), ContDiff ℝ (d + j + 1) φ →
      ∀ (v : Fin (j + 1) → E) (x : E),
      iteratedFDerivAlong ℝ (List.ofFn v)
        (averagedTaylorTerm b mu Omega φ (value (j + 1) u) (d + j + 1)) x =
        averagedTaylorTerm b mu Omega φ
          (fun y => evalTupleL j (v ∘ Fin.rev) (iteratedGradient j u y)) d x
  | 0, d, u, hφ, v, x => by
      have hw : HasWeakLineDerivOn mu Omega (value 1 u)
          (fun y => evalTupleL 0 (v ∘ Fin.rev) (iteratedGradient 0 u y)) (v 0) :=
        ((hasWeakFDerivOn_value u).hasWeakLineDerivOn (v 0)).congr_ae_deriv
          (.of_forall fun _ => by simp [real_inner_comm])
      simp only [Nat.zero_add, List.ofFn_succ, List.ofFn_zero, iteratedFDerivAlong_cons_apply,
        iteratedFDerivAlong_nil]
      simp only [Nat.add_zero] at hφ ⊢
      exact fderiv_averagedTaylorTerm b hw d hφ hφc hφs x
  | j + 1, d, u, hφ, v, x => by
      have hidx : d + (j + 1) + 1 = (d + 1) + j + 1 := by omega
      have hih : iteratedFDerivAlong ℝ (List.ofFn (Fin.tail v))
          (averagedTaylorTerm b mu Omega φ (value (j + 1 + 1) u) (d + (j + 1) + 1)) =
          averagedTaylorTerm b mu Omega φ (fun y => evalTupleL j ((Fin.tail v) ∘ Fin.rev)
            (iteratedGradient j (lowerOrder (j + 1) u) y)) (d + 1) := funext fun x' => by
        rw [hidx, value_succ]
        exact iteratedFDerivAlong_ofFn_sum_eq_of_ge b hφc hφs j (d + 1)
          (lowerOrder (j + 1) u) (hφ.of_le (by norm_cast; omega)) (Fin.tail v) x'
      have hw : HasWeakLineDerivOn mu Omega
          (fun y => evalTupleL j ((Fin.tail v) ∘ Fin.rev)
            (iteratedGradient j (lowerOrder (j + 1) u) y))
          (fun y => evalTupleL (j + 1) (v ∘ Fin.rev) (iteratedGradient (j + 1) u y)) (v 0) :=
        (((hasWeakFDerivOn_iteratedGradient j u).clm_comp
          (evalTupleL j ((Fin.tail v) ∘ Fin.rev))).hasWeakLineDerivOn (v 0)).congr_ae_deriv
            (.of_forall fun _ => by
              simp only [evalTupleL_succ, ContinuousLinearMap.comp_apply,
                Fin.init_comp_rev, Function.comp_apply, Fin.rev_last, Fin.tail_def]
              rw [ContinuousLinearMap.apply_apply])
      simp only [Fin.tail_def] at hih
      rw [List.ofFn_succ, iteratedFDerivAlong_cons_apply, hih]
      exact fderiv_averagedTaylorTerm b hw d (hφ.of_le (by norm_cast; omega)) hφc hφs x

/-- **Mixed weak derivative commutation for averaged Taylor pairings.**
For `u ∈ W^{j+1,p}(Ω)` (`1 ≤ p ≤ ∞`),
`v : Fin (j + 1) → E`, and `φ : E → ℝ` of class `C^m` compactly supported in `Ω`, evaluating the
order-`(j + 1)` derivative of the degree-`m` averaged Taylor pairing of `u` at `v` yields the
degree-`(m - j - 1)` averaged Taylor pairing of the corresponding weak derivative component
`evalTupleL j (v ∘ Fin.rev) (Wkp.iteratedGradient j u ·)`. The reversal accounts for the order
of the nested continuous linear maps. If `m ≤ j`, both sides vanish. -/
theorem iteratedFDeriv_sum_setIntegral_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (j m : ℕ) (u : Wkp mu Omega p (j + 1))
    {φ : E → ℝ} (hφ : ContDiff ℝ m φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega)
    (x : E) (v : Fin (j + 1) → E) :
    iteratedFDeriv ℝ (j + 1) (fun x' => ∑ r ∈ Finset.range (m + 1),
      ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι, ∫ y in Omega,
        iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
          value (j + 1) u y ∂mu) x v =
      ∑ d ∈ Finset.range (m - j), ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
        ∫ y in Omega, iteratedFDeriv ℝ d (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z)
          y (b ∘ J) * evalTupleL j (v ∘ Fin.rev) (iteratedGradient j u y) ∂mu := by
  let term := averagedTaylorTerm b mu Omega φ (value (j + 1) u)
  have hloc : LocallyIntegrableOn (value (j + 1) u) Omega mu := Lp.locallyIntegrableOn _ Fact.out
  have hI : ∀ {k : ℕ∞ω} {r : ℕ}, r ≤ m → ∀ I : Fin r → ι, ContDiff ℝ k (fun x' =>
      ∫ y in Omega, iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z)
        y (b ∘ I) * value (j + 1) u y ∂mu) := fun hr I =>
    contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I)
      (hφ.of_le (by norm_cast)) hφc hφs hloc
  have hS_smooth : ∀ {k : ℕ∞ω} {r : ℕ}, r ≤ m → ContDiff ℝ k (fun x' => ∑ I : Fin r → ι,
      ∫ y in Omega, iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z)
        y (b ∘ I) * value (j + 1) u y ∂mu) := fun hr => ContDiff.sum fun I _ => hI hr I
  have hterm_smooth : ∀ {k : ℕ∞ω}, ∀ r ∈ Finset.range (m + 1), ContDiff ℝ k (term r) :=
    fun _ hr => contDiff_const.mul (hS_smooth (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)))
  have hvanish : ∀ r ≤ m, r ≤ j →
      iteratedFDerivAlong ℝ (List.ofFn v) (term r) x = 0 := fun r hrm hrj => by
    dsimp only [term]; unfold averagedTaylorTerm
    rw [congrFun (iteratedFDerivAlong_const_mul (n := ∞) (hS_smooth hrm) _ _ (by simp)) x,
      iteratedFDerivAlong_fun_sum (n := ∞) Finset.univ (fun I _ => hI hrm I) _ (by simp),
      Finset.sum_eq_zero fun I _ => by
        simpa only [Function.comp_apply] using
          iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero (b ∘ I)
            (hφ.of_le (by norm_cast)) hφc hφs hloc _ (by simp; omega) x, mul_zero]
  have hgoal : (fun x' => ∑ r ∈ Finset.range (m + 1), term r x') =
      fun x' => ∑ r ∈ Finset.range (m + 1), ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
        ∫ y in Omega, iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z)
          y (b ∘ I) * value (j + 1) u y ∂mu := by ext x'; simp [term, averagedTaylorTerm]
  rw [← hgoal, ← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv
      (ContDiff.sum hterm_smooth) v x,
    iteratedFDerivAlong_fun_sum (n := ∞) _ hterm_smooth _ (by simp)]
  rcases lt_or_ge j m with hjm | hmj
  · have hm_split : m + 1 = (j + 1) + (m - j) := by omega
    rw [hm_split, Finset.sum_range_add, Finset.sum_eq_zero fun r hr =>
      hvanish r ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)).trans hjm.le)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)), zero_add]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm : d + j + 1 ≤ m := by have := Finset.mem_range.1 hd; omega
    have heq_idx : j + 1 + d = d + j + 1 := by omega
    dsimp only [term]; rw [heq_idx]
    exact iteratedFDerivAlong_ofFn_sum_eq_of_ge b hφc hφs j d u
      (hφ.of_le (by norm_cast)) v x
  · rw [Nat.sub_eq_zero_of_le hmj, Finset.range_zero, Finset.sum_empty]
    exact Finset.sum_eq_zero fun r hr => hvanish r (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))
      ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)).trans hmj)

/-- **Coordinate-free spatial derivative of a first-order contracted weak-gradient integral.** -/
theorem fderiv_setIntegral_fullContractL_sub_zero_eq
    (u : Wkp mu Omega p 1) {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ))
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega, fullContractL 0 (x' - y) (iteratedGradient 0 u y) * φ y ∂mu)
      x h = ∫ y in Omega, φ y * value 0 (lineDerivL h 0 u) y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  let G := iteratedGradient 0 u
  have hw₁ : HasWeakLineDerivOn mu Omega (value 1 u) (fun y => ⟪h, G y⟫_ℝ) h :=
    ((hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
      (.of_forall fun _ => by simp [G, real_inner_comm])
  have hae := hw₁.ae_eq (hasWeakLineDerivOn_lineDerivL h 0 u)
  rw [fderiv_setIntegral_fullContractL_sub_mul_eq b 0 (Lp.locallyIntegrableOn G Fact.out) hφ hφc
    hφs x h]
  refine integral_congr_ae (hae.mono fun y hy => ?_)
  dsimp only at hy ⊢
  rw [← hy, ← (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E))).symm.sum_comp]
  congr 1
  calc ∑ i, ∑ p : Fin 1, ⟪b i, h⟫_ℝ * (∏ _ ∈ Finset.univ.erase p, ⟪b i, x - y⟫_ℝ) *
          evalTupleL 0 (b ∘ (Equiv.funUnique (Fin 1) _).symm i) (G y)
      = ∑ i, ⟪⟪b i, h⟫_ℝ • b i, G y⟫_ℝ :=
        Finset.sum_congr rfl fun _ _ => by simp [inner_smul_left]
    _ = ⟪h, G y⟫_ℝ := by rw [← sum_inner, b.sum_repr' h]

private theorem fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {ψ : E → ℝ} (hψ : ContDiff ℝ (k + 2) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      fullContractL (k + 1) (x' - y) (iteratedGradient (k + 1) u y) * ψ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        fullContractL k (x - y) (iteratedGradient k (lineDerivL h (k + 1) u) y) * ψ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  rw [funext (setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b (k + 1) u hψ hψc hψs),
    (hasWeakLineDerivOn_lineDerivL h (k + 1) u
      ).fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b ((-1 : ℝ) ^ (k + 2))
      (k + 1) hψ hψc hψs x,
    setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b k (lineDerivL h (k + 1) u)
      (hψ.of_le (by exact_mod_cast Nat.le_succ (k + 1))) hψc hψs x, pow_succ (-1 : ℝ) (k + 1)]
  push_cast; ring

/-- **Coordinate-free spatial derivative of a higher-order contracted weak-gradient integral.** -/
theorem fderiv_setIntegral_fullContractL_sub_succ_eq (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ))
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      fullContractL (k + 1) (x' - y) (iteratedGradient (k + 1) u y) * φ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        fullContractL k (x - y) (iteratedGradient k (lineDerivL h (k + 1) u) y) * φ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  let G₁ := iteratedGradient (k + 1) u
  let G₂ := iteratedGradient k (lineDerivL h (k + 1) u)
  have hG₁ : LocallyIntegrableOn G₁ Omega mu := Lp.locallyIntegrableOn G₁ Fact.out
  have hG₂ : LocallyIntegrableOn G₂ Omega mu := Lp.locallyIntegrableOn G₂ Fact.out
  let W₁ : E → ℝ := fun y => ∑ I : Fin (k + 2) → Fin (Module.finrank ℝ E),
    ∑ p : Fin (k + 2), ⟪b (I p), h⟫_ℝ * (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) *
      evalTupleL (k + 1) (b ∘ I) (G₁ y)
  let W₂ : E → ℝ := fun y => (k + 2 : ℝ) * fullContractL k (x - y) (G₂ y)
  have hW₁ : LocallyIntegrableOn W₁ Omega mu :=
    locallyIntegrableOn_finsetSum _ fun I _ => locallyIntegrableOn_finsetSum _ fun p _ => by
      have hc : Continuous fun y => ⟪b (I p), h⟫_ℝ *
          ∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ :=
        continuous_const.mul (continuous_finsetProd _ fun l _ =>
          (innerSL ℝ (b (I l))).continuous.comp (continuous_const.sub continuous_id))
      simpa only [Function.comp_apply, smul_eq_mul, mul_assoc] using
        ((evalTupleL (k + 1) (b ∘ I)).locallyIntegrableOn_comp hG₁).continuousOn_smul_of_isOpen
          Omega.isOpen hc.continuousOn
  have hW₂ : LocallyIntegrableOn W₂ Omega mu := by
    simpa only [W₂, smul_eq_mul, Function.comp_apply, Pi.sub_apply, id_eq] using
      (hG₂.continuousOn_clm_apply Omega.isOpen.isLocallyClosed
        (((contDiff_fullContractL (n := 0) k).continuous.comp
          (continuous_const.sub continuous_id)).continuousOn)).continuousOn_smul_of_isOpen
        Omega.isOpen (continuousOn_const (c := (k + 2 : ℝ)))
  have hrhs : ∀ g : E → ℝ, (k + 2 : ℝ) *
      (∫ y in Omega, fullContractL k (x - y) (G₂ y) * g y ∂mu) = ∫ y in Omega, g y * W₂ y ∂mu :=
    fun g => by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => by dsimp only [W₂]; ring
  have hae : ∀ᵐ y ∂mu, y ∈ (Omega : Set E) → (W₁ - W₂) y = 0 :=
    Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hW₁.sub hW₂) fun g hg hgc hgs => by
      have hwhole : ∀ w : E → ℝ, ∫ y, g y • w y ∂mu = ∫ y in Omega, g y * w y ∂mu := fun w => by
        simp_rw [smul_eq_mul]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy => by
          rw [image_eq_zero_of_notMem_tsupport (hy <| hgs ·), zero_mul]).symm
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub
          (hW₁.integrable_smul_left_of_hasCompactSupport hg.continuous.continuousOn hgc hgs)
          (hW₂.integrable_smul_left_of_hasCompactSupport hg.continuous.continuousOn hgc hgs),
        hwhole W₁, hwhole W₂, sub_eq_zero, ← hrhs g,
        ← fderiv_setIntegral_fullContractL_sub_mul_eq b (k + 1) hG₁
          hg.continuous.continuousOn hgc hgs x h]
      exact fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff k u
        (hg.of_le (by simp)) hgc hgs x h
  rw [fderiv_setIntegral_fullContractL_sub_mul_eq b (k + 1) hG₁ hφ hφc hφs x h, hrhs φ]
  refine integral_congr_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).2 ?_)
  exact hae.mono fun y hy hΩ => by simpa only [W₁] using congrArg (φ y * ·) (sub_eq_zero.1 (hy hΩ))

/-- On `W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), `x ↦ ∫_Ω fullContractL k (x - y) (iteratedGradient k u y) φ y`
belongs to `polynomialsDegLE ι m` whenever `k + 1 ≤ m` and `φ` is continuous on its compact
`tsupport φ ⊆ Ω`. -/
theorem setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE
    {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ ι)} {k m : ℕ} (hkm : k + 1 ≤ m)
    (u : Wkp μ Ω p (k + 1)) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (fun x => ∫ y in Ω, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂μ) ∈
      polynomialsDegLE ι m :=
  setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE hkm (Lp.locallyIntegrableOn _ Fact.out)
    hφ hφc hφs

/-- **Order-zero cutoff integral bound on `W^{k,p}(Ω)`.** -/
theorem norm_setIntegral_value_mul_le_of_support_subset_closedBall
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p k)
    {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ} (hρ : 0 < ρ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, value k u y * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) * ‖value k u‖ := by
  refine Lp.norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd (value k u) hρ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
  rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hφ y hy) (norm_nonneg _)

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted weak
derivatives.** -/
theorem norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖iteratedGradient k u‖ :=
  norm_setIntegral_fullContractL_sub_mul_le hΩ_bdd k (iteratedGradient k u) hx hρ hdiam hsupp hφ

end TauCeti.Wkp
