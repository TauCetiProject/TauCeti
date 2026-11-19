/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedGradient.Integral
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.Analysis.Calculus.Taylor.Pairing.Polynomial
import TauCeti.Analysis.Sobolev.WeakDeriv.TaylorPairing
import TauCeti.Analysis.Sobolev.Wkp.IntegrationByParts
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Integral.ClosedBall

/-!
# Averaged Taylor pairings, weak-derivative commutation, and diameter bounds on `W^{k,p}`

This file collects the `W^{k,p}` specializations (`1 ≤ p ≤ ∞`, including `p = ∞`, without
smooth-function density) built from the lower-level pairing, contraction, polynomiality, and
weak-derivative modules:

* General Taylor-monomial pairings, powerset expansions, smoothness, spatial differentiation, and
  high-order vanishing live in `TauCeti.Analysis.Calculus.Taylor.Pairing.Basic`.
* Orthonormal-basis expansions, spatial differentiation, and the general `Lᵖ → L^∞` bound for
  contracted `IteratedGradient` fields live in
  `TauCeti.Analysis.Calculus.IteratedGradient.Integral`.
* Membership of general Taylor-monomial and contracted-field pairings in `TauCeti.polynomialsDegLE`
  lives in `TauCeti.Analysis.Calculus.Taylor.Pairing.Polynomial`.
* Single-step weak-derivative commutation for Taylor-monomial pairings lives in
  `TauCeti.Analysis.Sobolev.WeakDeriv.TaylorPairing`.

Here we specialize those ingredients to `u ∈ W^{k,p}(Ω)`:

1. **Higher-order commutation (`section WkpCommutation`):** contracting `iteratedGradientChain` of
   the degree-`m` averaged Taylor sum of `u ∈ W^{j+1,p}(Ω)` gives the degree-`(m - j - 1)` sum for
   the `j`-th contracted weak derivative
   (`TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`), and
   differentiating shifted full contractions in `x` commutes with `TauCeti.Wkp.lineDerivL` for
   arbitrary compactly supported weights `φ` continuous on `tsupport φ`
   (`TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq`,
   `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`).
2. **Polynomiality (`section Polynomiality`):** the contracted highest-derivative integral of
   `u ∈ W^{k+1,p}(Ω)` lies in `TauCeti.polynomialsDegLE ι m` when `k + 1 ≤ m`
   (`TauCeti.Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE`).
3. **`Lᵖ(Ω) → L^∞` diameter and chunkiness bounds (`section Bounds`):** explicit `diam Ω` and
   chunkiness scaling for order-zero and contracted weak-derivative pairings against cutoffs
   supported in `closedBall x₀ ρ`
   (`TauCeti.Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall`,
   `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`).

## Main declarations

* `TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`:
  Brenner–Scott Prop. 4.1.17 commutation for all `j, m : ℕ` on `W^{j+1,p}(Ω)`.
* `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq` and
  `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`: coordinate-free spatial derivative
  commutation for compactly supported weights continuous on their `tsupport`.
* `TauCeti.Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE`:
  membership in `TauCeti.polynomialsDegLE ι m`.
* `TauCeti.Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall` and
  `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`: explicit diameter and
  chunkiness bounds for `1 ≤ p ≤ ∞`.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Proposition 4.1.17 and Lemma 4.3.1.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

/-! ### Higher-order weak derivative commutation on `W^{k,p}` -/

section WkpCommutation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem iteratedFDerivAlong_replicate_sum_eq_of_ge
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Omega) (h : E) :
    ∀ (j d : ℕ) (u : Wkp mu Omega p (j + 1)), ContDiff ℝ (d + j + 1) φ → ∀ x : E,
      iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
        (fun x' => ((-1 : ℝ) ^ (d + j + 1) / ((d + j + 1).factorial : ℝ)) *
          ∑ I : Fin (d + j + 1) → ι,
            ∫ y in Omega, iteratedFDeriv ℝ (d + j + 1)
              (fun z => (∏ l : Fin (d + j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
              Wkp.value (j + 1) u y ∂mu) x =
        ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
          ∫ y in Omega, iteratedFDeriv ℝ d
            (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) *
            IteratedGradient.fullContractL j h (Wkp.iteratedGradient j u y) ∂mu
  | 0, d, u, hφ, x => by
      have hw : HasWeakLineDerivOn mu Omega (Wkp.value 1 u)
          (fun y => IteratedGradient.fullContractL 0 h (Wkp.iteratedGradient 0 u y)) h :=
        ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
          (.of_forall fun y => by simp [real_inner_comm])
      simp only [Nat.zero_add, List.replicate_one, iteratedFDerivAlong_cons_apply,
        iteratedFDerivAlong_nil]
      simp only [Nat.add_zero] at hφ ⊢
      exact hw.fderiv_neg_one_pow_div_factorial_mul_sum_setIntegral_iteratedFDeriv b d hφ hφc hφs x
  | j + 1, d, u, hφ, x => by
      have hidx : d + (j + 1) + 1 = (d + 1) + j + 1 := by omega
      have hih : iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
            (fun x'' => ((-1 : ℝ) ^ (d + (j + 1) + 1) / ((d + (j + 1) + 1).factorial : ℝ)) *
              ∑ I : Fin (d + (j + 1) + 1) → ι,
                ∫ y in Omega, iteratedFDeriv ℝ (d + (j + 1) + 1)
                  (fun z => (∏ l : Fin (d + (j + 1) + 1), ⟪b (I l), x'' - z⟫_ℝ) * φ z) y
                  (b ∘ I) * Wkp.value (j + 1 + 1) u y ∂mu) =
          fun x' => ((-1 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * ∑ J : Fin (d + 1) → ι,
            ∫ y in Omega, iteratedFDeriv ℝ (d + 1)
              (fun z => (∏ l : Fin (d + 1), ⟪b (J l), x' - z⟫_ℝ) * φ z) y (b ∘ J) *
              IteratedGradient.fullContractL j h
                (Wkp.iteratedGradient j (Wkp.lowerOrder (j + 1) u) y) ∂mu := by
        ext x'
        have hstep := iteratedFDerivAlong_replicate_sum_eq_of_ge b hφc hφs h j (d + 1)
          (Wkp.lowerOrder (j + 1) u) (hφ.of_le (by norm_cast; omega)) x'
        rw [← Wkp.value_succ] at hstep
        exact hidx.symm ▸ hstep
      have hw : HasWeakLineDerivOn mu Omega
          (fun y => IteratedGradient.fullContractL j h
            (Wkp.iteratedGradient j (Wkp.lowerOrder (j + 1) u) y))
          (fun y => IteratedGradient.fullContractL (j + 1) h
            (Wkp.iteratedGradient (j + 1) u y)) h :=
        (((Wkp.hasWeakFDerivOn_iteratedGradient j u).clm_comp
          (IteratedGradient.fullContractL j h)).hasWeakLineDerivOn h).congr_ae_deriv
          (.of_forall fun y => by
            simp only [IteratedGradient.fullContractL_succ, ContinuousLinearMap.comp_apply]
            rw [ContinuousLinearMap.apply_apply])
      rw [List.replicate_succ, iteratedFDerivAlong_cons_apply, hih]
      exact hw.fderiv_neg_one_pow_div_factorial_mul_sum_setIntegral_iteratedFDeriv b d
        (hφ.of_le (by norm_cast; omega)) hφc hφs x

private def averagedTaylorTerm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (mu : Measure E) (Omega : Opens E) (φ w : E → ℝ) (r : ℕ) : E → ℝ := fun x =>
  ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
    ∫ y in Omega, iteratedFDeriv ℝ r
      (fun z => (∏ l : Fin r, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu

/-- **Brenner–Scott weak derivative commutation identity.** For any `j, m : ℕ`, `u ∈ W^{j+1,p}(Ω)`
(`1 ≤ p ≤ ∞`), `h : E`, and `φ : E → ℝ` of class `C^m` compactly supported in `Ω`, contracting
`iteratedGradientChain · j x` of the degree-`m` averaged Taylor pairing of `u` along `h` yields
the degree-`(m - j - 1)` averaged Taylor pairing of
`y ↦ fullContractL j h (Wkp.iteratedGradient j u y)` (vanishing when `m ≤ j`). Only Sobolev order
`j + 1` is required. -/
theorem Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (j m : ℕ)
    (u : Wkp mu Omega p (j + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ m φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    IteratedGradient.fullContractL j h
      (iteratedGradientChain
        (fun x' => ∑ r ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
            ∫ y in Omega, iteratedFDeriv ℝ r
              (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
              Wkp.value (j + 1) u y ∂mu)
        j x) =
      ∑ d ∈ Finset.range (m - j),
        ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
          ∫ y in Omega, iteratedFDeriv ℝ d
            (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) *
            IteratedGradient.fullContractL j h (Wkp.iteratedGradient j u y) ∂mu := by
  let term := averagedTaylorTerm b mu Omega φ (Wkp.value (j + 1) u)
  have hloc : LocallyIntegrableOn (Wkp.value (j + 1) u) Omega mu :=
    Lp.locallyIntegrableOn _ Fact.out
  have hS_smooth : ∀ {k : ℕ∞ω} {r : ℕ}, r ≤ m → ContDiff ℝ k (fun x' => ∑ I : Fin r → ι,
      ∫ y in Omega, iteratedFDeriv ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z)
        y (b ∘ I) * Wkp.value (j + 1) u y ∂mu) := fun hr =>
    ContDiff.sum fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I)
      (hφ.of_le (by norm_cast)) hφc hφs hloc
  have hterm_smooth : ∀ {k : ℕ∞ω}, ∀ r ∈ Finset.range (m + 1), ContDiff ℝ k (term r) :=
    fun r hr => contDiff_const.mul (hS_smooth (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)))
  -- Terms of degree `r ≤ j` vanish under `j + 1` directional derivatives along `h`.
  have hvanish : ∀ r ≤ m, r ≤ j →
      iteratedFDerivAlong ℝ (List.replicate (j + 1) h) (term r) x = 0 := fun r hrm hrj => by
    dsimp only [term]; unfold averagedTaylorTerm
    rw [congrFun (iteratedFDerivAlong_const_mul (n := ∞) (hS_smooth hrm) _ _ (by simp)) x,
      iteratedFDerivAlong_fun_sum (n := ∞) Finset.univ
        (f := fun (I : Fin r → ι) x' => ∫ y in Omega, iteratedFDeriv ℝ r
          (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
          Wkp.value (j + 1) u y ∂mu)
        (fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I)
          (hφ.of_le (by norm_cast)) hφc hφs hloc) _ (by simp),
      Finset.sum_eq_zero fun I _ => by
        simpa only [Function.comp_apply] using
          iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero (b ∘ I)
            (hφ.of_le (by norm_cast)) hφc hφs hloc _ (by simp; omega) x,
      mul_zero]
  have hgoal : (fun x' => ∑ r ∈ Finset.range (m + 1), term r x') =
      fun x' => ∑ r ∈ Finset.range (m + 1), ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
        ∫ y in Omega, iteratedFDeriv ℝ r
          (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
          Wkp.value (j + 1) u y ∂mu := by ext x'; simp [term, averagedTaylorTerm]
  rw [← hgoal,
    IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong j
      (ContDiff.sum hterm_smooth).contDiffAt h,
    iteratedFDerivAlong_fun_sum (n := ∞) _ hterm_smooth _ (by simp)]
  -- Split into `r ≤ j` (vanishing) and `r = j + 1 + d` (transferred onto `iteratedGradient j u`).
  rcases lt_or_ge j m with hjm | hmj
  · have hm_split : m + 1 = (j + 1) + (m - j) := by omega
    rw [hm_split, Finset.sum_range_add,
      Finset.sum_eq_zero fun r hr =>
        hvanish r ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)).trans hjm.le)
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)),
      zero_add]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm : d + j + 1 ≤ m := by have := Finset.mem_range.1 hd; omega
    have heq_idx : j + 1 + d = d + j + 1 := by omega
    dsimp only [term]; unfold averagedTaylorTerm; rw [heq_idx]
    exact iteratedFDerivAlong_replicate_sum_eq_of_ge b hφc hφs h j d u (hφ.of_le (by norm_cast)) x
  · rw [Nat.sub_eq_zero_of_le hmj, Finset.range_zero, Finset.sum_empty]
    exact Finset.sum_eq_zero fun r hr =>
      hvanish r (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))
        ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)).trans hmj)

/-- **Coordinate-free spatial derivative of a first-order contracted weak-gradient integral.**
For `u ∈ W^{1,p}(Ω)` (`1 ≤ p ≤ ∞`) and any compactly supported weight `φ : E → ℝ` continuous on
`tsupport φ ⊆ Ω`, differentiating `x ↦ ∫ fullContractL 0 (x - y) (iteratedGradient 0 u y) * φ y`
along `h` yields `∫ φ y * Wkp.value 0 (Wkp.lineDerivL h 0 u) y`. -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq
    (u : Wkp mu Omega p 1) {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ))
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y ∂mu) x h =
      ∫ y in Omega, φ y * Wkp.value 0 (Wkp.lineDerivL h 0 u) y ∂mu := by
  let G := Wkp.iteratedGradient 0 u
  have hG : LocallyIntegrableOn G Omega mu := Lp.locallyIntegrableOn G Fact.out
  have hint₁ : IntegrableOn (fun y => φ y • G y) Omega mu := by
    simpa only [ContinuousLinearMap.id_apply] using
      (hG.integrable_smul_clm_apply_of_hasCompactSupport hφ hφc hφs
        (continuousOn_const (c := ContinuousLinearMap.id ℝ E))).integrableOn
  have hint₂ : IntegrableOn (fun y => φ y * ⟪y, G y⟫_ℝ) Omega mu := by
    simpa only [innerSL_apply_apply, smul_eq_mul] using
      (hG.integrable_smul_clm_apply_of_hasCompactSupport hφ hφc hφs
        (innerSL ℝ (E := E)).continuous.continuousOn).integrableOn
  let V : E := ∫ y in Omega, φ y • G y ∂mu
  let C : ℝ := ∫ y in Omega, φ y * ⟪y, G y⟫_ℝ ∂mu
  have hfun : (fun x' => ∫ y in Omega, IteratedGradient.fullContractL 0 (x' - y) (G y) * φ y ∂mu) =
      fun x' => innerSL ℝ V x' - C := by
    funext x'
    have hpt : ∀ y, IteratedGradient.fullContractL 0 (x' - y) (G y) * φ y =
        innerSL ℝ x' (φ y • G y) - φ y * ⟪y, G y⟫_ℝ := fun y => by
      simp only [IteratedGradient.fullContractL_zero, innerSL_apply_apply, inner_sub_left,
        inner_smul_right]
      ring
    simp_rw [hpt]
    rw [integral_sub ((innerSL ℝ x').integrable_comp hint₁) hint₂,
      (innerSL ℝ x').integral_comp_comm hint₁]
    simp only [V, C, innerSL_apply_apply, real_inner_comm]
  have hw₁ : HasWeakLineDerivOn mu Omega (Wkp.value 1 u) (fun y => ⟪h, G y⟫_ℝ) h :=
    ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
      (.of_forall fun y => by simp [G, real_inner_comm])
  have hae := hw₁.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL h 0 u)
  rw [hfun, ((innerSL ℝ V).hasFDerivAt.sub_const C).fderiv]
  have hVh : innerSL ℝ V h = ∫ y in Omega, φ y * ⟪h, G y⟫_ℝ ∂mu := by
    dsimp only [V]
    rw [innerSL_apply_apply, real_inner_comm, ← innerSL_apply_apply ℝ,
      ← (innerSL ℝ h).integral_comp_comm hint₁]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by simp
  rw [hVh]
  exact integral_congr_ae (hae.mono fun y hy => by dsimp only at hy ⊢; rw [hy])

private theorem fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {ψ : E → ℝ} (hψ : ContDiff ℝ (k + 2) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) (x' - y)
        (Wkp.iteratedGradient (k + 1) u y) * ψ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        IteratedGradient.fullContractL k (x - y)
          (Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u) y) * ψ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  have hw := Wkp.hasWeakLineDerivOn_lineDerivL h (k + 1) u
  rw [funext (Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv
        b (k + 1) u hψ hψc hψs),
    hw.fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
      b ((-1 : ℝ) ^ (k + 2)) (k + 1) hψ hψc hψs x,
    Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b k
      (Wkp.lineDerivL h (k + 1) u) (hψ.of_le (by norm_cast; omega)) hψc hψs x,
    pow_succ (-1 : ℝ) (k + 1)]
  push_cast
  ring

/-- **Coordinate-free spatial derivative of a higher-order contracted weak-gradient integral.**
For `u ∈ W^{k+2,p}(Ω)` (`1 ≤ p ≤ ∞`) and any compactly supported weight `φ : E → ℝ` continuous on
`tsupport φ ⊆ Ω`, differentiating `x ↦ ∫ fullContractL (k + 1) (x - y) (D^{k+2} u y) * φ y` along
`h` produces `(k + 2)` times the order-`(k + 1)` contracted integral of
`Wkp.lineDerivL h (k + 1) u`. -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ))
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) (x' - y)
        (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        IteratedGradient.fullContractL k (x - y)
          (Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u) y) * φ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  let G₁ := Wkp.iteratedGradient (k + 1) u
  let G₂ := Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u)
  have hG₁ : LocallyIntegrableOn G₁ Omega mu := Lp.locallyIntegrableOn G₁ Fact.out
  have hG₂ : LocallyIntegrableOn G₂ Omega mu := Lp.locallyIntegrableOn G₂ Fact.out
  let W₁ : E → ℝ := fun y => ∑ I : Fin (k + 2) → Fin (Module.finrank ℝ E),
    ∑ p : Fin (k + 2), ⟪b (I p), h⟫_ℝ * (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) *
      IteratedGradient.evalTupleL (k + 1) (b ∘ I) (G₁ y)
  let W₂ : E → ℝ := fun y => (k + 2 : ℝ) * IteratedGradient.fullContractL k (x - y) (G₂ y)
  -- Both integrands are locally integrable on `Ω`.
  have hW₁ : LocallyIntegrableOn W₁ Omega mu :=
    locallyIntegrableOn_finsetSum _ fun I _ => locallyIntegrableOn_finsetSum _ fun p _ => by
      have hcont : Continuous fun y =>
          ⟪b (I p), h⟫_ℝ * ∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ :=
        continuous_const.mul (continuous_finsetProd _ fun l _ =>
          (innerSL ℝ (b (I l))).continuous.comp (continuous_const.sub continuous_id))
      simpa only [Function.comp_apply, smul_eq_mul, mul_assoc] using
        ((IteratedGradient.evalTupleL (k + 1) (b ∘ I)).locallyIntegrableOn_comp hG₁
          ).continuousOn_smul_of_isOpen Omega.isOpen hcont.continuousOn
  have hW₂ : LocallyIntegrableOn W₂ Omega mu := by
    have hclm : Continuous fun y => IteratedGradient.fullContractL (E := E) k (x - y) :=
      (IteratedGradient.contDiff_fullContractL (n := 0) k).continuous.comp
        (continuous_const.sub continuous_id)
    simpa only [W₂, smul_eq_mul] using
      (hG₂.continuousOn_clm_apply Omega.isOpen.isLocallyClosed
        hclm.continuousOn).continuousOn_smul_of_isOpen Omega.isOpen
          (continuousOn_const (c := (k + 2 : ℝ)))
  have hrhs : ∀ g : E → ℝ, (k + 2 : ℝ) *
      (∫ y in Omega, IteratedGradient.fullContractL k (x - y) (G₂ y) * g y ∂mu) =
      ∫ y in Omega, g y * W₂ y ∂mu := fun g => by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by dsimp only [W₂]; ring
  -- `W₁` and `W₂` agree against every `C^∞_c(Ω)` test function, hence agree a.e. on `Ω`.
  have hae : ∀ᵐ y ∂mu, y ∈ (Omega : Set E) → (W₁ - W₂) y = 0 :=
    Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hW₁.sub hW₂) fun g hg hgc hgs => by
      have hwhole : ∀ w : E → ℝ, ∫ y, g y • w y ∂mu = ∫ y in Omega, g y * w y ∂mu := fun w => by
        simp_rw [smul_eq_mul]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport fun h' => hy (hgs h'), zero_mul]).symm
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub (hW₁.integrable_smul_left_of_hasCompactSupport hg.continuous hgc hgs)
          (hW₂.integrable_smul_left_of_hasCompactSupport hg.continuous hgc hgs),
        hwhole W₁, hwhole W₂, sub_eq_zero, ← hrhs g,
        ← fderiv_setIntegral_fullContractL_sub_mul_eq b (k + 1) hG₁
          hg.continuous.continuousOn hgc hgs x h]
      exact fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff k u
        (hg.of_le (by simp)) hgc hgs x h
  rw [fderiv_setIntegral_fullContractL_sub_mul_eq b (k + 1) hG₁ hφ hφc hφs x h, hrhs φ]
  refine integral_congr_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).2 ?_)
  exact hae.mono fun y hy hΩ => by
    simpa only [W₁] using congrArg (φ y * ·) (sub_eq_zero.1 (hy hΩ))

end WkpCommutation

/-! ### Polynomiality in `TauCeti.polynomialsDegLE` -/

section Polynomiality

/-- On `W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), the contracted highest-derivative integral
`x ↦ ∫ y in Ω, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂μ` belongs to
`polynomialsDegLE ι m` whenever `k + 1 ≤ m` and `φ` is compactly supported in `Ω` and continuous
on `tsupport φ`. -/
theorem Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE
    {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k m : ℕ} (hkm : k + 1 ≤ m)
    (u : Wkp μ Ω p (k + 1)) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (fun x => ∫ y in Ω,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂μ) ∈
      polynomialsDegLE ι m :=
  setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE hkm
    (Lp.locallyIntegrableOn _ Fact.out) hφ hφc hφs

end Polynomiality

/-! ### Explicit `Lᵖ(Ω) → L^∞` diameter and chunkiness bounds -/

section Bounds

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Order-zero cutoff integral bound on `W^{k,p}(Ω)`.** For bounded `Ω`, `1 ≤ p ≤ ∞`, and any
weight `φ` supported in `closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) satisfying
`‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`, the integral `∫_Ω (value k u y) φ y` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{-n/p} * ‖value k u‖`. -/
theorem Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p k)
    {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, Wkp.value k u y * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.value k u‖ := by
  refine Lp.norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd (Wkp.value k u) hρ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hφ y hy) (norm_nonneg _)

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted weak
derivatives.** Specialization of `TauCeti.norm_setIntegral_fullContractL_sub_mul_le` to
`Wkp.iteratedGradient k u`. -/
theorem Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ}
    (hρ : 0 < ρ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.iteratedGradient k u‖ :=
  norm_setIntegral_fullContractL_sub_mul_le hΩ_bdd k (Wkp.iteratedGradient k u) hx hρ hdiam
    hsupp hφ

end Bounds

/-! ### Concrete checks on `(-1, 1) ⊆ ℝ` -/

section Examples

-- Coordinate-free first-order derivative commutation on `(-1, 1) ⊆ ℝ` for `φ` continuous on its
-- `tsupport`: differentiating `x ↦ ∫ (x - y) u'(y) φ(y) dy` in direction `1` yields
-- `∫ φ(y) (∂₁ u)(y) dy`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 1)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) (x : ℝ) :
    fderiv ℝ (fun x' => ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y) x 1 =
      ∫ y in Set.Ioo (-1 : ℝ) 1, φ y * Wkp.value 0 (Wkp.lineDerivL 1 0 u) y :=
  Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq u hφ hφc hφs x 1

-- Second-order derivative commutation on `(-1, 1) ⊆ ℝ` for `φ` continuous on its `tsupport`:
-- differentiating `x ↦ ∫ (x - y)² u''(y) φ(y) dy` in direction `1` brings down the factor `2`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) (x : ℝ) :
    fderiv ℝ (fun x' => ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 1 (x' - y) (Wkp.iteratedGradient 1 u y) * φ y) x 1 =
      2 * ∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y)
          (Wkp.iteratedGradient 0 (Wkp.lineDerivL 1 1 u) y) * φ y := by
  simpa using Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq 0 u hφ hφc hφs x 1

-- One-dimensional `p = 1` scaling check on `Ω = (-1, 1)` (`diam Ω = 2`, `ρ = 1`, `γ = 2`):
-- the order-zero and order-one bounds carry diameter factors `2⁻¹` and `2⁰ = 1`, so with `γ = 2`
-- they simplify to `M * ‖value 1 u‖` and `2 * M * ‖iteratedGradient 0 u‖`.
example (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 1 1)
    {x : ℝ} (hx : x ∈ closure (Set.Ioo (-1 : ℝ) 1)) {φ : ℝ → ℝ} {M : ℝ}
    (hsupp : Function.support φ ⊆ Metric.closedBall (0 : ℝ) 1)
    (hφ : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ‖φ y‖ ≤ M) :
    ‖∫ y in Set.Ioo (-1 : ℝ) 1, Wkp.value 1 u y * φ y‖ +
      ‖∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y) (Wkp.iteratedGradient 0 u y) * φ y‖ ≤
      M * ‖Wkp.value 1 u‖ + 2 * M * ‖Wkp.iteratedGradient 0 u‖ := by
  let I : Opens ℝ := ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
  have hbdd : Bornology.IsBounded (I : Set ℝ) := Metric.isBounded_Ioo (-1) 1
  have hdiam : Metric.diam (Set.Ioo (-1 : ℝ) 1) = 2 := by
    rw [Real.diam_Ioo (by norm_num)]; norm_num
  have hφ' : ∀ y ∈ (I : Set ℝ), ‖φ y‖ ≤ M * (1 : ℝ) ^ (-(Module.finrank ℝ ℝ : ℝ)) :=
    fun y hy => by simpa [I] using hφ y hy
  have htwo : (2 : ℝ) * ((2 : ℝ) ^ (-1 : ℝ) * ‖Wkp.value 1 u‖) = ‖Wkp.value 1 u‖ := by
    rw [← mul_assoc]; norm_num
  have hb0 : ‖∫ y in Set.Ioo (-1 : ℝ) 1, Wkp.value 1 u y * φ y‖ ≤ M * ‖Wkp.value 1 u‖ :=
    (Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
      (Omega := I) hbdd 1 u zero_lt_one (γ := 2) (by simpa [I] using hdiam.le) hsupp
      hφ').trans_eq (by simpa [I, hdiam, mul_assoc] using congrArg (M * ·) htwo)
  have hb1 : ‖∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y) (Wkp.iteratedGradient 0 u y) * φ y‖ ≤
      2 * M * ‖Wkp.iteratedGradient 0 u‖ :=
    (Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
      (Omega := I) hbdd 0 u hx zero_lt_one (γ := 2) (by simpa [I] using hdiam.le) hsupp
      hφ').trans_eq (by simp [I, hdiam, mul_comm M 2])
  exact add_le_add hb0 hb1

end Examples

end TauCeti
