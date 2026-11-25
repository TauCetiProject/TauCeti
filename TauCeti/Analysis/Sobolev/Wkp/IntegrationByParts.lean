/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.IteratedGradient.RankOne
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedGradient.Integral
import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Higher-order weak integration by parts on `W^{k,p}`

Integrating `u ∈ W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`) by parts against a compactly supported `C^{k+1}` test
function or operator functional transfers all `k + 1` weak derivatives onto the test field without
assuming finite exponent or smooth-function density:
* `TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong` and
  `TauCeti.Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong` handle direction tuples and
  repeated directions.
* `TauCeti.Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv` and
  `TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv` expand `C^{k+1}` operator
  functionals and shifted full contractions along any finite orthonormal basis.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed., §4.1.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open _root_.MeasureTheory IteratedGradient Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem setIntegral_evalTupleL_succ_eq_neg (k : ℕ) (v : Fin (k + 2) → E)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 2) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega, evalTupleL (k + 1) v (iteratedGradient (k + 1) u y) * φ y ∂mu =
      -∫ y in Omega, evalTupleL k (Fin.init v) (iteratedGradient k (lowerOrder (k + 1) u) y) *
        iteratedFDerivAlong ℝ [v (Fin.last (k + 1))] φ y ∂mu := by
  let w := v (Fin.last (k + 1))
  let S := (ContinuousLinearMap.id ℝ ℝ).smulRight (evalTupleL k (Fin.init v))
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast; omega)
  have hΨd : ∀ y, fderiv ℝ (S ∘ φ) y w = S (fderiv ℝ φ y w) := fun y => by
    rw [(S.hasFDerivAt.comp y (hφ1.differentiable one_ne_zero y).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
  have hw := (hasWeakFDerivOn_iteratedGradient k u).hasWeakLineDerivOn w
  calc ∫ y in Omega, evalTupleL (k + 1) v (iteratedGradient (k + 1) u y) * φ y ∂mu
      = ∫ y in Omega, (S ∘ φ) y (iteratedGradient (k + 1) u y w) ∂mu :=
        setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => by
          rw [evalTupleL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
          simp [S, w, mul_comm]
    _ = _ := by
        rw [← neg_eq_iff_eq_neg, ← hw.setIntegral_fderiv_apply_eq_neg (S.contDiff.comp hφ1)
          (hφc.comp_left S.map_zero) ((tsupport_comp_subset S.map_zero φ).trans hφs)]
        exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
          rw [hΨd y]; simp [S, w, mul_comm]

/-- **Coordinate-free weak integration by parts along a tuple of directions.** -/
theorem setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong :
    ∀ (k : ℕ) (v : Fin (k + 1) → E) (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ},
      ContDiff ℝ (k + 1) φ → HasCompactSupport φ → tsupport φ ⊆ Omega →
      ∫ y in Omega, evalTupleL k v (iteratedGradient k u y) * φ y ∂mu =
        (-1 : ℝ) ^ (k + 1) * ∫ y in Omega,
          iteratedFDerivAlong ℝ (List.ofFn v) φ y * value (k + 1) u y ∂mu
  | 0, v, u, φ, hφ, hφc, hφs => by
      have hw : HasWeakLineDerivOn mu Omega (value 1 u)
          (fun y => evalTupleL 0 v (iteratedGradient 0 u y)) (v 0) :=
        ((hasWeakFDerivOn_value u).hasWeakLineDerivOn (v 0)).congr_ae_deriv
          (.of_forall fun _ => by simp [real_inner_comm])
      have hibp : ∫ y in Omega, φ y * evalTupleL 0 v (iteratedGradient 0 u y) ∂mu =
          -∫ y in Omega, fderiv ℝ φ y (v 0) * value 1 u y ∂mu := by
        linarith [hw.setIntegral_fderiv_mul_eq_neg hφ hφc hφs]
      rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => mul_comm _ _, hibp,
        List.ofFn_succ, List.ofFn_zero]; simp
  | k + 1, v, u, φ, hφ, hφc, hφs => by
      let w := v (Fin.last (k + 1))
      rw [setIntegral_evalTupleL_succ_eq_neg k v u hφ hφc hφs,
        setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (Fin.init v) (lowerOrder (k + 1) u)
          (hφ.iteratedFDerivAlong [w] (by simp [add_comm])) (hφc.iteratedFDerivAlong ℝ [w])
          ((tsupport_iteratedFDerivAlong_subset ℝ [w] φ).trans hφs), ← value_succ]
      have hlist : List.ofFn v = List.ofFn (Fin.init v) ++ [w] := by
        rw [List.ofFn_succ', Fin.init_def, List.concat_eq_append]
      simp_rw [← iteratedFDerivAlong_append, ← hlist]; ring

/-- **Coordinate-free weak integration by parts along a repeated direction.** -/
theorem setIntegral_fullContractL_mul_eq_iteratedFDerivAlong (h : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega, fullContractL k h (iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∫ y in Omega,
        iteratedFDerivAlong ℝ (List.replicate (k + 1) h) φ y * value (k + 1) u y ∂mu := by
  simpa only [evalTupleL_const, List.ofFn_const] using
    setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (fun _ => h) u hφ hφc hφs

/-- **Higher-order weak integration by parts against operator functionals.** -/
theorem setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {Φ : E → IteratedGradient E k →L[ℝ] ℝ} (hΦ : ContDiff ℝ (k + 1) Φ)
    (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Omega) :
    ∫ y in Omega, Φ y (iteratedGradient k u y) ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι, ∫ y in Omega,
        iteratedFDeriv ℝ (k + 1) (fun z => Φ z (rankOne k (b ∘ I))) y (b ∘ I) *
          value (k + 1) u y ∂mu := by
  have hφ_sub : ∀ I, Function.support (fun z => Φ z (rankOne k (b ∘ I))) ⊆ Function.support Φ :=
    fun _ => Function.support_subset_iff'.2 fun _ hy => by simp [Function.notMem_support.1 hy]
  rw [setIntegral_clm_apply_eq_sum_evalTupleL_rankOne b k (Lp.locallyIntegrableOn _ Fact.out)
      hΦ.continuous.continuousOn hΦc hΦs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hsm : ContDiff ℝ (k + 1) (fun z => Φ z (rankOne k (b ∘ I))) := hΦ.clm_apply contDiff_const
  rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => smul_eq_mul _ _,
    setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (b ∘ I) u hsm (hΦc.mono (hφ_sub I))
      ((closure_mono (hφ_sub I)).trans hΦs)]
  congr 1; exact setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => by
    rw [iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hsm]

/-- **Weak Taylor-monomial integration by parts (`iteratedFDeriv` form).** -/
theorem setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Omega) (x : E) :
    ∫ y in Omega, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι, ∫ y in Omega,
        iteratedFDeriv ℝ (k + 1) (fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z)
          y (b ∘ I) * value (k + 1) u y ∂mu := by
  let Φ : E → IteratedGradient E k →L[ℝ] ℝ := fun z => φ z • fullContractL k (x - z)
  have hΦ : ContDiff ℝ (k + 1) Φ :=
    hφ.smul ((contDiff_fullContractL k).comp (contDiff_const.sub contDiff_id))
  have hΦ_sub : Function.support Φ ⊆ Function.support φ :=
    Function.support_subset_iff'.2 fun _ hy => by simp [Φ, Function.notMem_support.1 hy]
  rw [setIntegral_congr_fun (g := fun y => Φ y (iteratedGradient k u y))
      Omega.isOpen.measurableSet fun _ _ => by simp [Φ, mul_comm],
    setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv b k u hΦ
      (hφc.mono hΦ_sub) ((closure_mono hΦ_sub).trans hφs)]
  congr 1; refine Finset.sum_congr rfl fun I _ =>
    setIntegral_congr_fun Omega.isOpen.measurableSet fun _ _ => ?_
  have hfun : (fun z => Φ z (rankOne k (b ∘ I))) =
      fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z := funext fun _ => by
    simp [Φ, mul_comm]
  rw [hfun]

end TauCeti.Wkp
