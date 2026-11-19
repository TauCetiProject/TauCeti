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
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Higher-order weak integration by parts on `W^{k,p}`

Integrating a positive-order Sobolev function `u ∈ W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`) by parts against a
compactly supported `C^{k+1}` test function or operator functional transfers all `k + 1` weak
derivatives onto the test field without assuming finite exponent or smooth-function density.

We first establish tuple integration by parts for `TauCeti.IteratedGradient.evalTupleL` along an
arbitrary `(k + 1)`-tuple of directions
(`TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong`), specialize to repeated directions
(`TauCeti.Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong`), and expand general `C^{k+1}`
functionals `Φ : E → IteratedGradient E k →L[ℝ] ℝ` along a finite orthonormal basis
(`TauCeti.Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv`,
`TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv`).

General Taylor-monomial pairings, contracted-field integrals, polynomiality, and weak-derivative
commutation live in `TauCeti.Analysis.Calculus.Taylor.Pairing.Basic`,
`TauCeti.Analysis.Calculus.IteratedGradient.Integral`,
`TauCeti.Analysis.Calculus.Taylor.Pairing.Polynomial`, and
`TauCeti.Analysis.Sobolev.WeakDeriv.TaylorPairing`; their `W^{k,p}` specializations live in
`TauCeti.Analysis.Sobolev.Wkp.AveragedTaylor`.

## Main declarations

* `TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong` and
  `TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDeriv`: coordinate-free weak integration by
  parts along an arbitrary tuple of `k + 1` directions.
* `TauCeti.Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong` and
  `TauCeti.Wkp.setIntegral_fullContractL_mul_eq_iteratedFDeriv`: specialization to repeated
  contraction along a single direction.
* `TauCeti.Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDerivAlong` and
  `TauCeti.Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv`: orthonormal-basis weak
  integration by parts against `C^{k+1}` operator functionals.
* `TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv` and
  `TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDerivAlong`: specialization to
  shifted full contractions `fullContractL k (x - y)`.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.1.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

section WkpIBP

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem setIntegral_evalTupleL_succ_eq_neg (k : ℕ) (v : Fin (k + 2) → E)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 2) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega,
      IteratedGradient.evalTupleL (k + 1) v (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu =
      -∫ y in Omega, IteratedGradient.evalTupleL k (Fin.init v)
        (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y) *
          iteratedFDerivAlong ℝ [v (Fin.last (k + 1))] φ y ∂mu := by
  let w := v (Fin.last (k + 1))
  let S : ℝ →L[ℝ] IteratedGradient E k →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (IteratedGradient.evalTupleL k (Fin.init v))
  let Ψ : E → IteratedGradient E k →L[ℝ] ℝ := S ∘ φ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast; omega)
  have hΨd : ∀ y, fderiv ℝ Ψ y w = S (fderiv ℝ φ y w) := fun y => by
    rw [(S.hasFDerivAt.comp y (hφ1.differentiable one_ne_zero y).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
  have hw := (Wkp.hasWeakFDerivOn_iteratedGradient k u).hasWeakLineDerivOn w
  calc ∫ y in Omega,
        IteratedGradient.evalTupleL (k + 1) v (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu
      = ∫ y in Omega, Ψ y (Wkp.iteratedGradient (k + 1) u y w) ∂mu :=
        setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
          rw [IteratedGradient.evalTupleL_succ, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.apply_apply]
          simp [Ψ, S, w, mul_comm]
    _ = -∫ y in Omega, IteratedGradient.evalTupleL k (Fin.init v)
          (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y) *
            iteratedFDerivAlong ℝ [w] φ y ∂mu := by
        rw [← neg_eq_iff_eq_neg,
          ← hw.setIntegral_fderiv_apply_eq_neg (S.contDiff.comp hφ1)
            (hφc.comp_left S.map_zero) ((tsupport_comp_subset S.map_zero φ).trans hφs)]
        exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
          rw [hΨd y]; simp [S, mul_comm]

/-- **Coordinate-free weak integration by parts along a tuple of directions.** For any
`u ∈ W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), tuple `v : Fin (k + 1) → E`, and `C^{k+1}` function `φ : E → ℝ`
compactly supported in `Ω`, pairing `evalTupleL k v (iteratedGradient k u y)` with `φ y` transfers
all `k + 1` directional derivatives along `List.ofFn v` onto `φ`. -/
theorem Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong :
    ∀ (k : ℕ) (v : Fin (k + 1) → E) (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ},
      ContDiff ℝ (k + 1) φ → HasCompactSupport φ → tsupport φ ⊆ Omega →
      ∫ y in Omega,
        IteratedGradient.evalTupleL k v (Wkp.iteratedGradient k u y) * φ y ∂mu =
        (-1 : ℝ) ^ (k + 1) * ∫ y in Omega,
          iteratedFDerivAlong ℝ (List.ofFn v) φ y * Wkp.value (k + 1) u y ∂mu
  | 0, v, u, φ, hφ, hφc, hφs => by
      have hw : HasWeakLineDerivOn mu Omega (Wkp.value 1 u)
          (fun y => IteratedGradient.evalTupleL 0 v (Wkp.iteratedGradient 0 u y)) (v 0) :=
        ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn (v 0)).congr_ae_deriv
          (.of_forall fun y => by simp [real_inner_comm])
      have hibp : ∫ y in Omega, φ y *
            IteratedGradient.evalTupleL 0 v (Wkp.iteratedGradient 0 u y) ∂mu =
          -∫ y in Omega, fderiv ℝ φ y (v 0) * Wkp.value 1 u y ∂mu := by
        linarith [hw.setIntegral_fderiv_mul_eq_neg hφ hφc hφs]
      rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => mul_comm _ _, hibp,
        List.ofFn_succ, List.ofFn_zero]
      simp
  | k + 1, v, u, φ, hφ, hφc, hφs => by
      let w := v (Fin.last (k + 1))
      have hφ' : ContDiff ℝ (k + 1) (iteratedFDerivAlong ℝ [w] φ) :=
        hφ.iteratedFDerivAlong [w] (by simp [add_comm])
      have hφ'c : HasCompactSupport (iteratedFDerivAlong ℝ [w] φ) :=
        hφc.iteratedFDerivAlong ℝ [w]
      have hφ's : tsupport (iteratedFDerivAlong ℝ [w] φ) ⊆ Omega :=
        (tsupport_iteratedFDerivAlong_subset ℝ [w] φ).trans hφs
      rw [setIntegral_evalTupleL_succ_eq_neg k v u hφ hφc hφs,
        Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (Fin.init v)
          (Wkp.lowerOrder (k + 1) u) hφ' hφ'c hφ's, ← Wkp.value_succ]
      have hlist : List.ofFn v = List.ofFn (Fin.init v) ++ [w] := by
        rw [List.ofFn_succ', Fin.init_def, List.concat_eq_append]
      simp_rw [← iteratedFDerivAlong_append, ← hlist]
      ring

/-- `iteratedFDeriv` form of `TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong`. -/
theorem Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDeriv (k : ℕ) (v : Fin (k + 1) → E)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega,
      IteratedGradient.evalTupleL k v (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) *
        ∫ y in Omega, iteratedFDeriv ℝ (k + 1) φ y v * Wkp.value (k + 1) u y ∂mu := by
  rw [Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k v u hφ hφc hφs]
  congr 1
  exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
    rw [iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hφ]

/-- **Coordinate-free weak integration by parts along a repeated direction.** Specializing
`TauCeti.Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong` to `fun _ => h` relates full
contraction of `iteratedGradient k u` to `k + 1` directional derivatives along `h`. -/
theorem Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong (h : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega, IteratedGradient.fullContractL k h (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∫ y in Omega,
        iteratedFDerivAlong ℝ (List.replicate (k + 1) h) φ y * Wkp.value (k + 1) u y ∂mu := by
  simpa only [IteratedGradient.evalTupleL_const, List.ofFn_const] using
    Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (fun _ => h) u hφ hφc hφs

/-- `iteratedFDeriv` form of
`TauCeti.Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong`. -/
theorem Wkp.setIntegral_fullContractL_mul_eq_iteratedFDeriv (h : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega, IteratedGradient.fullContractL k h (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) *
        ∫ y in Omega, iteratedFDeriv ℝ (k + 1) φ y (fun _ => h) * Wkp.value (k + 1) u y ∂mu := by
  simpa only [IteratedGradient.evalTupleL_const] using
    Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDeriv k (fun _ => h) u hφ hφc hφs

/-- **Higher-order weak integration by parts against operator functionals (`iteratedFDerivAlong`
form).** Pairing `iteratedGradient k u` against a `C^{k+1}` compactly supported functional
`Φ : E → IteratedGradient E k →L[ℝ] ℝ` expands along any finite orthonormal basis `b` of `E` into
order-`(k + 1)` directional derivatives of `Φ` evaluated on rank-one iterated gradients. -/
theorem Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDerivAlong
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {Φ : E → IteratedGradient E k →L[ℝ] ℝ}
    (hΦ : ContDiff ℝ (k + 1) Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Omega) :
    ∫ y in Omega, Φ y (Wkp.iteratedGradient k u y) ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι,
        ∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => Φ z (IteratedGradient.rankOne k (b ∘ I))) y * Wkp.value (k + 1) u y ∂mu := by
  let φ : (Fin (k + 1) → ι) → E → ℝ := fun I z => Φ z (IteratedGradient.rankOne k (b ∘ I))
  have hφ_sub : ∀ I, Function.support (φ I) ⊆ Function.support Φ := fun I =>
    Function.support_subset_iff'.2 fun y hy => by simp [φ, Function.notMem_support.1 hy]
  rw [setIntegral_clm_apply_eq_sum_evalTupleL_rankOne b k
      (Lp.locallyIntegrableOn _ Fact.out) hΦ.continuous.continuousOn hΦc hΦs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simpa only [smul_eq_mul] using Wkp.setIntegral_evalTupleL_mul_eq_iteratedFDerivAlong k (b ∘ I) u
    (hΦ.clm_apply contDiff_const) (hΦc.mono (hφ_sub I)) ((closure_mono (hφ_sub I)).trans hΦs)

/-- **Higher-order weak integration by parts against operator functionals (`iteratedFDeriv`
form).** -/
theorem Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {Φ : E → IteratedGradient E k →L[ℝ] ℝ}
    (hΦ : ContDiff ℝ (k + 1) Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Omega) :
    ∫ y in Omega, Φ y (Wkp.iteratedGradient k u y) ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι,
        ∫ y in Omega, iteratedFDeriv ℝ (k + 1)
          (fun z => Φ z (IteratedGradient.rankOne k (b ∘ I))) y (b ∘ I) *
          Wkp.value (k + 1) u y ∂mu := by
  rw [Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDerivAlong b k u hΦ hΦc hΦs]
  congr 1
  refine Finset.sum_congr rfl fun I _ =>
    setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  rw [iteratedFDerivAlong_ofFn_eq_iteratedFDeriv (hΦ.clm_apply contDiff_const)]

/-- **Weak Taylor-monomial integration by parts (`iteratedFDeriv` form).** For `u ∈ W^{k+1,p}(Ω)`
(`1 ≤ p ≤ ∞`) and `φ : E → ℝ` of class `C^{k+1}` compactly supported in `Ω`, integrating the full
contraction `fullContractL k (x - y) (iteratedGradient k u y)` against `φ y` yields the signed
orthonormal-basis Taylor-monomial derivatives tested against `Wkp.value (k + 1) u`. -/
theorem Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x : E) :
    ∫ y in Omega,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι,
        ∫ y in Omega, iteratedFDeriv ℝ (k + 1)
          (fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) *
          Wkp.value (k + 1) u y ∂mu := by
  let Φ : E → IteratedGradient E k →L[ℝ] ℝ :=
    fun z => φ z • IteratedGradient.fullContractL k (x - z)
  have hΦ : ContDiff ℝ (k + 1) Φ :=
    hφ.smul ((IteratedGradient.contDiff_fullContractL k).comp (contDiff_const.sub contDiff_id))
  have hΦ_sub : Function.support Φ ⊆ Function.support φ :=
    Function.support_subset_iff'.2 fun y hy => by simp [Φ, Function.notMem_support.1 hy]
  have hΦc : HasCompactSupport Φ := hφc.mono hΦ_sub
  have hΦs : tsupport Φ ⊆ Omega := (closure_mono hΦ_sub).trans hφs
  rw [setIntegral_congr_fun (g := fun y => Φ y (Wkp.iteratedGradient k u y))
      Omega.isOpen.measurableSet fun y _ => by simp [Φ, mul_comm],
    Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv b k u hΦ hΦc hΦs]
  congr 1
  refine Finset.sum_congr rfl fun I _ =>
    setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  have hfun : (fun z => Φ z (IteratedGradient.rankOne k (b ∘ I))) =
      fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z := by
    funext z; simp [Φ, mul_comm]
  rw [hfun]

/-- `iteratedFDerivAlong` form of
`TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv`. -/
theorem Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDerivAlong
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x : E) :
    ∫ y in Omega,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι,
        ∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z) y *
          Wkp.value (k + 1) u y ∂mu := by
  rw [Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b k u hφ hφc hφs x]
  congr 1
  exact Finset.sum_congr rfl fun I _ =>
    setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong (b ∘ I) hφ
      (Wkp.value (k + 1) u) x

end WkpIBP

-- Second-order integration by parts on `(-1, 1) ⊆ ℝ`: transferring two weak derivatives onto a
-- `C²` test function `φ` compactly supported in `(-1, 1)` carries the sign `(-1)² = +1`.
example {mu : Measure ℝ} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp mu ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) :
    ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 1 (1 : ℝ) (Wkp.iteratedGradient 1 u y) * φ y ∂mu =
      ∫ y in Set.Ioo (-1 : ℝ) 1,
        iteratedFDerivAlong ℝ [1, 1] φ y * Wkp.value 2 u y ∂mu := by
  simpa using Wkp.setIntegral_fullContractL_mul_eq_iteratedFDerivAlong (1 : ℝ) 1 u hφ hφc hφs

end TauCeti
