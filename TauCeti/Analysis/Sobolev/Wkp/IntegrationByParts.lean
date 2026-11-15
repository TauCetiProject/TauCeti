/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.IteratedGradient.RankOne
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Higher-order weak integration by parts and Taylor pairings on `W^{k,p}`

Integrating a positive-order Sobolev function `u ∈ W^{k+1,p}(Ω)` by parts against a compactly
supported `C^{k+1}` functional `Φ : E → IteratedGradient E k →L[ℝ] ℝ` transfers all `k + 1` weak
derivatives onto `Φ` without assuming finite exponent or smooth-function density (`1 ≤ p ≤ ∞`).

This file proves basis-free and orthonormal-basis higher-order weak integration by parts on
`TauCeti.Wkp`, specializes them to full contractions `fullContractL k (x - y)` against Taylor
monomials, establishes weak-derivative commutation and membership in `TauCeti.polynomialsDegLE`,
and bounds the resulting integrals uniformly on `closure Ω` in `Metric.diam Ω` and chunkiness `γ`.

## Main results

* `TauCeti.Wkp.setIntegral_iteratedFDerivAlong_replicate_mul_value_eq` and
  `TauCeti.Wkp.setIntegral_iteratedFDeriv_const_mul_value_eq`: coordinate-free integration by parts
  along a repeated direction.
* `TauCeti.Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDeriv` and
  `TauCeti.Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv`: orthonormal-basis weak
  integration by parts for operator functionals and Taylor-monomial contractions (`1 ≤ p ≤ ∞`).
* `TauCeti.HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul`,
  `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq`,
  `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`, and
  `TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_taylorMonomial_eq`: commutation of spatial
  differentiation with Taylor-monomial weak pairings at minimal Sobolev regularity.
* `TauCeti.sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE` and
  `TauCeti.Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE`:
  membership in `TauCeti.polynomialsDegLE`.
* `TauCeti.Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall` and
  `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`: explicit
  `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bounds across `1 ≤ p ≤ ∞`.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4, §§4.1–4.3 (Propositions 4.1.9 and 4.1.17, Lemma 4.3.1).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

/-! ### Higher-order weak integration by parts on `W^{k,p}` -/

section WkpIBP

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem setIntegral_fullContractL_succ_eq_neg (h : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 2) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) h (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu =
      -∫ y in Omega, IteratedGradient.fullContractL k h
        (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y) *
          iteratedFDerivAlong ℝ [h] φ y ∂mu := by
  let S : ℝ →L[ℝ] IteratedGradient E k →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (IteratedGradient.fullContractL k h)
  let Ψ : E → IteratedGradient E k →L[ℝ] ℝ := S ∘ φ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast; omega)
  have hΨd : ∀ y, fderiv ℝ Ψ y h = S (fderiv ℝ φ y h) := fun y => by
    rw [(S.hasFDerivAt.comp y (hφ1.differentiable one_ne_zero y).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
  have hw := (Wkp.hasWeakFDerivOn_iteratedGradient k u).hasWeakLineDerivOn h
  calc ∫ y in Omega,
        IteratedGradient.fullContractL (k + 1) h (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu
      = ∫ y in Omega, Ψ y (Wkp.iteratedGradient (k + 1) u y h) ∂mu :=
        setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
          rw [IteratedGradient.fullContractL_succ, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.apply_apply]
          simp [Ψ, S, mul_comm]
    _ = -∫ y in Omega, IteratedGradient.fullContractL k h
          (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y) *
            iteratedFDerivAlong ℝ [h] φ y ∂mu := by
        rw [← neg_eq_iff_eq_neg,
          ← hw.setIntegral_fderiv_apply_eq_neg (S.contDiff.comp hφ1)
            (hφc.comp_left S.map_zero) ((tsupport_comp_subset S.map_zero φ).trans hφs)]
        exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
          rw [hΨd y]; simp [S, mul_comm]

/-- **Coordinate-free weak integration by parts along a repeated direction.** For any
`u ∈ W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), direction `h : E`, and `C^{k+1}` function `φ : E → ℝ` compactly
supported in `Ω`, pairing the full contraction of `iteratedGradient k u` along `h` with `φ`
transfers `k + 1` directional derivatives along `h` onto `φ`. -/
theorem Wkp.setIntegral_iteratedFDerivAlong_replicate_mul_value_eq (h : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ}, ContDiff ℝ (k + 1) φ →
      HasCompactSupport φ → tsupport φ ⊆ Omega →
      ∫ y in Omega, IteratedGradient.fullContractL k h (Wkp.iteratedGradient k u y) * φ y ∂mu =
        (-1 : ℝ) ^ (k + 1) * ∫ y in Omega,
          iteratedFDerivAlong ℝ (List.replicate (k + 1) h) φ y * Wkp.value (k + 1) u y ∂mu
  | 0, u, φ, hφ, hφc, hφs => by
      have hw : HasWeakLineDerivOn mu Omega (Wkp.value 1 u)
          (fun y => IteratedGradient.fullContractL 0 h (Wkp.iteratedGradient 0 u y)) h :=
        ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
          (.of_forall fun y => by simp [real_inner_comm])
      have hibp : ∫ y in Omega, φ y *
            IteratedGradient.fullContractL 0 h (Wkp.iteratedGradient 0 u y) ∂mu =
          -∫ y in Omega, fderiv ℝ φ y h * Wkp.value 1 u y ∂mu := by
        linarith [hw.setIntegral_fderiv_mul_eq_neg hφ hφc hφs]
      rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => mul_comm _ _, hibp]
      simp
  | k + 1, u, φ, hφ, hφc, hφs => by
      have hφ'_eq : iteratedFDerivAlong ℝ [h] φ = fun y => fderiv ℝ φ y h :=
        funext fun y => by simp
      have hφ' : ContDiff ℝ (k + 1) (iteratedFDerivAlong ℝ [h] φ) :=
        hφ.iteratedFDerivAlong [h] (by simp [add_comm])
      have hφ'c : HasCompactSupport (iteratedFDerivAlong ℝ [h] φ) := by
        rw [hφ'_eq]
        exact (hφc.fderiv ℝ).comp_left (ContinuousLinearMap.apply ℝ ℝ h).map_zero
      have hφ's : tsupport (iteratedFDerivAlong ℝ [h] φ) ⊆ Omega := by
        rw [hφ'_eq]
        exact ((tsupport_comp_subset (ContinuousLinearMap.apply ℝ ℝ h).map_zero _).trans
          (tsupport_fderiv_subset ℝ)).trans hφs
      rw [setIntegral_fullContractL_succ_eq_neg h k u hφ hφc hφs,
        Wkp.setIntegral_iteratedFDerivAlong_replicate_mul_value_eq h k
          (Wkp.lowerOrder (k + 1) u) hφ' hφ'c hφ's, ← Wkp.value_succ]
      have hrep : List.replicate (k + 1 + 1) h = List.replicate (k + 1) h ++ [h] :=
        List.replicate_succ'
      simp_rw [← iteratedFDerivAlong_append, ← hrep]
      ring

/-- `iteratedFDeriv` form of
`TauCeti.Wkp.setIntegral_iteratedFDerivAlong_replicate_mul_value_eq`. -/
theorem Wkp.setIntegral_iteratedFDeriv_const_mul_value_eq (h : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 1) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) :
    ∫ y in Omega, IteratedGradient.fullContractL k h (Wkp.iteratedGradient k u y) * φ y ∂mu =
      (-1 : ℝ) ^ (k + 1) *
        ∫ y in Omega, iteratedFDeriv ℝ (k + 1) φ y (fun _ => h) * Wkp.value (k + 1) u y ∂mu := by
  rw [Wkp.setIntegral_iteratedFDerivAlong_replicate_mul_value_eq h k u hφ hφc hφs]
  congr 1
  refine setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  rw [← List.ofFn_const (k + 1) h, iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hφ]

private theorem setIntegral_clm_iteratedGradient_zero
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (u : Wkp mu Omega p 1)
    {Φ : E → E →L[ℝ] ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (hΦs : tsupport Φ ⊆ Omega) :
    ∫ y in Omega, Φ y (Wkp.iteratedGradient 0 u y) ∂mu =
      (-1 : ℝ) ^ 1 * ∑ I : Fin 1 → ι,
        ∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => Φ z (IteratedGradient.rankOne 0 (b ∘ I))) y * Wkp.value 1 u y ∂mu := by
  let φ : ι → E → ℝ := fun i y => Φ y (b i)
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := fun i => hΦ.clm_apply contDiff_const
  have hφs_sub : ∀ i, Function.support (φ i) ⊆ Function.support Φ := fun i =>
    Function.support_subset_iff'.2 fun y hy => by simp [φ, Function.notMem_support.1 hy]
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hΦc.mono (hφs_sub i)
  have hφs : ∀ i, tsupport (φ i) ⊆ Omega := fun i => (closure_mono (hφs_sub i)).trans hΦs
  have hw : ∀ i, HasWeakLineDerivOn mu Omega (Wkp.value 1 u)
      (fun y => ⟪b i, Wkp.iteratedGradient 0 u y⟫_ℝ) (b i) := fun i =>
    ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn (b i)).congr_ae_deriv
      (.of_forall fun y => by simp [real_inner_comm])
  have hint : ∀ i : ι, IntegrableOn
      (fun y => Φ y (b i) * ⟪b i, Wkp.iteratedGradient 0 u y⟫_ℝ) Omega mu := fun i =>
    ((hw i).locallyIntegrableOn_deriv.integrable_smul_left_of_hasCompactSupport
      (hφ i).continuous (hφc i) (hφs i)).integrableOn
  have hexp : ∀ y, Φ y (Wkp.iteratedGradient 0 u y) =
      ∑ i : ι, Φ y (b i) * ⟪b i, Wkp.iteratedGradient 0 u y⟫_ℝ := fun y => by
    conv_lhs => rw [← b.sum_repr' (Wkp.iteratedGradient 0 u y), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
  rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => hexp y,
    integral_finsetSum _ fun i _ => hint i,
    ← (Equiv.funUnique (Fin 1) ι).sum_comp, pow_one, neg_one_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hi : Equiv.funUnique (Fin 1) ι I = I 0 := rfl
  rw [hi, ← neg_eq_iff_eq_neg,
    ← (hw (I 0)).setIntegral_fderiv_mul_eq_neg (hφ (I 0)) (hφc (I 0)) (hφs (I 0))]
  refine setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  have hlist : List.ofFn (b ∘ I) = [b (I 0)] := by simp
  rw [hlist]; simp [φ]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem iteratedFDerivAlong_snoc_rankOne_eq {ι : Type*} (b : ι → E) {k : ℕ}
    {Φ : E → IteratedGradient E (k + 1) →L[ℝ] ℝ} (hΦ : Differentiable ℝ Φ)
    (J : Fin (k + 1) → ι) (i : ι) (y : E) :
    iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
      (fun z => fderiv ℝ Φ z (b i)
        ((innerSL ℝ (b i)).smulRight (IteratedGradient.rankOne k (b ∘ J)))) y =
    iteratedFDerivAlong ℝ (List.ofFn (b ∘ Fin.snoc J i))
      (fun z => Φ z (IteratedGradient.rankOne (k + 1) (b ∘ Fin.snoc J i))) y := by
  have hsnoc : b ∘ Fin.snoc J i = Fin.snoc (b ∘ J) (b i) :=
    funext (Fin.lastCases (by simp) fun l => by simp)
  have hfun : (fun z => fderiv ℝ Φ z (b i)
        ((innerSL ℝ (b i)).smulRight (IteratedGradient.rankOne k (b ∘ J)))) =
      iteratedFDerivAlong ℝ [b i]
        (fun z => Φ z (IteratedGradient.rankOne (k + 1) (b ∘ Fin.snoc J i))) := by
    funext z
    have hd := congrArg (fun L : E →L[ℝ] ℝ => L (b i))
      (((hΦ z).hasFDerivAt.clm_apply
        (hasFDerivAt_const (IteratedGradient.rankOne (k + 1) (b ∘ Fin.snoc J i)) z)).fderiv)
    rw [hsnoc, IteratedGradient.rankOne_snoc] at hd ⊢
    simpa [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil] using hd.symm
  have hlist : List.ofFn (b ∘ Fin.snoc J i) = List.ofFn (b ∘ J) ++ [b i] := by
    rw [hsnoc, List.ofFn_succ']; simp [List.concat_eq_append]
  rw [hfun, ← iteratedFDerivAlong_append, hlist]

/-- **Higher-order weak integration by parts against operator functionals (`iteratedFDerivAlong`
form).** Pairing `iteratedGradient k u` against a `C^{k+1}` compactly supported functional
`Φ : E → IteratedGradient E k →L[ℝ] ℝ` expands along any orthonormal basis `b` of `E` into
order-`(k + 1)` directional derivatives of `Φ` evaluated on rank-one iterated gradients. -/
theorem Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDerivAlong
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)) {Φ : E → IteratedGradient E k →L[ℝ] ℝ},
      ContDiff ℝ (k + 1) Φ → HasCompactSupport Φ → tsupport Φ ⊆ Omega →
      ∫ y in Omega, Φ y (Wkp.iteratedGradient k u y) ∂mu =
        (-1 : ℝ) ^ (k + 1) * ∑ I : Fin (k + 1) → ι,
          ∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
            (fun z => Φ z (IteratedGradient.rankOne k (b ∘ I))) y * Wkp.value (k + 1) u y ∂mu
  | 0, u, _, hΦ, hΦc, hΦs => setIntegral_clm_iteratedGradient_zero b u hΦ hΦc hΦs
  | k + 1, u, Φ, hΦ, hΦc, hΦs => by
      let S : ι → IteratedGradient E k →L[ℝ] IteratedGradient E (k + 1) := fun i =>
        ContinuousLinearMap.smulRightL ℝ E (IteratedGradient E k) (innerSL ℝ (b i))
      let Ψ : ι → E → IteratedGradient E k →L[ℝ] ℝ :=
        fun i y => (fderiv ℝ Φ y (b i)).comp (S i)
      have hΦ' : ContDiff ℝ (k + 1) (fderiv ℝ Φ) :=
        hΦ.fderiv_right (m := (k + 1 : ℕ)) (by norm_cast)
      have hΨ_sub : ∀ i, Function.support (Ψ i) ⊆ Function.support (fderiv ℝ Φ) := fun i =>
        Function.support_subset_iff'.2 fun y hy => by simp [Ψ, Function.notMem_support.1 hy]
      have hfirst := (Wkp.hasWeakFDerivOn_iteratedGradient k u
        ).setIntegral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis
        b (hΦ.of_le (by norm_cast; omega)) hΦc hΦs
      rw [hfirst]
      have hstep : ∀ i : ι,
          ∫ y in Omega, fderiv ℝ Φ y (b i)
            ((innerSL ℝ (b i)).smulRight
              (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y)) ∂mu =
          (-1 : ℝ) ^ (k + 1) * ∑ J : Fin (k + 1) → ι,
            ∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ Fin.snoc J i))
              (fun z => Φ z (IteratedGradient.rankOne (k + 1) (b ∘ Fin.snoc J i))) y *
              Wkp.value (k + 2) u y ∂mu := fun i => by
        have hΨ_eq : (∫ y in Omega, fderiv ℝ Φ y (b i) ((innerSL ℝ (b i)).smulRight
              (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y)) ∂mu) =
            ∫ y in Omega, Ψ i y (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) y) ∂mu := rfl
        rw [hΨ_eq, Wkp.setIntegral_clm_iteratedGradient_eq_sum_iteratedFDerivAlong b k
            (Wkp.lowerOrder (k + 1) u) ((hΦ'.clm_apply contDiff_const).clm_comp contDiff_const)
            ((hΦc.fderiv ℝ).mono (hΨ_sub i))
            ((closure_mono (hΨ_sub i)).trans ((tsupport_fderiv_subset ℝ).trans hΦs)),
          ← Wkp.value_succ]
        congr 1
        exact Finset.sum_congr rfl fun J _ =>
          setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ =>
            congrArg (· * Wkp.value (k + 2) u y)
              (iteratedFDerivAlong_snoc_rankOne_eq b (hΦ.differentiable (by simp)) J i y)
      simp_rw [hstep, ← Finset.mul_sum]
      rw [← (Fin.snocEquiv fun _ : Fin (k + 2) => ι).sum_comp]
      simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
      ring

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
  refine Finset.sum_congr rfl fun I _ =>
    setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  have hcont : ContDiff ℝ (k + 1) (fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z) :=
    ((contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hcont]

end WkpIBP

/-! ### Algebraic expansion and weak derivative commutation -/

section Commutation

/-- `iteratedFDerivAlong` distributes over finite sums of `C^n` functions when `vs.length ≤ n`. -/
private theorem iteratedFDerivAlong_finset_sum {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} (s : Finset ι) {f : ι → E → F} (hf : ∀ i ∈ s, ContDiff ℝ n (f i))
    (vs : List E) (hvs : vs.length ≤ n) (y : E) :
    iteratedFDerivAlong ℝ vs (fun z => ∑ i ∈ s, f i z) y =
      ∑ i ∈ s, iteratedFDerivAlong ℝ vs (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun _ : E => (0 : F)) = 0 := rfl
      simp [h0]
  | insert a s ha ih =>
      have h1 : ContDiff ℝ n (f a) := hf a (Finset.mem_insert_self a s)
      have h2 : ContDiff ℝ n (fun z => ∑ i ∈ s, f i z) :=
        ContDiff.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hadd := congrFun (iteratedFDerivAlong_add (f := f a)
        (g := fun z => ∑ i ∈ s, f i z) h1 h2 vs hvs) y
      simp only [Finset.sum_insert ha]
      exact hadd.trans (congrArg (iteratedFDerivAlong ℝ vs (f a) y + ·)
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private theorem iteratedFDerivAlong_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : E → ℝ} (hf : ContDiff ℝ n f) (c : ℝ) (vs : List E) (hvs : vs.length ≤ n)
    (y : E) :
    iteratedFDerivAlong ℝ vs (fun z => c * f z) y = c * iteratedFDerivAlong ℝ vs f y :=
  congrFun (iteratedFDerivAlong_const_smul hf c vs hvs) y

/-- Reindexing `Fin.insertNth` moves the inserted entry to the head up to list permutation. -/
private theorem ofFn_insertNth_perm {α : Type*} :
    ∀ {j : ℕ} (p : Fin (j + 1)) (a : α) (f : Fin j → α),
      List.Perm (List.ofFn (p.insertNth a f)) (a :: List.ofFn f)
  | j, ⟨0, _⟩, a, f => by simp [Fin.zero_eta]
  | 0, ⟨k + 1, hk⟩, _, _ => absurd hk (by omega)
  | j + 1, ⟨k + 1, hk⟩, a, f => by
      have hp : (⟨k + 1, hk⟩ : Fin (j + 2)) =
          (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin (j + 1)).succ := rfl
      conv_lhs => rw [hp, ← Fin.cons_self_tail f, Fin.insertNth_succ_cons, List.ofFn_succ]
      conv_rhs => rw [← Fin.cons_self_tail f, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact ((ofFn_insertNth_perm _ a (Fin.tail f)).cons (f 0)).trans (List.Perm.swap a (f 0) _)

section TaylorExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Iterated directional derivatives of `z ↦ g z * φ z` remain supported in `tsupport φ` and
define an integrable pairing against any `v` locally integrable on `Ω`. -/
private theorem hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
    {μ : Measure E} {Ω : Opens E} {n : ℕ∞ω} {g φ : E → ℝ}
    (hg : ContDiff ℝ n g) (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    tsupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ⊆ tsupport φ ∧
      HasCompactSupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ∧
      IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (fun z => g z * φ z) y * v y) Ω μ := by
  have hsub : tsupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ⊆ tsupport φ :=
    closure_minimal (Function.support_subset_iff'.2 fun y hy =>
      iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero
        (Filter.eventually_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds (Set.mem_compl hy))
          fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]) vs)
      (isClosed_tsupport φ)
  have hcs : HasCompactSupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) :=
    hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) hsub
  have hcont : Continuous (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) :=
    ((hg.mul hφ).iteratedFDerivAlong (m := 0) vs (by simpa using hvs)).continuous
  exact ⟨hsub, hcs,
    (hv.integrable_smul_left_of_hasCompactSupport hcont hcs (hsub.trans hφs)).integrableOn⟩

/-- Powerset expansion of a Taylor-monomial pairing in `x`: all `x`-dependence factors out of both
`iteratedFDerivAlong` and the integral over `Ω`. -/
private theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) (x : E) :
    ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ s, ⟪a l, x⟫_ℝ) *
        ∫ y in Ω, iteratedFDerivAlong ℝ vs
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) y * v y ∂μ := by
  let ψ : Finset (Fin j) → E → ℝ := fun s z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  have hg : ∀ s : Finset (Fin j), ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) :=
    fun s => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.neg).of_le le_top
  have hψ : ∀ s, ContDiff ℝ n (ψ s) := fun s => (hg s).mul hφ
  have hint : ∀ s, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (ψ s) y * v y) Ω μ := fun s =>
    (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hg s) hφ hφc hφs vs hvs hv).2.2
  have hexp : (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) =
      fun z => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ s, ⟪a l, x⟫_ℝ) * ψ s z := by
    funext z
    simp_rw [ψ, inner_sub_right, sub_eq_add_neg, Finset.prod_add, Finset.sum_mul, mul_assoc]
  have hstep : ∀ y, iteratedFDerivAlong ℝ vs (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y *
        v y = ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ s, ⟪a l, x⟫_ℝ) * (iteratedFDerivAlong ℝ vs (ψ s) y * v y) := fun y => by
    rw [hexp, iteratedFDerivAlong_finset_sum _
      (fun s _ => contDiff_const.mul (hψ s)) vs hvs, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by
      rw [iteratedFDerivAlong_const_mul (hψ s) _ vs hvs, mul_assoc]
  simp_rw [hstep]
  rw [integral_finsetSum _ fun s _ => (hint s).const_mul _]
  exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _

/-- Every Taylor-monomial pairing (`iteratedFDerivAlong` form) against a locally integrable
function is smooth (`C^∞`) on `E`. -/
theorem contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    ContDiff ℝ ∞ (fun x => ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) := by
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs vs hvs hv)]
  exact ContDiff.sum fun s _ =>
    (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff).mul contDiff_const

/-- Every Taylor-monomial pairing (`iteratedFDeriv` form) against a locally integrable function is
smooth (`C^∞`) on `E`. -/
theorem contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    ContDiff ℝ ∞ (fun x => ∫ y in Ω, iteratedFDeriv ℝ j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ) := by
  have hconv : (fun x => ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ) =
      fun x => ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ := by
    funext x
    refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
    have hc : ContDiff ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) :=
      ((contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
    rw [iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc]
  rw [hconv]
  exact contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul a hφ hφc hφs
    (List.ofFn a) (by simp) hv

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Comparing the product-rule and powerset derivatives of `x' ↦ (∏ l, ⟪a l, x' - z⟫_ℝ) * φ z`
with respect to `x'` gives a pointwise identity in `z`. -/
private theorem sum_erase_prod_inner_sub_eq_sum_powerset_fderiv {j : ℕ} (a : Fin j → E)
    (φ : E → ℝ) (x h z : E) :
    (∑ p : Fin j, ⟪a p, h⟫_ℝ * ((∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z)) =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        fderiv ℝ (fun x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ) x h *
          ((∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) := by
  let c : Finset (Fin j) → E → ℝ := fun s x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ
  let ψ : Finset (Fin j) → ℝ := fun s => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  have hc : ∀ s, Differentiable ℝ (c s) := fun s =>
    (contDiff_prod (n := 1) fun l _ => (innerSL ℝ (a l)).contDiff).differentiable one_ne_zero
  have hfun : (fun x' => (∏ l : Fin j, ⟪a l, x' - z⟫_ℝ) * φ z) =
      fun x' => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, c s x' * ψ s := by
    funext x'
    simp_rw [c, ψ, inner_sub_right, sub_eq_add_neg, Finset.prod_add, Finset.sum_mul, mul_assoc]
  have hp : HasFDerivAt (fun x' => ∏ l : Fin j, ⟪a l, x' - z⟫_ℝ)
      (∑ p ∈ (Finset.univ : Finset (Fin j)),
        (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) • innerSL ℝ (a p)) x :=
    HasFDerivAt.finsetProd fun l _ => by
      have h1 : HasFDerivAt (fun x' => ⟪a l, x'⟫_ℝ - ⟪a l, z⟫_ℝ) (innerSL ℝ (a l)) x :=
        (innerSL ℝ (a l)).hasFDerivAt.sub_const _
      simpa [inner_sub_right] using h1
  have hd1 := hp.mul_const (φ z)
  have hd2 : HasFDerivAt (fun x' => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, c s x' * ψ s)
      (∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, ψ s • fderiv ℝ (c s) x) x :=
    HasFDerivAt.fun_sum fun s _ => ((hc s x).hasFDerivAt).mul_const (ψ s)
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L h) (hd1.unique (hfun ▸ hd2))
  simp only [c, ψ, smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply,
    smul_eq_mul] at heq ⊢
  rw [Finset.mul_sum] at heq
  exact (Finset.sum_congr rfl fun p _ => by ring).trans
    (heq.trans (Finset.sum_congr rfl fun s _ => by ring))

/-- Spatial Fréchet derivative of a single Taylor-monomial pairing: differentiating in `x` along
`h` differentiates the polynomial factor `∏ l, ⟪a l, x - z⟫_ℝ` factor by factor under the integral
and `iteratedFDerivAlong`. -/
private theorem fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x' - z⟫_ℝ) * φ z) y * v y ∂μ) x h =
      ∑ p : Fin j, ⟪a p, h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ vs
        (fun z => (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ := by
  let ψ : Finset (Fin j) → E → ℝ := fun s z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  let gp : Fin j → E → ℝ := fun p z => (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z
  let c : Finset (Fin j) → E → ℝ := fun s x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ
  have hc : ∀ s, Differentiable ℝ (c s) := fun s =>
    (contDiff_prod (n := 1) fun l _ => (innerSL ℝ (a l)).contDiff).differentiable one_ne_zero
  have hgψ : ∀ s : Finset (Fin j), ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) :=
    fun s => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.neg).of_le le_top
  have hggp : ∀ p : Fin j, ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) :=
    fun p => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have hψ : ∀ s, ContDiff ℝ n (ψ s) := fun s => (hgψ s).mul hφ
  have hgp : ∀ p, ContDiff ℝ n (gp p) := fun p => (hggp p).mul hφ
  have hint : ∀ s, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (ψ s) y * v y) Ω μ := fun s =>
    (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hgψ s) hφ hφc hφs vs hvs hv).2.2
  have hint_p : ∀ p, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (gp p) y * v y) Ω μ :=
    fun p => (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hggp p) hφ hφc hφs vs
      hvs hv).2.2
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs vs hvs hv),
    (HasFDerivAt.fun_sum fun s _ => ((hc s x).hasFDerivAt).mul_const _).fderiv,
    FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, smul_eq_mul]
  calc ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        (∫ y in Ω, iteratedFDerivAlong ℝ vs (ψ s) y * v y ∂μ) * fderiv ℝ (c s) x h
      = ∫ y in Ω, (∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
          iteratedFDerivAlong ℝ vs (fun z => fderiv ℝ (c s) x h * ψ s z) y) * v y ∂μ := by
        rw [Finset.sum_congr rfl fun s _ => (mul_comm _ _).trans (integral_const_mul _ _).symm,
          ← integral_finsetSum _ fun s _ => (hint s).const_mul _]
        refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by
          rw [iteratedFDerivAlong_const_mul (hψ s) _ vs hvs, mul_assoc]
    _ = ∫ y in Ω, (∑ p : Fin j,
          iteratedFDerivAlong ℝ vs (fun z => ⟪a p, h⟫_ℝ * gp p z) y) * v y ∂μ :=
        setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => by
          rw [← iteratedFDerivAlong_finset_sum _ (fun s _ => contDiff_const.mul (hψ s)) vs hvs,
            ← funext (sum_erase_prod_inner_sub_eq_sum_powerset_fderiv a φ x h),
            iteratedFDerivAlong_finset_sum _ (fun p _ => contDiff_const.mul (hgp p)) vs hvs]
    _ = ∑ p : Fin j, ⟪a p, h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ vs (gp p) y * v y ∂μ := by
        simp_rw [iteratedFDerivAlong_const_mul (hgp _) _ vs hvs, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum _ fun p _ => (hint_p p).const_mul _]
        exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedFDerivAlong_insertNth_erase_eq {ι : Type*} (b : ι → E) {j : ℕ}
    {φ : E → ℝ} (hφ : ContDiff ℝ (j + 1) φ) (x : E) (p : Fin (j + 1)) (J : Fin j → ι)
    (i : ι) (y : E) :
    iteratedFDerivAlong ℝ (List.ofFn (b ∘ p.insertNth (α := fun _ => ι) i J))
      (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪b (p.insertNth (α := fun _ => ι) i J l), x - z⟫_ℝ) * φ z) y =
      fderiv ℝ (iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z)) y (b i) := by
  have hqg : ContDiff ℝ (j + 1) (fun z => ∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) :=
    (contDiff_prod fun l _ => (innerSL ℝ (b (J l))).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have herase : (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪b (p.insertNth (α := fun _ => ι) i J l), x - z⟫_ℝ) * φ z) =
      fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z := by
    funext z
    have he : (Finset.univ : Finset (Fin (j + 1))).erase p = Finset.univ.map p.succAboveEmb := by
      rw [Fin.univ_succAbove j p, Finset.erase_cons]
    simp [he, Fin.insertNth_apply_succAbove]
  have hcomp : b ∘ p.insertNth (α := fun _ => ι) i J = p.insertNth (b i) (b ∘ J) :=
    funext (p.succAboveCases (by simp) fun l => by simp)
  rw [herase, hcomp,
    congrFun ((ofFn_insertNth_perm p (b i) (b ∘ J)).iteratedFDerivAlong_eq (hqg.mul hφ)
      (by simp)) y, iteratedFDerivAlong_cons_apply]

/-- Evaluating the `p`-th slot sum in the derivative of a Taylor-monomial pairing via
`Fin.insertNthEquiv`, permutation invariance of `iteratedFDerivAlong`, and weak integration by
parts against `hu : HasWeakLineDerivOn μ Ω u u' h`. -/
private theorem sum_slot_setIntegral_iteratedFDerivAlong_eq_neg
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) {j : ℕ} {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (x : E) (p : Fin (j + 1)) :
    (∑ I : Fin (j + 1) → ι, ⟪b (I p), h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
      (fun z => (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - z⟫_ℝ) * φ z) y * u y ∂μ) =
      -∑ J : Fin j → ι, ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y * u' y ∂μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  rw [← (p.insertNthEquiv fun _ : Fin (j + 1) => ι).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.insertNthEquiv_apply]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  let qg : E → ℝ := fun z => ∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ
  let g : E → ℝ := iteratedFDerivAlong ℝ (List.ofFn (b ∘ J)) (fun z => qg z * φ z)
  have hqg : ContDiff ℝ (j + 1) qg := (contDiff_prod fun l _ =>
    (innerSL ℝ (b (J l))).contDiff.comp (contDiff_const.sub contDiff_id)).of_le le_top
  have hg : ContDiff ℝ 1 g := (hqg.mul hφ).iteratedFDerivAlong (List.ofFn (b ∘ J))
    (by simp [add_comm])
  obtain ⟨hgs_sub, hgc, -⟩ := hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
    hqg hφ hφc hφs (List.ofFn (b ∘ J)) (by simp) hu.locallyIntegrableOn
  have hgs : tsupport g ⊆ Ω := hgs_sub.trans hφs
  have hint_i : ∀ i : ι, IntegrableOn (fun y => ⟪b i, h⟫_ℝ * fderiv ℝ g y (b i) * u y) Ω μ :=
    fun i => by
      simpa only [smul_eq_mul, mul_assoc] using
        ((hu.locallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
          ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
          ((hgc.fderiv ℝ).comp_left (ContinuousLinearMap.apply ℝ ℝ (b i)).map_zero)
          (((tsupport_comp_subset (ContinuousLinearMap.apply ℝ ℝ (b i)).map_zero _).trans
            (tsupport_fderiv_subset ℝ)).trans hgs)).const_mul ⟪b i, h⟫_ℝ).integrableOn
  simp_rw [Fin.insertNth_apply_same, iteratedFDerivAlong_insertNth_erase_eq b hφ x p J,
    ← integral_const_mul, ← mul_assoc]
  rw [← integral_finsetSum _ fun i _ => hint_i i,
    ← hu.setIntegral_fderiv_mul_eq_neg hg hgc hgs]
  refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  conv_rhs => rw [← b.sum_repr' h, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- **Single-step weak derivative commutation for Taylor-monomial pairings.** If `u` has weak
directional derivative `u'` in the direction `h` on `Ω` and `φ : E → ℝ` is `C^{j+1}` with compact
support in `Ω`, differentiating the degree-`(j + 1)` orthonormal-basis Taylor-monomial pairing of
`u` at `x` along `h` yields `-(j + 1)` times the degree-`j` Taylor-monomial pairing of `u'`. No
translation invariance of `μ` is needed. -/
theorem HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) (j : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (x : E) :
    fderiv ℝ (fun x' => ∑ I : Fin (j + 1) → ι,
      ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x h =
      -(j + 1 : ℝ) * ∑ J : Fin j → ι,
        ∫ y in Ω, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * u' y ∂μ := by
  have hconv : ∀ (k : ℕ) (_ : k ≤ j + 1) (w : E → ℝ) (I : Fin k → ι) (x' : E),
      ∫ y in Ω, iteratedFDeriv ℝ k
        (fun z => (∏ l : Fin k, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂μ =
      ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
        (fun z => (∏ l : Fin k, ⟪b (I l), x' - z⟫_ℝ) * φ z) y * w y ∂μ := fun k hk w I x' => by
    refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
    have hc : ContDiff ℝ k (fun z => (∏ l : Fin k, ⟪b (I l), x' - z⟫_ℝ) * φ z) :=
      ((contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top).mul (hφ.of_le (by norm_cast))
    rw [iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc]
  simp_rw [hconv (j + 1) le_rfl u, hconv j (Nat.le_succ j) u']
  have hsum_d : HasFDerivAt
      (fun x' => ∑ I : Fin (j + 1) → ι, ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y * u y ∂μ)
      (∑ I ∈ (Finset.univ : Finset (Fin (j + 1) → ι)), fderiv ℝ
        (fun x' => ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y * u y ∂μ) x) x :=
    HasFDerivAt.fun_sum fun I _ =>
      (((contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul (fun l => b (I l)) hφ hφc hφs
        _ (by simp) hu.locallyIntegrableOn).differentiable (by simp)) x).hasFDerivAt
  rw [hsum_d.fderiv, FunLike.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl fun I _ => fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
      (fun l => b (I l)) hφ hφc hφs (List.ofFn (b ∘ I)) (by simp) hu.locallyIntegrableOn x h,
    Finset.sum_comm]
  simp_rw [sum_slot_setIntegral_iteratedFDerivAlong_eq_neg b hu hφ hφc hφs x]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

end TaylorExpansion

/-- Differentiating a product of `t.card < m` linear inner-product forms `m` times vanishes. -/
private theorem iteratedFDerivAlong_replicate_prod_inner_eq_zero
    {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : α → E) (h : E) :
    ∀ (m : ℕ) (t : Finset α), t.card < m → ∀ x : E,
      iteratedFDerivAlong ℝ (List.replicate m h) (fun x' => ∏ l ∈ t, ⟪a l, x'⟫_ℝ) x = 0
  | 0, _, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, t, ht, x => by
      classical
      have hdf : iteratedFDerivAlong ℝ [h] (fun x' => ∏ l ∈ t, ⟪a l, x'⟫_ℝ) =
          fun y => ∑ l ∈ t, ⟪a l, h⟫_ℝ * ∏ l' ∈ t.erase l, ⟪a l', y⟫_ℝ := by
        funext y
        have hp := HasFDerivAt.finsetProd (u := t) (g := fun l x' => ⟪a l, x'⟫_ℝ) (x := y)
          fun l _ => (innerSL ℝ (a l)).hasFDerivAt
        simpa [Finset.sum_apply, smul_eq_mul, mul_comm] using
          congrArg (fun L : E →L[ℝ] ℝ => L h) hp.fderiv
      rw [List.replicate_succ', iteratedFDerivAlong_append, hdf,
        iteratedFDerivAlong_finset_sum (n := ∞) t
          (f := fun l y => ⟪a l, h⟫_ℝ * ∏ l' ∈ t.erase l, ⟪a l', y⟫_ℝ)
          (fun l _ => contDiff_const.mul (contDiff_prod fun _ _ => (innerSL ℝ _).contDiff))
          _ (by simp)]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hprod : ContDiff ℝ ∞ (fun y => ∏ l' ∈ t.erase l, ⟪a l', y⟫_ℝ) :=
        contDiff_prod fun l' _ => (innerSL ℝ (a l')).contDiff
      rw [iteratedFDerivAlong_const_mul hprod ⟪a l, h⟫_ℝ _ (by simp),
        iteratedFDerivAlong_replicate_prod_inner_eq_zero a h m (t.erase l)
          (by have := Finset.card_erase_lt_of_mem hl; omega) x, mul_zero]

section WkpCommutation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem iteratedFDerivAlong_replicate_taylorMonomial_eq_zero_of_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {j r : ℕ} (hrj : r ≤ j)
    {φ : E → ℝ} (hφ : ContDiff ℝ r φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega)
    {w : E → ℝ} (hw : LocallyIntegrableOn w Omega mu) (x h : E) :
    iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
      (fun x' => ∑ I : Fin r → ι,
        ∫ y in Omega, iteratedFDeriv ℝ r
          (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) x = 0 := by
  rw [iteratedFDerivAlong_finset_sum (n := ∞) Finset.univ
    (f := fun (I : Fin r → ι) x' => ∫ y in Omega, iteratedFDeriv ℝ r
      (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu)
    (fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I) hφ hφc hφs hw)
    _ (by simp)]
  refine Finset.sum_eq_zero fun I _ => ?_
  have hexp : (fun x' => ∫ y in Omega, iteratedFDeriv ℝ r
        (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) =
      fun x' => ∑ s ∈ (Finset.univ : Finset (Fin r)).powerset,
        (∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪b (I l), z⟫_ℝ) * φ z) y * w y ∂mu) *
          ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ := by
    funext x'
    have hc : ContDiff ℝ r (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) :=
      ((contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
    rw [setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by
      rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc],
      setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum (fun l => b (I l)) hφ hφc hφs
        (List.ofFn (b ∘ I)) (by simp) hw]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hexp, iteratedFDerivAlong_finset_sum (n := ∞) (Finset.univ : Finset (Fin r)).powerset
    (f := fun s x' => (∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
      (fun z => (∏ l ∈ Finset.univ \ s, -⟪b (I l), z⟫_ℝ) * φ z) y * w y ∂mu) *
      ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ)
    (fun _ _ => contDiff_const.mul (contDiff_prod fun _ _ => (innerSL ℝ _).contDiff)) _ (by simp)]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hprod : ContDiff ℝ ∞ (fun x' => ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ) :=
    contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff
  rw [iteratedFDerivAlong_const_mul hprod _ _ (by simp),
    iteratedFDerivAlong_replicate_prod_inner_eq_zero (fun l => b (I l)) h (j + 1) s
      (lt_of_le_of_lt (s.card_le_univ.trans_eq (Fintype.card_fin r)) (by omega)) x, mul_zero]

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem fderiv_normalized_taylorMonomial_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {w w' : E → ℝ} {h : E}
    (hw : HasWeakLineDerivOn mu Omega w w' h) (d : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (d + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x : E) :
    fderiv ℝ (fun x' => ((-1 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) *
      ∑ I : Fin (d + 1) → ι,
        ∫ y in Omega, iteratedFDeriv ℝ (d + 1)
          (fun z => (∏ l : Fin (d + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) x h =
      ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
        ∫ y in Omega, iteratedFDeriv ℝ d
          (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * w' y ∂mu := by
  have hdiff : DifferentiableAt ℝ (fun x' => ∑ I : Fin (d + 1) → ι,
      ∫ y in Omega, iteratedFDeriv ℝ (d + 1)
        (fun z => (∏ l : Fin (d + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) x :=
    DifferentiableAt.fun_sum fun I _ =>
      ((contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I) hφ hφc hφs
        hw.locallyIntegrableOn).differentiable (by simp)) x
  rw [(hdiff.hasFDerivAt.const_mul _).fderiv, smul_apply, smul_eq_mul,
    hw.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b d hφ hφc hφs x,
    Nat.factorial_succ]
  have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
  push_cast; field_simp [hd1]; ring

private theorem iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge
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
      have hrep : List.replicate (0 + 1) h = [h] := rfl
      rw [hrep, iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil]
      simp only [Nat.add_zero] at hφ ⊢
      exact fderiv_normalized_taylorMonomial_eq b hw d hφ hφc hφs x
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
        have hstep := iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge b hφc hφs h j (d + 1)
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
      have hrep : List.replicate (j + 1 + 1) h = h :: List.replicate (j + 1) h :=
        List.replicate_succ
      rw [hrep, iteratedFDerivAlong_cons_apply, hih]
      exact fderiv_normalized_taylorMonomial_eq b hw d (hφ.of_le (by norm_cast; omega)) hφc hφs x

/-- **Brenner–Scott weak derivative commutation identity.** For `j < m`, `u ∈ W^{j+1,p}(Ω)`
(`1 ≤ p ≤ ∞`), `h : E`, and `φ : E → ℝ` of class `C^m` compactly supported in `Ω`, contracting
`iteratedGradientChain · j x` of the degree-`m` averaged Taylor pairing of `u` along `h` yields
the degree-`(m - j - 1)` averaged Taylor pairing of
`y ↦ fullContractL j h (Wkp.iteratedGradient j u y)`. Only Sobolev order `j + 1` is required. -/
theorem Wkp.fullContractL_iteratedGradientChain_sum_taylorMonomial_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {j m : ℕ} (hjm : j < m)
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
  let S : ℕ → E → ℝ := fun r x' => ∑ I : Fin r → ι,
    ∫ y in Omega, iteratedFDeriv ℝ r
      (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * Wkp.value (j + 1) u y ∂mu
  let term : ℕ → E → ℝ := fun r x' => ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * S r x'
  have hloc : LocallyIntegrableOn (Wkp.value (j + 1) u) Omega mu :=
    Lp.locallyIntegrableOn _ Fact.out
  have hS_smooth : ∀ {r : ℕ}, r ≤ m → ContDiff ℝ ∞ (S r) := fun hr =>
    ContDiff.sum fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I)
      (hφ.of_le (by norm_cast)) hφc hφs hloc
  have hterm_smooth : ∀ r ∈ Finset.range (m + 1), ContDiff ℝ ∞ (term r) := fun r hr =>
    contDiff_const.mul (hS_smooth (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)))
  have hsum_j : ContDiff ℝ (j + 1) (fun x' => ∑ r ∈ Finset.range (m + 1), term r x') :=
    Nat.cast_add_one (R := ℕ∞ω) j ▸ contDiff_infty.1 (ContDiff.sum hterm_smooth) (j + 1)
  have hm_split : m + 1 = (j + 1) + (m - j) := by omega
  have hgoal : (fun x' => ∑ r ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
          ∫ y in Omega, iteratedFDeriv ℝ r
            (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
            Wkp.value (j + 1) u y ∂mu) =
      fun x' => ∑ r ∈ Finset.range (m + 1), term r x' := rfl
  rw [hgoal,
    IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong j hsum_j x h,
    iteratedFDerivAlong_finset_sum _ hterm_smooth _ (by simp), hm_split, Finset.sum_range_add]
  have hlow : ∑ r ∈ Finset.range (j + 1),
      iteratedFDerivAlong ℝ (List.replicate (j + 1) h) (term r) x = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hrj : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    rw [iteratedFDerivAlong_const_mul (n := ∞) (hS_smooth (hrj.trans hjm.le)) _ _ (by simp),
      iteratedFDerivAlong_replicate_taylorMonomial_eq_zero_of_le b hrj
        (hφ.of_le (by norm_cast; omega)) hφc hφs hloc x h, mul_zero]
  rw [hlow, zero_add]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d + j + 1 ≤ m := by have := Finset.mem_range.1 hd; omega
  have heq_idx : j + 1 + d = d + j + 1 := by omega
  dsimp only [term, S]
  rw [heq_idx]
  exact iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge b hφc hφs h j d u
    (hφ.of_le (by norm_cast)) x

/-- **Coordinate-free spatial derivative of a first-order contracted weak-gradient integral.** -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq
    (u : Wkp mu Omega p 1) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y ∂mu) x h =
      ∫ y in Omega, φ y * Wkp.value 0 (Wkp.lineDerivL h 0 u) y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  have hw := Wkp.hasWeakLineDerivOn_lineDerivL h 0 u
  have hdiff : DifferentiableAt ℝ (fun x' => ∑ I : Fin 1 → Fin (Module.finrank ℝ E),
      ∫ y in Omega, iteratedFDeriv ℝ 1
        (fun z => (∏ l : Fin 1, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
        Wkp.value 1 u y ∂mu) x :=
    DifferentiableAt.fun_sum fun I _ =>
      ((contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I) hφ hφc hφs
        hw.locallyIntegrableOn).differentiable (by simp)) x
  rw [funext (Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b 0 u hφ hφc hφs),
    (hdiff.hasFDerivAt.const_mul _).fderiv, smul_apply, smul_eq_mul,
    hw.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b 0 hφ hφc hφs x]
  simp

/-- **Coordinate-free spatial derivative of a higher-order contracted weak-gradient integral.**
For `u ∈ W^{k+2,p}(Ω)`, differentiating `x ↦ ∫ fullContractL (k + 1) (x - y) (D^{k+2} u y) * φ y`
along `h` produces `(k + 2)` times the order-`(k + 1)` contracted integral of `Wkp.lineDerivL h`. -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : ContDiff ℝ (k + 2) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) (x' - y)
        (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        IteratedGradient.fullContractL k (x - y)
          (Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u) y) * φ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  have hw := Wkp.hasWeakLineDerivOn_lineDerivL h (k + 1) u
  have hdiff : DifferentiableAt ℝ (fun x' => ∑ I : Fin (k + 2) → Fin (Module.finrank ℝ E),
      ∫ y in Omega, iteratedFDeriv ℝ (k + 2)
        (fun z => (∏ l : Fin (k + 2), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
        Wkp.value (k + 2) u y ∂mu) x :=
    DifferentiableAt.fun_sum fun I _ =>
      ((contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I) hφ hφc hφs
        hw.locallyIntegrableOn).differentiable (by simp)) x
  rw [funext (Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b (k + 1) u hφ hφc hφs),
    (hdiff.hasFDerivAt.const_mul _).fderiv, smul_apply, smul_eq_mul,
    hw.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b (k + 1) hφ hφc hφs x,
    Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b k (Wkp.lineDerivL h (k + 1) u)
      (hφ.of_le (by norm_cast; omega)) hφc hφs x]
  have hsign : (-1 : ℝ) ^ (k + 2) * -(k + 1 + 1 : ℝ) = (k + 2 : ℝ) * (-1 : ℝ) ^ (k + 1) := by
    rw [pow_succ (-1 : ℝ) (k + 1)]; ring
  push_cast
  linarith [congrArg (· * ∑ J : Fin (k + 1) → Fin (Module.finrank ℝ E),
    ∫ y in Omega, iteratedFDeriv ℝ (k + 1)
      (fun z => (∏ l : Fin (k + 1), ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) *
      Wkp.value (k + 1) (Wkp.lineDerivL h (k + 1) u) y ∂mu) hsign]

end WkpCommutation

end Commutation

/-! ### Polynomiality in `TauCeti.polynomialsDegLE` -/

section Polynomiality

variable {ι : Type*} [Fintype ι]

/-- A finite product of at most `m` linear inner-product forms on `EuclideanSpace ℝ ι` belongs to
`TauCeti.polynomialsDegLE ι m`. -/
private theorem prod_inner_mem_polynomialsDegLE {α : Type*} (s : Finset α)
    (a : α → EuclideanSpace ℝ ι) {m : ℕ} (hm : s.card ≤ m) :
    (fun x : EuclideanSpace ℝ ι => ∏ l ∈ s, ⟪a l, x⟫_ℝ) ∈ polynomialsDegLE ι m := by
  let P : MvPolynomial ι ℝ :=
    ∏ l ∈ s, ∑ r : ι, MvPolynomial.C (a l r) * MvPolynomial.X r
  have hdeg : P.totalDegree ≤ m := by
    refine (MvPolynomial.totalDegree_finsetProd s _).trans ?_
    refine (Finset.sum_le_card_nsmul s _ 1 fun l _ => ?_).trans (by simpa using hm)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have heval : polynomialEvalₗ ι P = fun x : EuclideanSpace ℝ ι => ∏ l ∈ s, ⟪a l, x⟫_ℝ := by
    ext x; simp [P, PiLp.inner_apply, mul_comm]
  exact heval ▸ (polynomialEvalₗ_mem_polynomialsDegLE_iff ι m P).2 hdeg

/-- Every Taylor-monomial pairing of degree `j ≤ m` against a locally integrable function on an
open subset of `EuclideanSpace ℝ ι` defines a polynomial function in `polynomialsDegLE ι m`. -/
theorem sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) {μ : Measure (EuclideanSpace ℝ ι)}
    {Ω : Opens (EuclideanSpace ℝ ι)} {j m : ℕ} (hjm : j ≤ m) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    (fun x => ∑ I : Fin j → ι,
      ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  have hsum_fn : (fun x => ∑ I : Fin j → ι,
        ∫ y in Ω, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) =
      ∑ I : Fin j → ι, fun x => ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ := by
    ext x; simp
  rw [hsum_fn]
  refine Submodule.sum_mem (polynomialsDegLE ι m) fun I _ => ?_
  have hconv : (fun x => ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        (∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪b (I l), z⟫_ℝ) * φ z) y * v y ∂μ) •
          fun x => ∏ l ∈ s, ⟪b (I l), x⟫_ℝ := by
    ext x
    have hc : ContDiff ℝ j (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) :=
      ((contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
    rw [setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => by
      rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc],
      setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum (fun l => b (I l)) hφ hφc hφs
        (List.ofFn (b ∘ I)) (by simp) hv,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun s _ => by simp [smul_eq_mul, mul_comm]
  rw [hconv]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _
    (prod_inner_mem_polynomialsDegLE s (b ∘ I)
      ((s.card_le_univ.trans_eq (Fintype.card_fin j)).trans hjm))

/-- Integrating `fullContractL k (x - y) (G y) * φ y` against any locally integrable field `G` and
continuous compactly supported weight `φ` gives a polynomial of total degree at most `m` whenever
`k + 1 ≤ m`. No differentiability of `φ` is needed. -/
theorem setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Opens (EuclideanSpace ℝ ι)}
    {k m : ℕ} (hkm : k + 1 ≤ m)
    {G : EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) k}
    (hG : LocallyIntegrableOn G Ω μ) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (fun x => ∫ y in Ω, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) ∈
      polynomialsDegLE ι m := by
  let b := EuclideanSpace.basisFun ι ℝ
  have hint_coeff : ∀ (I : Fin (k + 1) → ι) (s : Finset (Fin (k + 1))),
      IntegrableOn (fun y => (∏ l ∈ Finset.univ \ s, -⟪b (I l), y⟫_ℝ) * φ y *
        IteratedGradient.evalTuple k (b ∘ I) (G y)) Ω μ := fun I s => by
    let ψ : EuclideanSpace ℝ ι → ℝ := fun y => (∏ l ∈ Finset.univ \ s, -⟪b (I l), y⟫_ℝ) * φ y
    have hψ : Continuous ψ :=
      ((contDiff_prod (n := 0) fun l _ => (innerSL ℝ (b (I l))).contDiff.neg).continuous).mul hφ
    have hψc : HasCompactSupport ψ := hφc.mono (Function.support_mul_subset_right _ _)
    have hψs : tsupport ψ ⊆ Ω := (closure_mono (Function.support_mul_subset_right _ _)).trans hφs
    exact (((IteratedGradient.evalTuple k (b ∘ I)).locallyIntegrableOn_comp hG
      ).integrable_smul_left_of_hasCompactSupport hψ hψc hψs).integrableOn
  have hexp : (fun x => ∫ y in Ω, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) =
      ∑ I : Fin (k + 1) → ι, ∑ s ∈ (Finset.univ : Finset (Fin (k + 1))).powerset,
        (∫ y in Ω, (∏ l ∈ Finset.univ \ s, -⟪b (I l), y⟫_ℝ) * φ y *
          IteratedGradient.evalTuple k (b ∘ I) (G y) ∂μ) • fun x => ∏ l ∈ s, ⟪b (I l), x⟫_ℝ := by
    ext x
    have hpt : ∀ y, IteratedGradient.fullContractL k (x - y) (G y) * φ y =
        ∑ I : Fin (k + 1) → ι, ∑ s ∈ (Finset.univ : Finset (Fin (k + 1))).powerset,
          (∏ l ∈ s, ⟪b (I l), x⟫_ℝ) * ((∏ l ∈ Finset.univ \ s, -⟪b (I l), y⟫_ℝ) * φ y *
            IteratedGradient.evalTuple k (b ∘ I) (G y)) := fun y => by
      conv_lhs =>
        rw [IteratedGradient.eq_sum_evalTuple_rankOne b k (G y), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_smul, smul_eq_mul, IteratedGradient.fullContractL_rankOne]
      have hprod_eq : (∏ l : Fin (k + 1), ⟪(b ∘ I) l, x - y⟫_ℝ) =
          ∑ s ∈ (Finset.univ : Finset (Fin (k + 1))).powerset,
            (∏ l ∈ s, ⟪b (I l), x⟫_ℝ) * (∏ l ∈ Finset.univ \ s, -⟪b (I l), y⟫_ℝ) := by
        simp_rw [Function.comp_apply, inner_sub_right, sub_eq_add_neg]
        exact Finset.prod_add _ _ _
      rw [hprod_eq, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp_rw [hpt, Finset.sum_apply, Pi.smul_apply]
    rw [integral_finsetSum _ fun I _ => integrable_finsetSum _ fun s _ =>
      (hint_coeff I s).const_mul _]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [integral_finsetSum _ fun s _ => (hint_coeff I s).const_mul _]
    exact Finset.sum_congr rfl fun s _ => by rw [integral_const_mul, smul_eq_mul, mul_comm]
  rw [hexp]
  exact Submodule.sum_mem (polynomialsDegLE ι m) fun I _ =>
    Submodule.sum_mem (polynomialsDegLE ι m) fun s _ => Submodule.smul_mem _ _
      (prod_inner_mem_polynomialsDegLE s (b ∘ I)
        ((s.card_le_univ.trans_eq (Fintype.card_fin (k + 1))).trans hkm))

/-- On `W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), the contracted highest-derivative integral
`x ↦ ∫ y in Ω, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂μ` belongs to
`polynomialsDegLE ι m` whenever `k + 1 ≤ m` and `φ` is continuous with compact support in `Ω`. -/
theorem Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k m : ℕ} (hkm : k + 1 ≤ m)
    (u : Wkp μ Ω p (k + 1)) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
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

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A nonempty open subset of a nontrivial normed space has strictly positive diameter. -/
private theorem diam_pos_of_nonempty_of_finrank_pos (hΩ_bdd : Bornology.IsBounded (Omega : Set E))
    (hΩ_ne : (Omega : Set E).Nonempty) (hn : 0 < Module.finrank ℝ E) :
    0 < Metric.diam (Omega : Set E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn
  obtain ⟨y₀, hy₀⟩ := hΩ_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Omega.isOpen y₀ hy₀
  obtain ⟨v, hv⟩ := exists_norm_eq E (c := ε / 2) (by positivity)
  have hy₁ : y₀ + v ∈ (Omega : Set E) := hball (by simp [dist_eq_norm, hv, half_lt_self hε])
  have hd : dist y₀ (y₀ + v) = ε / 2 := by simp [dist_eq_norm, hv]
  exact (half_pos hε).trans_le (hd ▸ Metric.dist_le_diam_of_mem hΩ_bdd hy₀ hy₁)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [Fact (1 ≤ p)] in
private theorem rpow_neg_finrank_div_le (hΩ_bdd : Bornology.IsBounded (Omega : Set E))
    (hΩ_ne : (Omega : Set E).Nonempty) {ρ γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ) :
    ρ ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) ≤
      γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) := by
  let n := Module.finrank ℝ E
  let d := Metric.diam (Omega : Set E)
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · simp [n, hn0]
  have hd_pos : 0 < d := diam_pos_of_nonempty_of_finrank_pos hΩ_bdd hΩ_ne hn_pos
  have hγ_pos : 0 < γ := pos_of_mul_pos_left (hd_pos.trans_le hdiam) hρ.le
  have hinv : ρ⁻¹ ≤ γ / d := by
    rw [inv_le_iff_one_le_mul₀ hρ, div_mul_eq_mul_div, le_div_iff₀ hd_pos, one_mul]
    exact hdiam
  calc ρ ^ (-(n : ℝ) / p.toReal)
      = (ρ⁻¹) ^ ((n : ℝ) / p.toReal) := by
        rw [Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le, neg_div]
    _ ≤ (γ / d) ^ ((n : ℝ) / p.toReal) :=
        Real.rpow_le_rpow (by positivity) hinv (by positivity)
    _ = γ ^ ((n : ℝ) / p.toReal) * d ^ (-(n : ℝ) / p.toReal) := by
        rw [div_eq_mul_inv, Real.mul_rpow hγ_pos.le (by positivity), Real.inv_rpow hd_pos.le,
          ← Real.rpow_neg hd_pos.le, neg_div]

private theorem norm_setIntegral_le_of_support_subset_closedBall
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (f : Lp F p (mu.restrict Omega))
    {g : E → G} {x₀ : E} {ρ K γ : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) (hγ : 0 ≤ γ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support g ⊆ Metric.closedBall x₀ ρ)
    (hg : ∀ᵐ y ∂mu.restrict (Omega : Set E),
      ‖g y‖ ≤ K * ρ ^ (-(Module.finrank ℝ E : ℝ)) * ‖f y‖) :
    ‖∫ y in Omega, g y ∂mu‖ ≤
      K * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) * ‖f‖ := by
  let n := Module.finrank ℝ E
  let S := (Omega : Set E) ∩ Metric.closedBall x₀ ρ
  rcases (Omega : Set E).eq_empty_or_nonempty with hΩ0 | hΩ_ne
  · rw [setIntegral_eq_zero_of_forall_eq_zero fun _ hy =>
      False.elim (Set.notMem_empty _ (hΩ0 ▸ hy)), norm_zero]
    positivity
  have hB_fin : mu (Metric.closedBall x₀ ρ) < ⊤ := (isCompact_closedBall x₀ ρ).measure_lt_top
  have hS_fin : mu S < ⊤ := (measure_mono inter_subset_right).trans_lt hB_fin
  have : IsFiniteMeasure (mu.restrict S) := isFiniteMeasure_restrict.2 hS_fin.ne
  have hfS : MemLp f p (mu.restrict S) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hgS : ∀ᵐ y ∂mu.restrict S, ‖g y‖ ≤ K * ρ ^ (-(n : ℝ)) * ‖hfS.toLp f y‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hg,
      hfS.coeFn_toLp] with y hy hcoe
    rwa [hcoe]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Omega.isOpen.measurableSet
    inter_subset_left fun y hy => Function.notMem_support.1 fun hgy => hy.2 ⟨hy.1, hsupp hgy⟩]
  have hnorm_le : ‖hfS.toLp f‖ ≤ ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_mono_measure f (Measure.restrict_mono inter_subset_left le_rfl))
  have hbase := (Lp.norm_integral_le_of_ae_norm_le_mul (hfS.toLp f) hgS).trans
    (mul_le_mul_of_nonneg_left hnorm_le (by positivity))
  have hexp : 0 ≤ 1 - 1 / p.toReal := ENNReal.one_sub_one_div_toReal_nonneg Fact.out
  have hmeas_le : ((mu.restrict S) Set.univ ^ (1 - 1 / p.toReal)).toReal ≤
      ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) *
        mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) := by
    rw [Measure.restrict_apply_univ, ← ENNReal.toReal_rpow, ← measureReal_def]
    refine (Real.rpow_le_rpow measureReal_nonneg
      ((measureReal_mono inter_subset_right hB_fin.ne).trans_eq
        (mu.addHaar_real_closedBall x₀ hρ.le)) hexp).trans_eq ?_
    rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast ρ n,
      ← Real.rpow_mul hρ.le]
  have hadd : ρ ^ (-(n : ℝ)) * ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) =
      ρ ^ (-(n : ℝ) / p.toReal) := by rw [← Real.rpow_add hρ]; congr 1; ring
  have hstep1 : ‖∫ y in S, g y ∂mu‖ ≤ K * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
      ρ ^ (-(n : ℝ) / p.toReal) * ‖f‖ :=
    (hbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmeas_le (by positivity)) (norm_nonneg f))).trans_eq
      (by linear_combination K * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) * ‖f‖ * hadd)
  refine hstep1.trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (a := K * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal))
      (rpow_neg_finrank_div_le hΩ_bdd hΩ_ne hρ hdiam) (by positivity))
    (norm_nonneg f)

/-- **Order-zero cutoff integral bound on `W^{k,p}(Ω)`.** For bounded `Ω`, `1 ≤ p ≤ ∞`, and any
weight `φ` supported in `closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) satisfying
`‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`, the integral `∫_Ω (value k u y) φ y` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{-n/p} * ‖value k u‖`. -/
theorem Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p k)
    {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hγ : 0 ≤ γ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, Wkp.value k u y * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.value k u‖ := by
  refine norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd (Wkp.value k u) hρ hM hγ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hφ y hy) (norm_nonneg _)

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted weak
derivatives.** For bounded `Ω`, `1 ≤ p ≤ ∞`, `x ∈ closure Ω`, and `φ` supported in
`closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) with `‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`,
`‖∫_Ω fullContractL k (x - y) (iteratedGradient k u y) φ y‖` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{k + 1 - n/p} * ‖iteratedGradient k u‖`. -/
theorem Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.iteratedGradient k u‖ := by
  let d := Metric.diam (Omega : Set E)
  let n := Module.finrank ℝ E
  rcases (Omega : Set E).eq_empty_or_nonempty with hΩ0 | hΩ_ne
  · rw [setIntegral_eq_zero_of_forall_eq_zero fun _ hy =>
      False.elim (Set.notMem_empty _ (hΩ0 ▸ hy)), norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 hn0
    have hzero : ∀ y, IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) *
        φ y = 0 := fun y => by
      rw [Subsingleton.elim (x - y) 0, IteratedGradient.fullContractL_zero_direction,
        zero_apply, zero_mul]
    simp only [hzero, integral_zero, norm_zero]; positivity
  have hd_pos : 0 < d := diam_pos_of_nonempty_of_finrank_pos hΩ_bdd hΩ_ne hn_pos
  refine (norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd
    (Wkp.iteratedGradient k u) (K := M * d ^ (k + 1)) hρ (by positivity) hγ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
    have hxy : ‖x - y‖ ≤ d := by
      dsimp only [d]; rw [← dist_eq_norm, ← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hΩ_bdd.closure hx (subset_closure hy)
    calc ‖IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y‖
        ≤ (‖Wkp.iteratedGradient k u y‖ * ‖x - y‖ ^ (k + 1)) * ‖φ y‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (IteratedGradient.norm_fullContractL_apply_le k _ _) (norm_nonneg _)
      _ ≤ (‖Wkp.iteratedGradient k u y‖ * d ^ (k + 1)) * (M * ρ ^ (-(n : ℝ))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy _) (norm_nonneg _))
            (hφ y hy) (norm_nonneg _) (by positivity)
      _ = M * d ^ (k + 1) * ρ ^ (-(n : ℝ)) * ‖Wkp.iteratedGradient k u y‖ := by ring
  · have hpow : d ^ (k + 1) * d ^ (-(n : ℝ) / p.toReal) =
        d ^ ((k + 1 : ℝ) - (n : ℝ) / p.toReal) := by
      rw [← Real.rpow_natCast d (k + 1), ← Real.rpow_add hd_pos]; congr 1; push_cast; ring
    linear_combination M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
      γ ^ ((n : ℝ) / p.toReal) * ‖Wkp.iteratedGradient k u‖ * hpow

end Bounds

/-! ### Concrete checks on `(-1, 1) ⊆ ℝ` -/

section Examples

-- Coordinate-free first-order derivative commutation on `(-1, 1) ⊆ ℝ`: differentiating
-- `x ↦ ∫ (x - y) u'(y) φ(y) dy` in direction `1` yields `∫ φ(y) (∂₁ u)(y) dy`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 1)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) (x : ℝ) :
    fderiv ℝ (fun x' => ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y) x 1 =
      ∫ y in Set.Ioo (-1 : ℝ) 1, φ y * Wkp.value 0 (Wkp.lineDerivL 1 0 u) y :=
  Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq u hφ hφc hφs x 1

-- Second-order derivative commutation on `(-1, 1) ⊆ ℝ`: differentiating
-- `x ↦ ∫ (x - y)² u''(y) φ(y) dy` in direction `1` brings down the factor `2`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
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
    {x : ℝ} (hx : x ∈ closure (Set.Ioo (-1 : ℝ) 1)) {φ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsupp : Function.support φ ⊆ Metric.closedBall (0 : ℝ) 1)
    (hφ : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ‖φ y‖ ≤ M) :
    ‖∫ y in Set.Ioo (-1 : ℝ) 1, Wkp.value 1 u y * φ y‖ +
      ‖∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y) (Wkp.iteratedGradient 0 u y) * φ y‖ ≤
      M * ‖Wkp.value 1 u‖ + 2 * M * ‖Wkp.iteratedGradient 0 u‖ := by
  let I : Opens ℝ := ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
  have hbdd : Bornology.IsBounded (I : Set ℝ) := Metric.isBounded_Ioo (-1) 1
  have hdiam : Metric.diam (I : Set ℝ) = 2 := by
    dsimp [I]; rw [Real.diam_Ioo (by norm_num)]; norm_num
  have hφ' : ∀ y ∈ (I : Set ℝ), ‖φ y‖ ≤ M * (1 : ℝ) ^ (-(Module.finrank ℝ ℝ : ℝ)) := by
    intro y hy; simpa using hφ y hy
  have hb0 := Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
    (Omega := I) hbdd 1 u zero_lt_one hM zero_le_two (by linarith [hdiam]) hsupp hφ'
  have hb1 := Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
    (Omega := I) hbdd 0 u hx zero_lt_one hM zero_le_two (by linarith [hdiam]) hsupp hφ'
  simp only [hdiam, Module.finrank_self, Nat.cast_one, ENNReal.toReal_one, div_one, sub_self,
    Real.rpow_zero, mul_one, Real.rpow_one, Nat.cast_zero, zero_add] at hb0 hb1
  have htwo : (2 : ℝ) * (2 : ℝ) ^ (-1 : ℝ) = 1 := by norm_num
  have hb0' : ‖∫ y in (I : Set ℝ), Wkp.value 1 u y * φ y‖ ≤ M * ‖Wkp.value 1 u‖ :=
    hb0.trans_eq (by linear_combination M * ‖Wkp.value 1 u‖ * htwo)
  dsimp [I] at hb0' hb1
  simp only [Real.norm_eq_abs] at hb0' hb1 ⊢
  linarith [hb0', hb1]

end Examples

end TauCeti
