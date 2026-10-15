/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.EntropicTransport
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Entropy

/-!
# Finite entropic transport as measure-theoretic entropic transport

This file identifies the finite matrix formulas for entropic optimal transport with the generic
measure-theoretic definitions. For probability mass functions `μ` and `ν` on finite spaces, a
transportation matrix `A` represents the coupling `A.toPMF.toMeasure`. Its matrix objective is the
real form of the sum of the transport integral and the Kullback--Leibler divergence from
`μ.toMeasure.prod ν.toMeasure`.

The same conventions agree on the dual side. The measure-theoretic Gibbs factor splits into the
row scaling, the finite Gibbs kernel, and the column scaling. Consequently the generic entropic
dual value is the temperature times `Matrix.relEntropyDual` after rescaling the potentials by the
temperature.

## Main results

* `TauCeti.TransportMatrix.ofReal_entropicTransportObjective_eq`: the matrix primal objective is
  the real representative of the measure-theoretic primal objective.
* `Matrix.ofReal_entropicTransportValue_eq`: the finite and measure-theoretic primal values agree.
* `Matrix.isDiagonalScaling_gibbs_iff`: finite diagonal scaling is exactly the generic Gibbs
  density formula.
* `Matrix.entropicDualValue_eq_mul_relEntropyDual`: the generic and finite dual objectives agree.
-/

public section

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators NNReal

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

end TauCeti

namespace PMF

variable {ι κ : Type*}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The real mass of a singleton under the product of two PMF measures is the product of their
point masses. -/
private theorem real_prod_toMeasure_singleton (μ : PMF ι) (ν : PMF κ) (i : ι) (j : κ) :
    (μ.toMeasure.prod ν.toMeasure).real {(i, j)} = (μ i).toReal * (ν j).toReal := by
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod, Measure.real,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.real,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

end PMF

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

namespace TransportMatrix

variable {μ : PMF ι} {ν : PMF κ}

/-- The finite matrix objective is the real representative of the measure-theoretic entropic
objective of the associated coupling. -/
theorem ofReal_entropicTransportObjective_eq (A : TransportMatrix μ ν) (C : Matrix ι κ ℝ)
    (ε : ℝ≥0) (hC : ∀ i j, 0 ≤ C i j) :
    ENNReal.ofReal
        (C.entropicTransportObjective ε (fun i ↦ (μ i).toReal) (fun j ↦ (ν j).toReal)
          (Matrix.of fun i j ↦ A.toRealFun (i, j))) =
      (∫⁻ q, ENNReal.ofReal (C q.1 q.2) ∂A.toPMF.toMeasure) +
        ε * klDiv A.toPMF.toMeasure (μ.toMeasure.prod ν.toMeasure) := by
  have hπ (i : ι) (j : κ) :
      A.toPMF.toMeasure.real {(i, j)} = A.toRealFun (i, j) := by
    rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [toPMF_apply, toRealFun_apply]
  have hR (i : ι) (j : κ) :
      (μ.toMeasure.prod ν.toMeasure).real {(i, j)} =
        (μ i).toReal * (ν j).toReal :=
    μ.real_prod_toMeasure_singleton ν i j
  have hkl :
      klDiv A.toPMF.toMeasure (μ.toMeasure.prod ν.toMeasure) =
        ENNReal.ofReal (Matrix.relEntropy
          (Matrix.of fun i j ↦ A.toRealFun (i, j))
          (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal)) := by
    rw [Measure.klDiv_eq_ofReal_relEntropy_add_mass_correction_of_real_singleton
      A.toPMF.toMeasure (μ.toMeasure.prod ν.toMeasure)
      (Matrix.of fun i j ↦ A.toRealFun (i, j))
      (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal)
      hπ hR (fun i j h ↦ by
        simp only [Matrix.vecMulVec_apply, mul_eq_zero] at h
        rcases h with h | h
        · exact le_antisymm (h ▸ le_toReal_fst_of_mem_realPlans
            A.toRealFun_mem_realPlans (i, j)) (A.toRealFun_nonneg (i, j))
        · exact le_antisymm (h ▸ le_toReal_snd_of_mem_realPlans
            A.toRealFun_mem_realPlans (i, j)) (A.toRealFun_nonneg (i, j)))]
    simp
  have hcost_nonneg :
      0 ≤ ∑ i, ∑ j, C i j * A.toRealFun (i, j) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (hC i j) (A.toRealFun_nonneg (i, j))
  have hcost :
      ENNReal.ofReal (∑ i, ∑ j, C i j * A.toRealFun (i, j)) =
        ∫⁻ q, ENNReal.ofReal (C q.1 q.2) ∂A.toPMF.toMeasure := by
    have hsum : (∑ i, ∑ j, C i j * A.toRealFun (i, j)) =
        A.cost (fun q ↦ C q.1 q.2) := by
      rw [A.cost_def, Fintype.sum_prod_type]
    rw [hsum, A.cost_eq_integral,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal Integrable.of_finite]
    exact Filter.Eventually.of_forall fun q ↦ hC q.1 q.2
  have hentropy_nonneg :
      0 ≤ Matrix.relEntropy
        (Matrix.of fun i j ↦ A.toRealFun (i, j))
        (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal) :=
    relEntropy_vecMulVec_nonneg_of_mem_realPlans A.toRealFun_mem_realPlans
  rw [Matrix.entropicTransportObjective_def]
  simp only [Matrix.of_apply]
  rw [
    ENNReal.ofReal_add hcost_nonneg (mul_nonneg ε.coe_nonneg hentropy_nonneg), hcost, hkl,
    ENNReal.ofReal_mul ε.coe_nonneg]
  simp

end TransportMatrix

end TauCeti

namespace Matrix

variable {ι κ : Type*}

section Finite

variable [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The finite matrix entropic transport value is the real representative of the generic
measure-theoretic entropic transport cost. -/
theorem ofReal_entropicTransportValue_eq (C : Matrix ι κ ℝ) (ε : ℝ≥0)
    (μ : PMF ι) (ν : PMF κ) (hC : ∀ i j, 0 ≤ C i j) :
    ENNReal.ofReal (C.entropicTransportValue ε (fun i ↦ (μ i).toReal)
      (fun j ↦ (ν j).toReal)) =
      TauCeti.entropicTransportCost (fun q ↦ ENNReal.ofReal (C q.1 q.2)) ε
        μ.toMeasure ν.toMeasure := by
  let A₀ := TauCeti.TransportMatrix.independent μ ν
  have hA₀ : Matrix.of (fun i j ↦ A₀.toRealFun (i, j)) ∈
      transportPolytope (fun i ↦ (μ i).toReal) (fun j ↦ (ν j).toReal) := by
    rw [mem_transportPolytope, hasMarginals_def]
    exact ⟨fun i j ↦ A₀.toRealFun_mem_realPlans.1 (i, j),
      A₀.toRealFun_mem_realPlans.2⟩
  obtain ⟨P, hP, hPmin⟩ := exists_isMinOn_entropicTransportObjective
    (a := fun i ↦ (μ i).toReal) (b := fun j ↦ (ν j).toReal) C ε
    ⟨Matrix.of fun i j ↦ A₀.toRealFun (i, j), hA₀⟩
  have hPdata := (mem_transportPolytope (P := P)
    (a := fun i ↦ (μ i).toReal) (b := fun j ↦ (ν j).toReal)).mp hP
  have hP' : (fun q ↦ P q.1 q.2) ∈ TauCeti.RealPlans μ ν := by
    exact ⟨fun q ↦ hPdata.1 q.1 q.2, (hasMarginals_def _ _ _).1 hPdata.2⟩
  let A := TauCeti.TransportMatrix.ofRealFun hP'
  have hA : Matrix.of (fun i j ↦ A.toRealFun (i, j)) = P := by
    ext i j
    simpa [A] using congrFun (TauCeti.TransportMatrix.toRealFun_ofRealFun hP') (i, j)
  rw [entropicTransportValue_eq_of_isMinOn hP hPmin]
  rw [← hA, TauCeti.TransportMatrix.ofReal_entropicTransportObjective_eq A C ε hC]
  apply le_antisymm
  · exact TauCeti.le_entropicTransportCost fun π hπ ↦ by
      obtain ⟨B, rfl⟩ := hπ.exists_transportMatrix
      rw [← TauCeti.TransportMatrix.ofReal_entropicTransportObjective_eq A C ε hC,
        ← TauCeti.TransportMatrix.ofReal_entropicTransportObjective_eq B C ε hC]
      apply ENNReal.ofReal_le_ofReal
      rw [hA]
      apply isMinOn_iff.1 hPmin
      rw [mem_transportPolytope, hasMarginals_def]
      exact ⟨fun i j ↦ B.toRealFun_mem_realPlans.1 (i, j),
        B.toRealFun_mem_realPlans.2⟩
  · exact TauCeti.entropicTransportCost_le A.isCoupling_toPMF_toMeasure _ _

end Finite

/-- A matrix is a diagonal scaling of the product-weighted Gibbs kernel exactly when its
entries are the product reference masses multiplied by the generic Gibbs factor. -/
theorem isDiagonalScaling_gibbs_iff (P C : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ε : ℝ≥0) (φ : ι → ℝ) (ψ : κ → ℝ) (hC : ∀ i j, 0 ≤ C i j) :
    IsDiagonalScaling P
        (of fun i j ↦ a i * b j * Real.exp (-C i j / ε))
        (fun i ↦ Real.exp (φ i / ε)) (fun j ↦ Real.exp (ψ j / ε)) ↔
      ∀ i j, P i j = a i * b j *
        TauCeti.entropicGibbsFactor (fun q ↦ ENNReal.ofReal (C q.1 q.2)) ε φ ψ (i, j) := by
  rw [isDiagonalScaling_def]
  constructor <;> intro h i j
  · rw [h i j, of_apply,
      entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp C ε φ ψ i j (hC i j)]
    ring
  · rw [h i j, of_apply,
      entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp C ε φ ψ i j (hC i j)]
    ring

end Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- On finite probability spaces, the generic entropic dual objective is the temperature times
the matrix relative-entropy dual objective for the product-weighted Gibbs kernel. -/
theorem entropicDualValue_eq_mul_relEntropyDual (C : Matrix ι κ ℝ) (ε : ℝ≥0)
    (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ) (hε : ε ≠ 0)
    (hC : ∀ i j, 0 ≤ C i j) :
    TauCeti.entropicDualValue (fun q ↦ ENNReal.ofReal (C q.1 q.2)) ε
      μ.toMeasure ν.toMeasure φ ψ =
      ε * (Matrix.of fun i j ↦ (μ i).toReal * (ν j).toReal * Real.exp (-C i j / ε)).relEntropyDual
        (fun i ↦ (μ i).toReal) (fun j ↦ (ν j).toReal)
        (fun i ↦ φ i / ε) (fun j ↦ ψ j / ε) := by
  have hprod (i : ι) (j : κ) :
      (μ.toMeasure.prod ν.toMeasure).real {(i, j)} =
        (μ i).toReal * (ν j).toReal :=
    μ.real_prod_toMeasure_singleton ν i j
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hmass : ∑ i, ∑ j, (μ i).toReal * (ν j).toReal = 1 := by
    simp_rw [← Finset.mul_sum]
    simp
  have hpenalty :
      (∑ i, ∑ j, (μ i).toReal * (ν j).toReal *
        (Real.exp (φ i / ε) * Real.exp (-C i j / ε) * Real.exp (ψ j / ε) - 1)) =
        (∑ i, ∑ j, Real.exp (φ i / ε) *
          ((μ i).toReal * (ν j).toReal * Real.exp (-C i j / ε)) *
            Real.exp (ψ j / ε)) - 1 := by
    calc
      _ = (∑ i, ∑ j, (μ i).toReal * (ν j).toReal *
            (Real.exp (φ i / ε) * Real.exp (-C i j / ε) * Real.exp (ψ j / ε))) -
          ∑ i, ∑ j, (μ i).toReal * (ν j).toReal := by
            simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = _ := by
        rw [hmass]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hφ :
      (ε : ℝ) * ∑ i, (μ i).toReal * (φ i / ε) = ∑ i, (μ i).toReal * φ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
  have hψ :
      (ε : ℝ) * ∑ j, (ν j).toReal * (ψ j / ε) = ∑ j, (ν j).toReal * ψ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp
  rw [TauCeti.entropicDualValue_def, ← TauCeti.finiteDualValue_eq_kantorovichDualValue,
    MeasureTheory.integral_fintype Integrable.of_finite, Matrix.relEntropyDual_def,
    Fintype.sum_prod_type]
  simp_rw [hprod,
    entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp C ε φ ψ _ _ (hC _ _)]
  simp only [TauCeti.finiteDualValue_def, Matrix.of_apply, smul_eq_mul, PMF.sum_toReal_eq_one]
  rw [hpenalty]
  linear_combination -hφ - hψ

end Matrix
