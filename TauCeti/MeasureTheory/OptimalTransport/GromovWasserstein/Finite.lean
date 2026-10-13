/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic

/-!
# Finite Gromov–Wasserstein objectives

The distortion of a finite transport matrix is exactly the weighted four-index sum of kernel
discrepancies. At exponent two this is the usual quadratic objective in the coupling entries.
The infimum over these matrices is the generic measured-kernel Gromov–Wasserstein distance;
there is no extra factor of `1 / 2`.

For kernels valued in a pseudometric space, `TauCeti.gromovWassersteinObjective p ωX ωY f` is the
same four-index sum read in `ℝ`, as a function of a real transport plan `f : ι × κ → ℝ`. It is
continuous, so it attains its minimum on the compact set `TauCeti.RealPlans μ ν` of real plans with
marginals `μ` and `ν`. On a transport matrix and for `0 < p < ∞` it is the `p`-th power of the
measure-theoretic distortion, so its minimizers are exactly the optimal couplings of the
Gromov–Wasserstein problem (`TauCeti.isMinOn_gromovWassersteinObjective_iff`).

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Definition 11 and §5.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace TauCeti

section Objective

variable {ι κ Z : Type*} [Fintype ι] [Fintype κ] [PseudoMetricSpace Z]

/-- The finite Gromov–Wasserstein objective of a real plan `f`: the sum over pairs of pairs
`q = (i, j)`, `q' = (i', j')` of `d(ωX (i, i'), ωY (j, j')) ^ p * f q * f q'`. On a transport
matrix and for `0 < p < ∞` it is the `p`-th power of `TauCeti.gromovWassersteinDistortion`
(`TauCeti.TransportMatrix.gromovWassersteinObjective_toRealFun`). -/
def gromovWassersteinObjective (p : ℝ) (ωX : ι × ι → Z) (ωY : κ × κ → Z) (f : ι × κ → ℝ) : ℝ :=
  ∑ q, ∑ q', dist (ωX (q.1, q'.1)) (ωY (q.2, q'.2)) ^ p * f q * f q'

theorem gromovWassersteinObjective_def (p : ℝ) (ωX : ι × ι → Z) (ωY : κ × κ → Z)
    (f : ι × κ → ℝ) :
    gromovWassersteinObjective p ωX ωY f =
      ∑ q, ∑ q', dist (ωX (q.1, q'.1)) (ωY (q.2, q'.2)) ^ p * f q * f q' :=
  (rfl)

theorem continuous_gromovWassersteinObjective (p : ℝ) (ωX : ι × ι → Z) (ωY : κ × κ → Z) :
    Continuous (gromovWassersteinObjective p ωX ωY) := by
  simp_rw [funext (gromovWassersteinObjective_def p ωX ωY)]
  fun_prop

/-- The finite Gromov–Wasserstein objective has a global minimizer among the real plans. -/
theorem exists_isMinOn_gromovWassersteinObjective (p : ℝ) (μ : PMF ι) (ωX : ι × ι → Z)
    (ν : PMF κ) (ωY : κ × κ → Z) :
    ∃ f ∈ RealPlans μ ν, IsMinOn (gromovWassersteinObjective p ωX ωY) (RealPlans μ ν) f :=
  isCompact_realPlans.exists_isMinOn (realPlans_nonempty μ ν)
    (continuous_gromovWassersteinObjective p ωX ωY).continuousOn

/-- With kernels valued in a pseudometric space, every term of the four-index objective of a
transport matrix is finite. -/
private theorem TransportMatrix.edist_rpow_mul_mul_ne_top {μ : PMF ι} {ν : PMF κ}
    (A : TransportMatrix μ ν) (ωX : ι × ι → Z) (ωY : κ × κ → Z) {r : ℝ}
    (hr : 0 ≤ r) (i : ι) (j : κ) (i' : ι) (j' : κ) :
    edist (ωX (i, i')) (ωY (j, j')) ^ r * A i j * A i' j' ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr (edist_ne_top _ _))
    (A.apply_ne_top _ _)) (A.apply_ne_top _ _)

end Objective

variable {ι κ Z : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSpace κ]
  [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
  {μ : PMF ι} {ν : PMF κ}

section EDist

variable [EDist Z]

/-- For a finite nonzero exponent, the powered distortion is the four-index matrix objective.
The target and its distances may be extended-valued. -/
theorem TransportMatrix.gromovWassersteinDistortion_rpow (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ^ p.toReal =
      ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ p.toReal * A i j * A i' j' := by
  rw [gromovWassersteinDistortion_def,
    eLpNorm_rpow_eq_lintegral hp0 hp (measurable_of_countable _).aemeasurable,
    lintegral_countable', tsum_fintype]
  simp only [Fintype.sum_prod_type, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    TransportMatrix.toPMF_apply, mul_assoc]

/-- The square of the two-distortion is the standard nonconvex quadratic GW objective. -/
theorem TransportMatrix.gromovWassersteinDistortion_sq (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) :
    gromovWassersteinDistortion 2 ωX ωY A.toPMF.toMeasure ^ 2 =
      ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' := by
  simpa using A.gromovWassersteinDistortion_rpow ωX ωY (p := 2) (by norm_num) (by norm_num)

/-- Infimizing the finite matrix distortions gives exactly the generic GW distance. -/
theorem gromovWassersteinEDist_eq_iInf_transportMatrix (p : ℝ≥0∞)
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist p μ.toMeasure ωX ν.toMeasure ωY =
      ⨅ A : TransportMatrix μ ν, gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure := by
  refine le_antisymm (le_iInf fun A ↦ gromovWassersteinEDist_le
    A.isCoupling_toPMF_toMeasure p ωX ωY) (le_gromovWassersteinEDist fun π hπ ↦ ?_)
  obtain ⟨A, rfl⟩ := hπ.exists_transportMatrix
  exact iInf_le _ A

/-- The finite GW problem is the infimum of the weighted four-index objectives. -/
theorem gromovWassersteinEDist_rpow_eq_iInf_transportMatrix {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist p μ.toMeasure ωX ν.toMeasure ωY ^ p.toReal =
      ⨅ A : TransportMatrix μ ν, ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ p.toReal * A i j * A i' j' := by
  rw [gromovWassersteinEDist_eq_iInf_transportMatrix,
    ← ENNReal.orderIsoRpow_apply p.toReal (ENNReal.toReal_pos hp0 hp), OrderIso.map_iInf]
  exact iInf_congr fun A ↦ A.gromovWassersteinDistortion_rpow ωX ωY hp0 hp

/-- Squared GW distance is the infimum of the quadratic matrix objective. -/
theorem gromovWassersteinEDist_sq_eq_iInf_transportMatrix
    (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    gromovWassersteinEDist 2 μ.toMeasure ωX ν.toMeasure ωY ^ 2 =
      ⨅ A : TransportMatrix μ ν, ∑ i, ∑ j, ∑ i', ∑ j',
        edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' := by
  simpa using gromovWassersteinEDist_rpow_eq_iInf_transportMatrix (p := 2)
    (by norm_num) (by norm_num) μ ωX ν ωY

end EDist

/-- For metric-valued matrices, the finite quadratic objective can be read entirely in `ℝ`. -/
theorem TransportMatrix.toReal_gromovWassersteinDistortion_sq [PseudoMetricSpace Z]
    (A : TransportMatrix μ ν) (ωX : ι × ι → Z) (ωY : κ × κ → Z) :
    (gromovWassersteinDistortion 2 ωX ωY A.toPMF.toMeasure).toReal ^ 2 =
      ∑ i, ∑ j, ∑ i', ∑ j',
        dist (ωX (i, i')) (ωY (j, j')) ^ 2 * (A i j).toReal * (A i' j').toReal := by
  have hfin : ∀ i j i' j',
      edist (ωX (i, i')) (ωY (j, j')) ^ 2 * A i j * A i' j' ≠ ∞ := by
    intros
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (edist_ne_top _ _))
      (A.apply_ne_top _ _)) (A.apply_ne_top _ _)
  have h := congrArg ENNReal.toReal (A.gromovWassersteinDistortion_sq ωX ωY)
  simpa (disch := simp [ENNReal.sum_ne_top, hfin]) only [ENNReal.toReal_sum,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ← dist_edist] using h

section PseudoMetricSpace

variable [PseudoMetricSpace Z] {ωX : ι × ι → Z} {ωY : κ × κ → Z} {f : ι × κ → ℝ}

/-- On a transport matrix and for `0 < p < ∞`, the finite objective at exponent `p.toReal` is the
`p`-th power of the measure-theoretic distortion of the associated coupling. -/
theorem TransportMatrix.gromovWassersteinObjective_toRealFun (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    gromovWassersteinObjective p.toReal ωX ωY A.toRealFun =
      (gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ^ p.toReal).toReal := by
  rw [A.gromovWassersteinDistortion_rpow ωX ωY hp0 hp, gromovWassersteinObjective_def]
  simp (disch := simp [ENNReal.sum_ne_top, A.edist_rpow_mul_mul_ne_top]) only
    [ENNReal.toReal_sum, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← dist_edist,
      Fintype.sum_prod_type, TransportMatrix.toRealFun_apply]

/-- The distortion of a transport matrix is finite: the kernels take values in a pseudometric
space and there are finitely many atoms. -/
theorem TransportMatrix.gromovWassersteinDistortion_ne_top (A : TransportMatrix μ ν)
    (ωX : ι × ι → Z) (ωY : κ × κ → Z) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ≠ ∞ := by
  have hpow : gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ^ p.toReal ≠ ∞ := by
    rw [A.gromovWassersteinDistortion_rpow ωX ωY hp0 hp]
    simp only [ne_eq, ENNReal.sum_eq_top, not_exists, not_and]
    exact fun i _ j _ i' _ j' _ ↦
      A.edist_rpow_mul_mul_ne_top ωX ωY ENNReal.toReal_nonneg i j i' j'
  intro h
  exact hpow (by rw [h, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp0 hp)])

/-- A real plan minimizes the finite objective at exponent `p.toReal`, for `0 < p < ∞`, exactly
when the distortion of the associated coupling is the Gromov–Wasserstein distance. So the
minimizers of the finite objective are the optimal couplings of the measure-theoretic problem. -/
theorem isMinOn_gromovWassersteinObjective_iff {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hf : f ∈ RealPlans μ ν) :
    IsMinOn (gromovWassersteinObjective p.toReal ωX ωY) (RealPlans μ ν) f ↔
      gromovWassersteinDistortion p ωX ωY (TransportMatrix.ofRealFun hf).toPMF.toMeasure =
        gromovWassersteinEDist p μ.toMeasure ωX ν.toMeasure ωY := by
  have key : ∀ A B : TransportMatrix μ ν,
      gromovWassersteinObjective p.toReal ωX ωY A.toRealFun ≤
          gromovWassersteinObjective p.toReal ωX ωY B.toRealFun ↔
        gromovWassersteinDistortion p ωX ωY A.toPMF.toMeasure ≤
          gromovWassersteinDistortion p ωX ωY B.toPMF.toMeasure := fun A B ↦ by
    have hpos := ENNReal.toReal_pos hp0 hp
    rw [A.gromovWassersteinObjective_toRealFun ωX ωY hp0 hp,
      B.gromovWassersteinObjective_toRealFun ωX ωY hp0 hp,
      ENNReal.toReal_le_toReal
        (ENNReal.rpow_ne_top_of_nonneg hpos.le (A.gromovWassersteinDistortion_ne_top ωX ωY hp0 hp))
        (ENNReal.rpow_ne_top_of_nonneg hpos.le (B.gromovWassersteinDistortion_ne_top ωX ωY hp0 hp)),
      ENNReal.rpow_le_rpow_iff hpos]
  rw [gromovWassersteinEDist_eq_iInf_transportMatrix, isMinOn_iff]
  constructor
  · refine fun h ↦ le_antisymm (le_iInf fun B ↦ (key _ B).1 ?_) (iInf_le _ _)
    simpa [TransportMatrix.toRealFun_ofRealFun] using h _ B.toRealFun_mem_realPlans
  · intro h g hg
    simpa [TransportMatrix.toRealFun_ofRealFun] using
      (key (.ofRealFun hf) (.ofRealFun hg)).2 (h ▸ iInf_le _ _)

end PseudoMetricSpace

end TauCeti
