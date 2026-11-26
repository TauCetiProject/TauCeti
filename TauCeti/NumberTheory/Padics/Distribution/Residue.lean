/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Convolution
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic.Residue
public import TauCeti.NumberTheory.Padics.Measure.Residue

/-!
# Restricting locally analytic distributions to residue classes

For `n : ℕ` and `a ∈ ZMod (pⁿ)`, the indicator of the residue class `a + pⁿℤ_p` is locally
analytic, so a locally analytic distribution `μ` on `ℤ_p` restricts to it:
`(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`. This restriction
`TauCeti.LocallyAnalyticDistribution.restrictResidue` is the transpose of the restriction
`TauCeti.LocallyAnalytic.restrictResidue` of locally analytic functions.

As for measures, the restrictions at a fixed depth are orthogonal idempotents adding up to the
identity. Restriction bounds the stage seminorm of level `h` by the stage seminorm of level
`max h n`, so it does not increase the stage seminorms of level at least `n`. Restriction extends
the restriction of measures `AbstractMeasure.restrictResidue` (`restrictResidue_ofMeasure`) and
keeps exactly the point masses in the class (`restrictResidue_dirac`).

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.restrictResidue n a`: restriction of distributions,
  `(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stage_restrictResidue_of_le`: on a stage of level `h ≥ n`,
  restriction is the coordinate projection.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_restrictResidue_le`: restriction bounds the
  stage seminorm of level `h` by that of level `max h n`.
* `TauCeti.LocallyAnalyticDistribution.restrictResidue_comp`,
  `TauCeti.LocallyAnalyticDistribution.sum_restrictResidue`: the restrictions at depth `n` are
  orthogonal idempotents with sum the identity.
* `TauCeti.LocallyAnalyticDistribution.restrictResidue_dirac`,
  `TauCeti.LocallyAnalyticDistribution.restrictResidue_ofMeasure`: compatibility with point masses
  and with the restriction of measures.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

open ZeroAtInftyContinuousMap

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  (n : ℕ) (a : ZMod (p ^ n))

/-- Restriction of a locally analytic distribution to the residue class `a + pⁿℤ_p`:
`(Res_a μ)(f) = μ(1_{a + pⁿℤ_p} f)`. -/
noncomputable def restrictResidue :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K :=
  dualMap (LocallyAnalytic.restrictResidue K n a) (fun _ ↦ AnalyticStage.restrictResidue K n a)
    (LocallyAnalytic.restrictResidue_ofStage K n a)

/-- The restriction `Res_a μ` takes the value `μ(1_{a + pⁿℤ_p} f)` on `f`. -/
@[simp]
theorem coe_restrictResidue_apply (μ : LocallyAnalyticDistribution p K)
    (f : LocallyAnalytic p K K) :
    (restrictResidue n a μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.restrictResidue K n a f) :=
  coe_dualMap_apply μ f

/-- The restriction of `Res_a μ` to the stage of level `h` is the restriction of `μ` to the stage
of level `max h n` composed with the restriction of coefficient vectors. -/
@[simp]
theorem stage_restrictResidue (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (restrictResidue n a μ) = stage (max h n) μ ∘L AnalyticStage.restrictResidue K n a :=
  stage_dualMap h μ

/-- On a stage of level `h ≥ n`, the restriction of `Res_a μ` is the restriction of `μ` composed
with the projection onto the discs of the classes in `a + pⁿℤ_p`. -/
theorem stage_restrictResidue_of_le {h : ℕ} (hnh : n ≤ h) (μ : LocallyAnalyticDistribution p K) :
    stage h (restrictResidue n a μ) =
      stage h μ ∘L
        indicatorCLM K (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a}) := by
  ext c
  simp [AnalyticStage.restrictResidue_of_le K n a hnh]

/-- Restriction to a residue class modulo `pⁿ` bounds the stage seminorm of level `h` by the stage
seminorm of level `max h n`. -/
theorem stageSeminorm_restrictResidue_le (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (restrictResidue n a μ) ≤ stageSeminorm (max h n) μ :=
  (stageSeminorm_dualMap_le h μ).trans
    (mul_le_of_le_one_left (apply_nonneg _ _) (opNorm_restrictResidue_le_one n a))

/-- The restrictions to the residue classes modulo `pⁿ` are orthogonal idempotents. -/
theorem restrictResidue_comp (b : ZMod (p ^ n)) (μ : LocallyAnalyticDistribution p K) :
    restrictResidue n a (restrictResidue n b μ) =
      if a = b then restrictResidue n a μ else 0 := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  by_cases hab : a = b
  · subst hab
    simp
  · simp [LocallyAnalytic.restrictResidue_comp, hab, Ne.symm hab]

/-- Restricting twice to the same residue class is restricting once. -/
@[simp]
theorem restrictResidue_idem (μ : LocallyAnalyticDistribution p K) :
    restrictResidue n a (restrictResidue n a μ) = restrictResidue n a μ := by
  simp [restrictResidue_comp]

/-- A distribution is the sum of its restrictions to the residue classes modulo `pⁿ`. -/
@[simp]
theorem sum_restrictResidue (μ : LocallyAnalyticDistribution p K) :
    ∑ a : ZMod (p ^ n), restrictResidue n a μ = μ := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [Submodule.coe_sum, LinearMap.sum_apply]
  simp only [coe_restrictResidue_apply, ← map_sum, LocallyAnalytic.sum_restrictResidue]

/-- Modulo `p ^ 0 = 1` there is a single residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (μ : LocallyAnalyticDistribution p K) :
    restrictResidue 0 a μ = μ :=
  Subtype.ext <| LinearMap.ext fun f ↦ by simp

/-- On the distribution of a measure, restriction to a residue class is the restriction of the
measure. -/
@[simp]
theorem restrictResidue_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    restrictResidue n a (ofMeasure μ) = ofMeasure (AbstractMeasure.restrictResidue n a μ) := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  rw [coe_restrictResidue_apply, coe_ofMeasure_apply, coe_ofMeasure_apply,
    AbstractMeasure.restrictResidue_apply]
  congr 1
  ext x
  simp [ContinuousMap.fiberIndicator_apply]

/-- Restriction to a residue class keeps exactly the point masses in the class. -/
@[simp]
theorem restrictResidue_dirac (x : ℤ_[p]) :
    restrictResidue n a (dirac (K := K) x) = if PadicInt.toZModPow n x = a then dirac x else 0 := by
  rw [← ofMeasure_dirac, restrictResidue_ofMeasure, AbstractMeasure.restrictResidue_dirac]
  split_ifs <;> simp

end LocallyAnalyticDistribution

end TauCeti
