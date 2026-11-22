/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.PiLp
public import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Endpoints
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
import TauCeti.Analysis.Normed.Lp.PiLp.Holder
import TauCeti.MeasureTheory.Integral.Bochner.PiLp

/-!
# Complex interpolation of finite vector-valued sequence spaces

Given a finite index type `ι`, exponents `1 ≤ q₀, q₁, q ≤ ∞`, a family of compatible couples
`C : ∀ i : ι, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)`, and `θ : ℝ` satisfying
`q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`, we prove the finite-index case of
**Bergh–Löfström, Theorem 5.1.2** (including `∞` endpoints), with no completeness, duality, or
density assumptions on `C i`:

`(piLp C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ)`.

For `θ ∈ [0, 1]`, the exponent hypothesis reduces to the usual Riesz–Thorin relation
`1 / q = (1 - θ) / q₀ + θ / q₁`. Outside `[0, 1]`, `ENNReal.ofReal` clamps negative weights to `0`
so the formal hypothesis differs from the real reciprocal relation; however, both
`(piLp C q₀ q₁).ComplexMethodSpace θ` and `(C i).ComplexMethodSpace θ` are zero
(`eq_zero_of_notMem`), so the isometry still holds degenerately.

## Main declarations

* `CompatibleCouple.piLpStripTracesEquiv`: canonical coordinatewise continuous linear equivalence
  for admissible boundary traces.
* `CompatibleCouple.ComplexMethodSpace.piLpContinuousLinearEquiv`: coordinatewise continuous linear
  equivalence `(piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.
* `CompatibleCouple.ComplexMethodSpace.piLpEquiv`: **Bergh–Löfström, Theorem 5.1.2** upgrading
  `piLpContinuousLinearEquiv` to a linear isometric equivalence under the exponent relation.
* `CompatibleCouple.ComplexMethodSpace.piLpReflEquiv`: `[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X`
  for `0 ≤ θ ≤ 1`.

## Implementation notes

For `0 < θ < 1`, the upper norm bound applies `norm_mk_le_stripPoisson_geometricMean`
coordinatewise, then log-convex Hölder in `PiLp` (`PiLp.norm_toLp_rpow_mul_rpow_le`) and
Bochner–Minkowski via `ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le`. For the reverse
bound (`q < ∞`), near-optimal traces `g i` with `‖g i‖ < b i` (`b i = ‖v i‖ + δ`, `B = ‖b‖_{ℓ^q}`)
are rescaled using `scaleFactor` with `M₀ = (b i / B) ^ (1 - α₀)` and
`M₁ = (b i / B) ^ (1 - α₁)`, where `α_j = q.toReal * (q_j⁻¹).toReal`. Endpoints `θ = 0, 1` follow
directly from `norm_mk_zero` and `norm_mk_one`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math.
  **24** (1964), 113–190, §13.6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines MeasureTheory Set TauCeti.Complex.HadamardThreeLines
open scoped ENNReal ZeroAtInfty

namespace TauCeti

namespace CompatibleCouple

section ComplexTraces

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

private def piLpStripTracesFwd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).stripTraces →L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearMap.pi fun i =>
    stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i)

private def piLpStripTracesInv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (∀ i, (C i).stripTraces) →L[ℂ] (piLp C q₀ q₁).stripTraces := by
  classical
  exact ∑ i : ι, (stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (piLpSingle_inter C q₀ q₁ i)).comp (ContinuousLinearMap.proj i)

private theorem piLpStripTracesFwd_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι) :
    piLpStripTracesFwd C q₀ q₁ g i =
      stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i) g :=
  ContinuousLinearMap.pi_apply _ _ i

private theorem piLpStripTracesFwd_apply_fst (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  rw [piLpStripTracesFwd_apply, stripTracesMap_apply_fst, PiLp.proj_apply]

private theorem piLpStripTracesFwd_apply_snd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  rw [piLpStripTracesFwd_apply, stripTracesMap_apply_snd, PiLp.proj_apply]

private theorem piLpStripTracesInv_apply_fst (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) (t : ℝ)
    (j : ι) :
    ((piLpStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).1 t := by
  classical
  simp only [piLpStripTracesInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.fst_sum, WithLp.ofLp_sum,
    stripTracesMap_apply_fst, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun i hij => PiLp.single_eq_of_ne q₀ hij.symm _),
    PiLp.single_eq_same]

private theorem piLpStripTracesInv_apply_snd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) (t : ℝ)
    (j : ι) :
    ((piLpStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).2 t := by
  classical
  simp only [piLpStripTracesInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.snd_sum, WithLp.ofLp_sum,
    stripTracesMap_apply_snd, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun i hij => PiLp.single_eq_of_ne q₁ hij.symm _),
    PiLp.single_eq_same]

/-- Admissible boundary traces for `CompatibleCouple.piLp C q₀ q₁` identify canonically with tuples
of admissible boundary traces `∀ i, (C i).stripTraces` via coordinatewise projection. -/
def piLpStripTracesEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).stripTraces ≃L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpStripTracesFwd C q₀ q₁)
    (piLpStripTracesInv C q₀ q₁)
    (ContinuousLinearMap.ext fun h => funext fun j => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun t => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          piLpStripTracesFwd_apply_fst, piLpStripTracesInv_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun t => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          piLpStripTracesFwd_apply_snd, piLpStripTracesInv_apply_snd])))
    (ContinuousLinearMap.ext fun g => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          piLpStripTracesInv_apply_fst, piLpStripTracesFwd_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          piLpStripTracesInv_apply_snd, piLpStripTracesFwd_apply_snd])))

private theorem piLpStripTracesEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) :
    piLpStripTracesEquiv C q₀ q₁ g = piLpStripTracesFwd C q₀ q₁ g := by
  dsimp [piLpStripTracesEquiv]

private theorem piLpStripTracesEquiv_symm_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) :
    (piLpStripTracesEquiv C q₀ q₁).symm h = piLpStripTracesInv C q₀ q₁ h := by
  dsimp [piLpStripTracesEquiv]

@[simp]
theorem piLpStripTracesEquiv_apply_fst (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  rw [piLpStripTracesEquiv_apply, piLpStripTracesFwd_apply_fst]

@[simp]
theorem piLpStripTracesEquiv_apply_snd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  rw [piLpStripTracesEquiv_apply, piLpStripTracesFwd_apply_snd]

@[simp]
theorem piLpStripTracesEquiv_symm_apply_fst (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) (t : ℝ) (i : ι) :
    (((piLpStripTracesEquiv C q₀ q₁).symm h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t := by
  rw [← piLpStripTracesEquiv_apply_fst, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem piLpStripTracesEquiv_symm_apply_snd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) (t : ℝ) (i : ι) :
    (((piLpStripTracesEquiv C q₀ q₁).symm h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t := by
  rw [← piLpStripTracesEquiv_apply_snd, ContinuousLinearEquiv.apply_symm_apply]

/-- Evaluation at `z` commutes coordinatewise with `piLpStripTracesEquiv`. -/
theorem stripEval_piLpStripTracesEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (z : ℂ) (g : (piLp C q₀ q₁).stripTraces)
    (i : ι) :
    (C i).stripEval z (piLpStripTracesEquiv C q₀ q₁ g i) =
      piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).stripEval z g) i := by
  rw [piLpStripTracesEquiv_apply, piLpStripTracesFwd_apply,
    stripEval_stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
      (piLpProj_inter C q₀ q₁ i),
    ← piLpSumEquiv_apply_eq_sumLift]

/-- `stripFunction` evaluation at `z` commutes coordinatewise with `piLpStripTracesEquiv`. -/
@[simp]
theorem stripFunction_piLpStripTracesEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (z : ℂ) :
    (C i).stripFunction (piLpStripTracesEquiv C q₀ q₁ g i) z =
      piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).stripFunction g z) i := by
  simpa only [stripEval_apply] using stripEval_piLpStripTracesEquiv_apply C q₀ q₁ z g i

/-- Evaluation at `z` on a trace pair assembled with `(piLpStripTracesEquiv C q₀ q₁).symm h`
projects coordinatewise to `(C i).stripEval z (h i)`. -/
theorem piLpSumEquiv_stripEval_piLpStripTracesEquiv_symm
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (z : ℂ) (h : ∀ i, (C i).stripTraces) (i : ι) :
    piLpSumEquiv C q₀ q₁
        ((piLp C q₀ q₁).stripEval z ((piLpStripTracesEquiv C q₀ q₁).symm h)) i =
      (C i).stripEval z (h i) := by
  rw [← stripEval_piLpStripTracesEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- `stripFunction` evaluation at `z` on a trace pair assembled with
`(piLpStripTracesEquiv C q₀ q₁).symm h` projects coordinatewise to `(C i).stripFunction (h i) z`. -/
@[simp]
theorem piLpSumEquiv_stripFunction_piLpStripTracesEquiv_symm
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (h : ∀ i, (C i).stripTraces) (z : ℂ) (i : ι) :
    piLpSumEquiv C q₀ q₁
        ((piLp C q₀ q₁).stripFunction ((piLpStripTracesEquiv C q₀ q₁).symm h) z) i =
      (C i).stripFunction (h i) z := by
  rw [← stripFunction_piLpStripTracesEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end ComplexTraces

namespace ComplexMethodSpace

section PiLpEquiv

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

private def piLpCLEFwd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ) :
    (piLp C q₀ q₁).ComplexMethodSpace θ →L[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  (PiLp.continuousLinearEquiv q ℂ (fun i => (C i).ComplexMethodSpace θ)).symm
    |>.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      map θ (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i))

private def piLpCLEInv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ) :
    PiLp q (fun i => (C i).ComplexMethodSpace θ) →L[ℂ] (piLp C q₀ q₁).ComplexMethodSpace θ := by
  classical
  exact ∑ i : ι, (map θ (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (piLpSingle_inter C q₀ q₁ i)).comp (PiLp.proj q (fun j => (C j).ComplexMethodSpace θ) i)

private theorem piLpCLEFwd_mk (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (g : (piLp C q₀ q₁).stripTraces) :
    piLpCLEFwd C q₀ q₁ q θ (mk θ g) =
      WithLp.toLp q fun i => mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
  refine PiLp.ext fun i => ?_
  simp only [piLpCLEFwd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply, map_mk, PiLp.toLp_apply]
  rw [piLpStripTracesEquiv_apply, piLpStripTracesFwd_apply]

private theorem piLpCLEInv_mk (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (h : ∀ i, (C i).stripTraces) :
    piLpCLEInv C q₀ q₁ q θ (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) := by
  simp only [piLpCLEInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, map_mk, ← map_sum]
  rw [piLpStripTracesEquiv_symm_apply]
  congr 1
  simp only [piLpStripTracesInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- Coordinatewise continuous linear equivalence between `(piLp C q₀ q₁).ComplexMethodSpace θ` and
`PiLp q (fun i => (C i).ComplexMethodSpace θ)`. Unlike `piLpEquiv`, this topological isomorphism
requires no relation between `q₀`, `q₁`, `q`, and `θ`, and no `1 ≤ q` assumption on `q`. -/
def piLpContinuousLinearEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ) :
    (piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpCLEFwd C q₀ q₁ q θ) (piLpCLEInv C q₀ q₁ q θ)
    (ContinuousLinearMap.ext fun v => by
      choose h hh using fun i => mk_surjective (v i)
      have hv : v = WithLp.toLp q fun i => mk θ (h i) := PiLp.ext fun i => (hh i).symm
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hv, piLpCLEInv_mk,
        piLpCLEFwd_mk]
      refine PiLp.ext fun i => ?_
      rw [PiLp.toLp_apply, (piLpStripTracesEquiv C q₀ q₁).apply_symm_apply])
    (ContinuousLinearMap.ext fun u => by
      obtain ⟨g, rfl⟩ := mk_surjective u
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, piLpCLEFwd_mk,
        piLpCLEInv_mk]
      exact congrArg (mk θ) ((piLpStripTracesEquiv C q₀ q₁).symm_apply_apply g))

private theorem piLpContinuousLinearEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (u : (piLp C q₀ q₁).ComplexMethodSpace θ) :
    piLpContinuousLinearEquiv C q₀ q₁ q θ u = piLpCLEFwd C q₀ q₁ q θ u := by
  dsimp [piLpContinuousLinearEquiv]

@[simp]
theorem piLpContinuousLinearEquiv_mk_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (g : (piLp C q₀ q₁).stripTraces) (i : ι) :
    piLpContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i =
      mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
  rw [piLpContinuousLinearEquiv_apply, piLpCLEFwd_mk, PiLp.toLp_apply]

@[simp]
theorem toSum_piLpContinuousLinearEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (u : (piLp C q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    toSum (piLpContinuousLinearEquiv C q₀ q₁ q θ u i) = piLpSumEquiv C q₀ q₁ (toSum u) i := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [piLpContinuousLinearEquiv_mk_apply, toSum_mk, toSum_mk, stripEval_piLpStripTracesEquiv_apply]

@[simp]
theorem piLpContinuousLinearEquiv_symm_mk (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (h : ∀ i, (C i).stripTraces) :
    (piLpContinuousLinearEquiv C q₀ q₁ q θ).symm (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) := by
  apply (piLpContinuousLinearEquiv C q₀ q₁ q θ).injective
  refine PiLp.ext fun i => ?_
  rw [ContinuousLinearEquiv.apply_symm_apply, PiLp.toLp_apply,
    piLpContinuousLinearEquiv_mk_apply, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem toSum_piLpContinuousLinearEquiv_symm (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    toSum ((piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v) =
      (piLpSumEquiv C q₀ q₁).symm fun i => toSum (v i) := by
  apply (piLpSumEquiv C q₀ q₁).injective
  ext i
  rw [ContinuousLinearEquiv.apply_symm_apply, ← toSum_piLpContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-! ### Forward and inverse norm bounds on `piLpContinuousLinearEquiv` -/

private theorem norm_piLpContinuousLinearEquiv_zero
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)]
    [Fact (1 ≤ q₁)] (u : (piLp C q₀ q₁).ComplexMethodSpace 0) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q₀ 0 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [← PiLp.norm_norm (piLpContinuousLinearEquiv C q₀ q₁ q₀ 0 (mk 0 g))]
  simp_rw [piLpContinuousLinearEquiv_mk_apply, norm_mk_zero, piLpStripTracesEquiv_apply_fst]
  rw [PiLp.norm_norm]

private theorem norm_piLpContinuousLinearEquiv_one
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)]
    [Fact (1 ≤ q₁)] (u : (piLp C q₀ q₁).ComplexMethodSpace 1) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q₁ 1 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [← PiLp.norm_norm (piLpContinuousLinearEquiv C q₀ q₁ q₁ 1 (mk 1 g))]
  simp_rw [piLpContinuousLinearEquiv_mk_apply, norm_mk_one, piLpStripTracesEquiv_apply_snd]
  rw [PiLp.norm_norm]

private theorem norm_piLpContinuousLinearEquiv_le (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp C q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q θ u‖ ≤ ‖u‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · have : q = q₀ := inv_injective (by simpa using hq); subst q
      exact (norm_piLpContinuousLinearEquiv_zero C q₀ q₁ u).le
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · have : q = q₁ := inv_injective (by simpa using hq); subst q
        exact (norm_piLpContinuousLinearEquiv_one C q₀ q₁ u).le
      · have hθoo : θ ∈ Ioo (0 : ℝ) 1 := ⟨hθ0, hθ1⟩
        refine le_of_forall_gt fun r hr => ?_
        obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
        let a : ι → ℝ := fun i => (1 - θ)⁻¹ * ∫ t, ‖g.val.1 t i‖ * stripPoisson₀ θ t
        let b : ι → ℝ := fun i => θ⁻¹ * ∫ t, ‖g.val.2 t i‖ * stripPoisson₁ θ t
        have ha (i : ι) : 0 ≤ a i := mul_nonneg (inv_pos.2 (sub_pos.2 hθ1)).le
          (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (stripPoisson₀_pos hθoo t).le)
        have hb (i : ι) : 0 ≤ b i := mul_nonneg (inv_pos.2 hθ0).le
          (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (stripPoisson₁_pos hθoo t).le)
        have hpt (i : ι) : ‖piLpContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i‖ ≤
            a i ^ (1 - θ) * b i ^ θ := by
          rw [piLpContinuousLinearEquiv_mk_apply]
          simpa only [piLpStripTracesEquiv_apply_fst, piLpStripTracesEquiv_apply_snd] using
            norm_mk_le_stripPoisson_geometricMean hθoo (piLpStripTracesEquiv C q₀ q₁ g i)
        have ha_norm := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.1
          (sub_pos.2 hθ1) (integrable_stripPoisson₀ θ) (fun t => (stripPoisson₀_pos hθoo t).le)
          (integral_stripPoisson₀ ⟨hθ0, hθ1.le⟩)).trans
          ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))
        have hb_norm := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.2 hθ0
          (integrable_stripPoisson₁ θ) (fun t => (stripPoisson₁_pos hθoo t).le)
          (integral_stripPoisson₁ ⟨hθ0.le, hθ1⟩)).trans
          ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))
        refine ((PiLp.norm_mono (y := WithLp.toLp q fun i => a i ^ (1 - θ) * b i ^ θ)
          fun i => (hpt i).trans (le_abs_self _)).trans
          (PiLp.norm_toLp_rpow_mul_rpow_le (Ioo_subset_Icc_self hθoo) hq ha hb)).trans_lt
          (lt_of_le_of_lt ?_ hg)
        calc ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ
            ≤ ‖g‖ ^ (1 - θ) * ‖g‖ ^ θ :=
              mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha_norm (sub_pos.2 hθ1).le)
                (Real.rpow_le_rpow (norm_nonneg _) hb_norm hθ0.le)
                (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖g‖ := by rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_pos.2 hθ1).le hθ0.le,
              sub_add_cancel, Real.rpow_one]
  · rw [eq_zero_of_notMem hθ u, map_zero, norm_zero, norm_zero]

private theorem exists_stripTraces_rescale {E₀ E₁ W : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    {C₀ : CompatibleCouple ℂ E₀ E₁ W} {θ α₀ α₁ b B : ℝ}
    (hα : (1 - θ) * α₀ + θ * α₁ = 1) (hb : 0 < b) (hB : 0 < B) (g : C₀.stripTraces)
    (hg : ‖g‖ < b) :
    ∃ g' : C₀.stripTraces, mk θ g' = mk θ g ∧
      (∀ t : ℝ, ‖g'.val.1 t‖ ≤ B * (b / B) ^ α₀) ∧
      (∀ t : ℝ, ‖g'.val.2 t‖ ≤ B * (b / B) ^ α₁) := by
  have hqpos : 0 < b / B := div_pos hb hB
  let M₀ : ℝ := (b / B) ^ (1 - α₀)
  let M₁ : ℝ := (b / B) ^ (1 - α₁)
  have hM₀ : 0 < M₀ := Real.rpow_pos_of_pos hqpos _
  have hM₁ : 0 < M₁ := Real.rpow_pos_of_pos hqpos _
  obtain ⟨g', hg₀', hg₁', heq⟩ := exists_stripTraces_smul_of_diffContOnCl g
    (differentiable_scaleFactor M₀ M₁).diffContOnCl fun _ hz => norm_scaleFactor_le hz
  have hcθ : scaleFactor M₀ M₁ θ = 1 := by
    have hre : ((θ : ℂ) - 1) * Real.log M₀ - θ * Real.log M₁ = 0 := by
      norm_cast
      simp only [M₀, M₁, Real.log_rpow hqpos]
      have hlin : (θ - 1) * (1 - α₀) - θ * (1 - α₁) = 0 := by linarith
      calc (θ - 1) * ((1 - α₀) * Real.log (b / B)) - θ * ((1 - α₁) * Real.log (b / B))
          = ((θ - 1) * (1 - α₀) - θ * (1 - α₁)) * Real.log (b / B) := by ring
        _ = 0 := by rw [hlin, zero_mul]
    rw [scaleFactor_def, hre, Complex.exp_zero]
  have hscale (α x : ℝ) (hx : x ≤ b) : ((b / B) ^ (1 - α))⁻¹ * x ≤ B * (b / B) ^ α := by
    rw [← Real.rpow_neg hqpos.le, neg_sub]
    calc (b / B) ^ (α - 1) * x
        ≤ (b / B) ^ (α - 1) * b := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hqpos.le _)
      _ = B * ((b / B) ^ (α - 1) * (b / B) ^ (1 : ℝ)) := by
          rw [Real.rpow_one]; field_simp [hB.ne']
      _ = B * (b / B) ^ α := by rw [← Real.rpow_add hqpos, sub_add_cancel]
  refine ⟨g', by rw [heq θ, hcθ, one_smul], fun t => ?_, fun t => ?_⟩
  · rw [hg₀', norm_smul, norm_scaleFactor_mul_I hM₀]
    exact hscale α₀ _ (((ZeroAtInftyContinuousMap.norm_coe_le_norm g.val.1 t).trans
      ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))).trans hg.le)
  · rw [hg₁', norm_smul, norm_scaleFactor_one_add_mul_I hM₁]
    exact hscale α₁ _ (((ZeroAtInftyContinuousMap.norm_coe_le_norm g.val.2 t).trans
      ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))).trans hg.le)

private theorem norm_piLpCLE_symm_le_of_mk (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {θ : ℝ}
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) {B : ℝ}
    (g : ∀ i, (C i).stripTraces) (hg_mk : ∀ i, mk θ (g i) = v i)
    (hG : ‖((piLpStripTracesEquiv C q₀ q₁).symm g).val‖ ≤ B) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ B := by
  let G : (piLp C q₀ q₁).stripTraces := (piLpStripTracesEquiv C q₀ q₁).symm g
  have hv : v = WithLp.toLp q fun i => mk θ (g i) := PiLp.ext fun i => (hg_mk i).symm
  rw [hv, piLpContinuousLinearEquiv_symm_mk]
  exact (norm_mk_le G).trans ((Submodule.norm_coe G).symm.trans_le hG)

private theorem norm_symm_le_of_eq_top (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {q₀ q₁ : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : (∞ : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp ∞ (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ ∞ θ).symm v‖ ≤ ‖v‖ := by
  obtain ⟨rfl, rfl⟩ := (TauCeti.eq_top_iff_of_inv_eq hθ hq).1 rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hex (i : ι) : ∃ g : (C i).stripTraces, mk θ g = v i ∧ ‖g‖ < ‖v‖ + ε :=
    norm_lt_iff.1 ((PiLp.norm_apply_le v i).trans_lt (lt_add_of_pos_right ‖v‖ hε))
  choose g hg_mk hg_norm using hex
  have hB : 0 ≤ ‖v‖ + ε := add_nonneg (norm_nonneg v) hε.le
  refine norm_piLpCLE_symm_le_of_mk C v g hg_mk ?_
  rw [Prod.norm_def]
  refine max_le ((ZeroAtInftyContinuousMap.norm_le hB).2 fun t => ?_)
    ((ZeroAtInftyContinuousMap.norm_le hB).2 fun t => ?_)
  · rw [← PiLp.norm_ofLp, pi_norm_le_iff_of_nonneg hB]; intro i
    rw [piLpStripTracesEquiv_symm_apply_fst]
    exact ((ZeroAtInftyContinuousMap.norm_coe_le_norm (g i).val.1 t).trans
      ((norm_fst_le (g i).val).trans_eq (Submodule.norm_coe (g i)))).trans (hg_norm i).le
  · rw [← PiLp.norm_ofLp, pi_norm_le_iff_of_nonneg hB]; intro i
    rw [piLpStripTracesEquiv_symm_apply_snd]
    exact ((ZeroAtInftyContinuousMap.norm_coe_le_norm (g i).val.2 t).trans
      ((norm_snd_le (g i).val).trans_eq (Submodule.norm_coe (g i)))).trans (hg_norm i).le

private theorem norm_symm_le_of_ne_top (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq_top : q ≠ ∞) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  cases isEmpty_or_nonempty ι
  · rw [Subsingleton.elim v 0, map_zero, norm_zero, norm_zero]
  have hα := TauCeti.one_sub_mul_toReal_inv_add
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hq_top ⟨hθ.1.le, hθ.2.le⟩ hq
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b, B, hB, hB_le, hb, hsum⟩ := PiLp.exists_pos_perturbation hq_top v hε
  have hex (i : ι) : ∃ g' : (C i).stripTraces, mk θ g' = v i ∧
      (∀ t, ‖g'.val.1 t‖ ≤ B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal)) ∧
      (∀ t, ‖g'.val.2 t‖ ≤ B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal)) := by
    obtain ⟨g, hg_eq, hg⟩ := norm_lt_iff.1 (hb i).2
    obtain ⟨g', hg'_eq, hg'₀, hg'₁⟩ := exists_stripTraces_rescale hα (hb i).1 hB g hg
    exact ⟨g', hg'_eq.trans hg_eq, hg'₀, hg'₁⟩
  choose g' hg'_mk hg'_0 hg'_1 using hex
  refine (norm_piLpCLE_symm_le_of_mk C v g' hg'_mk ?_).trans hB_le
  rw [Prod.norm_def]
  exact max_le ((ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
      (PiLp.norm_mono (y := WithLp.toLp q₀ fun i => B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal))
        fun i => by
          rw [piLpStripTracesEquiv_symm_apply_fst]
          exact (hg'_0 i t).trans (le_abs_self _)).trans
        (PiLp.norm_toLp_mul_div_rpow_le hB (fun i => (hb i).1) hsum))
    ((ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
      (PiLp.norm_mono (y := WithLp.toLp q₁ fun i => B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal))
        fun i => by
          rw [piLpStripTracesEquiv_symm_apply_snd]
          exact (hg'_1 i t).trans (le_abs_self _)).trans
        (PiLp.norm_toLp_mul_div_rpow_le hB (fun i => (hb i).1) hsum))

private theorem norm_piLpContinuousLinearEquiv_symm_le
    (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · have : q = q₀ := inv_injective (by simpa using hq); subst q
      exact (norm_piLpContinuousLinearEquiv_zero C q₀ q₁ _).symm.trans_le
        (by rw [ContinuousLinearEquiv.apply_symm_apply])
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · have : q = q₁ := inv_injective (by simpa using hq); subst q
        exact (norm_piLpContinuousLinearEquiv_one C q₀ q₁ _).symm.trans_le
          (by rw [ContinuousLinearEquiv.apply_symm_apply])
      · rcases eq_or_ne q ∞ with rfl | hq_top
        · exact norm_symm_le_of_eq_top C ⟨hθ0, hθ1⟩ hq v
        · exact norm_symm_le_of_ne_top C ⟨hθ0, hθ1⟩ hq_top hq v
  · rw [eq_zero_of_notMem hθ ((piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v), norm_zero]
    exact norm_nonneg v

/-! ### Main linear isometric equivalences -/

/-- **Bergh–Löfström, Theorem 5.1.2 (finite index sets, including `∞` endpoints).**
For a finite family of compatible couples `C i` (`i : ι`), exponents `1 ≤ q₀, q₁, q ≤ ∞`, and
`θ : ℝ` satisfying `q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`, complex
interpolation commutes isometrically with `PiLp`:
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.

For `θ ∈ [0, 1]`, the exponent hypothesis reduces to the usual `1 / q = (1 - θ) / q₀ + θ / q₁`;
for `θ ∉ [0, 1]`, both interpolation spaces are zero (`eq_zero_of_notMem`) so the isometry holds
degenerately. -/
def piLpEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLp C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  LinearIsometryEquiv.ofBounds (piLpContinuousLinearEquiv C q₀ q₁ q θ).toLinearEquiv
    (norm_piLpContinuousLinearEquiv_le C hq)
    (norm_piLpContinuousLinearEquiv_symm_le C hq)

@[simp]
theorem coe_piLpEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLpEquiv C hq : (piLp C q₀ q₁).ComplexMethodSpace θ →
      PiLp q (fun i => (C i).ComplexMethodSpace θ)) =
      piLpContinuousLinearEquiv C q₀ q₁ q θ :=
  (rfl)

@[simp]
theorem coe_piLpEquiv_symm (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    ((piLpEquiv C hq).symm : PiLp q (fun i => (C i).ComplexMethodSpace θ) →
      (piLp C q₀ q₁).ComplexMethodSpace θ) =
      (piLpContinuousLinearEquiv C q₀ q₁ q θ).symm :=
  (rfl)

end PiLpEquiv

section Refl

/-- **Complex interpolation of finite vector-valued sequence spaces (`[ℓ_{q₀}^N(E), ℓ_{q₁}^N(E)]_θ =
ℓ_q^N(E)` with equal norms).** For a finite family of complex normed spaces `X : ι → Type*`,
exponents `1 ≤ q₀, q₁, q ≤ ∞`, and `0 ≤ θ ≤ 1` satisfying `1 / q = (1 - θ) / q₀ + θ / q₁`, the
complex interpolation space of `(PiLp q₀ X, PiLp q₁ X)` is canonically linearly isometric to
`PiLp q X`. -/
def piLpReflEquiv {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, NormedAddCommGroup (X i)]
    [∀ i, NormedSpace ℂ (X i)] {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]
    {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (piLp (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q X :=
  (piLpEquiv (fun i => refl ℂ (X i)) hq).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ => reflEquiv hθ)

@[simp]
theorem piLpReflEquiv_apply_apply {ι : Type*} [Fintype ι] (X : ι → Type*)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)] {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    piLpReflEquiv X hθ hq u i =
      (piLp (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed (toSum u) i := by
  rw [piLpReflEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply, reflEquiv_apply, coe_piLpEquiv,
    toSum_piLpContinuousLinearEquiv_apply (fun j => refl ℂ (X j)),
    sumSpaceEmbed_piLpSumEquiv_apply (fun j => refl ℂ (X j))]

@[simp]
theorem sumSpaceEmbed_toSum_piLpReflEquiv_symm {ι : Type*} [Fintype ι] (X : ι → Type*)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)] {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) (x : PiLp q X) (i : ι) :
    (piLp (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed
        (toSum ((piLpReflEquiv X hθ hq).symm x)) i = x i := by
  rw [← piLpReflEquiv_apply_apply X hθ hq, LinearIsometryEquiv.apply_symm_apply]

end Refl

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
