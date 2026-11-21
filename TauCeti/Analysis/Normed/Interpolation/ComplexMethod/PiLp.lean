/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Data.ENNReal.InterpolatedExponent
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Complex interpolation of finite vector-valued sequence spaces

Given a finite index type `ι`, exponents `1 ≤ q₀, q₁, q ≤ ∞`, a family of compatible couples
`C : ∀ i : ι, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)`, and `θ : ℝ` satisfying the Riesz–Thorin
relation `q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`, we prove the finite-index
case of **Bergh–Löfström, Theorem 5.1.2** (including `∞` endpoints), with no completeness, duality,
or density assumptions on `C i`:

`(piLp C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ)`.

## Main declarations

* `CompatibleCouple.piLp`: the `PiLp` couple `(PiLp q₀ X₀, PiLp q₁ X₁)` in `∀ i, V i`.
* `CompatibleCouple.piLpSumEquiv`, `CompatibleCouple.piLpStripTracesEquiv`: canonical coordinatewise
  equivalences for the sum space and admissible boundary traces.
* `CompatibleCouple.ComplexMethodSpace.piLpContinuousLinearEquiv`: coordinatewise continuous linear
  equivalence `(piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.
* `CompatibleCouple.ComplexMethodSpace.piLpEquiv`: **Bergh–Löfström, Theorem 5.1.2** upgrading
  `piLpContinuousLinearEquiv` to a linear isometric equivalence under the exponent relation.
* `CompatibleCouple.ComplexMethodSpace.reflEquiv`, `piLpReflEquiv`: `[X, X]_θ ≃ₗᵢ[ℂ] X` and
  `[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X` for `0 ≤ θ ≤ 1`.

## Implementation notes

For `0 < θ < 1`, the upper norm bound applies `norm_mk_le_integral_stripPoisson` coordinatewise,
then log-convex Hölder in `PiLp` and Minkowski's integral inequality via
`MeasureTheory.eval_integral_piLp`. For the reverse bound (`q < ∞`), near-optimal traces `g i` with
`‖g i‖ < b i` (`b i = ‖v i‖ + δ`, `B = ‖b‖_{ℓ^q}`) are rescaled by
`z ↦ exp (((1 - z) α₀ + z α₁ - 1) log (b i / B))` with `α_j = q.toReal * (q_j⁻¹).toReal`.
Endpoints `θ = 0, 1` follow directly from `norm_mk_zero` and `norm_mk_one`.

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

section CoupleDef

variable {𝕜 ι : Type*} [Semiring 𝕜]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, Module 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, Module 𝕜 (X₁ i)]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module 𝕜 (V i)] [∀ i, TopologicalSpace (V i)]

/-- Given a family of compatible couples `C i` (`i : ι`) and exponents `q₀, q₁ : ℝ≥0∞`,
`CompatibleCouple.piLp C q₀ q₁` is the compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` inside the
product ambient space `∀ i, V i`. -/
def piLp (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i => (C i).embed₀.comp (PiLp.proj q₀ X₀ i)
  embed₁ := ContinuousLinearMap.pi fun i => (C i).embed₁.comp (PiLp.proj q₁ X₁ i)
  embed₀_injective x y h := by
    ext i
    exact (C i).embed₀_injective (congrFun h i)
  embed₁_injective x y h := by
    ext i
    exact (C i).embed₁_injective (congrFun h i)

@[simp]
theorem piLp_embed₀_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    (x : PiLp q₀ X₀) (i : ι) :
    (piLp C q₀ q₁).embed₀ x i = (C i).embed₀ (x i) :=
  (rfl)

@[simp]
theorem piLp_embed₁_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    (x : PiLp q₁ X₁) (i : ι) :
    (piLp C q₀ q₁).embed₁ x i = (C i).embed₁ (x i) :=
  (rfl)

end CoupleDef

section Couple

variable {𝕜 ι : Type*} [NormedField 𝕜]

/-- Single-coordinate continuous linear inclusion `β i →L[𝕜] PiLp p β`, using classical decidability
internally so no `[DecidableEq ι]` assumption leaks into public APIs. -/
private def piLpSingleCLM (p : ℝ≥0∞) {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace 𝕜 (β i)] (i : ι) : β i →L[𝕜] PiLp p β := by
  classical
  exact (PiLp.continuousLinearEquiv p 𝕜 β).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single (R := 𝕜) (φ := β) i)

private theorem piLpSingleCLM_apply [DecidableEq ι] (p : ℝ≥0∞) {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] (i : ι) (x : β i) :
    piLpSingleCLM (𝕜 := 𝕜) p i x = PiLp.single p i x := by
  ext j
  simp only [piLpSingleCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.single_apply, PiLp.ofLp_single]
  congr! 1

variable [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace 𝕜 (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)]

private theorem piLpProj_inter (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (i : ι) (x : (piLp C q₀ q₁).inter) :
    (C i).fstToSum (PiLp.proj (𝕜 := 𝕜) q₀ X₀ i ((piLp C q₀ q₁).interFst x)) =
      (C i).sndToSum (PiLp.proj (𝕜 := 𝕜) q₁ X₁ i ((piLp C q₀ q₁).interSnd x)) := by
  apply (C i).sumSpace_ext
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
  exact congrFun ((piLp C q₀ q₁).embed₀_interFst x) i

private theorem piLpSingle_inter (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (i : ι) (x : (C i).inter) :
    (piLp C q₀ q₁).fstToSum (piLpSingleCLM (𝕜 := 𝕜) q₀ i ((C i).interFst x)) =
      (piLp C q₀ q₁).sndToSum (piLpSingleCLM (𝕜 := 𝕜) q₁ i ((C i).interSnd x)) := by
  classical
  apply (piLp C q₀ q₁).sumSpace_ext
  ext j
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, piLp_embed₀_apply, piLp_embed₁_apply,
    piLpSingleCLM_apply, piLpSingleCLM_apply]
  by_cases hji : j = i
  · subst hji
    rw [PiLp.single_eq_same, PiLp.single_eq_same]
    exact (C j).embed₀_interFst x
  · simp [PiLp.single_eq_of_ne _ hji]

/-- The sum space of `CompatibleCouple.piLp C q₀ q₁` identifies canonically with the product of the
coordinate sum spaces `∀ i, (C i).SumSpace`. -/
def piLpSumEquiv (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).SumSpace ≃L[𝕜] ∀ i, (C i).SumSpace := by
  classical
  have hproj (i : ι) (x : (piLp C q₀ q₁).inter) :
      ((C i).fstToSum.comp (PiLp.proj q₀ X₀ i)) ((piLp C q₀ q₁).interFst x) =
        ((C i).sndToSum.comp (PiLp.proj q₁ X₁ i)) ((piLp C q₀ q₁).interSnd x) := by
    simpa only [ContinuousLinearMap.comp_apply] using piLpProj_inter C q₀ q₁ i x
  have hsingle (i : ι) (x : (C i).inter) :
      ((piLp C q₀ q₁).fstToSum.comp (piLpSingleCLM q₀ i)) ((C i).interFst x) =
        ((piLp C q₀ q₁).sndToSum.comp (piLpSingleCLM q₁ i)) ((C i).interSnd x) := by
    simpa only [ContinuousLinearMap.comp_apply] using piLpSingle_inter C q₀ q₁ i x
  let fwd : (piLp C q₀ q₁).SumSpace →L[𝕜] ∀ i, (C i).SumSpace :=
    ContinuousLinearMap.pi fun i => (piLp C q₀ q₁).sumLift _ _ (hproj i)
  let inv : (∀ i, (C i).SumSpace) →L[𝕜] (piLp C q₀ q₁).SumSpace :=
    ∑ i : ι, ((C i).sumLift _ _ (hsingle i)).comp (ContinuousLinearMap.proj i)
  refine ContinuousLinearEquiv.equivOfInverse fwd inv (fun u => ?_) (fun v => ?_)
  · obtain ⟨x₀, x₁, rfl⟩ := (piLp C q₀ q₁).exists_fstToSum_add_sndToSum_eq u
    apply (piLp C q₀ q₁).sumSpace_ext; ext j
    simp only [fwd, inv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply, map_add, map_sum,
      sumLift_fstToSum, sumLift_sndToSum, PiLp.proj_apply, sumSpaceEmbed_fstToSum,
      sumSpaceEmbed_sndToSum, Pi.add_apply, piLp_embed₀_apply, piLp_embed₁_apply,
      piLpSingleCLM_apply]
    rw [Fintype.sum_eq_single j (fun i hij => by simp [PiLp.single_eq_of_ne _ hij.symm]),
      Fintype.sum_eq_single j (fun i hij => by simp [PiLp.single_eq_of_ne _ hij.symm])]
    simp
  · ext j; apply (C j).sumSpace_ext
    have hsum : (C j).sumSpaceEmbed (fwd (inv v) j) =
        ∑ i : ι, (C j).sumSpaceEmbed (fwd ((C i).sumLift _ _ (hsingle i) (v i)) j) := by
      simp [inv, map_sum]
    rw [hsum, Fintype.sum_eq_single j]
    · obtain ⟨y₀, y₁, hy⟩ := (C j).exists_fstToSum_add_sndToSum_eq (v j)
      rw [← hy]; simp [fwd, sumLift_fstToSum, sumLift_sndToSum, piLpSingleCLM_apply]
    · intro i hij
      obtain ⟨z₀, z₁, hz⟩ := (C i).exists_fstToSum_add_sndToSum_eq (v i)
      rw [← hz]
      simp [fwd, sumLift_fstToSum, sumLift_sndToSum, piLpSingleCLM_apply,
        PiLp.single_eq_of_ne _ hij.symm]

@[simp]
theorem piLpSumEquiv_fstToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₀ X₀) (i : ι) :
    piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).fstToSum x) i = (C i).fstToSum (x i) := by
  simp [piLpSumEquiv, sumLift_fstToSum]

@[simp]
theorem piLpSumEquiv_sndToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₁ X₁) (i : ι) :
    piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).sndToSum x) i = (C i).sndToSum (x i) := by
  simp [piLpSumEquiv, sumLift_sndToSum]

@[simp]
theorem sumSpaceEmbed_piLpSumEquiv_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (u : (piLp C q₀ q₁).SumSpace) (i : ι) :
    (C i).sumSpaceEmbed (piLpSumEquiv C q₀ q₁ u i) = (piLp C q₀ q₁).sumSpaceEmbed u i := by
  obtain ⟨x₀, x₁, rfl⟩ := (piLp C q₀ q₁).exists_fstToSum_add_sndToSum_eq u
  simp

@[simp]
theorem sumSpaceEmbed_piLpSumEquiv_symm (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (v : ∀ i, (C i).SumSpace) (i : ι) :
    (piLp C q₀ q₁).sumSpaceEmbed ((piLpSumEquiv C q₀ q₁).symm v) i =
      (C i).sumSpaceEmbed (v i) := by
  rw [← sumSpaceEmbed_piLpSumEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end Couple

section ComplexTraces

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

/-- Admissible boundary traces for `CompatibleCouple.piLp C q₀ q₁` identify canonically with tuples
of admissible boundary traces `∀ i, (C i).stripTraces` via coordinatewise projection. -/
def piLpStripTracesEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).stripTraces ≃L[ℂ] ∀ i, (C i).stripTraces := by
  classical
  let fwd : (piLp C q₀ q₁).stripTraces →L[ℂ] ∀ i, (C i).stripTraces :=
    ContinuousLinearMap.pi fun i =>
      stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i)
  let inv : (∀ i, (C i).stripTraces) →L[ℂ] (piLp C q₀ q₁).stripTraces :=
    ∑ i : ι, (stripTracesMap (piLpSingleCLM q₀ i) (piLpSingleCLM q₁ i)
      (piLpSingle_inter C q₀ q₁ i)).comp (ContinuousLinearMap.proj i)
  have hinv_fst (k : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
      ((inv k).val.1 t) j = (k j).val.1 t := by
    simp only [inv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.fst_sum, WithLp.ofLp_sum,
      stripTracesMap_apply_fst, piLpSingleCLM_apply]
    rw [Fintype.sum_eq_single j (fun i hij => PiLp.single_eq_of_ne q₀ hij.symm _),
      PiLp.single_eq_same]
  have hinv_snd (k : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
      ((inv k).val.2 t) j = (k j).val.2 t := by
    simp only [inv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.snd_sum, WithLp.ofLp_sum,
      stripTracesMap_apply_snd, piLpSingleCLM_apply]
    rw [Fintype.sum_eq_single j (fun i hij => PiLp.single_eq_of_ne q₁ hij.symm _),
      PiLp.single_eq_same]
  refine ContinuousLinearEquiv.equivOfInverse fwd inv (fun g => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by rw [hinv_fst]; simp [fwd])
      (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by rw [hinv_snd]; simp [fwd])))
    (fun h => funext fun j => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun t => by simp [fwd, hinv_fst])
      (ZeroAtInftyContinuousMap.ext fun t => by simp [fwd, hinv_snd])))

@[simp]
theorem piLpStripTracesEquiv_apply_fst (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  simp [piLpStripTracesEquiv]

@[simp]
theorem piLpStripTracesEquiv_apply_snd (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (g : (piLp C q₀ q₁).stripTraces) (i : ι)
    (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  simp [piLpStripTracesEquiv]

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
      piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).stripEval z g) i :=
  stripEval_stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i) z g

end ComplexTraces

namespace ComplexMethodSpace

section PiLpEquiv

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

/-- Coordinatewise continuous linear equivalence between `(piLp C q₀ q₁).ComplexMethodSpace θ` and
`PiLp q (fun i => (C i).ComplexMethodSpace θ)`. Unlike `piLpEquiv`, this topological isomorphism
requires no relation between `q₀`, `q₁`, `q`, and `θ`, and no `1 ≤ q` assumption on `q`. -/
def piLpContinuousLinearEquiv (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ) :
    (piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) := by
  classical
  let fwd : (piLp C q₀ q₁).ComplexMethodSpace θ →L[ℂ]
      PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
    (PiLp.continuousLinearEquiv q ℂ (fun i => (C i).ComplexMethodSpace θ)).symm
      |>.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        map θ (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i) (piLpProj_inter C q₀ q₁ i))
  let inv : PiLp q (fun i => (C i).ComplexMethodSpace θ) →L[ℂ]
      (piLp C q₀ q₁).ComplexMethodSpace θ :=
    ∑ i : ι, (map θ (piLpSingleCLM q₀ i) (piLpSingleCLM q₁ i)
      (piLpSingle_inter C q₀ q₁ i)).comp (PiLp.proj q (fun j => (C j).ComplexMethodSpace θ) i)
  have hinv_mk (h : ∀ i, (C i).stripTraces) :
      inv (WithLp.toLp q fun i => mk θ (h i)) = mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) := by
    simp only [inv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply, map_mk, ← map_sum]
    congr 1
    simp [piLpStripTracesEquiv]
  have hfwd_mk (g : (piLp C q₀ q₁).stripTraces) :
      fwd (mk θ g) = WithLp.toLp q fun i => mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
    refine PiLp.ext fun i => ?_
    simp [fwd, piLpStripTracesEquiv]
  refine ContinuousLinearEquiv.equivOfInverse fwd inv (fun u => ?_) (fun v => ?_)
  · obtain ⟨g, rfl⟩ := mk_surjective u
    rw [hfwd_mk, hinv_mk]
    exact congrArg (mk θ) ((piLpStripTracesEquiv C q₀ q₁).symm_apply_apply g)
  · choose h hh using fun i => mk_surjective (v i)
    have hv : v = WithLp.toLp q fun i => mk θ (h i) := PiLp.ext fun i => (hh i).symm
    rw [hv, hinv_mk, hfwd_mk]
    refine PiLp.ext fun i => ?_
    simp only [(piLpStripTracesEquiv C q₀ q₁).apply_symm_apply]

@[simp]
theorem piLpContinuousLinearEquiv_mk_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)
    (g : (piLp C q₀ q₁).stripTraces) (i : ι) :
    piLpContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i =
      mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
  simp [piLpContinuousLinearEquiv, piLpStripTracesEquiv]

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

/-! ### Auxiliary `PiLp`, Hölder, and Bochner–Minkowski estimates -/

private theorem norm_toLp_integral_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    ‖WithLp.toLp p (fun i => ∫ t, f i t)‖ ≤ ∫ t, ‖WithLp.toLp p (fun i => f i t)‖ := by
  let F : ℝ → PiLp p (fun _ : ι => ℝ) := fun t => WithLp.toLp p (fun i => f i t)
  rw [show WithLp.toLp p (fun i => ∫ t, f i t) = ∫ t, F t by
    ext i; exact (MeasureTheory.eval_integral_piLp (f := F) hf i).symm]
  exact norm_integral_le_integral_norm F

private theorem norm_toLp_integral_weighted_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] (f : C₀(ℝ, PiLp p β)) {w : ℝ → ℝ} {α : ℝ}
    (hα : 0 < α) (hw_int : Integrable w) (hw_nonneg : ∀ t, 0 ≤ w t) (hw_sum : ∫ t, w t = α) :
    ‖WithLp.toLp p (fun i => α⁻¹ * ∫ t, ‖f t i‖ * w t)‖ ≤ ‖f‖ := by
  have hint (i : ι) : Integrable (fun t => ‖f t i‖ * w t) :=
    hw_int.bdd_mul ((PiLp.continuous_apply p β i).comp f.continuous).norm.aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (PiLp.norm_apply_le (f t) i).trans (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))
  change ‖α⁻¹ • WithLp.toLp p (fun i => ∫ t, ‖f t i‖ * w t)‖ ≤ ‖f‖
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le]
  calc α⁻¹ * ‖WithLp.toLp p (fun i => ∫ t, ‖f t i‖ * w t)‖
      ≤ α⁻¹ * ∫ t, ‖WithLp.toLp p (fun i => ‖f t i‖ * w t)‖ :=
        mul_le_mul_of_nonneg_left (norm_toLp_integral_le _ hint) (inv_pos.2 hα).le
    _ ≤ α⁻¹ * ∫ t, ‖f‖ * w t := by
        refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (ae_of_all _ fun _ => norm_nonneg _) (hw_int.const_mul ‖f‖)
          (ae_of_all _ fun t => ?_)) (inv_pos.2 hα).le
        have hfactor : WithLp.toLp p (fun i => ‖f t i‖ * w t) =
            w t • WithLp.toLp p (fun i => ‖f t i‖) := by ext i; simp [mul_comm]
        dsimp only
        rw [hfactor, norm_smul, Real.norm_of_nonneg (hw_nonneg t), PiLp.norm_norm (f t), mul_comm]
        exact mul_le_mul_of_nonneg_right (ZeroAtInftyContinuousMap.norm_coe_le_norm f t)
          (hw_nonneg t)
    _ = ‖f‖ := by rw [integral_const_mul, hw_sum, mul_comm ‖f‖, inv_mul_cancel_left₀ hα.ne']

private theorem norm_toLp_rpow_mul_rpow_le_of_right_eq_top {q₀ q : ℝ≥0∞} [Fact (1 ≤ q₀)]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (hq₀ : q₀ ≠ ∞)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹) {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i => a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp ∞ b‖ ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hq_top : q ≠ ∞ := by
    rw [← ENNReal.inv_ne_zero, hq]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 h1θ).ne' (ENNReal.inv_ne_zero.2 hq₀)
  have hq0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  have hq₀_pos := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne' hq₀
  have hqr : (1 - θ) * q.toReal = q₀.toReal := by
    have htr := congrArg ENNReal.toReal hq
    rw [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1θ.le,
      ENNReal.toReal_inv] at htr
    calc (1 - θ) * q.toReal = q.toReal * ((1 - θ) * q₀.toReal⁻¹) * q₀.toReal := by
          field_simp [hq₀_pos.ne']
      _ = q.toReal * q.toReal⁻¹ * q₀.toReal := by rw [← htr]
      _ = q₀.toReal := by rw [mul_inv_cancel₀ hq0.ne', one_mul]
  rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq₀_pos]
  calc (∑ i, ‖a i ^ (1 - θ) * b i ^ θ‖ ^ q.toReal) ^ (1 / q.toReal)
      ≤ (∑ i, |a i| ^ q₀.toReal * (‖WithLp.toLp ∞ b‖ ^ θ) ^ q.toReal) ^ (1 / q.toReal) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
          (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha i) _)
          (Real.rpow_nonneg (hb i) _)), Real.mul_rpow (Real.rpow_nonneg (ha i) _)
          (Real.rpow_nonneg (hb i) _), ← Real.rpow_mul (ha i), hqr, abs_of_nonneg (ha i)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.rpow_nonneg (hb i) _)
          (Real.rpow_le_rpow (hb i) ((le_abs_self (b i)).trans
            (PiLp.norm_apply_le (WithLp.toLp ∞ b) i)) hθ.1.le) hq0.le) (Real.rpow_nonneg (ha i) _)
    _ = ((∑ i, ‖a i‖ ^ q₀.toReal) ^ (1 / q₀.toReal)) ^ (1 - θ) * ‖WithLp.toLp ∞ b‖ ^ θ := by
        rw [← Finset.sum_mul, Real.mul_rpow (Finset.sum_nonneg fun i _ => by positivity)
          (by positivity), ← Real.rpow_mul (Real.rpow_nonneg (norm_nonneg _) _),
          mul_one_div_cancel hq0.ne', Real.rpow_one,
          ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
        congr 2; rw [← hqr]; field_simp [hq0.ne', h1θ.ne']

private theorem one_sub_mul_toReal_inv_add {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (hq_top : q ≠ ∞)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    (1 - θ) * (q.toReal * (q₀⁻¹).toReal) + θ * (q.toReal * (q₁⁻¹).toReal) = 1 := by
  have hq0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  have htr := congrArg ENNReal.toReal (TauCeti.inv_eq_ofReal_of_inv_eq
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' ⟨hθ.1.le, hθ.2.le⟩ hq)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (add_nonneg
    (mul_nonneg (sub_pos.2 hθ.2).le ENNReal.toReal_nonneg)
    (mul_nonneg hθ.1.le ENNReal.toReal_nonneg))] at htr
  calc (1 - θ) * (q.toReal * (q₀⁻¹).toReal) + θ * (q.toReal * (q₁⁻¹).toReal)
      = q.toReal * ((1 - θ) * (q₀⁻¹).toReal + θ * (q₁⁻¹).toReal) := by ring
    _ = q.toReal * q.toReal⁻¹ := by rw [← htr]
    _ = 1 := mul_inv_cancel₀ hq0.ne'

private theorem norm_toLp_rpow_mul_rpow_le_of_ne_top {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)]
    [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (hq₀ : q₀ ≠ ∞) (hq₁ : q₁ ≠ ∞)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i => a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hq_top : q ≠ ∞ := fun htop => hq₀ ((TauCeti.eq_top_iff_of_inv_eq hθ hq).1 htop).1
  have hq0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  have hq₀_pos := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne' hq₀
  have hq₁_pos := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' hq₁
  let p₀ := q₀.toReal / ((1 - θ) * q.toReal)
  let p₁ := q₁.toReal / (θ * q.toReal)
  have hp_sum : p₀⁻¹ + p₁⁻¹ = 1 := by
    dsimp only [p₀, p₁]; rw [inv_div, inv_div]
    convert one_sub_mul_toReal_inv_add hθ hq_top hq using 1
    simp [ENNReal.toReal_inv, div_eq_mul_inv, mul_assoc]
  have hp₀_pos : 0 < p₀⁻¹ := inv_pos.2 (div_pos hq₀_pos (mul_pos h1θ hq0))
  have hp₁_pos : 0 < p₁⁻¹ := inv_pos.2 (div_pos hq₁_pos (mul_pos hθ.1 hq0))
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (Real.holderConjugate_iff.2 ⟨by
      simpa only [inv_inv] using (one_lt_inv₀ hp₀_pos).2 (by linarith), hp_sum⟩)
    (f := fun i => a i ^ ((1 - θ) * q.toReal)) (g := fun i => b i ^ (θ * q.toReal))
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun i _ => Real.rpow_nonneg (hb i) _)
  rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq₀_pos, PiLp.norm_eq_sum hq₁_pos]
  refine (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
    (le_trans ?_ hholder) (by positivity)).trans_eq ?_
  · refine Finset.sum_le_sum fun i _ => le_of_eq ?_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _)),
      Real.mul_rpow (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _),
      ← Real.rpow_mul (ha i), ← Real.rpow_mul (hb i)]
  · have hsimp₀ (i : ι) : (a i ^ ((1 - θ) * q.toReal)) ^ p₀ = ‖a i‖ ^ q₀.toReal := by
      rw [← Real.rpow_mul (ha i), Real.norm_of_nonneg (ha i)]
      congr 1; dsimp only [p₀]; field_simp [h1θ.ne', hq0.ne']
    have hsimp₁ (i : ι) : (b i ^ (θ * q.toReal)) ^ p₁ = ‖b i‖ ^ q₁.toReal := by
      rw [← Real.rpow_mul (hb i), Real.norm_of_nonneg (hb i)]
      congr 1; dsimp only [p₁]; field_simp [hθ.1.ne', hq0.ne']
    simp_rw [hsimp₀, hsimp₁]
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity),
      ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity),
      ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity),
      ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
    congr 2 <;> dsimp only [p₀, p₁] <;> field_simp [hq0.ne', hq₀_pos.ne', hq₁_pos.ne']

private theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i => a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  rcases eq_or_ne q₀ ∞ with rfl | hq₀
  · rcases eq_or_ne q₁ ∞ with rfl | hq₁
    · obtain rfl : q = ∞ := (TauCeti.eq_top_iff_of_inv_eq hθ hq).2 ⟨rfl, rfl⟩
      rw [PiLp.norm_toLp, pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _))]
      exact mul_le_mul (Real.rpow_le_rpow (ha i) ((le_abs_self (a i)).trans
          (PiLp.norm_apply_le (WithLp.toLp ∞ a) i)) (sub_pos.2 hθ.2).le)
        (Real.rpow_le_rpow (hb i) ((le_abs_self (b i)).trans
          (PiLp.norm_apply_le (WithLp.toLp ∞ b) i)) hθ.1.le)
        (Real.rpow_nonneg (hb i) _) (by positivity)
    · rw [show (fun i => a i ^ (1 - θ) * b i ^ θ) =
        fun i => b i ^ (1 - (1 - θ)) * a i ^ (1 - θ) by ext i; rw [sub_sub_cancel, mul_comm],
        mul_comm]
      simpa only [sub_sub_cancel] using norm_toLp_rpow_mul_rpow_le_of_right_eq_top
        ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ hq₁ (by simpa [sub_sub_cancel] using hq) hb ha
  · rcases eq_or_ne q₁ ∞ with rfl | hq₁
    · exact norm_toLp_rpow_mul_rpow_le_of_right_eq_top hθ hq₀ (by simpa using hq) ha hb
    · exact norm_toLp_rpow_mul_rpow_le_of_ne_top hθ hq₀ hq₁ hq ha hb

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
            norm_mk_le_integral_stripPoisson hθoo (piLpStripTracesEquiv C q₀ q₁ g i)
        have ha_norm := (norm_toLp_integral_weighted_le g.val.1 (sub_pos.2 hθ1)
          (integrable_stripPoisson₀ θ) (fun t => (stripPoisson₀_pos hθoo t).le)
          (integral_stripPoisson₀ ⟨hθ0, hθ1.le⟩)).trans
          ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))
        have hb_norm := (norm_toLp_integral_weighted_le g.val.2 hθ0 (integrable_stripPoisson₁ θ)
          (fun t => (stripPoisson₁_pos hθoo t).le) (integral_stripPoisson₁ ⟨hθ0.le, hθ1⟩)).trans
          ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))
        refine ((PiLp.norm_mono (y := WithLp.toLp q fun i => a i ^ (1 - θ) * b i ^ θ)
          fun i => (hpt i).trans (le_abs_self _)).trans
          (norm_toLp_rpow_mul_rpow_le hθoo hq ha hb)).trans_lt (lt_of_le_of_lt ?_ hg)
        calc ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ
            ≤ ‖g‖ ^ (1 - θ) * ‖g‖ ^ θ :=
              mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha_norm (sub_pos.2 hθ1).le)
                (Real.rpow_le_rpow (norm_nonneg _) hb_norm hθ0.le)
                (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖g‖ := by rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_pos.2 hθ1).le hθ0.le,
              sub_add_cancel, Real.rpow_one]
  · rw [eq_zero_of_notMem hθ u, map_zero, norm_zero, norm_zero]

private theorem norm_toLp_mul_div_rpow_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {B qr : ℝ} (hB : 0 < B)
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i ^ qr = B ^ qr) :
    ‖WithLp.toLp p (fun i => B * (b i / B) ^ (qr * (p⁻¹).toReal))‖ ≤ B := by
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [PiLp.norm_toLp, pi_norm_le_iff_of_nonneg hB.le]
    intro i; simp [abs_of_pos hB]
  · have hp0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hp0]
    have hterm (i : ι) : ‖B * (b i / B) ^ (qr * (p⁻¹).toReal)‖ ^ p.toReal =
        B ^ p.toReal * (b i ^ qr / B ^ qr) := by
      have hpos : 0 < b i / B := div_pos (hb i) hB
      rw [Real.norm_of_nonneg (by positivity), Real.mul_rpow hB.le (Real.rpow_nonneg hpos.le _),
        ← Real.rpow_mul hpos.le, ENNReal.toReal_inv, inv_mul_cancel_right₀ hp0.ne',
        Real.div_rpow (hb i).le hB.le]
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_div, hsum,
      div_self (Real.rpow_pos_of_pos hB qr).ne', mul_one, one_div,
      Real.rpow_rpow_inv hB.le hp0.ne']
    exact le_rfl

private theorem exists_stripTraces_rescale {E₀ E₁ W : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
    {C₀ : CompatibleCouple ℂ E₀ E₁ W} {θ α₀ α₁ b B : ℝ} (hθ : θ ∈ Icc 0 1)
    (hα : (1 - θ) * α₀ + θ * α₁ = 1) (hb : 0 < b) (hB : 0 < B) (g : C₀.stripTraces)
    (hg : ‖g‖ < b) :
    ∃ g' : C₀.stripTraces, mk θ g' = mk θ g ∧
      (∀ t : ℝ, ‖g'.val.1 t‖ ≤ B * (b / B) ^ α₀) ∧
      (∀ t : ℝ, ‖g'.val.2 t‖ ≤ B * (b / B) ^ α₁) := by
  let L : ℝ := Real.log (b / B)
  let c : ℂ → ℂ := fun z => Complex.exp ((((1 - z) * (α₀ : ℂ) + z * (α₁ : ℂ)) - 1) * (L : ℂ))
  have hc_norm (z : ℂ) : ‖c z‖ = (b / B) ^ ((1 - z.re) * α₀ + z.re * α₁ - 1) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos (div_pos hb hB)]
    congr 1; simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, one_re]
    ring
  let M : ℝ := max ((α₀ - 1) * L) ((α₁ - 1) * L)
  have hK (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ Real.exp M := by
    rw [hc_norm, Real.rpow_def_of_pos (div_pos hb hB)]
    refine Real.exp_le_exp.2 ((le_of_eq (by ring :
      L * ((1 - z.re) * α₀ + z.re * α₁ - 1) =
        (1 - z.re) * ((α₀ - 1) * L) + z.re * ((α₁ - 1) * L))).trans ?_)
    calc (1 - z.re) * ((α₀ - 1) * L) + z.re * ((α₁ - 1) * L)
        ≤ (1 - z.re) * M + z.re * M := add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.2 hz.2))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hz.1)
      _ = M := by ring
  obtain ⟨g', hg₀', hg₁', heq⟩ := exists_stripTraces_smul_of_diffContOnCl g
    (by unfold c; fun_prop : Differentiable ℂ c).diffContOnCl hK
  have hcθ : c θ = 1 := by
    dsimp only [c]
    have h0 : (((1 - (θ : ℂ)) * (α₀ : ℂ) + (θ : ℂ) * (α₁ : ℂ)) - 1) = 0 := by
      exact_mod_cast sub_eq_zero.2 hα
    rw [h0, zero_mul, Complex.exp_zero]
  have hmul (α x : ℝ) (hx : x ≤ b) : (b / B) ^ (α - 1) * x ≤ B * (b / B) ^ α :=
    (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (div_pos hb hB).le _)).trans_eq <| by
      calc (b / B) ^ (α - 1) * b = B * ((b / B) ^ (α - 1) * (b / B) ^ (1 : ℝ)) := by
            rw [Real.rpow_one]; field_simp [hB.ne']
        _ = B * (b / B) ^ α := by rw [← Real.rpow_add (div_pos hb hB), sub_add_cancel]
  refine ⟨g', by rw [heq hθ, hcθ, one_smul], fun t => ?_, fun t => ?_⟩
  · rw [hg₀', norm_smul, hc_norm]
    simp only [mul_I_re, ofReal_im, neg_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact hmul α₀ _ (((ZeroAtInftyContinuousMap.norm_coe_le_norm g.val.1 t).trans
      ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))).trans hg.le)
  · rw [hg₁', norm_smul, hc_norm]
    simp only [add_re, one_re, mul_I_re, ofReal_im, neg_zero, add_zero, sub_self, zero_mul,
      one_mul, zero_add]
    exact hmul α₁ _ (((ZeroAtInftyContinuousMap.norm_coe_le_norm g.val.2 t).trans
      ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))).trans hg.le)

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
  let G : (piLp C ∞ ∞).stripTraces := (piLpStripTracesEquiv C ∞ ∞).symm g
  have hB : 0 ≤ ‖v‖ + ε := add_nonneg (norm_nonneg v) hε.le
  have hG : ‖G.val‖ ≤ ‖v‖ + ε := by
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
  rw [show (piLpContinuousLinearEquiv C ∞ ∞ ∞ θ).symm v = mk θ G by
    rw [show v = WithLp.toLp ∞ (fun i => mk θ (g i)) from PiLp.ext fun i => (hg_mk i).symm,
      piLpContinuousLinearEquiv_symm_mk]]
  exact (norm_mk_le G).trans ((Submodule.norm_coe G).symm.trans_le hG)

private theorem exists_pos_perturbation [Nonempty ι] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq_top : q ≠ ∞)
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] (v : PiLp q β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (b : ι → ℝ) (B : ℝ), 0 < B ∧ B ≤ ‖v‖ + ε ∧ (∀ i, 0 < b i ∧ ‖v i‖ < b i) ∧
      ∑ i, b i ^ q.toReal = B ^ q.toReal := by
  have hq0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  let u1 : PiLp q (fun _ : ι => ℝ) := WithLp.toLp q (fun _ => 1)
  let δ : ℝ := ε / (‖u1‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let b : ι → ℝ := fun i => ‖v i‖ + δ
  have hb (i : ι) : 0 < b i := add_pos_of_nonneg_of_pos (norm_nonneg _) hδ
  let B : ℝ := ‖WithLp.toLp q b‖
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hB : 0 < B := (hb i₀).trans_le ((le_abs_self (b i₀)).trans
    (PiLp.norm_apply_le (WithLp.toLp q b) i₀))
  refine ⟨b, B, hB, ?_, fun i => ⟨hb i, lt_add_of_pos_right ‖v i‖ hδ⟩, ?_⟩
  · have hδu : δ * ‖u1‖ ≤ ε := by
      dsimp only [δ]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg u1, hε.le]
    calc B ≤ ‖WithLp.toLp q (fun i => ‖v i‖)‖ + ‖δ • u1‖ := by
          dsimp only [B]; rw [show WithLp.toLp q b = WithLp.toLp q (fun i => ‖v i‖) + δ • u1 by
            ext i; simp [b, u1]]
          exact norm_add_le _ _
      _ = ‖v‖ + δ * ‖u1‖ := by rw [PiLp.norm_norm, norm_smul, Real.norm_of_nonneg hδ.le]
      _ ≤ ‖v‖ + ε := add_le_add_right hδu ‖v‖
  · have hBeq : B = (∑ i, b i ^ q.toReal) ^ (1 / q.toReal) := by
      dsimp only [B]; rw [PiLp.norm_eq_sum hq0]
      congr 1; exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_of_nonneg (hb i).le]
    rw [hBeq, one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ => by positivity) hq0.ne']

private theorem norm_symm_le_of_ne_top (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i))
    {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq_top : q ≠ ∞) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  cases isEmpty_or_nonempty ι
  · rw [Subsingleton.elim v 0, map_zero, norm_zero, norm_zero]
  have hα := one_sub_mul_toReal_inv_add hθ hq_top hq
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b, B, hB, hB_le, hb, hsum⟩ := exists_pos_perturbation hq_top v hε
  have hex (i : ι) : ∃ g' : (C i).stripTraces, mk θ g' = v i ∧
      (∀ t, ‖g'.val.1 t‖ ≤ B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal)) ∧
      (∀ t, ‖g'.val.2 t‖ ≤ B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal)) := by
    obtain ⟨g, hg_eq, hg⟩ := norm_lt_iff.1 (hb i).2
    obtain ⟨g', hg'_eq, hg'₀, hg'₁⟩ :=
      exists_stripTraces_rescale ⟨hθ.1.le, hθ.2.le⟩ hα (hb i).1 hB g hg
    exact ⟨g', hg'_eq.trans hg_eq, hg'₀, hg'₁⟩
  choose g' hg'_mk hg'_0 hg'_1 using hex
  let G : (piLp C q₀ q₁).stripTraces := (piLpStripTracesEquiv C q₀ q₁).symm g'
  have hG : ‖G.val‖ ≤ B := by
    rw [Prod.norm_def]
    exact max_le ((ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₀ fun i => B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal))
          fun i => by
            rw [piLpStripTracesEquiv_symm_apply_fst]
            exact (hg'_0 i t).trans (le_abs_self _)).trans
          (norm_toLp_mul_div_rpow_le hB (fun i => (hb i).1) hsum))
      ((ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₁ fun i => B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal))
          fun i => by
            rw [piLpStripTracesEquiv_symm_apply_snd]
            exact (hg'_1 i t).trans (le_abs_self _)).trans
          (norm_toLp_mul_div_rpow_le hB (fun i => (hb i).1) hsum))
  rw [show (piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v = mk θ G by
    rw [show v = WithLp.toLp q (fun i => mk θ (g' i)) from PiLp.ext fun i => (hg'_mk i).symm,
      piLpContinuousLinearEquiv_symm_mk]]
  exact ((norm_mk_le G).trans ((Submodule.norm_coe G).symm.trans_le hG)).trans hB_le

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
`θ : ℝ` satisfying `1 / q = (1 - θ) / q₀ + θ / q₁`, complex interpolation commutes isometrically
with `PiLp`:
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`. -/
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

/-- Evaluating `piLpEquiv` on an admissible trace class projects the trace coordinatewise. -/
theorem piLpEquiv_mk_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (g : (piLp C q₀ q₁).stripTraces) (i : ι) :
    piLpEquiv C hq (mk θ g) i = mk θ (piLpStripTracesEquiv C q₀ q₁ g i) :=
  piLpContinuousLinearEquiv_mk_apply C q₀ q₁ q θ g i

/-- `piLpEquiv` intertwines `toSum` coordinatewise with `piLpSumEquiv`. -/
theorem toSum_piLpEquiv_apply (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp C q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    toSum (piLpEquiv C hq u i) = piLpSumEquiv C q₀ q₁ (toSum u) i :=
  toSum_piLpContinuousLinearEquiv_apply C q₀ q₁ q θ u i

@[simp]
theorem piLpEquiv_symm_mk (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (h : ∀ i, (C i).stripTraces) :
    (piLpEquiv C hq).symm (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) :=
  piLpContinuousLinearEquiv_symm_mk C q₀ q₁ q θ h

end PiLpEquiv

section Refl

/-- For `0 ≤ θ ≤ 1`, the complex interpolation space `[X, X]_θ` of the constant couple `refl ℂ X`
is canonically linearly isometric to `X`. -/
def reflEquiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ} (hθ : θ ∈ Icc 0 1) :
    (refl ℂ X).ComplexMethodSpace θ ≃ₗᵢ[ℂ] X where
  toFun u := (refl ℂ X).sumSpaceEmbed (toSum u)
  invFun x := ofInter θ
    ⟨(x, x), (refl ℂ X).mem_inter_iff.2 (by dsimp only; rw [refl_embed₀, refl_embed₁])⟩
  map_add' u v := by simp
  map_smul' c u := by simp
  left_inv u := by
    dsimp only
    apply toSum_injective
    rw [toSum_ofInter hθ, interFst_apply]
    exact refl_fstToSum_sumSpaceEmbed (toSum u)
  right_inv x := by
    dsimp only
    rw [toSum_ofInter hθ, interFst_apply, sumSpaceEmbed_fstToSum]
    change (refl ℂ X).embed₀ x = x
    rw [refl_embed₀, ContinuousLinearMap.id_apply]
  norm_map' u := (norm_refl_sumSpaceEmbed (toSum u)).trans (norm_refl u).symm

@[simp]
theorem reflEquiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (hθ : θ ∈ Icc 0 1) (u : (refl ℂ X).ComplexMethodSpace θ) :
    reflEquiv hθ u = (refl ℂ X).sumSpaceEmbed (toSum u) :=
  (rfl)

@[simp]
theorem reflEquiv_symm_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (hθ : θ ∈ Icc 0 1) (x : X) :
    (reflEquiv hθ).symm x = ofInter θ
      ⟨(x, x), (refl ℂ X).mem_inter_iff.2 (by dsimp only; rw [refl_embed₀, refl_embed₁])⟩ :=
  (rfl)

/-- `reflEquiv.symm` lifts `x : X` over `fstToSum x` in the sum space of `refl ℂ X`. -/
theorem toSum_reflEquiv_symm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (hθ : θ ∈ Icc 0 1) (x : X) :
    toSum ((reflEquiv hθ).symm x) = (refl ℂ X).fstToSum x := by
  rw [reflEquiv_symm_apply, toSum_ofInter hθ, interFst_apply]

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
    PiLp.toLp_apply, reflEquiv_apply, toSum_piLpEquiv_apply (fun j => refl ℂ (X j)),
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
