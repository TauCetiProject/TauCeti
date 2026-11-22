/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Finite `PiLp` compatible couples

Given a family of compatible couples `C i` (`i : ι`) and exponents `q₀, q₁ : ℝ≥0∞`, this file
forms the product compatible couple `TauCeti.CompatibleCouple.piLp C q₀ q₁` of
`(PiLp q₀ X₀, PiLp q₁ X₁)` inside the ambient product `∀ i, V i`, together with the canonical
continuous linear equivalence `TauCeti.CompatibleCouple.piLpSumEquiv` identifying its sum space
with `∀ i, (C i).SumSpace`.
-/

public noncomputable section

open scoped ENNReal

namespace TauCeti.CompatibleCouple

section CoupleDef

variable {𝕜 ι : Type*} [Semiring 𝕜]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, AddCommGroup (X₀ i)] [∀ i, Module 𝕜 (X₀ i)] [∀ i, TopologicalSpace (X₀ i)]
  [∀ i, AddCommGroup (X₁ i)] [∀ i, Module 𝕜 (X₁ i)] [∀ i, TopologicalSpace (X₁ i)]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module 𝕜 (V i)] [∀ i, TopologicalSpace (V i)]

/-- Given a family of compatible couples `C i` (`i : ι`) and exponents `q₀, q₁ : ℝ≥0∞`,
`CompatibleCouple.piLp C q₀ q₁` is the compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` inside the
product ambient space `∀ i, V i`. -/
def piLp (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i =>
    (C i).embed₀.comp ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv q₀ 𝕜 X₀).toContinuousLinearMap)
  embed₁ := ContinuousLinearMap.pi fun i =>
    (C i).embed₁.comp ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv q₁ 𝕜 X₁).toContinuousLinearMap)
  embed₀_injective x y h := by
    ext i
    exact (C i).embed₀_injective (congrFun h i)
  embed₁_injective x y h := by
    ext i
    exact (C i).embed₁_injective (congrFun h i)

@[simp]
theorem piLp_embed₀_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    (x : PiLp q₀ X₀) (i : ι) :
    (piLp C q₀ q₁).embed₀ x i = (C i).embed₀ (x i) := by
  dsimp [piLp]
  rfl

@[simp]
theorem piLp_embed₁_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    (x : PiLp q₁ X₁) (i : ι) :
    (piLp C q₀ q₁).embed₁ x i = (C i).embed₁ (x i) := by
  dsimp [piLp]
  rfl

end CoupleDef

section Couple

variable {𝕜 ι : Type*} [NormedField 𝕜] [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace 𝕜 (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)]

/-- Projecting an element of the intersection of `piLp C q₀ q₁` to coordinate `i` commutes with
the inclusions into the `i`th coordinate sum space. -/
theorem piLpProj_inter (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (i : ι) (x : (piLp C q₀ q₁).inter) :
    (C i).fstToSum (PiLp.proj (𝕜 := 𝕜) q₀ X₀ i ((piLp C q₀ q₁).interFst x)) =
      (C i).sndToSum (PiLp.proj (𝕜 := 𝕜) q₁ X₁ i ((piLp C q₀ q₁).interSnd x)) := by
  apply (C i).sumSpace_ext
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
  exact congrFun ((piLp C q₀ q₁).embed₀_interFst x) i

/-- Embedding an element of the `i`th coordinate intersection into the `i`th slot via
`PiLp.singleCLM` commutes with the inclusions into the product sum space. -/
theorem piLpSingle_inter [DecidableEq ι] (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (i : ι) (x : (C i).inter) :
    (piLp C q₀ q₁).fstToSum (PiLp.singleCLM q₀ 𝕜 X₀ i ((C i).interFst x)) =
      (piLp C q₀ q₁).sndToSum (PiLp.singleCLM q₁ 𝕜 X₁ i ((C i).interSnd x)) := by
  apply (piLp C q₀ q₁).sumSpace_ext
  ext j
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, piLp_embed₀_apply, piLp_embed₁_apply,
    PiLp.singleCLM_apply, PiLp.singleCLM_apply]
  by_cases hji : j = i
  · subst hji
    rw [PiLp.single_eq_same, PiLp.single_eq_same]
    exact (C j).embed₀_interFst x
  · simp [PiLp.single_eq_of_ne _ hji]

private def piLpSumFwd (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).SumSpace →L[𝕜] ∀ i, (C i).SumSpace :=
  ContinuousLinearMap.pi fun i =>
    (piLp C q₀ q₁).sumLift ((C i).fstToSum.comp (PiLp.proj q₀ X₀ i))
      ((C i).sndToSum.comp (PiLp.proj q₁ X₁ i)) fun x => by
        simpa only [ContinuousLinearMap.comp_apply] using piLpProj_inter C q₀ q₁ i x

private def piLpSumInv (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (∀ i, (C i).SumSpace) →L[𝕜] (piLp C q₀ q₁).SumSpace := by
  classical
  exact ∑ i : ι,
    ((C i).sumLift ((piLp C q₀ q₁).fstToSum.comp (PiLp.singleCLM q₀ 𝕜 X₀ i))
      ((piLp C q₀ q₁).sndToSum.comp (PiLp.singleCLM q₁ 𝕜 X₁ i)) fun x => by
        simpa only [ContinuousLinearMap.comp_apply] using piLpSingle_inter C q₀ q₁ i x).comp
      (ContinuousLinearMap.proj i)

private theorem piLpSumFwd_fstToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₀ X₀) (i : ι) :
    piLpSumFwd C q₀ q₁ ((piLp C q₀ q₁).fstToSum x) i = (C i).fstToSum (x i) := by
  simp [piLpSumFwd, sumLift_fstToSum]

private theorem piLpSumFwd_sndToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₁ X₁) (i : ι) :
    piLpSumFwd C q₀ q₁ ((piLp C q₀ q₁).sndToSum x) i = (C i).sndToSum (x i) := by
  simp [piLpSumFwd, sumLift_sndToSum]

/-- The sum space of `CompatibleCouple.piLp C q₀ q₁` identifies canonically with the product of the
coordinate sum spaces `∀ i, (C i).SumSpace`. -/
def piLpSumEquiv (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] :
    (piLp C q₀ q₁).SumSpace ≃L[𝕜] ∀ i, (C i).SumSpace :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpSumFwd C q₀ q₁) (piLpSumInv C q₀ q₁)
    (ContinuousLinearMap.ext fun v => by
      classical
      ext j
      apply (C j).sumSpace_ext
      have hsum : (C j).sumSpaceEmbed (piLpSumFwd C q₀ q₁ (piLpSumInv C q₀ q₁ v) j) =
          ∑ i : ι, (C j).sumSpaceEmbed (piLpSumFwd C q₀ q₁
            ((C i).sumLift ((piLp C q₀ q₁).fstToSum.comp (PiLp.singleCLM q₀ 𝕜 X₀ i))
              ((piLp C q₀ q₁).sndToSum.comp (PiLp.singleCLM q₁ 𝕜 X₁ i)) (fun x => by
                simpa only [ContinuousLinearMap.comp_apply] using piLpSingle_inter C q₀ q₁ i x)
              (v i)) j) := by
        simp [piLpSumInv, map_sum]
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hsum,
        Fintype.sum_eq_single j]
      · obtain ⟨y₀, y₁, hy⟩ := (C j).exists_fstToSum_add_sndToSum_eq (v j)
        rw [← hy]
        simp [sumLift_fstToSum, sumLift_sndToSum, piLpSumFwd_fstToSum, piLpSumFwd_sndToSum,
          PiLp.singleCLM_apply]
      · intro i hij
        obtain ⟨z₀, z₁, hz⟩ := (C i).exists_fstToSum_add_sndToSum_eq (v i)
        rw [← hz]
        simp [sumLift_fstToSum, sumLift_sndToSum, piLpSumFwd_fstToSum, piLpSumFwd_sndToSum,
          PiLp.singleCLM_apply, PiLp.single_eq_of_ne _ hij.symm])
    (ContinuousLinearMap.ext fun u => by
      classical
      obtain ⟨x₀, x₁, rfl⟩ := (piLp C q₀ q₁).exists_fstToSum_add_sndToSum_eq u
      apply (piLp C q₀ q₁).sumSpace_ext
      ext j
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, piLpSumInv,
        FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply, map_add, map_sum,
        piLpSumFwd_fstToSum, piLpSumFwd_sndToSum, sumLift_fstToSum, sumLift_sndToSum,
        sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply, piLp_embed₀_apply,
        piLp_embed₁_apply, PiLp.singleCLM_apply]
      rw [Fintype.sum_eq_single j (fun i hij => by simp [PiLp.single_eq_of_ne _ hij.symm]),
        Fintype.sum_eq_single j (fun i hij => by simp [PiLp.single_eq_of_ne _ hij.symm])]
      simp)

private theorem piLpSumEquiv_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (u : (piLp C q₀ q₁).SumSpace) :
    piLpSumEquiv C q₀ q₁ u = piLpSumFwd C q₀ q₁ u := by
  dsimp [piLpSumEquiv]

@[simp]
theorem piLpSumEquiv_fstToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₀ X₀) (i : ι) :
    piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).fstToSum x) i = (C i).fstToSum (x i) := by
  rw [piLpSumEquiv_apply, piLpSumFwd_fstToSum]

@[simp]
theorem piLpSumEquiv_sndToSum (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (x : PiLp q₁ X₁) (i : ι) :
    piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).sndToSum x) i = (C i).sndToSum (x i) := by
  rw [piLpSumEquiv_apply, piLpSumFwd_sndToSum]

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

end TauCeti.CompatibleCouple
