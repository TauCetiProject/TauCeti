/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# `PiLp` compatible couple families

Given an arbitrary index type `ι`, a family of compatible couples `C i` (`i : ι`), and exponents
`q₀, q₁ : ℝ≥0∞`, `TauCeti.CompatibleCouple.piLpFamily C q₀ q₁` forms the product compatible couple
`(PiLp q₀ X₀, PiLp q₁ X₁)` inside the ambient product `∀ i, V i`, with constant-family
specialization `TauCeti.CompatibleCouple.piLp C ι q₀ q₁ := piLpFamily (fun _ : ι => C) q₀ q₁`.

For finite index types (`[Fintype ι]`) and `1 ≤ q₀, q₁`, this file also records the intersection
characterization `TauCeti.CompatibleCouple.mem_piLpFamily_inter_iff`, the coordinate sum-space
compatibility lemmas, and the canonical continuous linear equivalence
`TauCeti.CompatibleCouple.piLpFamilySumEquiv` identifying `(piLpFamily C q₀ q₁).SumSpace` with
`∀ i, (C i).SumSpace`.
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
`CompatibleCouple.piLpFamily C q₀ q₁` is the compatible couple `(PiLp q₀ X₀, PiLp q₁ X₁)` inside
the product ambient space `∀ i, V i`. -/
def piLpFamily (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞) :
    CompatibleCouple 𝕜 (PiLp q₀ X₀) (PiLp q₁ X₁) (∀ i, V i) where
  embed₀ := ContinuousLinearMap.pi fun i =>
    (C i).embed₀.comp ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv q₀ 𝕜 X₀).toContinuousLinearMap)
  embed₁ := ContinuousLinearMap.pi fun i =>
    (C i).embed₁.comp ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv q₁ 𝕜 X₁).toContinuousLinearMap)
  embed₀_injective _ _ h := by ext i; exact (C i).embed₀_injective (congrFun h i)
  embed₁_injective _ _ h := by ext i; exact (C i).embed₁_injective (congrFun h i)

@[simp] theorem piLpFamily_embed₀_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) (x : PiLp q₀ X₀) (i : ι) :
    (piLpFamily C q₀ q₁).embed₀ x i = (C i).embed₀ (x i) := by simp [piLpFamily]

@[simp] theorem piLpFamily_embed₁_apply (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    (q₀ q₁ : ℝ≥0∞) (x : PiLp q₁ X₁) (i : ι) :
    (piLpFamily C q₀ q₁).embed₁ x i = (C i).embed₁ (x i) := by simp [piLpFamily]

end CoupleDef

section Couple

variable {𝕜 ι : Type*} [NormedField 𝕜] [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace 𝕜 (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace 𝕜 (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, TopologicalSpace (V i)]

/-- A pair of families lies in the intersection `(piLpFamily C q₀ q₁).inter` exactly when each
pair of coordinates lies in `(C i).inter`. -/
theorem mem_piLpFamily_inter_iff (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i))
    {q₀ q₁ : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {x : PiLp q₀ X₀ × PiLp q₁ X₁} :
    x ∈ (piLpFamily C q₀ q₁).inter ↔ ∀ i, (x.1 i, x.2 i) ∈ (C i).inter := by
  simp [funext_iff]

section
variable [∀ i, ContinuousAdd (V i)]
variable (C : ∀ i, CompatibleCouple 𝕜 (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

/-- Projecting an element of the intersection of `piLpFamily C q₀ q₁` to coordinate `i` commutes
with the inclusions into the `i`th coordinate sum space. -/
theorem fstToSum_proj_interFst_eq_sndToSum_proj_interSnd (i : ι)
    (x : (piLpFamily C q₀ q₁).inter) :
    (C i).fstToSum (PiLp.proj (𝕜 := 𝕜) q₀ X₀ i ((piLpFamily C q₀ q₁).interFst x)) =
      (C i).sndToSum (PiLp.proj (𝕜 := 𝕜) q₁ X₁ i ((piLpFamily C q₀ q₁).interSnd x)) := by
  apply (C i).sumSpace_ext
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
  simpa only [piLpFamily_embed₀_apply, piLpFamily_embed₁_apply, PiLp.proj_apply] using
    congrFun ((piLpFamily C q₀ q₁).embed₀_interFst x) i

/-- Embedding an element of the `i`th coordinate intersection into the `i`th slot via
`PiLp.singleCLM` commutes with the inclusions into the product sum space. -/
theorem fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd [DecidableEq ι]
    (i : ι) (x : (C i).inter) :
    (piLpFamily C q₀ q₁).fstToSum (PiLp.singleCLM q₀ 𝕜 X₀ i ((C i).interFst x)) =
      (piLpFamily C q₀ q₁).sndToSum (PiLp.singleCLM q₁ 𝕜 X₁ i ((C i).interSnd x)) := by
  apply (piLpFamily C q₀ q₁).sumSpace_ext; ext j
  rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, piLpFamily_embed₀_apply,
    piLpFamily_embed₁_apply, PiLp.singleCLM_apply, PiLp.singleCLM_apply]
  by_cases hji : j = i
  · subst hji; rw [PiLp.single_eq_same, PiLp.single_eq_same]; exact (C j).embed₀_interFst x
  · simp [PiLp.single_eq_of_ne _ hji]

private def piLpFamilySumFwd : (piLpFamily C q₀ q₁).SumSpace →L[𝕜] ∀ i, (C i).SumSpace :=
  ContinuousLinearMap.pi fun i =>
    (piLpFamily C q₀ q₁).sumLift ((C i).fstToSum.comp (PiLp.proj q₀ X₀ i))
      ((C i).sndToSum.comp (PiLp.proj q₁ X₁ i))
      (fun x => by simpa using fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i x)

open Classical in
private def piLpFamilySumInvSingle (i : ι) :
    (C i).SumSpace →L[𝕜] (piLpFamily C q₀ q₁).SumSpace :=
  (C i).sumLift ((piLpFamily C q₀ q₁).fstToSum.comp (PiLp.singleCLM q₀ 𝕜 X₀ i))
    ((piLpFamily C q₀ q₁).sndToSum.comp (PiLp.singleCLM q₁ 𝕜 X₁ i))
    (fun x => by
      simpa using fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i x)

private def piLpFamilySumInv : (∀ i, (C i).SumSpace) →L[𝕜] (piLpFamily C q₀ q₁).SumSpace :=
  ∑ i : ι, (piLpFamilySumInvSingle C q₀ q₁ i).comp (ContinuousLinearMap.proj i)

@[simp] private theorem sumSpaceEmbed_piLpFamilySumFwd (u : (piLpFamily C q₀ q₁).SumSpace)
    (j : ι) :
    (C j).sumSpaceEmbed (piLpFamilySumFwd C q₀ q₁ u j) =
      (piLpFamily C q₀ q₁).sumSpaceEmbed u j := by
  obtain ⟨x₀, x₁, rfl⟩ := (piLpFamily C q₀ q₁).exists_fstToSum_add_sndToSum_eq u
  simp [piLpFamilySumFwd]

open Classical in
@[simp] private theorem sumSpaceEmbed_piLpFamilySumInvSingle (i j : ι) (x : (C i).SumSpace) :
    (piLpFamily C q₀ q₁).sumSpaceEmbed (piLpFamilySumInvSingle C q₀ q₁ i x) j =
      Pi.single i ((C i).sumSpaceEmbed x) j := by
  obtain ⟨x₀, x₁, rfl⟩ := (C i).exists_fstToSum_add_sndToSum_eq x
  rcases eq_or_ne j i with rfl | hji <;>
    simp [piLpFamilySumInvSingle, PiLp.single_eq_of_ne, *]

@[simp] private theorem sumSpaceEmbed_piLpFamilySumInv (v : ∀ i, (C i).SumSpace) (j : ι) :
    (piLpFamily C q₀ q₁).sumSpaceEmbed (piLpFamilySumInv C q₀ q₁ v) j =
      (C j).sumSpaceEmbed (v j) := by
  classical
  simp [piLpFamilySumInv, map_sum]

open Classical in
@[simp] private theorem piLpFamilySumFwd_piLpFamilySumInvSingle (i j : ι) (x : (C i).SumSpace) :
    piLpFamilySumFwd C q₀ q₁ (piLpFamilySumInvSingle C q₀ q₁ i x) j =
      Pi.single (M := fun k => (C k).SumSpace) i x j := by
  apply (C j).sumSpace_ext
  rw [sumSpaceEmbed_piLpFamilySumFwd, sumSpaceEmbed_piLpFamilySumInvSingle]
  rcases eq_or_ne j i with rfl | hji <;> simp [Pi.single_eq_of_ne, *]

/-- The sum space of `CompatibleCouple.piLpFamily C q₀ q₁` identifies canonically with the product
of the coordinate sum spaces `∀ i, (C i).SumSpace`. -/
def piLpFamilySumEquiv : (piLpFamily C q₀ q₁).SumSpace ≃L[𝕜] ∀ i, (C i).SumSpace :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpFamilySumFwd C q₀ q₁)
    (piLpFamilySumInv C q₀ q₁)
    (ContinuousLinearMap.ext fun v => by
      ext j
      simp [piLpFamilySumInv, map_sum])
    (ContinuousLinearMap.ext fun u => by
      apply (piLpFamily C q₀ q₁).sumSpace_ext; ext j
      simp)

/-- Coordinatewise application formula for `piLpFamilySumEquiv` in terms of `sumLift`. -/
theorem piLpFamilySumEquiv_apply_eq_sumLift (u : (piLpFamily C q₀ q₁).SumSpace) (i : ι) :
    piLpFamilySumEquiv C q₀ q₁ u i =
      (piLpFamily C q₀ q₁).sumLift ((C i).fstToSum.comp (PiLp.proj q₀ X₀ i))
        ((C i).sndToSum.comp (PiLp.proj q₁ X₁ i))
        (fun x => by simpa using fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i x)
        u := ContinuousLinearMap.pi_apply _ _ i

@[simp] theorem piLpFamilySumEquiv_fstToSum (x : PiLp q₀ X₀) (i : ι) :
    piLpFamilySumEquiv C q₀ q₁ ((piLpFamily C q₀ q₁).fstToSum x) i = (C i).fstToSum (x i) := by
  simp [piLpFamilySumEquiv, piLpFamilySumFwd, sumLift_fstToSum]

@[simp] theorem piLpFamilySumEquiv_sndToSum (x : PiLp q₁ X₁) (i : ι) :
    piLpFamilySumEquiv C q₀ q₁ ((piLpFamily C q₀ q₁).sndToSum x) i = (C i).sndToSum (x i) := by
  simp [piLpFamilySumEquiv, piLpFamilySumFwd, sumLift_sndToSum]

@[simp] theorem sumSpaceEmbed_piLpFamilySumEquiv_apply (u : (piLpFamily C q₀ q₁).SumSpace)
    (i : ι) : (C i).sumSpaceEmbed (piLpFamilySumEquiv C q₀ q₁ u i) =
      (piLpFamily C q₀ q₁).sumSpaceEmbed u i :=
  sumSpaceEmbed_piLpFamilySumFwd C q₀ q₁ u i

@[simp] theorem sumSpaceEmbed_piLpFamilySumEquiv_symm (v : ∀ i, (C i).SumSpace) (i : ι) :
    (piLpFamily C q₀ q₁).sumSpaceEmbed ((piLpFamilySumEquiv C q₀ q₁).symm v) i =
      (C i).sumSpaceEmbed (v i) := by
  rw [← sumSpaceEmbed_piLpFamilySumEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end Couple

section ConstantCouple

variable {𝕜 X₀ X₁ V : Type*} [Semiring 𝕜]
  [AddCommGroup X₀] [Module 𝕜 X₀] [TopologicalSpace X₀]
  [AddCommGroup X₁] [Module 𝕜 X₁] [TopologicalSpace X₁]
  [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- For a single compatible couple `C` and an arbitrary index type `ι`,
`CompatibleCouple.piLp C ι q₀ q₁` is the product compatible couple
`(PiLp q₀ (fun _ : ι => X₀), PiLp q₁ (fun _ : ι => X₁))` inside `ι → V`, defined as the
constant-family specialization `piLpFamily (fun _ : ι => C) q₀ q₁`. -/
abbrev piLp (C : CompatibleCouple 𝕜 X₀ X₁ V) (ι : Type*) (q₀ q₁ : ℝ≥0∞) :
    CompatibleCouple 𝕜 (PiLp q₀ fun _ : ι => X₀) (PiLp q₁ fun _ : ι => X₁) (ι → V) :=
  piLpFamily (fun _ : ι => C) q₀ q₁

end ConstantCouple

end TauCeti.CompatibleCouple
