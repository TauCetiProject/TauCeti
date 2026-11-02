/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianCech.Continuous
public import Mathlib.Topology.Algebra.GroupCompletion

/-!
# The separated completed rational-localization Čech complex

Complete the terms of the rational-localization Čech complex for their natural additive
uniformities. Continuity of the algebraic maps gives continuous maps on the separated
completions, using Mathlib’s `AddMonoidHom.completion` on
`TauCeti.cechLocalizationAugmentation` and `TauCeti.cechLocalizationDifferential`. Their values
on the dense algebraic terms characterize them, and consecutive maps compose to zero.

These are the maps of the separated completion of the topologised algebraic Čech complex.
For `M = B` they give the maps of Huber's analytic Čech complex; for finite `M` over a ring with a
noetherian ring of definition, identifying the completed terms with Huber's terms requires a
comparison not proved here. This construction does not assert exactness: that requires strictness
of the algebraic complex, in addition to its algebraic exactness. The construction here allows
non-Hausdorff uncompleted terms and does not assume noetherianity, completeness of the coefficient
ring, or finite generation of the module.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, complexes (*) and (**) in the proof of Theorem 2.5, Case I.
-/

public section

open UniformSpace

namespace TauCeti.Huber.NoetherianCech

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {ι : Type*} (f : ι → B) (P : PairOfDefinition B) (M : Type*) [AddCommGroup M] [Module B M]
  (hf : Ideal.span (Set.range f) = ⊤)

/-- The separated completion of the degree-`p` term of the rational-localization Čech complex,
for the product of the natural module topologies on its faces. -/
abbrev completedTerm (p : ℕ) :=
  @Completion (cechLocalizationTerm M f p) (termUniformSpace f P M hf p)

section Differential

variable [LinearOrder ι]

/-- The differential of the separated completed rational-localization Čech complex. -/
noncomputable def completedDifferential (p : ℕ) :
    completedTerm f P M hf p →+ completedTerm f P M hf (p + 1) := by
  let sourceUniform := termUniformSpace f P M hf p
  let targetUniform := termUniformSpace f P M hf (p + 1)
  exact (cechLocalizationDifferential M f p).toAddMonoidHom.completion <| by
    have hc := continuous_cechLocalizationDifferential f P hf M p
    rw [← termUniformSpace_toTopologicalSpace f P M hf p,
      ← termUniformSpace_toTopologicalSpace f P M hf (p + 1)] at hc
    exact hc

/-- The completed differential is continuous. -/
@[fun_prop]
theorem continuous_completedDifferential (p : ℕ) :
    Continuous (completedDifferential f P M hf p) := by
  let _ := termUniformSpace f P M hf p
  let _ := termUniformSpace f P M hf (p + 1)
  unfold completedDifferential
  exact AddMonoidHom.continuous_completion _ _

/-- The completed differential agrees with the algebraic differential on the dense algebraic
term. -/
@[simp]
theorem completedDifferential_coe (p : ℕ) (x : cechLocalizationTerm M f p) :
    completedDifferential f P M hf p (x : completedTerm f P M hf p) =
      (cechLocalizationDifferential M f p x : completedTerm f P M hf (p + 1)) := by
  let _ := termUniformSpace f P M hf p
  let _ := termUniformSpace f P M hf (p + 1)
  unfold completedDifferential
  exact AddMonoidHom.completion_coe _ _ x

/-- Two consecutive differentials of the completed complex compose to zero. -/
theorem completedDifferential_comp_differential (p : ℕ) :
    (completedDifferential f P M hf (p + 1)).comp (completedDifferential f P M hf p) = 0 := by
  let _ := termUniformSpace f P M hf p
  let _ := termUniformSpace f P M hf (p + 1)
  let _ := termUniformSpace f P M hf (p + 1 + 1)
  apply DFunLike.coe_injective
  refine Completion.ext ((continuous_completedDifferential f P M hf (p + 1)).comp
    (continuous_completedDifferential f P M hf p)) continuous_const fun x ↦ ?_
  have h := LinearMap.congr_fun (cechLocalizationDifferential_comp_differential M f p) x
  simpa using congrArg (fun y : cechLocalizationTerm M f (p + 1 + 1) ↦
    (y : completedTerm f P M hf (p + 1 + 1))) h

end Differential

section Augmentation

variable [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology B M]

/-- The augmentation from the separated completion of `M` to the degree-zero completed term. -/
noncomputable def completedAugmentation : Completion M →+ completedTerm f P M hf 0 := by
  let targetUniform := termUniformSpace f P M hf 0
  exact (cechLocalizationAugmentation M f).toAddMonoidHom.completion <| by
    have hc := continuous_cechLocalizationAugmentation f P hf M
    rw [← termUniformSpace_toTopologicalSpace f P M hf 0] at hc
    exact hc

/-- The completed augmentation is continuous. -/
@[fun_prop]
theorem continuous_completedAugmentation : Continuous (completedAugmentation f P M hf) := by
  let _ := termUniformSpace f P M hf 0
  unfold completedAugmentation
  exact AddMonoidHom.continuous_completion _ _

/-- The completed augmentation agrees with the algebraic augmentation on the original module. -/
@[simp]
theorem completedAugmentation_coe (m : M) :
    completedAugmentation f P M hf (m : Completion M) =
      (cechLocalizationAugmentation M f m : completedTerm f P M hf 0) := by
  let _ := termUniformSpace f P M hf 0
  unfold completedAugmentation
  exact AddMonoidHom.completion_coe _ _ m

/-- The completed augmentation followed by the first completed differential is zero. -/
theorem completedDifferential_comp_augmentation [LinearOrder ι] :
    (completedDifferential f P M hf 0).comp (completedAugmentation f P M hf) = 0 := by
  apply DFunLike.coe_injective
  refine Completion.ext ((continuous_completedDifferential f P M hf 0).comp
    (continuous_completedAugmentation f P M hf)) continuous_const fun m ↦ ?_
  have h := LinearMap.congr_fun (cechLocalizationDifferential_comp_augmentation M f) m
  simpa using congrArg (fun y : cechLocalizationTerm M f 1 ↦ (y : completedTerm f P M hf 1)) h

end Augmentation

end TauCeti.Huber.NoetherianCech
