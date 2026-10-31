/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing

/-!
# Entire analytic elements form a core for the generator

For a point-norm continuous real action on a possibly nonunital C⋆-algebra, Gaussian smearing
commutes with the infinitesimal generator on its domain. Consequently the smearings of a domain
element converge to it together with their generator values. Thus the entire analytic subalgebra
is a core in the sense of `LinearPMap.HasCore`: closing the restriction of the generator to
this subalgebra recovers the full generator.

This graph approximation allows identities involving the generator to be extended from entire
analytic elements to its whole domain. It is stronger than norm density of analytic elements.
No unitality or countability assumption is needed.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.5.3, for Gaussian approximation by entire analytic elements.
-/

public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] (α : CStarAction (Multiplicative ℝ) A)

/-- Gaussian smearing commutes with the generator on its domain. -/
@[simp]
theorem generator_gaussianSmear (c : ℝ) (a : α.generator.domain) :
    α.generator ⟨α.gaussianSmear c a,
      (α.isEntireAnalytic_gaussianSmear c a).mem_generator_domain⟩ =
      α.gaussianSmear c (α.generator a) := by
  let D := α.toStronglyContinuousGroup.toSemigroup.complexGenerator
    α.toStronglyContinuousGroup_isComplexLinear
  have hD : α.generator ≤ D := le_of_eq α.generator_def
  obtain ⟨hm, heq⟩ := α.toStronglyContinuousGroup.toSemigroup.complexGenerator_commute
    α.toStronglyContinuousGroup_isComplexLinear (α.gaussianSmearCLM c)
      (α.toSemigroup_gaussianSmearCLM c) ⟨a, hD.1 a.property⟩
  simp only [gaussianSmearCLM_apply] at hm heq
  calc
    α.generator ⟨α.gaussianSmear c a,
        (α.isEntireAnalytic_gaussianSmear c a).mem_generator_domain⟩ =
        D ⟨α.gaussianSmear c a, hm⟩ := hD.2 rfl
    _ = α.gaussianSmear c (D ⟨a, hD.1 a.property⟩) := heq
    _ = α.gaussianSmear c (α.generator a) :=
      congrArg (α.gaussianSmear c) (hD.2 (x := a) rfl).symm

/-- The Gaussian smearings of a domain element converge in the graph of the generator. -/
theorem tendsto_gaussianSmear_graph (a : α.generator.domain) :
    Tendsto (fun c : ℝ => (α.gaussianSmear c a,
      α.generator ⟨α.gaussianSmear c a,
        (α.isEntireAnalytic_gaussianSmear c a).mem_generator_domain⟩))
      atTop (𝓝 ((a : A), α.generator a)) := by
  simp only [α.generator_gaussianSmear]
  exact (α.tendsto_gaussianSmear a).prodMk_nhds (α.tendsto_gaussianSmear (α.generator a))

/-- The entire analytic subalgebra is a core for the closed infinitesimal generator. -/
theorem generator_hasCore_entireAnalytic :
    α.generator.HasCore α.entireAnalytic.toSubmodule := by
  refine ⟨fun a ha => (mem_entireAnalytic.mp ha).mem_generator_domain, ?_⟩
  have hle : α.generator.domRestrict α.entireAnalytic.toSubmodule ≤ α.generator :=
    LinearPMap.domRestrict_le
  have hclosable := α.isClosed_generator.isClosable.leIsClosable hle
  apply LinearPMap.eq_of_eq_graph
  rw [← hclosable.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle)
      α.isClosed_generator
  · intro p hp
    obtain ⟨a, rfl⟩ := (α.generator.mem_graph_iff').mp hp
    apply mem_closure_of_tendsto (α.tendsto_gaussianSmear_graph a)
    refine .of_forall fun c => ?_
    let b : (α.generator.domRestrict α.entireAnalytic.toSubmodule).domain :=
      ⟨α.gaussianSmear c a, mem_entireAnalytic.mpr (α.isEntireAnalytic_gaussianSmear c a),
        (α.isEntireAnalytic_gaussianSmear c a).mem_generator_domain⟩
    exact (α.generator.domRestrict α.entireAnalytic.toSubmodule).mem_graph_iff'.mpr
      ⟨b, Prod.ext rfl (LinearPMap.domRestrict_apply rfl)⟩

end TauCeti.CStarAction
