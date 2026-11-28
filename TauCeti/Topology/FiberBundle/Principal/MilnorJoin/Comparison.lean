/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Bundle

/-!
# Comparison from the weak simplicial classifying space to Milnor's strong model

This module constructs the canonical continuous comparison map
`TauCeti.weakToMilnorClassifyingSpace G : C(classifyingSpace G, MilnorClassifyingSpace G)`
descending from `TauCeti.weakToMilnorTotalSpace G` on the total spaces, proves its orbit-projection
and base-point formulas, and establishes naturality under continuous group homomorphisms.

## Main definitions and results

* `TauCeti.weakToMilnorClassifyingSpace`: continuous map comparing the weak-topology classifying
  space to the strong-topology `MilnorClassifyingSpace G`.
* `TauCeti.weakToMilnorClassifyingSpace_proj`, `TauCeti.weakToMilnorClassifyingSpace_basepoint`:
  compatibility with the orbit projection and base point.
* `ContinuousMonoidHom.milnorClassifyingSpaceMap_comp_weakToMilnorClassifyingSpace`: naturality
  square with `MonoidHom.classifyingSpaceMap`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. (2) 63 (1956), 430–436, §§2–3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, §14.4.3.
-/

public section

noncomputable section

open TauCeti

universe u v

namespace TauCeti

/-- Continuous comparison map `classifyingSpace G → MilnorClassifyingSpace G` induced by
`weakToMilnorTotalSpace G`. -/
def weakToMilnorClassifyingSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(classifyingSpace G, MilnorClassifyingSpace G) :=
  classifyingSpaceLift
    ⟨milnorClassifyingSpaceProj G ∘ weakToMilnorTotalSpace G,
      (continuous_milnorClassifyingSpaceProj G).comp (weakToMilnorTotalSpace G).continuous⟩
    fun g x ↦ by
      rw [ContinuousMap.coe_mk, Function.comp_apply, weakToMilnorTotalSpace_smul]
      exact milnorClassifyingSpaceProj_smul _ _

/-- Applying `weakToMilnorClassifyingSpace G` on a weak orbit representative equals the strong
orbit of `weakToMilnorTotalSpace G x`. -/
@[simp] theorem weakToMilnorClassifyingSpace_proj {G : Type u} [Group G] [TopologicalSpace G]
    (x : universalGSpace G) :
    weakToMilnorClassifyingSpace G (classifyingSpaceProj G x) =
      milnorClassifyingSpaceProj G (weakToMilnorTotalSpace G x) :=
  classifyingSpaceLift_apply _ _ x

/-- `weakToMilnorClassifyingSpace G` preserves the distinguished base point. -/
@[simp] theorem weakToMilnorClassifyingSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorClassifyingSpace G (classifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint G := by
  rw [← classifyingSpaceProj_universalGSpaceBasepoint, weakToMilnorClassifyingSpace_proj,
    weakToMilnorTotalSpace_basepoint, milnorClassifyingSpaceProj_basepoint]

end TauCeti

namespace ContinuousMonoidHom

open TauCeti

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- **Naturality of `weakToMilnorClassifyingSpace`** with respect to continuous group
homomorphisms. -/
theorem milnorClassifyingSpaceMap_comp_weakToMilnorClassifyingSpace (φ : G →ₜ* H) :
    φ.milnorClassifyingSpaceMap.comp (weakToMilnorClassifyingSpace G) =
      (weakToMilnorClassifyingSpace H).comp φ.toMonoidHom.classifyingSpaceMap := by
  apply ContinuousMap.ext
  intro b
  obtain ⟨x, rfl⟩ := classifyingSpaceProj_surjective G b
  simp only [ContinuousMap.comp_apply, weakToMilnorClassifyingSpace_proj,
    milnorClassifyingSpaceMap_proj, MonoidHom.classifyingSpaceMap_proj]
  exact congrArg (milnorClassifyingSpaceProj H)
    (congrArg (· x) φ.milnorTotalSpaceMap_comp_weakToMilnorTotalSpace)

end ContinuousMonoidHom
