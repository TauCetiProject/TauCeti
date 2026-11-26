/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Preserving
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent

/-!
# The Lie algebra of vector fields preserving a distribution

Let `D` be a distribution on a real manifold `M` modelled on a complete space. The smooth vector
fields of `M` form a real Lie algebra under the Lie bracket of vector fields, the sections
`(TauCeti.LieAlgebroid.tangent I M).Sections` of the tangent Lie algebroid. The smooth vector fields
preserving `D` (`TauCeti.PreservesDistribution`), the infinitesimal automorphisms of `D`, are
closed under addition, real multiples and the Lie bracket
(`TauCeti.PreservesDistribution.mlieBracket`), so they form a Lie subalgebra,
`TauCeti.preservesDistributionLieSubalgebra I D`. For a contact structure these are the contact
vector fields.

## References

* P. Libermann, C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, D. Reidel, 1987,
  Chapter V, Section 13 (infinitesimal automorphisms of a contact structure).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}

variable (I D) in
/-- The **Lie algebra of vector fields preserving a distribution** `D`: the smooth vector fields `X`
whose Lie bracket with every smooth vector field tangent to `D` is tangent to `D`
(`TauCeti.PreservesDistribution`), as a Lie subalgebra of the Lie algebra of smooth vector fields.
For a contact structure `D` these are the contact vector fields. -/
def preservesDistributionLieSubalgebra : LieSubalgebra ℝ (LieAlgebroid.tangent I M).Sections where
  carrier := {X | PreservesDistribution I D ((LieAlgebroid.tangent I M).sectionsEquiv X)}
  add_mem' {X Y} hX hY := by
    have h : ⇑((LieAlgebroid.tangent I M).sectionsEquiv (X + Y)) =
        ⇑((LieAlgebroid.tangent I M).sectionsEquiv X) +
          ⇑((LieAlgebroid.tangent I M).sectionsEquiv Y) := by
      rw [map_add, ContMDiffSection.coe_add]
    have hXY := PreservesDistribution.add hX hY
      ((LieAlgebroid.tangent I M).sectionsEquiv X).mdifferentiable
      ((LieAlgebroid.tangent I M).sectionsEquiv Y).mdifferentiable
    rw [← h] at hXY
    exact hXY
  zero_mem' := by
    have h : ⇑((LieAlgebroid.tangent I M).sectionsEquiv 0) = 0 := by
      rw [map_zero, ContMDiffSection.coe_zero]
    have h0 : PreservesDistribution I D (0 : Π x : M, TangentSpace I x) :=
      preservesDistribution_zero
    rw [← h] at h0
    exact h0
  smul_mem' c X hX := by
    have h : ⇑((LieAlgebroid.tangent I M).sectionsEquiv (c • X)) =
        c • ⇑((LieAlgebroid.tangent I M).sectionsEquiv X) := by
      rw [LinearMapClass.map_smul_of_tower, ContMDiffSection.coe_smul]
    have hcX := PreservesDistribution.const_smul hX c
    rw [← h] at hcX
    exact hcX
  lie_mem' {X Y} hX hY := by
    -- The bracket of the sections is the Lie bracket of the underlying vector fields.
    have h : ⇑((LieAlgebroid.tangent I M).sectionsEquiv ⁅X, Y⁆) =
        mlieBracket I ((LieAlgebroid.tangent I M).sectionsEquiv X)
          ((LieAlgebroid.tangent I M).sectionsEquiv Y) :=
      funext fun x ↦ by rw [LieAlgebroid.sectionsEquiv_lie, LieAlgebroid.tangent_bracket_apply]
    have hXY := PreservesDistribution.mlieBracket hX hY
      ((LieAlgebroid.tangent I M).sectionsEquiv X).contMDiff
      ((LieAlgebroid.tangent I M).sectionsEquiv Y).contMDiff
    rw [← h] at hXY
    exact hXY

/-- A smooth vector field lies in the Lie algebra of vector fields preserving `D` exactly when it
preserves `D`. -/
@[simp]
theorem mem_preservesDistributionLieSubalgebra_iff {X : (LieAlgebroid.tangent I M).Sections} :
    X ∈ preservesDistributionLieSubalgebra I D ↔
      PreservesDistribution I D ((LieAlgebroid.tangent I M).sectionsEquiv X) :=
  Iff.rfl

end TauCeti
