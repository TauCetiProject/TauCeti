/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Space
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.SumGenerators

/-!
# Root-space membership of the split type-B generators

The standard positive and negative short-root, difference-root, and positive and negative sum-root
families belong to the root spaces of their coordinate weights for the split diagonal Cartan.
These statements hold over any commutative ring; they do not claim that the generators exhaust
each root space.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The standard positive short-root generator belongs to its coordinate root space. -/
theorem typeBShortRootGenerator_mem_rootSpace (i : ι) :
    typeBShortRootGenerator (K := K) i ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι) (typeBEpsilon i) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_shortRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard negative short-root generator belongs to its coordinate root space. -/
theorem typeBShortNegativeRootGenerator_mem_rootSpace (i : ι) :
    typeBShortNegativeRootGenerator (K := K) i ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι) (-typeBEpsilon i) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_shortNegativeRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard difference-root generator belongs to its coordinate root space. -/
theorem typeBDifferenceRootGenerator_mem_rootSpace (i : ι) (j : ι) (hij : i ≠ j) :
    typeBDifferenceRootGenerator (K := K) i j hij ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (typeBEpsilon (K := K) i - typeBEpsilon (K := K) j) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_differenceRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard positive sum-root generator belongs to its coordinate root space. -/
theorem typeBSumRootGenerator_mem_rootSpace (i : ι) (j : ι) :
    typeBSumRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (typeBEpsilon (K := K) i + typeBEpsilon (K := K) j) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_sumRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard negative sum-root generator belongs to its coordinate root space. -/
theorem typeBSumNegativeRootGenerator_mem_rootSpace (i : ι) (j : ι) :
    typeBSumNegativeRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (-(typeBEpsilon (K := K) i + typeBEpsilon (K := K) j)) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_sumNegativeRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

end TauCeti
