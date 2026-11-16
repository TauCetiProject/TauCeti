/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Topology.VectorBundle.Complex.Structure

/-!
# The tangent bundle of an almost complex manifold as a complex vector bundle

An almost complex structure `J` of any regularity `n` (in particular a continuous one) on a manifold
`M` modelled on a real normed space `E` is a continuous complex structure on the tangent bundle
(`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`); a smooth almost complex
structure `J` is covered through `J.toContMDiff n`. Hence, when `E` is finite-dimensional, the
tangent spaces, with `J` as multiplication by `i`, form a complex vector bundle
`J.toContinuousComplexStructure.Fiber` over `M`, with model fibre any finite-dimensional complex
normed space `G` with `finrank ℝ E = 2 * finrank ℂ G`
(`TauCeti.Bundle.ContinuousComplexStructure.vectorPrebundle`), and its total space is the tangent
bundle (`TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph`).

For a symplectic manifold with a compatible almost complex structure this is the complex vector
bundle `(TM, J)` whose first Chern class is the first Chern class of `M`; its pairing with spheres
is the Chern number entering the grading of capped Hamiltonian Floer theory.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 2.1.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ContMDiffAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ∞}

/-- An almost complex structure of any regularity, as a continuous complex structure on the tangent
bundle. -/
def toContinuousComplexStructure (J : ContMDiffAlmostComplexStructure I n M) :
    Bundle.ContinuousComplexStructure E (TangentSpace I : M → Type _) where
  toFun := J.toEndomorphism
  comp_self := J.square_neg
  continuous := J.toEndomorphism.contMDiff.continuous

@[simp]
theorem toContinuousComplexStructure_apply (J : ContMDiffAlmostComplexStructure I n M) (x : M)
    (v : TangentSpace I x) : J.toContinuousComplexStructure x v = J x v := (rfl)

/-- The pointwise almost complex structures of `J.toContinuousComplexStructure`, which give the
complex structures of its fibres, are those of `J`. -/
@[simp]
theorem toContinuousComplexStructure_almostComplexStructureAt
    (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    J.toContinuousComplexStructure.almostComplexStructureAt x = J.almostComplexStructureAt x := by
  ext v
  rw [Bundle.ContinuousComplexStructure.almostComplexStructureAt_apply,
    toContinuousComplexStructure_apply, almostComplexStructureAt_apply]

end TauCeti.ContMDiffAlmostComplexStructure
