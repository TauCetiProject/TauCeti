/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Contractible
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

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

Along a continuous map `f` from a contractible paracompact R₁ space, for instance a disc, this
complex vector bundle has a frame: real-linear isomorphisms `G ≃ T_(f y) M`, continuous into the
tangent bundle, carrying multiplication by `i` to `J`
(`TauCeti.ContMDiffAlmostComplexStructure.exists_continuous_frame`).

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


section Frame

variable [FiniteDimensional ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G] {Y : Type*} [TopologicalSpace Y] {f : Y → M}

open Module in
/-- **Complex frames along maps from contractible spaces.** For an almost complex structure `J`
on `M` and a complex normed space `G` of half the real dimension of `M`, along a continuous map
`f` from a contractible paracompact R₁ space there are real-linear isomorphisms
`φ y : G ≃ T_(f y) M`, continuous into the tangent bundle, carrying multiplication by `i` to `J`:
frames of the complex vector bundle `(TM, J)` along `f`. -/
theorem exists_continuous_frame (J : ContMDiffAlmostComplexStructure I n M)
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
    (hf : Continuous f) :
    ∃ φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y),
      Continuous (fun q : Y × G ↦ (⟨f q.1, φ q.1 q.2⟩ : TangentBundle I M)) ∧
      ∀ y v, φ y (Complex.I • v) = J (f y) (φ y v) := by
  have : CompleteSpace G := FiniteDimensional.completeSpace ℂ G
  -- A frame of the complex vector bundle `(TM, J)` along `f`, read as real frames of `TM`.
  set Jc := J.toContinuousComplexStructure
  obtain ⟨ψ, hψ⟩ := _root_.TauCeti.exists_continuous_frame (𝕜 := ℂ) (F := G) (E := Jc.Fiber) hf
  let φ : ∀ y, G ≃L[ℝ] TangentSpace I (f y) := fun y ↦
    ((ψ y).restrictScalars' ℝ).trans (Jc.fiberEquiv (f y))
  have hφ (y : Y) (v : G) : φ y v = Jc.fiberEquiv (f y) (ψ y v) := by
    simp only [φ, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_restrictScalars']
  refine ⟨φ, ((Jc.totalSpaceHomeomorph G).continuous.comp hψ).congr fun q ↦ ?_, fun y v ↦ ?_⟩
  · simp only [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
      hφ]
  · rw [hφ, hφ, map_smul, Bundle.ContinuousComplexStructure.fiberEquiv_I_smul]
    exact J.toContinuousComplexStructure_apply (f y) _

end Frame

end TauCeti.ContMDiffAlmostComplexStructure
