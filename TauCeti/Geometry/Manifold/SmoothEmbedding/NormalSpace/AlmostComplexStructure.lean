/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Almost-complex obstructions for real-codimension-one embeddings

For any `C^n` (`n ≠ 0`) real smooth embedding `f : H → M` of real codimension one
(`Module.finrank ℝ EH + 1 = Module.finrank ℝ EM`), real-dimension parity obstructs almost complex
and compatible complex structures on both the tangent image and the normal fibres:

* `TauCeti.SmoothEmbedding.not_forall_almostComplexStructure_mem_tangentRange`: no pointwise almost
  complex structure `Jx` on `TangentSpace J (f x)` preserves `f.tangentRange x hn`, since `Jx`
  forces both the ambient tangent space and any `Jx`-invariant subspace to have even real dimension.
* `TauCeti.SmoothEmbedding.isEmpty_almostComplexStructure_normalSpace`: each normal fibre
  `f.NormalSpace x hn` has real dimension `1` and therefore admits no almost complex structure.
* `TauCeti.SmoothEmbedding.not_exists_module_complex_isScalarTower_normalSpace`: consequently, no
  normal fibre `f.NormalSpace x hn` admits a `ℂ`-module structure compatible with its `ℝ`-module
  structure.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.1.
* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, AMS, 2012,
  Section 2.1.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {EH EM HH HM H M : Type*}
  [NormedAddCommGroup EH] [NormedSpace ℝ EH] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HH] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EH HH} {J : ModelWithCorners ℝ EM HM}
  [TopologicalSpace H] [ChartedSpace HH H] [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} (f : SmoothEmbedding I J n H M) (hn : n ≠ 0)
  (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H)

include hcodim

/-- **A real-smooth hypersurface never has `J`-invariant tangent spaces.** For any `C^n` (`n ≠ 0`)
real embedding `f : H → M` of real codimension one (`finrank ℝ EH + 1 = finrank ℝ EM`) and any
almost complex structure `Jx` on the ambient tangent space `TangentSpace J (f x)`, the tangent
image `f.tangentRange x hn` is not preserved by `Jx`. -/
theorem not_forall_almostComplexStructure_mem_tangentRange
    (Jx : AlmostComplexStructure (TangentSpace J (f x))) :
    ¬ ∀ v ∈ f.tangentRange x hn, Jx v ∈ f.tangentRange x hn := by
  intro hinv
  have hEH : Even (Module.finrank ℝ EH) := by
    rw [← TauCeti.finrank_tangentSpace (I := I) (x := x),
      ← LinearMap.finrank_range_of_inj (f.isImmersion.mfderiv_injective hn x)]
    exact Jx.even_finrank_of_forall_mem hinv
  have hEM : Even (Module.finrank ℝ EM) := by
    rw [← TauCeti.finrank_tangentSpace (I := J) (x := f x)]; exact Jx.even_finrank_real
  obtain ⟨a, ha⟩ := hEH; obtain ⟨b, hb⟩ := hEM; omega

/-- **The normal space of a real-smooth hypersurface admits no almost complex structure.** For any
`C^n` (`n ≠ 0`) real embedding `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`), each normal fibre `f.NormalSpace x hn` is one-dimensional over
`ℝ` and therefore carries no almost complex structure. -/
theorem isEmpty_almostComplexStructure_normalSpace :
    IsEmpty (AlmostComplexStructure (f.NormalSpace x hn)) :=
  AlmostComplexStructure.isEmpty_of_odd_finrank
    (f.finrank_normalSpace_eq_one hn hcodim x ▸ odd_one)

/-- **The normal space of a real-smooth hypersurface admits no compatible `ℂ`-module structure.**
In particular, the quotient bundle `f* TM / TH` of a real-smooth hypersurface cannot be given any
complex vector-bundle structure compatible with its real vector-space fibres. -/
theorem not_exists_module_complex_isScalarTower_normalSpace :
    ¬ ∃ m : Module ℂ (f.NormalSpace x hn),
      @IsScalarTower ℝ ℂ (f.NormalSpace x hn) _ m.toSMul _ := by
  rintro ⟨m, hst⟩
  let _ : Module ℂ (f.NormalSpace x hn) := m
  have _ : IsScalarTower ℝ ℂ (f.NormalSpace x hn) := hst
  exact (f.isEmpty_almostComplexStructure_normalSpace hn hcodim x).false
    (AlmostComplexStructure.ofComplexModule (f.NormalSpace x hn))

end TauCeti.SmoothEmbedding
