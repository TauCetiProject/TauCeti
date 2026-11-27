/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Almost-complex obstructions for real-codimension-one immersions

For any `C^n` (`n ≠ 0`) real immersion `f : H → M` of real codimension one
(`Module.finrank ℝ EH + 1 = Module.finrank ℝ EM`), real-dimension parity obstructs almost complex
and compatible complex structures on both the tangent image and the normal fibres:

* `Manifold.IsImmersion.not_forall_almostComplexStructure_mem_tangentRange`: no pointwise almost
  complex structure `Jx` on `TangentSpace J (f x)` preserves `hf.tangentRange x hn`, since `Jx`
  forces both the ambient tangent space and any `Jx`-invariant subspace to have even real dimension.
* `Manifold.IsImmersion.isEmpty_almostComplexStructure_normalSpace`: each normal fibre
  `hf.NormalSpace x hn` has real dimension `1` and therefore admits no almost complex structure.
* `Manifold.IsImmersion.not_exists_module_complex_isScalarTower_normalSpace`: consequently, no
  normal fibre `hf.NormalSpace x hn` admits a `ℂ`-module structure compatible with its `ℝ`-module
  structure.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.1.
* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, AMS, 2012,
  Section 2.1.
-/

public noncomputable section

open TauCeti
open scoped Manifold ContDiff

namespace Manifold.IsImmersion

variable {EH EM HH HM H M : Type*}
  [NormedAddCommGroup EH] [NormedSpace ℝ EH] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HH] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EH HH} {J : ModelWithCorners ℝ EM HM}
  [TopologicalSpace H] [ChartedSpace HH H] [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {f : H → M} (hf : IsImmersion I J n f) (hn : n ≠ 0)
  (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H)

include hcodim

/-- **A real-codimension-one immersion never has `J`-invariant tangent spaces.** For any `C^n`
(`n ≠ 0`) real immersion `f : H → M` of real codimension one (`finrank ℝ EH + 1 = finrank ℝ EM`)
and any almost complex structure `Jx` on the ambient tangent space `TangentSpace J (f x)`, the
tangent image `hf.tangentRange x hn` is not preserved by `Jx`. -/
theorem not_forall_almostComplexStructure_mem_tangentRange
    (Jx : AlmostComplexStructure (TangentSpace J (f x))) :
    ¬ ∀ v ∈ hf.tangentRange x hn, Jx v ∈ hf.tangentRange x hn := by
  intro hinv
  have hEH : Even (Module.finrank ℝ EH) := by
    rw [← finrank_tangentSpace (I := I) (x := x),
      ← LinearMap.finrank_range_of_inj (hf.mfderiv_injective hn x)]
    exact Jx.even_finrank_of_forall_mem hinv
  have hEM : Even (Module.finrank ℝ EM) := by
    rw [← finrank_tangentSpace (I := J) (x := f x)]; exact Jx.even_finrank_real
  obtain ⟨a, ha⟩ := hEH; obtain ⟨b, hb⟩ := hEM; omega

/-- **The normal space of a real-codimension-one immersion admits no almost complex structure.** For
any `C^n` (`n ≠ 0`) real immersion `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`), each normal fibre `hf.NormalSpace x hn` is one-dimensional
over `ℝ` and therefore carries no almost complex structure. -/
theorem isEmpty_almostComplexStructure_normalSpace :
    IsEmpty (AlmostComplexStructure (hf.NormalSpace x hn)) :=
  AlmostComplexStructure.isEmpty_of_odd_finrank
    (hf.finrank_normalSpace_eq_one hn hcodim x ▸ odd_one)

/-- **The normal space of a real-codimension-one immersion admits no compatible `ℂ`-module
structure.** In particular, the quotient normal fibres of a real-smooth hypersurface cannot be given
any complex vector-space structure compatible with their real scalar multiplication. -/
theorem not_exists_module_complex_isScalarTower_normalSpace :
    ¬ ∃ m : Module ℂ (hf.NormalSpace x hn),
      @IsScalarTower ℝ ℂ (hf.NormalSpace x hn) _ m.toSMul _ := by
  rintro ⟨m, hst⟩
  let _ : Module ℂ (hf.NormalSpace x hn) := m
  have _ : IsScalarTower ℝ ℂ (hf.NormalSpace x hn) := hst
  exact (hf.isEmpty_almostComplexStructure_normalSpace hn hcodim x).false
    (AlmostComplexStructure.ofComplexModule (hf.NormalSpace x hn))

end Manifold.IsImmersion
