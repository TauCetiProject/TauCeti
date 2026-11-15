/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# The complex normal quotient

The derivative of a pseudoholomorphic map has invariant image. Thus its actual normal
quotient inherits an almost complex structure from the range-quotient construction
`IsComplexLinearMap.quotientRange`.

No complement, metric or integrability assumption on the ambient structure is used. The
construction applies even without immersivity; for an immersion the quotient is the normal
fiber. It does not construct a global normal bundle.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1.
-/

public section

noncomputable section

namespace TauCeti

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The almost complex structure on the actual normal quotient of a pseudoholomorphic map. -/
def normalComplexStructure (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (u : U → V) (x : U) (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    AlmostComplexStructure (V ⧸ (fderiv ℝ u x).toLinearMap.range) :=
  hu.quotientRange

/-- The normal complex structure is the range-quotient structure of the derivative. -/
theorem normalComplexStructure_def (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    normalComplexStructure j J u x hu = hu.quotientRange := (rfl)

/-- Applying the normal complex structure is applying `J` to any ambient lift. -/
@[simp]
theorem normalComplexStructure_mk (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) (v : V) :
    normalComplexStructure j J u x hu (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (J v) := by
  simp only [normalComplexStructure_def, IsComplexLinearMap.quotientRange_mk]

/-- The projection to the normal quotient is complex-linear. -/
@[simp]
theorem isComplexLinearMap_normalComplexStructure_mkQ (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    IsComplexLinearMap J (normalComplexStructure j J u x hu)
      (fderiv ℝ u x).toLinearMap.range.mkQ := by
  rw [normalComplexStructure_def]
  exact hu.isComplexLinearMap_quotientRange_mkQ

end TauCeti
