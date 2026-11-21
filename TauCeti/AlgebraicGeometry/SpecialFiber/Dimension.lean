/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.AlgebraicGeometry.SpecialFiber.Components
public import TauCeti.AlgebraicGeometry.SpecialFiber.Subscheme

/-!
# The components of the special fibre are curves

Let `R` be a local ring and let `X → Spec R` be a scheme over `R`. The closure of a point of the
special fibre, with its reduced structure, is a closed subscheme of the special fibre, hence a
scheme over the residue field `κ` of `R` (`TauCeti.subschemeOverResidueField`). If all points of
`X` have codimension at most `d + 1`, then the closure of a point of the special fibre which is
not the generic point of an irreducible component of `X` has relative dimension at most `d` over
`κ`. For a regular model of a curve, with `d = 1`, the irreducible components of the special
fibre are therefore curves over the residue field.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton`:
  the closure of a non-generic point of the special fibre has relative dimension at most `d` over
  the residue field when all points of `X` have codimension at most `d + 1`.
-/

public section

open AlgebraicGeometry IsLocalRing Order TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- **The components of the special fibre are curves.** If all points of `X` have codimension at
most `d + 1`, then the closure of a point of the special fibre which is not a generic point of an
irreducible component of `X`, with its reduced structure, has relative dimension at most `d` over
the residue field. For a regular model of a curve, the components of the special fibre are
codimension-one points and `d = 1`. -/
theorem relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton {d : ℕ}
    (hX : ∀ x : X, coheight x ≤ d + 1) {η : X} (hmax : ¬IsMax η)
    (hη : toBase η = closedPoint R) :
    letI := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hη)
    TauCeti.AlgebraicGeometry.RelativeDimensionLE d
      ((vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subscheme ↘
        Spec (.of (ResidueField R))) := by
  rw [relativeDimensionLE_iff_of_field,
    ← topologicalKrullDim_range_of_isPreimmersion
      (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι,
    IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
  exact topologicalKrullDim_closure_singleton_le_of_not_isMax hX hmax

end AlgebraicGeometry.Scheme.Hom
