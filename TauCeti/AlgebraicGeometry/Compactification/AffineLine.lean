/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# The projective compactification of the affine line

The standard chart `D₊(X₀)` realizes `Spec R[X]` as a schematically dense open subscheme of
`ℙ¹_R` for every commutative ring `R`. Together with the proper structure morphism this gives
`projectiveLine.denseCompactification`, retaining the scheme structure over nonreduced bases.

The infinity-section and boundary geometry are in
`TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine`. This module supplies only the
compactification and the equations identifying its ambient scheme, interior map and proper map.

The construction uses the polynomial chart equivalences of
`TauCeti.AlgebraicGeometry.projectiveLine` and the homogeneous-nonzerodivisor criterion
`AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

/-- The projective line compactifies the affine line over any commutative base ring. -/
-- The selected ambient carrier must reduce to use its two maps without transports.
@[expose, implicit_reducible]
noncomputable def denseCompactification :
    DenseCompactification (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) :=
  ⟨Compactification.ofHom (polynomialChartι R 0) (projectiveLine R ↘ Spec (.of R))
    (polynomialChartι_over R 0), (denseCompactificationProperty_iff _ _).mpr inferInstance⟩

/-- The ambient scheme of the affine-line compactification is the projective line. -/
@[simp]
theorem denseCompactification_Xbar : (denseCompactification R).obj.Xbar = projectiveLine R :=
  (rfl)

/-- The interior map of the affine-line compactification is the zeroth polynomial chart. -/
@[simp]
theorem denseCompactification_j :
    (denseCompactification R).obj.j = polynomialChartι R 0 :=
  (rfl)

/-- The proper map of the affine-line compactification is the projective structure map. -/
@[simp]
theorem denseCompactification_p :
    (denseCompactification R).obj.p = (projectiveLine R ↘ Spec (.of R)) :=
  (rfl)

end TauCeti.AlgebraicGeometry.projectiveLine
