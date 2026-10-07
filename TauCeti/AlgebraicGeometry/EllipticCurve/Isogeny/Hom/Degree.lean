/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom

/-!
# Elementary values of the polarised degree

The degree on morphisms of elliptic curves is extended by `degree 0 = 0` and is homogeneous of
degree two. Mathlib's generic `QuadraticMap.polar` therefore gives the expression

    polar degree f g = deg (f + g) - deg f - deg g.

This file records the values at zero and on the diagonal. Bilinearity is the substantive isogeny
theorem; the separable case is proved in `Isogeny/Dual/Degree.lean` from additivity of the dual.

## Main results

* `TauCeti.Isogeny.Hom.polar_degree_zero_left` and
  `TauCeti.Isogeny.Hom.polar_degree_zero_right`: zero is orthogonal to every morphism.
* `TauCeti.Isogeny.Hom.polar_degree_self`: the diagonal is twice the degree.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.3.
-/

public section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₂.IsElliptic]

/-- The degree polarisation vanishes when its left argument is zero. -/
@[simp]
theorem polar_degree_zero_left (f : Hom W₁ W₂) :
    QuadraticMap.polar (fun g : Hom W₁ W₂ ↦ (g.degree : ℤ)) 0 f = 0 := by
  rw [QuadraticMap.polar, zero_add, degree_zero]
  omega

/-- The degree polarisation vanishes when its right argument is zero. -/
@[simp]
theorem polar_degree_zero_right (f : Hom W₁ W₂) :
    QuadraticMap.polar (fun g : Hom W₁ W₂ ↦ (g.degree : ℤ)) f 0 = 0 := by
  rw [QuadraticMap.polar_comm, polar_degree_zero_left]

/-- On the diagonal, the degree polarisation is twice the degree. -/
@[simp]
theorem polar_degree_self (f : Hom W₁ W₂) :
    QuadraticMap.polar (fun g : Hom W₁ W₂ ↦ (g.degree : ℤ)) f f = 2 * f.degree := by
  rw [QuadraticMap.polar, ← two_nsmul f, degree_nsmul]
  push_cast
  ring

end TauCeti.Isogeny.Hom

end
