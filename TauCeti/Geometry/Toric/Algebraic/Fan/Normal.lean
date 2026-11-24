/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import TauCeti.Geometry.Toric.Algebraic.Normal

/-!
# Normality of toric schemes of finite fans

The toric scheme `Φ.algebraicRealization` of any finite fan `Φ` is covered by the open affine toric
charts `affineToricScheme Φ.lattice σ` of the cones of `Φ`
(`TauCeti.Toric.Fan.affineToricOpenCover`). Since every affine toric chart is normal
(`TauCeti.Toric.isNormalScheme_affineToricScheme`) and normality is local on open covers,
`Φ.algebraicRealization` is a normal scheme even when the cones of `Φ` are singular.

## Main declarations

* `TauCeti.Toric.Fan.isNormalScheme_algebraicRealization`: the toric scheme of any finite fan is
  normal.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1, Proposition (p. 29).
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.1.19.
-/

public section

open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- Every toric scheme associated to a finite fan is normal, regardless of whether its cones are
regular. -/
instance isNormalScheme_algebraicRealization (Φ : Fan i) :
    IsNormalScheme Φ.algebraicRealization :=
  (isNormalScheme_iff_openCover Φ.affineToricOpenCover).mpr fun σ ↦
    isNormalScheme_affineToricScheme Φ.lattice σ.val

end TauCeti.Toric.Fan
