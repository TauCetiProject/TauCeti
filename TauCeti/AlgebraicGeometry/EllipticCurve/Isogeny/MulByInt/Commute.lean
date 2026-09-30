/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom

/-!
# Separable isogenies commute with multiplication

A separable isogeny over a separably closed field commutes with every nonzero multiplication
isogeny. This is the isogeny-level consequence of the `ℤ`-linearity of composition in the inner
morphism proved in `Isogeny/Hom/PointMap.lean`.

## Main results

* `TauCeti.Isogeny.comp_mulByIntIsogenyOfNeZero`: `φ ∘ [n] = [n] ∘ φ` for a separable
  isogeny `φ` over a separably closed field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.8.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [IsSepClosed F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **A separable isogeny commutes with multiplication by `n`** over a separably closed field:
`φ ∘ [n] = [n] ∘ φ` (Silverman III.4.8). -/
theorem comp_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    φ.comp (mulByIntIsogenyOfNeZero W₁ hn) = (mulByIntIsogenyOfNeZero W₂ hn).comp φ :=
  Hom.ofIsogeny_injective <| by
    simp only [← Hom.ofIsogeny_comp_ofIsogeny, ofIsogeny_mulByIntIsogeny,
      Hom.ofIsogeny_comp_zsmul, Hom.zsmul_comp, Hom.comp_id, Hom.id_comp]

end TauCeti.Isogeny

end
