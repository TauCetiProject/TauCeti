/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add

/-!
# The isogeny `1 − π`

For an elliptic curve `W` over a finite field `F`, the difference of the identity and the Frobenius
isogeny `π` in the endomorphism carrier `Hom W W` is nonzero — the two have different degrees, by
`TauCeti.Isogeny.frobeniusIsogeny_ne_id` — and so is an isogeny `W → W`. Its kernel is the group
of `F`-rational points, and its degree is the number of them; this file provides the isogeny itself.

## Main definitions

* `TauCeti.Isogeny.oneSubFrobeniusIsogeny`: the isogeny `1 − π`.

## Main results

* `TauCeti.Isogeny.id_ne_ofIsogeny_frobeniusIsogeny`: `π` is not the identity in `Hom W W`.
* `TauCeti.Isogeny.ofIsogeny_oneSubFrobeniusIsogeny`: in `Hom W W`, the isogeny `1 − π` is
  `1 − π`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.
-/

public section

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F)

/-- **`π` is not the identity of the endomorphism carrier**, stated in the form `simp` normalises
`1 - π = 0` to. -/
@[simp]
theorem id_ne_ofIsogeny_frobeniusIsogeny : Hom.id W ≠ Hom.ofIsogeny (frobeniusIsogeny W) :=
  fun h ↦ frobeniusIsogeny_ne_id W
    (Hom.ofIsogeny_injective (by rw [← Hom.id_def]; exact h.symm))

variable [W.IsElliptic]

/-- **The isogeny `1 − π`**: the difference of the identity and the Frobenius isogeny. -/
noncomputable def oneSubFrobeniusIsogeny : Isogeny W W :=
  have hne : (1 : Hom W W) ≠ Hom.ofIsogeny (frobeniusIsogeny W) := by
    rw [Hom.one_def]
    exact id_ne_ofIsogeny_frobeniusIsogeny W
  Hom.toIsogeny (sub_ne_zero.2 hne)

/-- **`1 − π` in the endomorphism carrier**: the isogeny `oneSubFrobeniusIsogeny` is the
difference of `1` and the Frobenius isogeny in `Hom W W`. -/
@[simp]
theorem ofIsogeny_oneSubFrobeniusIsogeny :
    Hom.ofIsogeny (oneSubFrobeniusIsogeny W) = 1 - Hom.ofIsogeny (frobeniusIsogeny W) :=
  Hom.ofIsogeny_toIsogeny _

end TauCeti.Isogeny

end
