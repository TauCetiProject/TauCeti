/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint

/-!
# Translation moves the tautological point of Frobenius by the translating point

Translating by a rational point `P` sends the generic point `g` to `g + P`. The tautological point
of the Frobenius isogeny is `g` pushed along the `q`-power map, and that map commutes with
translation and fixes `P`, whose coordinates lie in the base field. So the tautological point of
Frobenius moves by `P` as well.

## Main results

* `TauCeti.Isogeny.map_translation_tautologicalPoint_frobeniusIsogeny`: translation by `P` adds
  `P` to the tautological point of Frobenius.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- **Translation by a rational point adds that point to the tautological point of Frobenius**,
exactly as it does to the generic point. -/
theorem map_translation_tautologicalPoint_frobeniusIsogeny (P : (W⁄F).toAffine.Point) :
    Point.map (translation W P).toAlgHom (frobeniusIsogeny W).pullback.tautologicalPoint =
      (frobeniusIsogeny W).pullback.tautologicalPoint +
        Point.baseChange (W' := W) F W.FunctionField P := by
  rw [tautologicalPoint_eq_map_genericPoint, Point.map_map,
    AlgHom.comp_fieldPullback_frobeniusIsogeny, ← Point.map_map]
  simp [map_translation_genericPoint, translatedGenericPoint_def, Point.map_baseChange]

end TauCeti.Isogeny

end
