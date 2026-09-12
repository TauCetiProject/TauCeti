/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Basic

/-!
# The tautological point of `1 − π`

The tautological point is additive on morphisms, and the identity's is the generic point, so the
tautological point of `1 − π_q` is the generic point minus that of Frobenius.

## Main results

* `TauCeti.Isogeny.tautologicalPoint_oneSubFrobeniusIsogeny`: the tautological point of
  `1 − π_q` is `g − π_q(g)`.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

-- Not `@[simp]`: `tautologicalPoint_eq_map_genericPoint` already rewrites this left-hand side to
-- `Point.map (oneSubFrobeniusIsogeny W).fieldPullback (genericPoint W)`, so the annotation puts
-- the lemma out of simp-normal form.
/-- **The tautological point of `1 − π_q` is the generic point minus that of Frobenius.** -/
theorem tautologicalPoint_oneSubFrobeniusIsogeny :
    (oneSubFrobeniusIsogeny W).pullback.tautologicalPoint =
      genericPoint W - (frobeniusIsogeny W).pullback.tautologicalPoint := by
  rw [← Hom.tautologicalPoint_ofIsogeny, ofIsogeny_oneSubFrobeniusIsogeny]
  simp [Hom.one_def, Hom.id_def]

end TauCeti.Isogeny

end
