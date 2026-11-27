/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Basic
import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

/-!
# Point stabilizers in the affine Weyl group

For a crystallographic reduced root pairing `P` with finitely many roots and a base `b` over a
characteristic-zero domain, the Weyl group `P.weylGroup` is finite
(`RootPairing.finite_weylGroup_of_base`) without assuming that the roots span. Combining this with
the linear-part embedding `RootPairing.finite_affinePointStabilizer_of_finite_weylGroup` shows that
every point stabilizer `P.affinePointStabilizer x` in the affine Weyl group is finite.

## Main results

* `RootPairing.finite_affinePointStabilizer_of_base`: point stabilizers in `W_aff` are finite for a
  crystallographic reduced pairing with finitely many roots and a base over a characteristic-zero
  domain (even without requiring the roots to span).
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

/-- For a crystallographic reduced root pairing with finitely many roots and a base `b` over a
characteristic-zero domain, every point stabilizer in `W_aff` is finite; the roots need not
span. -/
theorem finite_affinePointStabilizer_of_base [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) (x : N) :
    Finite (P.affinePointStabilizer x) := by
  let _ : Finite P.weylGroup := P.finite_weylGroup_of_base b
  exact P.finite_affinePointStabilizer_of_finite_weylGroup x

end RootPairing
