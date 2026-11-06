/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Morphisms.Smooth.CohenMacaulay

/-!
# Tests for Cohen–Macaulay schemes

The spectrum of a field and the affine plane over a field are Cohen–Macaulay, being regular. The
spectrum of an Artinian ring, such as the non-reduced and hence non-regular `k[ε] = k[X] ⧸ (X²)`,
is Cohen–Macaulay because its local rings have dimension zero. The affine plane over such a ring
is smooth over it, so it is again Cohen–Macaulay without being regular.
-/

namespace AlgebraicGeometry.Scheme

universe u

/-- *test_field*: the spectrum of a field is Cohen–Macaulay. -/
example (k : Type u) [Field k] : (Spec (CommRingCat.of k)).IsCohenMacaulay :=
  inferInstance

/-- *test_affinePlane*: the affine plane `Spec k[x, y]` over a field is Cohen–Macaulay. -/
example (k : Type u) [Field k] :
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).IsCohenMacaulay :=
  inferInstance

/-- The spectrum of an Artinian ring is Cohen–Macaulay: its local rings have dimension zero. This
includes non-regular schemes such as `Spec k[ε]`. -/
example (R : CommRingCat.{u}) [IsArtinianRing R] : (Spec R).IsCohenMacaulay :=
  (isCohenMacaulay_Spec_iff R).mpr
    TauCeti.Ring.IsCohenMacaulay.of_krullDimLE_zero

/-- The affine plane over an Artinian ring, such as `k[ε]`, is smooth over a Cohen–Macaulay
scheme and hence Cohen–Macaulay. -/
example (R : CommRingCat.{u}) [IsArtinianRing R] :
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) R))).IsCohenMacaulay :=
  have : (Spec R).IsCohenMacaulay :=
    (isCohenMacaulay_Spec_iff R).mpr TauCeti.Ring.IsCohenMacaulay.of_krullDimLE_zero
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  .of_smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R))))

end AlgebraicGeometry.Scheme
