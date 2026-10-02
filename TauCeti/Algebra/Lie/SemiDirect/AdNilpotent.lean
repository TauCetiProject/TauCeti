/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.SemiDirect.Basic

/-!
# Adjoint nilpotence in a split ideal extension

The projection from a semidirect sum `I ⋊⁅ψ⁆ H` onto `H` is a surjective Lie homomorphism.
Consequently, if an element of the semidirect sum has nilpotent adjoint action, its right
component has nilpotent adjoint action on `H`.

The internal form says that, for a Lie ideal `I` and a complementary Lie subalgebra `H` of `L`,
nilpotence of `ad (i + h)` on `L` implies nilpotence of `ad h` on `H`. In a Levi decomposition,
this extracts the adjoint-nilpotent semisimple component of an adjoint-nilpotent element. The
argument only uses the split ideal extension; neither semisimplicity nor solvability, finite
dimension, or characteristic zero is required.

## Main results

* `LieAlgebra.SemiDirectSum.isNilpotent_ad_right`: adjoint nilpotence passes to the right
  component of a semidirect sum.
* `LieIdeal.isNilpotent_ad_right_of_isCompl`: the corresponding result for an internal split
  ideal extension, stated on a sum of elements in the two complementary factors.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966),
  531–533, for the use of this implication on the semisimple component.
-/

public section

namespace TauCeti

variable {R I H : Type*} [CommRing R] [LieRing I] [LieAlgebra R I]
  [LieRing H] [LieAlgebra R H] {ψ : H →ₗ⁅R⁆ LieDerivation R I I}

/-- The right component of an adjoint-nilpotent element of a semidirect sum is
adjoint-nilpotent in the right factor. -/
theorem _root_.LieAlgebra.SemiDirectSum.isNilpotent_ad_right (x : I ⋊⁅ψ⁆ H)
    (hx : IsNilpotent (LieAlgebra.ad R (I ⋊⁅ψ⁆ H) x)) :
    IsNilpotent (LieAlgebra.ad R H x.right) := by
  simpa only [LieAlgebra.SemiDirectSum.projr_mk] using
    (LieAlgebra.SemiDirectSum.projr ψ).isNilpotent_ad_of_surjective
    (LieAlgebra.SemiDirectSum.projr_surjective ψ) hx

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- For an ideal and a complementary Lie subalgebra, adjoint nilpotence of the sum of two
components implies adjoint nilpotence of the subalgebra component on that subalgebra.

Taking the ideal to be the solvable radical and the subalgebra to be a Levi complement gives
the projection step in the nilpotence argument for the semisimple component. -/
theorem _root_.LieIdeal.isNilpotent_ad_right_of_isCompl (J : LieIdeal R L)
    (S : LieSubalgebra R L) (h : IsCompl J.toSubmodule S.toSubmodule) (i : J) (s : S)
    (hx : IsNilpotent (LieAlgebra.ad R L ((i : L) + (s : L)))) :
    IsNilpotent (LieAlgebra.ad R S s) := by
  let e := J.semiDirectSumEquiv S h
  have he : IsNilpotent
      (LieAlgebra.ad R (↥J ⋊⁅(J.ad).comp S.incl⁆ ↥S) (e.symm ((i : L) + (s : L)))) :=
    e.symm.toLieHom.isNilpotent_ad_of_surjective e.symm.surjective hx
  have hs : (e.symm ((i : L) + (s : L))).right = s := by
    simp [e]
  simpa only [hs] using
    LieAlgebra.SemiDirectSum.isNilpotent_ad_right _ he

end TauCeti
