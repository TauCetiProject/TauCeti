/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction

/-!
# Endomorphisms of the left regular representation

On the monoid algebra `k[G]`, a monoid element `g` acts in the left regular representation as
left multiplication by the monomial `single g 1`. Consequently every endomorphism of the left
regular representation, as an intertwining map, is right multiplication by its value at `1`:
this is the intertwining-map form of `Rep.leftRegularHomEquiv_symm_apply`.

## Main results

* `Representation.leftRegular_apply_eq_single_mul`: the left regular action of `g` is left
  multiplication by `single g 1`.
* `Representation.IntertwiningMap.apply_eq_mul_apply_single_one`: an endomorphism of the left
  regular representation is right multiplication by its value at `1`.
-/

public section

namespace Representation

/-- A monoid element acts on the regular representation by left multiplication with the
corresponding basis element: the case `c = 1` of `TauCeti.single_mul_eq_smul_ofMulAction`,
oriented to rewrite the action. -/
theorem leftRegular_apply_eq_single_mul {k G : Type*} [CommSemiring k] [Monoid G] (g : G)
    (x : MonoidAlgebra k G) : leftRegular k G g x = MonoidAlgebra.single g 1 * x := by
  rw [TauCeti.single_mul_eq_smul_ofMulAction, one_smul]

/-- **An endomorphism of the regular representation is right multiplication** by its value at
`1`: the intertwining-map form of `Rep.leftRegularHomEquiv_symm_apply`. -/
theorem IntertwiningMap.apply_eq_mul_apply_single_one {k G : Type*} [CommRing k] [Monoid G]
    (f : (leftRegular k G).IntertwiningMap (leftRegular k G)) (x : MonoidAlgebra k G) :
    f x = x * f (MonoidAlgebra.single 1 1) := by
  have h := Rep.leftRegularHomEquiv_symm_apply
    (Rep.leftRegularHomEquiv (Rep.leftRegular k G) (Rep.ofHom f)) x
  rw [LinearEquiv.symm_apply_apply] at h
  simpa [Rep.homEquiv] using h

end Representation
