/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# The Clifford algebras of `Q` and `-Q` over a ring containing a square root of `-1`

There is in general no algebra isomorphism between the Clifford algebras of a quadratic form `Q`
and of its negative; Mathlib's `CliffordAlgebra.evenEquivEvenNeg` only identifies their even
subalgebras. If the coefficient ring contains an element `u` with `u * u = -1`, however, the
vectors `u • ι (-Q) m` satisfy the Clifford relation of `Q`, and `ι Q m ↦ u • ι (-Q) m` extends to
an algebra isomorphism `CliffordAlgebra.equivNeg` of the full Clifford algebras. Over `ℂ`, with
`u = Complex.I`, this is the map `v ↦ i v` from the complexified Clifford algebra of a real form to
that of its negative, which compares the positive-definite and negative-definite (geometric)
sign conventions for Clifford multiplication.

The isomorphism preserves the `ℤ/2`-grading and commutes with the grade involution, reversal and
Clifford conjugation. On the even subalgebra the factors of `u` pair up to `u * u = -1`, so a
bivector `ι Q a * ι Q b` goes to `-(ι (-Q) a * ι (-Q) b)`; this is the sign of
`CliffordAlgebra.evenToNeg`, and `CliffordAlgebra.equivNeg` restricts to that map on even
elements. In particular, the complex isomorphism of `ℂ ⊗ V` restricts on the image of the real
even subalgebra to the scalar extension of `CliffordAlgebra.evenEquivEvenNeg`. For a nonzero real
vector space it is not the scalar extension of any real isomorphism of the full algebras: it sends
a nonzero real generator `ι Q m` to `i • ι (-Q) m`, which is not real. (When the vector space is
zero, both algebras are the scalars and the isomorphism is the identity.)

The target form is a parameter `Q'` with a proof of `Q' = -Q`, as for Mathlib's
`CliffordAlgebra.evenToNeg`. This covers the inverse direction, and the base-changed form
`(-Q).baseChange A`, which is only propositionally equal to `-(Q.baseChange A)`.

## Main results

* `CliffordAlgebra.equivNeg`: the isomorphism `CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q'`,
  `ι Q m ↦ u • ι Q' m`, for `Q' = -Q` and `u * u = -1`.
* `CliffordAlgebra.equivNeg_symm`: its inverse is the same construction for `-u`.
* `CliffordAlgebra.equivNeg_ι_mul_ι`: a bivector `ι Q a * ι Q b` goes to `-(ι Q' a * ι Q' b)`.
* `CliffordAlgebra.equivNeg_coe`: on even elements it is `CliffordAlgebra.evenToNeg`.
* `CliffordAlgebra.map_evenOdd_equivNeg`: it carries `evenOdd Q i` onto `evenOdd Q' i`.
* `CliffordAlgebra.equivNeg_involute`, `CliffordAlgebra.equivNeg_reverse`,
  `CliffordAlgebra.equivNeg_star`: compatibility with the Clifford involutions.
* `CliffordAlgebra.map_equivNeg`: naturality along quadratic isometries.
* `CliffordAlgebra.equivNeg_ofBaseChangeAux`: after extension of scalars to an algebra containing
  `u`, it restricts on real even elements to `CliffordAlgebra.evenEquivEvenNeg`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section General

variable (Q Q' : QuadraticForm R M) (h : Q' = -Q) {u : R} (hu : u * u = -1)

/-- If `u * u = -1`, the Clifford algebras of `Q` and of `Q' = -Q` are isomorphic, by the algebra
map sending a vector `ι Q m` to `u • ι Q' m`; this is `CliffordAlgebra.equivOfIsometry` for the
isometry `m ↦ u • m`. Over `ℂ`, with `u = Complex.I`, this is the map `v ↦ i v` between the
complexified Clifford algebras of a real form and of its negative. -/
def equivNeg : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q' :=
  equivOfIsometry (QuadraticMap.isometryEquivNeg h hu)

/-- `CliffordAlgebra.equivNeg` multiplies each vector by `u`. -/
@[simp]
theorem equivNeg_ι (m : M) : equivNeg Q Q' h hu (ι Q m) = u • ι Q' m :=
  (map_apply_ι _ m).trans <| (congrArg (ι Q') (QuadraticMap.isometryEquivNeg_apply h hu m)).trans
    (map_smul (ι Q') u m)

/-- The inverse of `CliffordAlgebra.equivNeg` multiplies each vector by `-u`. -/
@[simp]
theorem equivNeg_symm_ι (m : M) : (equivNeg Q Q' h hu).symm (ι Q' m) = -(u • ι Q m) :=
  (equivNeg Q Q' h hu).symm_apply_eq.mpr (by simp [smul_smul, hu])

/-- The inverse of `CliffordAlgebra.equivNeg` for `u` is `CliffordAlgebra.equivNeg` for `-u`, in
the opposite direction. -/
theorem equivNeg_symm :
    (equivNeg Q Q' h hu).symm =
      equivNeg Q' Q (by rw [h, neg_neg]) (u := -u) (by rw [neg_mul_neg, hu]) := by
  rw [equivNeg, equivOfIsometry_symm, QuadraticMap.isometryEquivNeg_symm]
  rfl

/-- A bivector `ι Q a * ι Q b` goes to the negative `-(ι Q' a * ι Q' b)` of the corresponding
bivector, since the two factors of `u` multiply to `-1`. -/
theorem equivNeg_ι_mul_ι (a b : M) :
    equivNeg Q Q' h hu (ι Q a * ι Q b) = -(ι Q' a * ι Q' b) := by
  rw [map_mul, equivNeg_ι, equivNeg_ι, smul_mul_smul_comm, hu, neg_one_smul]

/-- On the even subalgebra, `CliffordAlgebra.equivNeg` is Mathlib's `CliffordAlgebra.evenToNeg`;
for `Q' = -Q` this is `CliffordAlgebra.evenEquivEvenNeg` (`CliffordAlgebra.evenEquivEvenNeg_apply`).
In particular it does not depend on the choice of `u` there. -/
@[simp]
theorem equivNeg_coe (x : even Q) :
    equivNeg Q Q' h hu (x : CliffordAlgebra Q) = (evenToNeg Q Q' h x : CliffordAlgebra Q') := by
  have key : (equivNeg Q Q' h hu).toAlgHom.comp (even Q).val =
      (even Q').val.comp (evenToNeg Q Q' h) := by
    ext m₁ m₂ : 4
    simp [equivNeg_ι_mul_ι]
  exact congr($key x)

/-- `CliffordAlgebra.equivNeg` commutes with the grade involution. -/
@[simp]
theorem equivNeg_involute (x : CliffordAlgebra Q) :
    equivNeg Q Q' h hu (involute x) = involute (equivNeg Q Q' h hu x) :=
  map_involute _ x

/-- `CliffordAlgebra.equivNeg` commutes with reversal. -/
@[simp]
theorem equivNeg_reverse (x : CliffordAlgebra Q) :
    equivNeg Q Q' h hu (reverse x) = reverse (equivNeg Q Q' h hu x) :=
  map_reverse _ x

/-- `CliffordAlgebra.equivNeg` commutes with Clifford conjugation. -/
@[simp]
theorem equivNeg_star (x : CliffordAlgebra Q) :
    equivNeg Q Q' h hu (star x) = star (equivNeg Q Q' h hu x) :=
  map_star _ x

/-- `CliffordAlgebra.equivNeg` preserves the `ℤ/2`-grading: it carries `evenOdd Q i` onto
`evenOdd Q' i`. -/
theorem map_evenOdd_equivNeg (i : ZMod 2) :
    (evenOdd Q i).map (equivNeg Q Q' h hu).toLinearMap = evenOdd Q' i :=
  map_evenOdd_equivOfIsometry _ i

variable {Q Q'} in
/-- An element lies in `evenOdd Q' i` after applying `CliffordAlgebra.equivNeg` exactly when it
lies in `evenOdd Q i`. -/
@[simp]
theorem equivNeg_mem_evenOdd_iff {x : CliffordAlgebra Q} {i : ZMod 2} :
    equivNeg Q Q' h hu x ∈ evenOdd Q' i ↔ x ∈ evenOdd Q i :=
  equivOfIsometry_mem_evenOdd_iff _

/-- `CliffordAlgebra.equivNeg` is natural along quadratic isometries: for an isometry `f` from
`Q` to `Q₂`, whose underlying linear map is also an isometry `f'` from `Q'` to `Q₂'`, the
isomorphisms for `Q` and for `Q₂` intertwine the algebra maps induced by `f` and by `f'`. -/
theorem map_equivNeg {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {Q₂ Q₂' : QuadraticForm R M₂}
    (h₂ : Q₂' = -Q₂) (f : Q →qᵢ Q₂) (f' : Q' →qᵢ Q₂') (hf : f'.toLinearMap = f.toLinearMap)
    (x : CliffordAlgebra Q) :
    map f' (equivNeg Q Q' h hu x) = equivNeg Q₂ Q₂' h₂ hu (map f x) := by
  have key : f'.comp (QuadraticMap.isometryEquivNeg h hu).toIsometry =
      (QuadraticMap.isometryEquivNeg h₂ hu).toIsometry.comp f :=
    QuadraticMap.Isometry.ext fun m ↦ by
      simpa using congr($hf (u • m))
  exact (AlgHom.congr_fun (map_comp_map _ _) x).trans <| congr(map $key x).trans
    (AlgHom.congr_fun (map_comp_map _ _) x).symm

end General

section BaseChange

variable {A : Type*} [CommRing A] [Algebra R A] [Invertible (2 : R)]
variable (Q : QuadraticForm R M) {u : A} (hu : u * u = -1)

/-- After extension of scalars to an algebra containing `u` with `u * u = -1`, the isomorphism
`CliffordAlgebra.equivNeg` of the extended Clifford algebras of `Q` and `-Q` restricts on the
image of the even subalgebra to the scalar extension of `CliffordAlgebra.evenEquivEvenNeg`. Over
`ℂ`, this compares `v ↦ i v` with the real even-algebra comparison of `Q` and `-Q`. -/
theorem equivNeg_ofBaseChangeAux (x : even Q) :
    equivNeg (Q.baseChange A) ((-Q).baseChange A) (QuadraticForm.baseChange_neg Q) hu
        (ofBaseChangeAux A Q x) =
      ofBaseChangeAux A (-Q) (evenEquivEvenNeg Q x) := by
  have key : ((equivNeg (Q.baseChange A) ((-Q).baseChange A) (QuadraticForm.baseChange_neg Q)
      hu).toAlgHom.restrictScalars R).comp ((ofBaseChangeAux A Q).comp (even Q).val) =
      (ofBaseChangeAux A (-Q)).comp ((even (-Q)).val.comp (evenEquivEvenNeg Q).toAlgHom) := by
    ext m₁ m₂ : 4
    simp [equivNeg_ι_mul_ι]
  exact congr($key x)

end BaseChange

end CliffordAlgebra
