/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.GroupTheory.Coxeter.Hecke.Basis

/-!
# The basis theorem for the type-A Hecke algebra

Let `cs` be a Coxeter system of type `A_(n-1)` on a group `W`. The elements `T_w`, `w : W`, of the
Hecke algebra `TypeAHeckeAlgebra R q n` (`TauCeti.TypeAHeckeAlgebra.Tw`) span it; this file proves
that they are linearly independent over every commutative ring `R` and every unit `q`, so that they
form a basis `TauCeti.TypeAHeckeAlgebra.basisTw`.

The statements are transported from the basis theorem for the Hecke algebra of a Coxeter system
(`TauCeti.GroupTheory.Coxeter.Hecke.Basis`) along the isomorphism
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` with the Hecke algebra of the type-A Coxeter
matrix and parameter `q - q⁻¹`, which matches the elements `T_w` of the two algebras. In
particular the **regular representation** `TauCeti.TypeAHeckeAlgebra.regularRep`, in which the
generator `T i` acts by the left regular operator `CoxeterSystem.heckeLeftMul`, is the general one
composed with this isomorphism, and the coordinates of the basis are read off from it
(`TauCeti.TypeAHeckeAlgebra.basisTw_repr_apply`).

The Coxeter system is an arbitrary one of type `A_(n-1)`. For the abstract Coxeter group
`(CoxeterMatrix.A (n - 1)).Group` this shows that the Hecke algebra is a free module; for a
concrete finite model of the Coxeter group, such as the symmetric group on `n` letters, the rank
is the order of that group (`TauCeti.TypeAHeckeAlgebra.finrank_eq_natCard`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.regularRep`: the regular representation on `W →₀ R`.
* `TauCeti.TypeAHeckeAlgebra.basisTw`: the basis `T_w` indexed by `W`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.regularRep_Tw_apply_single_one`: `T_w` takes the basis vector of `1`
  to that of `w`.
* `TauCeti.TypeAHeckeAlgebra.linearIndependent_Tw`: the elements `T_w` are linearly independent.
* `TauCeti.TypeAHeckeAlgebra.basisTw_repr`: the coordinates in the basis `T_w` are those of the
  image in the Hecke algebra of the type-A Coxeter matrix.
* `TauCeti.TypeAHeckeAlgebra.basisTw_repr_apply`: the coordinates in the basis `T_w` are read off
  from the regular representation.
* `TauCeti.TypeAHeckeAlgebra.regularRep_injective`: the regular representation is faithful.
* `TauCeti.TypeAHeckeAlgebra.finrank_eq_natCard`: the rank is the order of `W`.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Chapter 7.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4.
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

open CoxeterSystem Finsupp

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

variable (q) in
/-- The **regular representation** of the type-A Hecke algebra on the free module `W →₀ R`: the
generator `T i` acts by the left regular operator `CoxeterSystem.heckeLeftMul` with quadratic
coefficient `q - q⁻¹`, sending the basis vector of `w` to that of `s i * w` when `i` is not a left
descent of `w`, and to `(q - q⁻¹)` times itself plus that of `s i * w` when it is. It is the
regular representation `CoxeterMatrix.HeckeAlgebra.regularRep` of the Hecke algebra of the type-A
Coxeter matrix, composed with `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`. -/
noncomputable def regularRep : TypeAHeckeAlgebra R q n →ₐ[R] Module.End R (W →₀ R) :=
  (CoxeterMatrix.HeckeAlgebra.regularRep _ cs).comp (algEquivHeckeAlgebra R q n).toAlgHom

/-- The regular representation is the general one applied to the image under
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`. -/
theorem regularRep_apply (x : TypeAHeckeAlgebra R q n) :
    regularRep q cs x =
      CoxeterMatrix.HeckeAlgebra.regularRep _ cs (algEquivHeckeAlgebra R q n x) :=
  (rfl)

/-- The regular representation takes the generator `T i` to the left regular operator of the
simple reflection `s i`. -/
@[simp]
theorem regularRep_T (i : Fin (n - 1)) :
    regularRep q cs (T q i) = cs.heckeLeftMul ((q : R) - ↑q⁻¹) i := by
  simp [regularRep_apply]

/-- The regular representation commutes with every right regular Hecke operator. -/
theorem commute_regularRep_heckeRightMul (x : TypeAHeckeAlgebra R q n)
    (i : Fin (n - 1)) :
    Commute (regularRep q cs x) (cs.heckeRightMul ((q : R) - ↑q⁻¹) i) :=
  CoxeterMatrix.HeckeAlgebra.commute_regularRep_heckeRightMul _ cs _ i

/-- In the regular representation, `T_w` takes the basis vector of `1` to that of `w`. -/
@[simp]
theorem regularRep_Tw_apply_single_one (w : W) :
    regularRep q cs (Tw q cs w) (single 1 1) = single w (1 : R) := by
  simp [regularRep_apply]

variable (q) in
/-- **The basis theorem**: the elements `T_w`, `w : W`, form a basis of the type-A Hecke algebra
over every commutative ring and for every unit parameter. -/
noncomputable def basisTw : Module.Basis W R (TypeAHeckeAlgebra R q n) :=
  (CoxeterMatrix.HeckeAlgebra.basisTw _ cs).map (algEquivHeckeAlgebra R q n).symm.toLinearEquiv

/-- The basis vectors of `TauCeti.TypeAHeckeAlgebra.basisTw` are the elements `T_w`. -/
@[simp]
theorem coe_basisTw : ⇑(basisTw q cs) = (Tw q cs : W → TypeAHeckeAlgebra R q n) := by
  ext w
  simp [basisTw]

/-- The coordinates of `x` in the basis `T_w` are those of its image under
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` in the basis `T_w` of the Hecke algebra of the
Coxeter matrix. -/
theorem basisTw_repr (x : TypeAHeckeAlgebra R q n) :
    (basisTw q cs).repr x =
      (CoxeterMatrix.HeckeAlgebra.basisTw _ cs).repr (algEquivHeckeAlgebra R q n x) := by
  simp [basisTw]

/-- **The elements `T_w` are linearly independent** over every commutative ring and for every unit
parameter. -/
theorem linearIndependent_Tw : LinearIndependent R (Tw q cs : W → TypeAHeckeAlgebra R q n) := by
  simpa using (basisTw q cs).linearIndependent

/-- The coordinates of `x` in the basis `T_w` are the image under the regular representation of
`x` of the basis vector of `1`. -/
theorem basisTw_repr_apply (x : TypeAHeckeAlgebra R q n) :
    (basisTw q cs).repr x = regularRep q cs x (single 1 1) := by
  rw [basisTw_repr, CoxeterMatrix.HeckeAlgebra.basisTw_repr_apply, regularRep_apply]

open scoped Classical in
/-- The coefficient of `T_w` after left multiplication by a simple generator. -/
theorem basisTw_repr_T_mul (i : Fin (n - 1)) (x : TypeAHeckeAlgebra R q n) (w : W) :
    (basisTw q cs).repr (T q i * x) w =
      (if cs.IsLeftDescent w i then ((q : R) - ↑q⁻¹) * (basisTw q cs).repr x w else 0) +
        (basisTw q cs).repr x (cs.simple i * w) := by
  simp [basisTw_repr, CoxeterMatrix.HeckeAlgebra.basisTw_repr_T_mul]

open scoped Classical in
/-- The coefficient of `T_w` after right multiplication by a simple generator. -/
theorem basisTw_repr_mul_T (x : TypeAHeckeAlgebra R q n) (i : Fin (n - 1)) (w : W) :
    (basisTw q cs).repr (x * T q i) w =
      (if cs.IsRightDescent w i then ((q : R) - ↑q⁻¹) * (basisTw q cs).repr x w else 0) +
        (basisTw q cs).repr x (w * cs.simple i) := by
  simp [basisTw_repr, CoxeterMatrix.HeckeAlgebra.basisTw_repr_mul_T]

/-- **The regular representation is faithful.** -/
theorem regularRep_injective :
    Function.Injective (regularRep q cs : TypeAHeckeAlgebra R q n → Module.End R (W →₀ R)) :=
  (CoxeterMatrix.HeckeAlgebra.regularRep_injective _ cs).comp
    (algEquivHeckeAlgebra R q n).injective

/-- The type-A Hecke algebra is a free module, with basis the elements `T_w` of the abstract
Coxeter group of type `A_(n-1)`. -/
instance : Module.Free R (TypeAHeckeAlgebra R q n) :=
  .of_basis (basisTw q (CoxeterMatrix.A (n - 1)).toCoxeterSystem)

include cs in
/-- Over a nontrivial commutative ring, the rank of the type-A Hecke algebra is the order of the
Coxeter group `W` of type `A_(n-1)`. (When `W` is infinite, both sides are `0` by convention.) -/
theorem finrank_eq_natCard [Nontrivial R] :
    Module.finrank R (TypeAHeckeAlgebra R q n) = Nat.card W :=
  Module.finrank_eq_nat_card_basis (basisTw q cs)

end TypeAHeckeAlgebra

end TauCeti
