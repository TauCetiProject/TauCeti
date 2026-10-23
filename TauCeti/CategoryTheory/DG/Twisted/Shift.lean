/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.AdditiveClosure.Shift
public import TauCeti.CategoryTheory.DG.Twisted.Basic

/-!
# Shifts of twisted objects

Let `C` be a differential graded category.  The twisted objects `(⊕ᵢ Xᵢ[rᵢ], δ)` of the additive
closure of the shift closure of `C` are shifted summandwise: the shift by `n` is the twisted object
`(⊕ᵢ Xᵢ[rᵢ + n], δ)`, whose twisting matrix has the same entries as `δ`, viewed as morphisms of
`C`.  Since `Hom(Xᵢ[rᵢ + n], Xⱼ[rⱼ + n]) = Hom(Xᵢ, Xⱼ)[rⱼ - rᵢ] = Hom(Xᵢ[rᵢ], Xⱼ[rⱼ])` in the shift
closure, with the same differential and composition signs, this is the image of the twisted object
under the DG functor induced by the shift `X[r] ↦ X[r + n]` of the shift closure
(`TauCeti.DGShiftClosure.shiftFunctor`).  So the shift is a DG functor
`TauCeti.DGTwistedObject.shiftFunctor n`, which does not change the matrix entries of morphisms.

What makes `P⟦n⟧` the shift of `P` is a closed invertible morphism `P ⟶ P⟦n⟧` of degree `-n`:
composing with it identifies `Hom(Z, P⟦n⟧)` with `Hom(Z, P)[n]` and `Hom(P⟦n⟧, Z)` with
`Hom(P, Z)[-n]`.  It is the diagonal matrix `TauCeti.DGTwistedObject.toShift` whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`
(`TauCeti.DGShiftClosure.toShift`), that is, the comparison morphism
`TauCeti.DGAdditiveClosure.toShift` of the underlying objects.  The signs make it natural up to
the Koszul sign, `f ≫ σ_Q = (-1)^(n * p) • σ_P ≫ f⟦n⟧` for `f` of degree `p`
(`TauCeti.DGTwistedObject.dgComp_toShift`).  Applied to the twisting matrix, of degree one, this
says that `σ_P` is closed for the twisted differential `d σ + (-1)^n • σ ≫ δ⟦n⟧ - δ ≫ σ`.  Without
the signs it would not be: the identity entries alone would leave the error
`((-1)^n - (-1)^(n * (1 + rⱼ - rᵢ))) • δᵢⱼ` in the entry from `Xᵢ` to `Xⱼ`.  The diagonal matrix
`TauCeti.DGTwistedObject.fromShift` with the same entries is its inverse, of degree `n`.

Shifts are the second ingredient, with extensions (see
`TauCeti/CategoryTheory/DG/Twisted/Extension.lean`), of the cone `(Q ⊕ P⟦1⟧, δ)` of a closed
degree-zero morphism `u : P ⟶ Q` of twisted objects, along the closed degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q`.

## Main definitions

* `TauCeti.DGTwistedObject.shiftFunctor`: the DG functor shifting every summand of a twisted
  object by `n`.
* `TauCeti.DGTwistedObject.toShift` and `TauCeti.DGTwistedObject.fromShift`: the comparison
  morphisms `P ⟶ P⟦n⟧` of degree `-n` and `P⟦n⟧ ⟶ P` of degree `n`.

## Main results

* `TauCeti.DGTwistedObject.dgHomEquiv_toShift` and `TauCeti.DGTwistedObject.dgHomEquiv_fromShift`:
  the comparison morphisms are those of the underlying objects of the additive closure.
* `TauCeti.DGTwistedObject.dgHomEquiv_twist_shiftFunctor_obj` and
  `TauCeti.DGTwistedObject.dgHomEquiv_dgMap_shiftFunctor`: the shift does not change the matrix
  entries of the twist or of a morphism, as morphisms of `C`.
* `TauCeti.DGTwistedObject.dgDifferential_toShift` and
  `TauCeti.DGTwistedObject.dgDifferential_fromShift`: the comparison morphisms are closed.
* `TauCeti.DGTwistedObject.dgComp_toShift_fromShift` and
  `TauCeti.DGTwistedObject.dgComp_fromShift_toShift`: they are mutually inverse.
* `TauCeti.DGTwistedObject.dgComp_toShift` and `TauCeti.DGTwistedObject.dgComp_fromShift`: they
  are natural up to the Koszul sign.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

namespace DGTwistedObject

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/- `matrixEquiv` is a local name for `TauCeti.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `TauCeti.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

/-! ### The shift functor -/

/-- The DG functor shifting the twisted objects of the additive closure of the shift closure by
`n`: it sends `(⊕ᵢ Xᵢ[rᵢ], δ)` to `(⊕ᵢ Xᵢ[rᵢ + n], δ)`, the entries of the twisting matrix and of
every morphism being unchanged as morphisms of `C`. -/
-- This is reducible so that the summands of the shift of `P` are reducibly indexed by those of
-- `P`.
noncomputable abbrev shiftFunctor (n : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :=
  (DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.mapDGTwistedObject

variable {R}

/-- The shift does not change the entries of the twisting matrix, as morphisms of `C`. -/
theorem dgHomEquiv_twist_shiftFunctor_obj (n : ℤ)
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 ((shiftFunctor R n).obj P).twist i j =
      DGShiftClosure.shiftHomEquiv R _ _ n 1 (matrixEquiv R _ _ 1 P.twist i j) := by
  dsimp only [EnrichedFunctor.mapDGTwistedObjectObj]
  rw [EnrichedFunctor.dgMap_mapDGAdditiveClosure]
  exact (EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom _ P.twist i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-- The shift does not change the entries of a morphism, as morphisms of `C`. -/
theorem dgHomEquiv_dgMap_shiftFunctor (n : ℤ)
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {p : ℤ} (f : DGHom R p P Q)
    (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ p (dgHomEquiv R _ _ p ((shiftFunctor R n).dgMap p f)) i j =
      DGShiftClosure.shiftHomEquiv R _ _ n p (matrixEquiv R _ _ p (dgHomEquiv R P Q p f) i j) := by
  rw [EnrichedFunctor.dgMap_mapDGTwistedObject, EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
    EnrichedFunctor.dgMap_mapDGAdditiveClosure]
  exact (EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom _ _ i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-! ### The comparison morphisms of twisted objects -/

variable (P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (n : ℤ)

/-- The comparison morphism `P ⟶ P⟦n⟧` of degree `-n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def toShift : DGHom R (-n) P ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ (-n)).symm (DGAdditiveClosure.toShift R P.obj n)

/-- The comparison morphism `P⟦n⟧ ⟶ P` of degree `n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def fromShift : DGHom R n ((shiftFunctor R n).obj P) P :=
  (dgHomEquiv R _ _ n).symm (DGAdditiveClosure.fromShift R P.obj n)

/-- The matrix of `P ⟶ P⟦n⟧` is the comparison morphism of the underlying objects. -/
@[simp]
theorem dgHomEquiv_toShift :
    dgHomEquiv R _ _ (-n) (toShift P n) = DGAdditiveClosure.toShift R P.obj n :=
  LinearEquiv.apply_symm_apply _ _

/-- The matrix of `P⟦n⟧ ⟶ P` is the inverse comparison morphism of the underlying objects. -/
@[simp]
theorem dgHomEquiv_fromShift :
    dgHomEquiv R _ _ n (fromShift P n) = DGAdditiveClosure.fromShift R P.obj n :=
  LinearEquiv.apply_symm_apply _ _

/-- **The comparison morphisms are natural up to the Koszul sign**: for `f : P ⟶ Q` of degree
`p`, `f` followed by `Q ⟶ Q⟦n⟧` is `(-1)^(n * p)` times `P ⟶ P⟦n⟧` followed by the shift of
`f`. -/
theorem dgComp_toShift {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {p m : ℤ} (f : DGHom R p P Q) (h : p + -n = m) :
    dgComp R f (toShift Q n) h =
      (n * p).negOnePow • dgComp R (toShift P n) ((shiftFunctor R n).dgMap p f) (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp, dgHomEquiv_toShift,
      dgHomEquiv_toShift, EnrichedFunctor.dgMap_mapDGTwistedObject,
      EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
      DGAdditiveClosure.dgComp_toShift]

/-- **The inverse comparison morphisms are natural up to the Koszul sign**: for `f : P ⟶ Q` of
degree `p`, the shift of `f` followed by `Q⟦n⟧ ⟶ Q` is `(-1)^(n * p)` times `P⟦n⟧ ⟶ P` followed
by `f`. -/
theorem dgComp_fromShift {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {p m : ℤ} (f : DGHom R p P Q) (h : p + n = m) :
    dgComp R ((shiftFunctor R n).dgMap p f) (fromShift Q n) h =
      (n * p).negOnePow • dgComp R (fromShift P n) f (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp, dgHomEquiv_fromShift,
      dgHomEquiv_fromShift, EnrichedFunctor.dgMap_mapDGTwistedObject,
      EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
      DGAdditiveClosure.dgComp_fromShift]

/-- **The comparison morphism `P ⟶ P⟦n⟧` is closed** for the twisted differential: by
naturality, `δ ≫ σ = (-1)^n • σ ≫ δ⟦n⟧`, which cancels the twisting terms of `D σ`. -/
@[simp↓]
theorem dgDifferential_toShift : dgDifferential R (-n) (toShift P n) = 0 :=
  (dgHomEquiv R _ _ (-n + 1)).injective <| by
    rw [dgHomEquiv_dgDifferential, map_zero, dgHomEquiv_toShift,
      DGAdditiveClosure.dgDifferential_toShift, DGAdditiveClosure.dgComp_toShift, mul_one,
      Int.negOnePow_neg, zero_add]
    exact sub_self _

/-- The comparison morphisms `P ⟶ P⟦n⟧ ⟶ P` compose to the identity of `P`. -/
@[simp↓]
theorem dgComp_toShift_fromShift :
    dgComp R (toShift P n) (fromShift P n) (neg_add_cancel n) = dgId R P :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, dgHomEquiv_toShift,
      dgHomEquiv_fromShift, DGAdditiveClosure.dgComp_toShift_fromShift]

/-- The comparison morphisms `P⟦n⟧ ⟶ P ⟶ P⟦n⟧` compose to the identity of `P⟦n⟧`. -/
@[simp↓]
theorem dgComp_fromShift_toShift :
    dgComp R (fromShift P n) (toShift P n) (add_neg_cancel n) =
      dgId R ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, dgHomEquiv_toShift,
      dgHomEquiv_fromShift, DGAdditiveClosure.dgComp_fromShift_toShift]

/-- The comparison morphism `P⟦n⟧ ⟶ P` is closed, as the inverse of a closed morphism. -/
@[simp↓]
theorem dgDifferential_fromShift : dgDifferential R n (fromShift P n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toShift P n) (neg_add_cancel n)
    (dgComp_toShift_fromShift P n) (dgComp_fromShift_toShift P n)

end DGTwistedObject

end TauCeti
