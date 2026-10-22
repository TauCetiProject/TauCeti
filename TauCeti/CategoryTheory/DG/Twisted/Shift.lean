/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.AdditiveClosure
public import TauCeti.CategoryTheory.DG.ShiftClosure.Basic
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
(`TauCeti.DGShiftClosure.toShift`).  The signs make it natural up to the Koszul sign,
`f ≫ σ_Q = (-1)^(n * p) • σ_P ≫ f⟦n⟧` for `f` of degree `p`
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

* `TauCeti.DGTwistedObject.matrixEquiv_twist_shiftFunctor_obj` and
  `TauCeti.DGTwistedObject.matrixEquiv_dgMap_shiftFunctor`: the shift does not change the matrix
  entries of the twist or of a morphism, as morphisms of `C`.
* `TauCeti.DGTwistedObject.dgDifferential_toShift` and
  `TauCeti.DGTwistedObject.dgDifferential_fromShift`: the comparison morphisms are closed.
* `TauCeti.DGTwistedObject.dgComp_toShift_fromShift` and
  `TauCeti.DGTwistedObject.dgComp_fromShift_toShift`: they are mutually inverse.
* `TauCeti.DGTwistedObject.dgComp_toShift`: they are natural up to the Koszul sign.

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
  map R (DGAdditiveClosure.map R (DGShiftClosure.shiftFunctor R n))

variable {R}

/-- The shift does not change the entries of the twisting matrix, as morphisms of `C`. -/
theorem matrixEquiv_twist_shiftFunctor_obj (n : ℤ)
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 ((shiftFunctor R n).obj P).twist i j =
      DGShiftClosure.shiftHomEquiv R _ _ n 1 (matrixEquiv R _ _ 1 P.twist i j) := by
  dsimp only [mapObj]
  rw [DGAdditiveClosure.dgMap_map]
  exact (DGAdditiveClosure.dgHomEquiv_mapHom R _ P.twist i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-- The shift does not change the entries of a morphism, as morphisms of `C`. -/
theorem matrixEquiv_dgMap_shiftFunctor (n : ℤ)
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {p : ℤ} (f : DGHom R p P Q)
    (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ p (dgHomEquiv R _ _ p ((shiftFunctor R n).dgMap p f)) i j =
      DGShiftClosure.shiftHomEquiv R _ _ n p (matrixEquiv R _ _ p (dgHomEquiv R P Q p f) i j) := by
  rw [dgMap_map, dgHomEquiv_mapHom, DGAdditiveClosure.dgMap_map]
  exact (DGAdditiveClosure.dgHomEquiv_mapHom R _ _ i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-! ### The comparison morphisms on the additive closure -/

/-- The diagonal matrix `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` of the comparison morphisms of the summands. -/
private noncomputable def matrixToShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    DGHom R (-n) M ((DGAdditiveClosure.map R (DGShiftClosure.shiftFunctor R n)).obj M) :=
  (matrixEquiv R _ _ (-n)).symm fun i ↦ by
    classical
    exact Pi.single i (DGShiftClosure.toShift R (M.X i) n)

private theorem matrixEquiv_matrixToShift_self (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ)
    (i : M.ι) :
    matrixEquiv R _ _ (-n) (matrixToShift M n) i i = DGShiftClosure.toShift R (M.X i) n := by
  simp [matrixToShift]

private theorem matrixEquiv_matrixToShift_of_ne (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ)
    {i j : M.ι} (h : i ≠ j) : matrixEquiv R _ _ (-n) (matrixToShift M n) i j = 0 := by
  classical
  simp [matrixToShift, Pi.single_eq_of_ne (Ne.symm h)]

/-- The diagonal matrix `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` of the inverse comparison morphisms of the
summands. -/
private noncomputable def matrixFromShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    DGHom R n ((DGAdditiveClosure.map R (DGShiftClosure.shiftFunctor R n)).obj M) M :=
  (matrixEquiv R _ _ n).symm fun i ↦ by
    classical
    exact Pi.single i (DGShiftClosure.fromShift R (M.X i) n)

private theorem matrixEquiv_matrixFromShift_self (M : DGAdditiveClosure (DGShiftClosure C))
    (n : ℤ) (i : M.ι) :
    matrixEquiv R _ _ n (matrixFromShift M n) i i = DGShiftClosure.fromShift R (M.X i) n := by
  simp [matrixFromShift]

private theorem matrixEquiv_matrixFromShift_of_ne (M : DGAdditiveClosure (DGShiftClosure C))
    (n : ℤ) {i j : M.ι} (h : i ≠ j) : matrixEquiv R _ _ n (matrixFromShift M n) i j = 0 := by
  classical
  simp [matrixFromShift, Pi.single_eq_of_ne (Ne.symm h)]

/-- Multiplying a column on the left by the diagonal comparison matrix picks out one entry. -/
private theorem sum_dgComp_matrixToShift {M : DGAdditiveClosure (DGShiftClosure C)} {n q m : ℤ}
    {Z : DGShiftClosure C} (g : ∀ j, DGHom R q ((DGShiftClosure.shiftFunctor R n).obj (M.X j)) Z)
    (h : -n + q = m) (i : M.ι) :
    ∑ j, dgComp R (matrixEquiv R _ _ (-n) (matrixToShift M n) i j) (g j) h =
      dgComp R (DGShiftClosure.toShift R (M.X i) n) (g i) h := by
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by
    rw [matrixEquiv_matrixToShift_of_ne M n (Ne.symm hj), zero_dgComp]) (by simp),
    matrixEquiv_matrixToShift_self]

/-- Multiplying a row on the right by the diagonal comparison matrix picks out one entry. -/
private theorem sum_matrixToShift_dgComp {M : DGAdditiveClosure (DGShiftClosure C)} {n p m : ℤ}
    {Z : DGShiftClosure C} (f : ∀ j, DGHom R p Z (M.X j)) (h : p + -n = m) (k : M.ι) :
    ∑ j, dgComp R (f j) (matrixEquiv R _ _ (-n) (matrixToShift M n) j k) h =
      dgComp R (f k) (DGShiftClosure.toShift R (M.X k) n) h := by
  rw [Finset.sum_eq_single k (fun j _ hj ↦ by
    rw [matrixEquiv_matrixToShift_of_ne M n hj, dgComp_zero]) (by simp),
    matrixEquiv_matrixToShift_self]

/-- The diagonal comparison matrices are natural up to the Koszul sign. -/
private theorem dgComp_matrixToShift {M N : DGAdditiveClosure (DGShiftClosure C)} (n : ℤ)
    {p m : ℤ} (f : DGHom R p M N) (h : p + -n = m) :
    dgComp R f (matrixToShift N n) h = (n * p).negOnePow • dgComp R (matrixToShift M n)
      ((DGAdditiveClosure.map R (DGShiftClosure.shiftFunctor R n)).dgMap p f) (by omega) :=
  DGAdditiveClosure.dgHom_ext R fun i k ↦ by
    rw [map_zsmul_unit, Pi.smul_apply, Pi.smul_apply, DGAdditiveClosure.dgHomEquiv_dgComp,
      DGAdditiveClosure.dgHomEquiv_dgComp, sum_matrixToShift_dgComp, sum_dgComp_matrixToShift,
      DGAdditiveClosure.dgMap_map, DGAdditiveClosure.dgHomEquiv_mapHom,
      DGShiftClosure.dgComp_toShift]

private theorem dgDifferential_matrixToShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    dgDifferential R (-n) (matrixToShift M n) = 0 :=
  DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, map_zero, Pi.zero_apply, Pi.zero_apply]
    rcases eq_or_ne i j with rfl | h
    · rw [matrixEquiv_matrixToShift_self, DGShiftClosure.dgDifferential_toShift]
    · rw [matrixEquiv_matrixToShift_of_ne M n h, map_zero]

private theorem dgComp_matrixToShift_matrixFromShift (M : DGAdditiveClosure (DGShiftClosure C))
    (n : ℤ) : dgComp R (matrixToShift M n) (matrixFromShift M n) (neg_add_cancel n) = dgId R M :=
  DGAdditiveClosure.dgHom_ext R fun i k ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgComp, sum_dgComp_matrixToShift]
    rcases eq_or_ne i k with rfl | h
    · rw [matrixEquiv_matrixFromShift_self, DGShiftClosure.dgComp_toShift_fromShift,
        DGAdditiveClosure.dgHomEquiv_dgId_self]
    · rw [matrixEquiv_matrixFromShift_of_ne M n h, dgComp_zero,
        DGAdditiveClosure.dgHomEquiv_dgId_of_ne R M h]

private theorem dgComp_matrixFromShift_matrixToShift (M : DGAdditiveClosure (DGShiftClosure C))
    (n : ℤ) : dgComp R (matrixFromShift M n) (matrixToShift M n) (add_neg_cancel n) =
      dgId R ((DGAdditiveClosure.map R (DGShiftClosure.shiftFunctor R n)).obj M) :=
  DGAdditiveClosure.dgHom_ext R fun i k ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgComp, sum_matrixToShift_dgComp]
    rcases eq_or_ne i k with rfl | h
    · rw [matrixEquiv_matrixFromShift_self, DGShiftClosure.dgComp_fromShift_toShift,
        DGAdditiveClosure.dgHomEquiv_dgId_self]
    · rw [matrixEquiv_matrixFromShift_of_ne M n h, zero_dgComp,
        DGAdditiveClosure.dgHomEquiv_dgId_of_ne R _ h]

/-! ### The comparison morphisms of twisted objects -/

variable (P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (n : ℤ)

/-- The comparison morphism `P ⟶ P⟦n⟧` of degree `-n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def toShift : DGHom R (-n) P ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ (-n)).symm (matrixToShift P.obj n)

/-- The comparison morphism `P⟦n⟧ ⟶ P` of degree `n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def fromShift : DGHom R n ((shiftFunctor R n).obj P) P :=
  (dgHomEquiv R _ _ n).symm (matrixFromShift P.obj n)

/-- The diagonal entries of `P ⟶ P⟦n⟧` are the comparison morphisms of the summands. -/
@[simp]
theorem matrixEquiv_toShift_self (i : P.obj.ι) :
    matrixEquiv R _ _ (-n) (dgHomEquiv R _ _ (-n) (toShift P n)) i i =
      DGShiftClosure.toShift R (P.obj.X i) n := by
  rw [toShift, LinearEquiv.apply_symm_apply, matrixEquiv_matrixToShift_self]

/-- The off-diagonal entries of `P ⟶ P⟦n⟧` vanish. -/
@[simp]
theorem matrixEquiv_toShift_of_ne {i j : P.obj.ι} (h : i ≠ j) :
    matrixEquiv R _ _ (-n) (dgHomEquiv R _ _ (-n) (toShift P n)) i j = 0 := by
  rw [toShift, LinearEquiv.apply_symm_apply, matrixEquiv_matrixToShift_of_ne _ _ h]

/-- The diagonal entries of `P⟦n⟧ ⟶ P` are the inverse comparison morphisms of the summands. -/
@[simp]
theorem matrixEquiv_fromShift_self (i : P.obj.ι) :
    matrixEquiv R _ _ n (dgHomEquiv R _ _ n (fromShift P n)) i i =
      DGShiftClosure.fromShift R (P.obj.X i) n := by
  rw [fromShift, LinearEquiv.apply_symm_apply, matrixEquiv_matrixFromShift_self]

/-- The off-diagonal entries of `P⟦n⟧ ⟶ P` vanish. -/
@[simp]
theorem matrixEquiv_fromShift_of_ne {i j : P.obj.ι} (h : i ≠ j) :
    matrixEquiv R _ _ n (dgHomEquiv R _ _ n (fromShift P n)) i j = 0 := by
  rw [fromShift, LinearEquiv.apply_symm_apply, matrixEquiv_matrixFromShift_of_ne _ _ h]

/-- **The comparison morphisms are natural up to the Koszul sign**: for `f : P ⟶ Q` of degree
`p`, `f` followed by `Q ⟶ Q⟦n⟧` is `(-1)^(n * p)` times `P ⟶ P⟦n⟧` followed by the shift of
`f`. -/
theorem dgComp_toShift {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {p m : ℤ} (f : DGHom R p P Q) (h : p + -n = m) :
    dgComp R f (toShift Q n) h =
      (n * p).negOnePow • dgComp R (toShift P n) ((shiftFunctor R n).dgMap p f) (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp, toShift, toShift,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, dgMap_map, dgHomEquiv_mapHom,
      dgComp_matrixToShift]

/-- **The comparison morphism `P ⟶ P⟦n⟧` is closed** for the twisted differential: by
naturality, `δ ≫ σ = (-1)^n • σ ≫ δ⟦n⟧`, which cancels the twisting terms of `D σ`. -/
theorem dgDifferential_toShift : dgDifferential R (-n) (toShift P n) = 0 :=
  (dgHomEquiv R _ _ (-n + 1)).injective <| by
    rw [dgHomEquiv_dgDifferential, map_zero, toShift, LinearEquiv.apply_symm_apply,
      dgDifferential_matrixToShift, dgComp_matrixToShift, mul_one, Int.negOnePow_neg, zero_add]
    exact sub_self _

/-- The comparison morphisms `P ⟶ P⟦n⟧ ⟶ P` compose to the identity of `P`. -/
theorem dgComp_toShift_fromShift :
    dgComp R (toShift P n) (fromShift P n) (neg_add_cancel n) = dgId R P :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, toShift, fromShift, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, dgComp_matrixToShift_matrixFromShift]

/-- The comparison morphisms `P⟦n⟧ ⟶ P ⟶ P⟦n⟧` compose to the identity of `P⟦n⟧`. -/
theorem dgComp_fromShift_toShift :
    dgComp R (fromShift P n) (toShift P n) (add_neg_cancel n) =
      dgId R ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, toShift, fromShift, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, dgComp_matrixFromShift_matrixToShift]

/-- The comparison morphism `P⟦n⟧ ⟶ P` is closed, as the inverse of a closed morphism. -/
theorem dgDifferential_fromShift : dgDifferential R n (fromShift P n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toShift P n) (neg_add_cancel n)
    (dgComp_toShift_fromShift P n) (dgComp_fromShift_toShift P n)

end DGTwistedObject

end TauCeti
