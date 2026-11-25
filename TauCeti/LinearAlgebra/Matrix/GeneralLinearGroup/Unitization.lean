/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Algebra.Quasiregular
public import TauCeti.Algebra.Algebra.Unitization.Matrix
public import TauCeti.Algebra.Algebra.Unitization

/-!
# Invertible matrices over a forced unitization

Let `A` be a possibly nonunital algebra over a commutative semiring `R`, and
`A⁺ = Unitization R A` its forced unitization. An `n × n` matrix over `A⁺` is a pair of a
scalar matrix over `R` and a matrix over `A`. The invertible matrices whose scalar part is the
identity matrix form a subgroup `unitizationGLFstOne R A n` of `GLₙ(A⁺)`, the kernel of the map
to `GLₙ(R)` induced by the augmentation. Such a matrix is `1 + x` for a matrix `x` over `A`, and
`(1 + x) * (1 + y) = 1 + (x + y + x * y)`, so this subgroup is the group of quasi-units of the
nonunital matrix ring `Mₙ(A)`. In particular it does not depend on the scalar ring `R`: for an
algebra `R → S` and an `S`-algebra `A`, the change of scalars `Unitization.mapScalars`,
`(r, a) ↦ (algebraMap R S r, a)`, matches the two subgroups. When `A` itself has an identity,
quasi-units of `Mₙ(A)` are invertible matrices over `A`, and the subgroup is isomorphic to
`GLₙ(A)` through the map `Unitization R A → A`, `(r, a) ↦ r • 1 + a`.

This is the matrix form of Mathlib's `Unitization.unitsFstOne_mulEquiv_quasiregular`, which
treats the units of `A⁺` itself. Since matrices with identity scalar part represent every class
of the relative `K₁` of `A`, it compares relative `K₁` over different scalar rings, and with
`K₁(A)` when `A` is unital.

## Main definitions

* `TauCeti.unitizationGLFstOne R A n`: invertible matrices over `A⁺` with identity scalar part.
* `TauCeti.unitizationGLFstOneEquiv R A n`: its isomorphism with the quasi-units of `Mₙ(A)`,
  `u ↦ u - 1`, with inverse `x ↦ 1 + x`.
* `TauCeti.unitizationGLFstOneEquivGL R A n`: for a unital algebra `A`, its isomorphism with
  `GLₙ(A)`, `(r, a) ↦ r • 1 + a` on entries.

## Main results

* `TauCeti.mem_unitizationGLFstOne_iff`: membership means that the scalar part is the identity.
* `TauCeti.units_map_unitizationGLFstOneEquiv_symm`: the inverse isomorphisms for two scalar rings
  `R → S` are compatible with `Unitization R A → Unitization S A`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Remark 2.2.1, for matrices congruent to `1` modulo a
  nonunital algebra, independently of the unital ring acting on it.
-/

public section

noncomputable section

namespace TauCeti

open Unitization

section Semiring

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] (n : Type*) [Fintype n] [DecidableEq n]

/-- The invertible `n × n` matrices over `A⁺ = Unitization R A` whose scalar part is the identity
matrix: the kernel of the homomorphism `GLₙ(A⁺) →* GLₙ(R)` induced by the augmentation. -/
def unitizationGLFstOne : Subgroup (GL n (Unitization R A)) :=
  (Units.map ((fstHom R A : Unitization R A →+* R).mapMatrix (m := n)).toMonoidHom).ker

variable {R A n}

/-- `unitizationGLFstOne` is the kernel of the map induced by the augmentation. -/
theorem unitizationGLFstOne_def :
    unitizationGLFstOne R A n =
      (Units.map ((fstHom R A : Unitization R A →+* R).mapMatrix (m := n)).toMonoidHom).ker :=
  (rfl)

/-- An invertible matrix over `A⁺` lies in `unitizationGLFstOne` exactly when its scalar part is
the identity matrix. -/
@[simp]
theorem mem_unitizationGLFstOne_iff {u : GL n (Unitization R A)} :
    u ∈ unitizationGLFstOne R A n ↔
      (fstHom R A : Unitization R A →+* R).mapMatrix (u : Matrix n n (Unitization R A)) = 1 := by
  simp [unitizationGLFstOne, Units.ext_iff]

/-- An invertible matrix in `unitizationGLFstOne` has identity scalar part, stated entrywise with
`Matrix.map` rather than `RingHom.mapMatrix`. -/
private theorem map_fst_of_mem {u : GL n (Unitization R A)}
    (hu : u ∈ unitizationGLFstOne R A n) :
    (u : Matrix n n (Unitization R A)).map (fun x ↦ x.fst) = 1 := by
  ext i j
  simpa using congr_fun₂ (mem_unitizationGLFstOne_iff.1 hu) i j

/-- The matrix of components in `A` of a matrix with identity scalar part, as a quasi-unit. -/
private def toQuasiregular (u : unitizationGLFstOne R A n) :
    (PreQuasiregular (Matrix n n A))ˣ where
  val := PreQuasiregular.equiv (((u : GL n (Unitization R A)) : Matrix n n (Unitization R A)).map
    fun x ↦ x.snd)
  inv := PreQuasiregular.equiv ((((u⁻¹ : unitizationGLFstOne R A n) : GL n (Unitization R A)) :
    Matrix n n (Unitization R A)).map fun x ↦ x.snd)
  val_inv := PreQuasiregular.equiv.symm.injective <| by
    simp only [PreQuasiregular.equiv_symm_apply, PreQuasiregular.val_mul,
      PreQuasiregular.val_one]
    exact Matrix.map_snd_add_map_snd_add_mul_eq_zero (map_fst_of_mem u.property)
      (map_fst_of_mem u⁻¹.property) (by simp)
  inv_val := PreQuasiregular.equiv.symm.injective <| by
    simp only [PreQuasiregular.equiv_symm_apply, PreQuasiregular.val_mul,
      PreQuasiregular.val_one]
    exact Matrix.map_snd_add_map_snd_add_mul_eq_zero (map_fst_of_mem u⁻¹.property)
      (map_fst_of_mem u.property) (by simp)

private theorem val_val_toQuasiregular (u : unitizationGLFstOne R A n) :
    (toQuasiregular u).val.val =
      ((u : GL n (Unitization R A)) : Matrix n n (Unitization R A)).map fun x ↦ x.snd :=
  (rfl)

/-- The matrix `1 + x` over `A⁺` of a quasi-unit `x` of `Mₙ(A)`. -/
private def ofQuasiregular (x : (PreQuasiregular (Matrix n n A))ˣ) :
    unitizationGLFstOne R A n :=
  ⟨{ val := 1 + x.val.val.map (↑)
     inv := 1 + x⁻¹.val.val.map (↑)
     val_inv := by simp [Matrix.one_add_map_inr_mul_one_add_map_inr, Matrix.map_zero _ (inr_zero R)]
     inv_val := by
      simp [Matrix.one_add_map_inr_mul_one_add_map_inr, Matrix.map_zero _ (inr_zero R)] },
    mem_unitizationGLFstOne_iff.2 (Matrix.map_fst_one_add_map_inr _)⟩

private theorem coe_ofQuasiregular (x : (PreQuasiregular (Matrix n n A))ˣ) :
    (((ofQuasiregular x : unitizationGLFstOne R A n) : GL n (Unitization R A)) :
      Matrix n n (Unitization R A)) = 1 + x.val.val.map (↑) :=
  (rfl)

variable (R A n)

/-- The invertible matrices over `A⁺ = Unitization R A` with identity scalar part are the
quasi-units of the nonunital matrix ring `Mₙ(A)`: `u ↦ u - 1`, with inverse `x ↦ 1 + x`. The
target does not involve `R`. -/
def unitizationGLFstOneEquiv :
    unitizationGLFstOne R A n ≃* (PreQuasiregular (Matrix n n A))ˣ where
  toFun := toQuasiregular
  invFun := ofQuasiregular
  left_inv u := Subtype.ext <| Units.ext <| by
    rw [coe_ofQuasiregular, val_val_toQuasiregular]
    exact Matrix.one_add_map_inr_map_snd (map_fst_of_mem u.property)
  right_inv x := Units.ext <| PreQuasiregular.equiv.symm.injective <| by
    simp only [PreQuasiregular.equiv_symm_apply, val_val_toQuasiregular, coe_ofQuasiregular]
    exact Matrix.map_snd_one_add_map_inr _
  map_mul' u v := Units.ext <| PreQuasiregular.equiv.symm.injective <| by
    simp only [PreQuasiregular.equiv_symm_apply, Units.val_mul, PreQuasiregular.val_mul,
      val_val_toQuasiregular, Subgroup.coe_mul]
    exact Matrix.map_snd_mul_of_map_fst_eq_one (map_fst_of_mem u.property)
      (map_fst_of_mem v.property)

variable {R A n}

/-- `unitizationGLFstOneEquiv` sends a matrix to its matrix of components in `A`. -/
@[simp]
theorem val_val_unitizationGLFstOneEquiv_apply (u : unitizationGLFstOne R A n) :
    (unitizationGLFstOneEquiv R A n u).val.val =
      ((u : GL n (Unitization R A)) : Matrix n n (Unitization R A)).map fun x ↦ x.snd :=
  (rfl)

/-- The inverse of `unitizationGLFstOneEquiv` sends a quasi-unit `x` to `1 + x`. -/
@[simp]
theorem coe_unitizationGLFstOneEquiv_symm_apply (x : (PreQuasiregular (Matrix n n A))ˣ) :
    (((unitizationGLFstOneEquiv R A n).symm x : GL n (Unitization R A)) :
      Matrix n n (Unitization R A)) = 1 + x.val.val.map (↑) :=
  (rfl)

end Semiring

section ChangeOfScalars

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [NonUnitalSemiring A]
  [Module S A] [IsScalarTower S A A] [SMulCommClass S A A] [Module R A] [IsScalarTower R S A]
  [IsScalarTower R A A] [SMulCommClass R A A] {n : Type*} [Fintype n] [DecidableEq n]

/-- The isomorphisms `unitizationGLFstOneEquiv` for scalar rings `R` and `S` are compatible with
the change of scalars `Unitization.mapScalars`, `(r, a) ↦ (algebraMap R S r, a)`: the matrix
`1 + x` over `Unitization R A` goes to the matrix `1 + x` over `Unitization S A`. -/
theorem units_map_unitizationGLFstOneEquiv_symm (x : (PreQuasiregular (Matrix n n A))ˣ) :
    Units.map ((mapScalars R S A : Unitization R A →+* Unitization S A).mapMatrix
        (m := n)).toMonoidHom
      ((unitizationGLFstOneEquiv R A n).symm x) = (unitizationGLFstOneEquiv S A n).symm x := by
  ext i j : 2
  by_cases hij : i = j <;> simp [hij]

end ChangeOfScalars

section Unital

variable (R A : Type*) [CommSemiring R] [Ring A] [Algebra R A] (n : Type*) [Fintype n]
  [DecidableEq n]

/-- For a unital algebra `A`, the invertible matrices over `A⁺ = Unitization R A` with identity
scalar part are isomorphic to `GLₙ(A)`, through the map `(r, a) ↦ r • 1 + a` on entries: both are
the quasi-units of `Mₙ(A)`. The inverse sends `u` to `1 + (u - 1)`. -/
def unitizationGLFstOneEquivGL : unitizationGLFstOne R A n ≃* GL n A :=
  (unitizationGLFstOneEquiv R A n).trans
    (Units.mapEquiv (PreQuasiregular.oneAddMulEquiv (Matrix n n A)))

variable {R A n}

/-- `unitizationGLFstOneEquivGL` applies `(r, a) ↦ r • 1 + a` to the entries. -/
@[simp]
theorem unitizationGLFstOneEquivGL_apply (u : unitizationGLFstOne R A n) :
    unitizationGLFstOneEquivGL R A n u =
      Units.map ((lift (NonUnitalAlgHom.id R A) : Unitization R A →+* A).mapMatrix
        (m := n)).toMonoidHom u := by
  ext i j
  have h := congr_fun₂ (map_fst_of_mem u.property) i j
  simp only [Matrix.map_apply, Matrix.one_apply] at h
  simp [unitizationGLFstOneEquivGL, Matrix.one_apply, h, apply_ite (algebraMap R A)]

/-- The inverse of `unitizationGLFstOneEquivGL` sends `u` to `1 + (u - 1)`, with `u - 1` read in
`A ⊆ A⁺`. -/
@[simp]
theorem coe_unitizationGLFstOneEquivGL_symm_apply (u : GL n A) :
    (((unitizationGLFstOneEquivGL R A n).symm u : GL n (Unitization R A)) :
      Matrix n n (Unitization R A)) = 1 + ((u : Matrix n n A) - 1).map (↑) := by
  simp [unitizationGLFstOneEquivGL]

end Unital

end TauCeti
