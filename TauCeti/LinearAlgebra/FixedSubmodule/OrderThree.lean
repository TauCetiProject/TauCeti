/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.BaseChange
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# An order-three Cartan action and specialization of its fixed module

The integral matrix `[[0,-1],[1,-1]]` acts with order three on a rank-two free
cocharacter lattice. Such an action is permitted on the Cartan part of a root-free
reductive datum: there are no root vectors to constrain it. Its fixed lattice is zero,
but after reduction modulo three the vector `(-1,1)` is fixed and nonzero.

`TauCeti.OrderThreeCartan.fixedSubmoduleEquiv` identifies the fixed module over every
commutative ring with the annihilator of three. The explicit unimodular diagonalization
of the automorphism minus the identity has coefficients `1,3`.
`TauCeti.OrderThreeCartan.not_surjective_fixedSubmoduleBaseChange` proves that the canonical
map from scalar-extended integral fixed vectors to fixed vectors after extension is not
surjective over `ZMod 3`. Thus absence of 2-torsion does not suffice for fixed modules
to commute with scalar extension.

The construction uses Mathlib's `LinearMap.fixedSubmodule`, `Matrix.toLinearEquiv` and
`TensorProduct.piScalarRight`, together with the canonical comparison
`LinearMap.fixedSubmoduleBaseChange`.
-/

public section

namespace TauCeti.OrderThreeCartan

variable (R : Type*) [CommRing R]

/-- The integral Cartan matrix, specialized to the coefficient ring. -/
abbrev matrix : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, -1]

/-- The specialization of the integral order-three Cartan automorphism. -/
noncomputable def automorphism : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) :=
  (matrix R).toLinearEquiv (Pi.basisFun R (Fin 2)) (by
    simp [matrix, Matrix.det_fin_two])

/-- The action in the original cocharacter coordinates. -/
@[simp]
theorem automorphism_apply (x : Fin 2 → R) :
    automorphism R x = ![-x 1, x 0 - x 1] := by
  simp [automorphism, Matrix.toLin_eq_toLin', Matrix.toLin'_apply, matrix,
    dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- The third iterate is the identity after every specialization. -/
theorem automorphism_cube (x : Fin 2 → R) :
    automorphism R (automorphism R (automorphism R x)) = x := by
  ext i
  fin_cases i <;> simp
  ring

/-- The automorphism has exact order three over every nontrivial coefficient ring. -/
theorem orderOf_automorphism [Nontrivial R] : orderOf (automorphism R) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply LinearEquiv.ext
    intro x
    simpa only [pow_succ, pow_zero, mul_one, mul_apply_eq_comp,
      FunLike.coe_one_eq_id, id_eq] using automorphism_cube R x
  · intro h
    have hx := congrFun (LinearEquiv.congr_fun h ![1, 0]) 0
    norm_num at hx

/-- An explicit unimodular diagonalization of the automorphism minus the identity.
Both change-of-basis matrices have determinant one; the diagonal factors are `1,3`. -/
theorem diagonalization :
    !![-1, 0; -1, -1] * (matrix R - 1) * !![1, -1; 0, 1] =
      Matrix.diagonal ![(1 : R), 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.diagonal]
  ring

/-- Fixed vectors have opposite coordinates, with the second coordinate annihilated by three. -/
theorem mem_fixedSubmodule_iff (x : Fin 2 → R) :
    x ∈ (automorphism R).toLinearMap.fixedSubmodule ↔
      x 0 + x 1 = 0 ∧ (3 : R) * x 1 = 0 := by
  simp only [LinearMap.mem_fixedSubmodule_iff, LinearEquiv.coe_coe, automorphism_apply,
    funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · rw [← h0]
      ring
    · rw [← h0] at h1
      linear_combination -h1
  · rintro ⟨h0, h1⟩
    constructor
    · linear_combination -h0
    · linear_combination h0 - h1

/-- The fixed module is exactly the scalar annihilator of three, via the second coordinate. -/
noncomputable def fixedSubmoduleEquiv :
    (automorphism R).toLinearMap.fixedSubmodule ≃ₗ[R]
      LinearMap.ker (LinearMap.mulLeft R (3 : R)) where
  toFun x := ⟨x.val 1, ((mem_fixedSubmodule_iff R x).mp x.property).2⟩
  invFun a := ⟨![-(a : R), (a : R)], (mem_fixedSubmodule_iff R _).mpr
    ⟨by simp, a.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · exact (eq_neg_of_add_eq_zero_left ((mem_fixedSubmodule_iff R x).mp x.property).1).symm
    · rfl
  right_inv a := rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The fixed-module equivalence takes the second original coordinate. -/
@[simp]
theorem fixedSubmoduleEquiv_apply (x : (automorphism R).toLinearMap.fixedSubmodule) :
    (fixedSubmoduleEquiv R x : R) = x.val 1 :=
  (rfl)

/-- The inverse equivalence sends a three-torsion scalar to the opposite-coordinate vector. -/
@[simp]
theorem fixedSubmoduleEquiv_symm_apply
    (a : LinearMap.ker (LinearMap.mulLeft R (3 : R))) :
    ((fixedSubmoduleEquiv R).symm a : Fin 2 → R) = ![-(a : R), (a : R)] :=
  (rfl)

/-- The integral Cartan lattice has no nonzero fixed vectors. -/
theorem fixedSubmodule_int_eq_bot :
    (automorphism ℤ).toLinearMap.fixedSubmodule = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨hadd, hthree⟩ := (mem_fixedSubmodule_iff ℤ x).mp hx
  have h1 : x 1 = 0 := by omega
  have h0 : x 0 = 0 := by omega
  ext i
  fin_cases i <;> assumption

/-- Reduction modulo three creates the fixed vector `(-1,1)`. -/
theorem neg_one_one_mem_fixedSubmodule_zmod_three :
    ![-1, 1] ∈ (automorphism (ZMod 3)).toLinearMap.fixedSubmodule := by
  rw [mem_fixedSubmodule_iff]
  decide

/-- The fixed module modulo three is nonzero, despite the vanishing integral fixed lattice. -/
theorem fixedSubmodule_zmod_three_ne_bot :
    (automorphism (ZMod 3)).toLinearMap.fixedSubmodule ≠ ⊥ := by
  intro h
  have hz : (![-1, 1] : Fin 2 → ZMod 3) = 0 := by
    simpa only [h, Submodule.mem_bot] using neg_one_one_mem_fixedSubmodule_zmod_three
  have := congrFun hz 1
  norm_num at this

/-- Standard tensor coordinates intertwine the extended integral automorphism and its
coefficient-ring specialization. -/
theorem piScalarRight_comp_baseChange :
    (TensorProduct.piScalarRight ℤ R R (Fin 2)).toLinearMap ∘ₗ
        (automorphism ℤ).toLinearMap.baseChange R =
      (automorphism R).toLinearMap ∘ₗ
        (TensorProduct.piScalarRight ℤ R R (Fin 2)).toLinearMap := by
  ext x i
  fin_cases i <;>
    simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      sub_smul]

/-- The canonical scalar-extension comparison for this integral fixed lattice is not
surjective modulo three. This is failure of surjectivity of the actual tensor comparison,
not just a dimension discrepancy between two coordinate models. -/
theorem not_surjective_fixedSubmoduleBaseChange :
    ¬ Function.Surjective ((automorphism ℤ).toLinearMap.fixedSubmoduleBaseChange (ZMod 3)) := by
  let f := (automorphism ℤ).toLinearMap
  let e := TensorProduct.piScalarRight ℤ (ZMod 3) (ZMod 3) (Fin 2)
  let w := e.symm ![-1, 1]
  have hw : w ∈ (f.baseChange (ZMod 3)).fixedSubmodule := by
    rw [LinearMap.mem_fixedSubmodule_iff]
    apply e.injective
    have h := LinearMap.congr_fun (piScalarRight_comp_baseChange (ZMod 3)) w
    simpa only [w, e, f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using h.trans (LinearMap.mem_fixedSubmodule_iff.mp
        neg_one_one_mem_fixedSubmodule_zmod_three)
  have hw0 : w ≠ 0 := by
    intro h
    have he : e w = ![-1, 1] := e.apply_symm_apply _
    rw [h, map_zero] at he
    have := congrFun he 1
    norm_num at this
  let : Subsingleton f.fixedSubmodule :=
    Submodule.subsingleton_iff_eq_bot.mpr fixedSubmodule_int_eq_bot
  intro hs
  obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
  have hv0 : v = 0 := Subsingleton.elim _ _
  apply hw0
  have := congrArg Subtype.val hv
  simpa [hv0] using this.symm

end TauCeti.OrderThreeCartan
