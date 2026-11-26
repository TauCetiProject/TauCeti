/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Diagonal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The action of `GL(2, ℤ/Nℤ)` on the modular function field `F_N`

The field `F_N` of modular functions of level `N` with Fourier coefficients in `ℚ(ζ_N)` carries
two separate actions: `SL(2, ℤ/Nℤ)` acts on the right by fractional linear maps
(`TauCeti.modularFunctionFieldActionZMod`), and `diag(1, d)` acts on the Fourier coefficients by
`ζ_N ↦ ζ_N^d` (`TauCeti.modularFunctionFieldDiagAction`). Every `γ ∈ GL(2, ℤ/Nℤ)` factors uniquely
as `γ = g · diag(1, det γ)` with `g ∈ SL(2, ℤ/Nℤ)`, and letting `γ` act by `g` followed by
`diag(1, det γ)` defines a right action of the whole of `GL(2, ℤ/Nℤ)` on `F_N`
(`TauCeti.modularFunctionFieldGLAction`). Row vectors are acted on from the right, so the Fricke
function `f_a` is sent to `f_{a γ}`.

That this is a right action rests on the twisted commutation of the two actions: if
`g diag(1, d) = diag(1, d) g'`, then acting by `g` and then by `diag(1, d)` is acting by
`diag(1, d)` and then by `g'`. We check it on the generators of `F_N`: the cyclotomic constants,
on which `γ` acts by `ζ_N ↦ ζ_N^(det γ)`, the modular invariant `j`, which is fixed, and the
Fricke functions.

The kernel of the action is `{±1}`, so `GL(2, ℤ/Nℤ)/{±1}` acts faithfully on `F_N`
(`TauCeti.modularFunctionFieldGLAction_eq_iff`). For `N ∣ 2` the two signs coincide, and the
action of `GL(2, ℤ/Nℤ)` itself is faithful (`TauCeti.modularFunctionFieldGLAction_injective_iff`);
at `N = 2` the group acting on `F_2` has order six
(`TauCeti.natCard_range_modularFunctionFieldGLAction_two`). The elements of `F_N` fixed by all
of `GL(2, ℤ/Nℤ)` are those pulled back from the level-one field `F₁ = ℚ(j)`
(`TauCeti.forall_unop_modularFunctionFieldGLAction_apply_eq_iff`).

## Main declarations

* `TauCeti.modularFunctionFieldGLAction`: the right action of `GL(2, ℤ/Nℤ)` on `F_N`.
* `TauCeti.modularFunctionFieldGLAction_toGL` and
  `TauCeti.unop_modularFunctionFieldGLAction_diagGL`: it restricts to the fractional linear
  action of `SL(2, ℤ/Nℤ)` and to the coefficient action of `diag(1, d)`.
* `TauCeti.unop_modularFunctionFieldGLAction_modularFunctionFieldConst`,
  `TauCeti.unop_modularFunctionFieldGLAction_modularFunctionFieldMapOfLevelOne` and
  `TauCeti.unop_modularFunctionFieldGLAction_frickeModularFunction`: the action on generators.
* `TauCeti.modularFunctionFieldGLAction_eq_one_iff`: the kernel is `{±1}`.
* `TauCeti.natCard_range_modularFunctionFieldGLAction_two`: at level two, `GL(2, ℤ/2ℤ)` of
  order six acts faithfully.
* `TauCeti.forall_unop_modularFunctionFieldGLAction_apply_eq_iff`: the fixed field is `ℚ(j)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§6.1–6.2.
* Dong Hwa Shin, *Generation of class fields by Siegel-Ramachandra invariants*,
  arXiv:1009.2253, §2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient
open TauCeti.RiemannSurface
open Matrix.GeneralLinearGroup (det)
open scoped Matrix MatrixGroups

namespace TauCeti

variable {N : ℕ}

variable [NeZero N]

/-- The action of `γ`: the fractional linear map of the special linear factor of `γ`, followed
by `diag(1, det γ)`. -/
private def glActionAux (γ : GL (Fin 2) (ZMod N)) :
    modularFunctionField N ≃+* modularFunctionField N :=
  modularFunctionFieldDiagAction N (det γ) * unop (modularFunctionFieldActionZMod N γ.slFactor)

private theorem glActionAux_modularFunctionFieldConst (γ : GL (Fin 2) (ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    glActionAux γ (modularFunctionFieldConst N c) =
      modularFunctionFieldConst N ((det γ).cyclotomicConjugate c) := by
  simp [glActionAux, RingAut.mul_apply]

private theorem glActionAux_modularFunctionFieldMapOfLevelOne (γ : GL (Fin 2) (ZMod N))
    (F : coeffSubfield ModularGroup.cuspDatumInfty ⊥) :
    glActionAux γ (modularFunctionFieldMapOfLevelOne N F) =
      modularFunctionFieldMapOfLevelOne N F := by
  simp [glActionAux, RingAut.mul_apply]

private theorem glActionAux_frickeModularFunction (γ : GL (Fin 2) (ZMod N))
    (a : Fin 2 → ZMod N) :
    glActionAux γ (frickeModularFunction a) =
      frickeModularFunction (a ᵥ* (γ : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  rw [glActionAux, RingAut.mul_apply, unop_modularFunctionFieldActionZMod_frickeModularFunction,
    modularFunctionFieldDiagAction_frickeModularFunction]
  conv_rhs => rw [← Matrix.GeneralLinearGroup.toGL_slFactor_mul_diagGL γ]
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, diagGL_coe,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  congr 1
  ext i
  fin_cases i <;> simp [Matrix.vecMul_diagonal, mul_comm]

variable (N) in
/-- **The right action of `GL(2, ℤ/Nℤ)` on `F_N`.** Writing `γ = g diag(1, det γ)` with
`g ∈ SL(2, ℤ/Nℤ)`, the element `γ` acts by the fractional linear map of `g` followed by the
coefficient action `ζ_N ↦ ζ_N^(det γ)` of `diag(1, det γ)`. It sends the Fricke function `f_a`
to `f_{a γ}` (`TauCeti.unop_modularFunctionFieldGLAction_frickeModularFunction`). -/
def modularFunctionFieldGLAction :
    GL (Fin 2) (ZMod N) →* (modularFunctionField N ≃+* modularFunctionField N)ᵐᵒᵖ where
  toFun γ := op (glActionAux γ)
  map_one' := by
    have h : (1 : GL (Fin 2) (ZMod N)).slFactor = 1 := by
      simpa using Matrix.GeneralLinearGroup.slFactor_toGL (1 : SL(2, ZMod N))
    simp [glActionAux, h]
  map_mul' γ δ := by
    apply unop_injective
    simp only [unop_op, unop_mul]
    apply RingEquiv.toRingHom_injective
    refine RingHom.eq_of_eqOn_of_field_closure_eq_top modularFunctionField_closure_eq_top ?_
    intro F hF
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_image] at hF
    rcases hF with ⟨c, rfl⟩ | rfl | ⟨a, -, rfl⟩ <;>
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingAut.mul_apply]
    · -- `det (γ δ) = det δ * det γ` in the commutative group of units, and the coefficient
      -- action is a homomorphism, so `γ δ` acts on constants by `det γ` and then by `det δ`.
      simp only [glActionAux_modularFunctionFieldConst]
      simp only [← modularFunctionFieldDiagAction_modularFunctionFieldConst]
      rw [map_mul, mul_comm (det γ) (det δ), map_mul, RingAut.mul_apply]
    · simp only [glActionAux_modularFunctionFieldMapOfLevelOne]
    · simp only [glActionAux_frickeModularFunction, Units.val_mul, Matrix.vecMul_vecMul]

private theorem unop_modularFunctionFieldGLAction (γ : GL (Fin 2) (ZMod N)) :
    unop (modularFunctionFieldGLAction N γ) = glActionAux γ :=
  rfl

/-- `γ ∈ GL(2, ℤ/Nℤ)` acts on cyclotomic constants by `ζ_N ↦ ζ_N^(det γ)`. -/
@[simp]
theorem unop_modularFunctionFieldGLAction_modularFunctionFieldConst (γ : GL (Fin 2) (ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    unop (modularFunctionFieldGLAction N γ) (modularFunctionFieldConst N c) =
      modularFunctionFieldConst N ((det γ).cyclotomicConjugate c) := by
  rw [unop_modularFunctionFieldGLAction, glActionAux_modularFunctionFieldConst]

/-- `GL(2, ℤ/Nℤ)` fixes every function pulled back from the level-one field `ℚ(j)`. -/
@[simp]
theorem unop_modularFunctionFieldGLAction_modularFunctionFieldMapOfLevelOne
    (γ : GL (Fin 2) (ZMod N)) (F : coeffSubfield ModularGroup.cuspDatumInfty ⊥) :
    unop (modularFunctionFieldGLAction N γ) (modularFunctionFieldMapOfLevelOne N F) =
      modularFunctionFieldMapOfLevelOne N F := by
  rw [unop_modularFunctionFieldGLAction, glActionAux_modularFunctionFieldMapOfLevelOne]

/-- `γ ∈ GL(2, ℤ/Nℤ)` sends the Fricke function `f_a` to `f_{a γ}`. -/
@[simp]
theorem unop_modularFunctionFieldGLAction_frickeModularFunction (γ : GL (Fin 2) (ZMod N))
    (a : Fin 2 → ZMod N) :
    unop (modularFunctionFieldGLAction N γ) (frickeModularFunction a) =
      frickeModularFunction (a ᵥ* (γ : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  rw [unop_modularFunctionFieldGLAction, glActionAux_frickeModularFunction]

/-- On `SL(2, ℤ/Nℤ)`, the action of `GL(2, ℤ/Nℤ)` is the fractional linear action. -/
@[simp]
theorem modularFunctionFieldGLAction_toGL (g : SL(2, ZMod N)) :
    modularFunctionFieldGLAction N g = modularFunctionFieldActionZMod N g := by
  apply unop_injective
  rw [unop_modularFunctionFieldGLAction, glActionAux, Matrix.GeneralLinearGroup.slFactor_toGL,
    Matrix.SpecialLinearGroup.coeToGL_det, map_one, one_mul]

/-- On `diag(1, d)`, the action of `GL(2, ℤ/Nℤ)` is the coefficient action
`ζ_N ↦ ζ_N^d`. -/
@[simp]
theorem unop_modularFunctionFieldGLAction_diagGL (d : (ZMod N)ˣ) :
    unop (modularFunctionFieldGLAction N (diagGL ![1, d])) =
      modularFunctionFieldDiagAction N d := by
  rw [unop_modularFunctionFieldGLAction, glActionAux, Matrix.GeneralLinearGroup.slFactor_diagGL,
    map_one, unop_one, mul_one, det_diagGL_one_left]

/-- Opposite matrices act in the same way on `F_N`. -/
@[simp]
theorem modularFunctionFieldGLAction_neg (γ : GL (Fin 2) (ZMod N)) :
    modularFunctionFieldGLAction N (-γ) = modularFunctionFieldGLAction N γ := by
  rw [← mul_neg_one, map_mul, ← Matrix.SpecialLinearGroup.toGL_neg_one,
    modularFunctionFieldGLAction_toGL,
    modularFunctionFieldActionZMod_neg, map_one, mul_one]

/-- **The kernel of the action of `GL(2, ℤ/Nℤ)` on `F_N` is `{±1}`.** This statement also applies
when the two signs coincide. -/
@[simp]
theorem modularFunctionFieldGLAction_eq_one_iff (γ : GL (Fin 2) (ZMod N)) :
    modularFunctionFieldGLAction N γ = 1 ↔ γ = 1 ∨ γ = -1 := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · have hdet : det γ = 1 := (det γ).eq_one_of_forall_cyclotomicConjugate_apply_eq fun c ↦ by
      apply (modularFunctionFieldConst N).injective
      rw [← unop_modularFunctionFieldGLAction_modularFunctionFieldConst, hγ, unop_one,
        RingAut.one_apply]
    have hγg : γ = (γ.slFactor : GL (Fin 2) (ZMod N)) :=
      (Matrix.GeneralLinearGroup.toGL_slFactor_of_det_eq_one hdet).symm
    rw [hγg, modularFunctionFieldGLAction_toGL, modularFunctionFieldActionZMod_eq_one_iff] at hγ
    rw [hγg]
    rcases hγ with h | h <;> simp [h]
  · rintro (rfl | rfl)
    · exact map_one _
    · rw [modularFunctionFieldGLAction_neg, map_one]

/-- **`GL(2, ℤ/Nℤ)/{±1}` acts faithfully on `F_N`.** Two elements of `GL(2, ℤ/Nℤ)` act in the
same way exactly when they agree up to sign. -/
theorem modularFunctionFieldGLAction_eq_iff {γ γ' : GL (Fin 2) (ZMod N)} :
    modularFunctionFieldGLAction N γ = modularFunctionFieldGLAction N γ' ↔
      γ = γ' ∨ γ = -γ' := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, modularFunctionFieldGLAction_eq_one_iff,
    mul_inv_eq_one, mul_inv_eq_iff_eq_mul, neg_one_mul]

/-- The action of `GL(2, ℤ/Nℤ)` on `F_N` is faithful exactly at the positive levels dividing two,
where the two signs coincide. -/
theorem modularFunctionFieldGLAction_injective_iff :
    Function.Injective (modularFunctionFieldGLAction N) ↔ N ∣ 2 := by
  have hsign : (-1 : GL (Fin 2) (ZMod N)) = 1 ↔ N ∣ 2 := by
    simpa using (Matrix.SpecialLinearGroup.toGL_inj (-1) 1).trans
      Matrix.SpecialLinearGroup.neg_one_eq_one_iff_dvd_two
  rw [← hsign, injective_iff_map_eq_one]
  simp [or_imp]

/-- **At level two, the group acting on `F_2` is `GL(2, ℤ/2ℤ)`, of order six.** The signs `±1`
coincide modulo two, so no quotient of order three arises. -/
theorem natCard_range_modularFunctionFieldGLAction_two :
    Nat.card (modularFunctionFieldGLAction 2).range = 6 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
      (modularFunctionFieldGLAction_injective_iff.mpr dvd_rfl)).toEquiv,
    Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

/-- **The fixed field of `GL(2, ℤ/Nℤ)` is `F₁ = ℚ(j)`.** An element of `F_N` is fixed by every
`γ ∈ GL(2, ℤ/Nℤ)` exactly when it is pulled back from the level-one field `ℚ(j)`. -/
theorem forall_unop_modularFunctionFieldGLAction_apply_eq_iff {F : modularFunctionField N} :
    (∀ γ : GL (Fin 2) (ZMod N), unop (modularFunctionFieldGLAction N γ) F = F) ↔
      F ∈ (modularFunctionFieldMapOfLevelOne N).fieldRange := by
  rw [mem_fieldRange_modularFunctionFieldMapOfLevelOne_iff]
  refine ⟨fun h ↦ ⟨fun g ↦ ?_, fun d ↦ ?_⟩, fun ⟨hSL, hdiag⟩ γ ↦ ?_⟩
  · rw [← modularFunctionFieldGLAction_toGL]
    exact h g
  · rw [← unop_modularFunctionFieldGLAction_diagGL]
    exact h _
  · rw [← Matrix.GeneralLinearGroup.toGL_slFactor_mul_diagGL γ, map_mul, unop_mul,
      RingAut.mul_apply, modularFunctionFieldGLAction_toGL, hSL,
      unop_modularFunctionFieldGLAction_diagGL, hdiag]

end TauCeti
