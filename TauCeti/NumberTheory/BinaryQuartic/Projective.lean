/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Action
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Projective changes of variables in binary quartics

The determinant-twisted substitution descends to an action of `PGL₂` and commutes with
base change. This is the action on binary quartics used in two-descent.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §2.6, (32).
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.BinaryQuartic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The determinant-twisted change of variables descends to the projective linear group. -/
instance : MulAction (PGL(2, R)) (BinaryQuartic R) :=
  letI : MulAction (GL (Fin 2) R) (BinaryQuartic R) :=
    { smul := twistedSMul, one_smul := twistedSMul_one, mul_smul := twistedSMul_mul }
  ProjGenLinGroup.mulActionOfGL twistedSMul_scalar

/-- A projective matrix acts by twisted substitution with any representative. -/
@[simp] theorem mk_smul (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    ProjGenLinGroup.mk g • f = twistedSMul g f :=
  (rfl)

/-- The coefficient of `x^(4-i) y^i` under the twisted action of `diag(1,u)` is
scaled by `u^(i-2)`. Multiplying by `u²` writes the formula with natural powers. -/
theorem sq_mul_mk_diagGL_smul_apply (u : Rˣ) (f : BinaryQuartic R) (i : Fin 5) :
    (u : R) ^ 2 * (ProjGenLinGroup.mk (diagGL ![1, u]) • f) i =
      (u : R) ^ i.val * f i := by
  rw [mk_smul, twistedSMul_def, det_diagGL, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, Pi.smul_apply,
    smul_eq_mul, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [smul_eq_subst, diagGL_coe, subst_def]
  fin_cases i <;> simp [eval_def, Matrix.diagonal] <;> ring

/-- The projective action preserves the quadratic invariant. -/
@[simp] theorem invI_smul_projGenLinGroup (g : PGL(2, R)) (f : BinaryQuartic R) :
    invI (g • f) = invI f := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => simp

/-- The projective action preserves the cubic invariant. -/
@[simp] theorem invJ_smul_projGenLinGroup (g : PGL(2, R)) (f : BinaryQuartic R) :
    invJ (g • f) = invJ f := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => simp

/-- The projective action preserves the discriminant. -/
@[simp] theorem disc_smul_projGenLinGroup (g : PGL(2, R)) (f : BinaryQuartic R) :
    disc (g • f) = disc f := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => simp

/-- Projective changes of variables commute with base change of coefficients. -/
@[simp] theorem projGenLinGroup_map_smul_comp (f : BinaryQuartic R) (φ : R →+* S)
    (g : PGL(2, R)) : ProjGenLinGroup.map φ g • (φ ∘ f) = φ ∘ (g • f) := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    simp only [ProjGenLinGroup.map_mk, mk_smul, twistedSMul_def]
    funext i
    have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.map φ g))⁻¹ : Sˣ).val =
        φ ((GeneralLinearGroup.det g)⁻¹ : Rˣ).val := by
      rw [GeneralLinearGroup.map_det, ← map_inv (Units.map (φ : R →* S))]
      rfl
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_mul, map_pow, hdet]
    exact congrArg (fun x ↦ φ ((GeneralLinearGroup.det g)⁻¹ : Rˣ).val ^ 2 * x)
      (congrFun (smul_comp f φ g) i)

end TauCeti.BinaryQuartic
