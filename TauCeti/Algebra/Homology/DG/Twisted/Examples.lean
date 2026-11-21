/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Fin
public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Twisted complexes: the dependence on the coefficient action

The twisted differential of `TauCeti.Algebra.Homology.DG.Twisted.Complex` is built from the right
action of the algebra on the coefficient module.  This file records the smallest example in which
that dependence is visible, and checks the twisted differential on it.

Take `A = ℚ × ℚ` concentrated in degree `0` with zero differential, two generators `x, y` with
`ind x = 1` and `ind y = 0`, and the single coefficient `m x y = (1, 0)`.  The module `M = ℚ`,
concentrated in degree `0` with zero differential, is a right `A`-module in two ways, through the
first and through the second projection.  Both are differential graded right modules over
`(A, 0)`, and the twisted differential of `1 ⊗ x` is `1 ⊗ y` for the first action and `0` for the
second (`twistedDifferential_single_fst`, `twistedDifferential_single_snd`).  Any construction of
the twisted differential that did not take the action as an input would have to give the same
answer in both cases.

The twisted differential also takes as a parameter the commutation of the right action with the
scalars `R` (`SMulCommClass R Aᵐᵒᵖ M`), and this is what makes it `R`-linear.  For coefficients in
degree `0` with zero differential the twisted differential is the matrix action
`(D f) y = Σ_x op (m x y) • f x` (`TauCeti.twistedDifferential_trivialGrading_apply`), a formula
that still makes sense for a right action that does not commute with the scalars.  Take
`R = A = ℚ × ℚ` and `M = ℚ²`, with `(a, b) • (u, v) = (a u, b v)` on the left and
`(u, v) · (a, b) = (a u + (b - a) v, b v)` on the right.  The two actions do not commute
(`not_smulCommClass_upper`), and for the cocycle above the formula is not `ℚ × ℚ`-linear
(`not_isLinearMap_sum_op_projCocycle_smul`): the scalar `(1, 0)` kills `(0, 1) ⊗ x`, but fixes its
image `(-1, 0) ⊗ y`.  So the commutation hypothesis cannot be dropped from the definition.

The actions are declared as local instances in separate sections, so that no instance leaks out
of this file.

## Main results

* `TauCeti.TwistedExamples.projCocycle`: the twisting cocycle `m x y = (1, 0)` over `ℚ × ℚ`, with
  its entries `projCocycle_m`.
* `TauCeti.TwistedExamples.twistedDifferential_single_fst`,
  `TauCeti.TwistedExamples.twistedDifferential_single_snd`: the two values of `D (1 ⊗ x)`.
* `TauCeti.TwistedExamples.not_smulCommClass_upper`,
  `TauCeti.TwistedExamples.not_isLinearMap_sum_op_projCocycle_smul`: for the noncommuting actions
  on `ℚ²`, the formula of the twisted differential is not linear over the scalars.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
-/

public section

open MulOpposite

namespace TauCeti

namespace TwistedExamples

/-- The generators: `x = 0` of index `1` and `y = 1` of index `0`. -/
def ind : Fin 2 → ℤ := ![1, 0]

/-- The coefficient matrix: `m x y = (1, 0)`, every other entry zero. -/
def projMatrix : Fin 2 → Fin 2 → ℚ × ℚ := fun i j ↦ if i = 0 ∧ j = 1 then (1, 0) else 0

/-- The twisting cocycle `m x y = (1, 0)` over `ℚ × ℚ` in degree `0` with zero differential. -/
def projCocycle : TwistingCocycle (trivialGrading ℚ (ℚ × ℚ)) 0 (Fin 2) ind :=
  TwistingCocycle.ofNonpos projMatrix
    (fun i j ↦ by
      rw [mem_trivialGrading_iff]
      fin_cases i <;> fin_cases j <;> simp [projMatrix, ind])
    (fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [projMatrix])
    (fun n hn ↦ trivialGrading_eq_bot ℚ (ℚ × ℚ) hn.ne')

/-- The entries of the cocycle: `m x y = (1, 0)` and every other entry zero. -/
@[simp]
theorem projCocycle_m (i j : Fin 2) :
    projCocycle.m i j = if i = 0 ∧ j = 1 then (1, 0) else 0 := by
  rw [projCocycle, TwistingCocycle.ofNonpos_m, projMatrix]

section Fst

/-- `ℚ` as a right `ℚ × ℚ`-module through the first projection. -/
local instance instModuleFst : Module (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  Module.compHom ℚ ((RingHom.fst ℚ ℚ).fromOpposite fun _ _ ↦ Commute.all _ _)

private theorem op_smul_fst (a : ℚ × ℚ) (r : ℚ) : op a • r = a.1 * r :=
  rfl

local instance instIsScalarTowerFst : IsScalarTower ℚ (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  ⟨fun c a r ↦ by
    induction a using MulOpposite.rec' with
    | h a =>
      rw [← op_smul, op_smul_fst, op_smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

/-- With the action through the first projection, `D (1 ⊗ x) = 1 ⊗ y`. -/
theorem twistedDifferential_single_fst :
    twistedDifferential projCocycle.m (trivialGrading ℚ ℚ) 0 (Pi.single 0 1) = Pi.single 1 1 := by
  rw [twistedDifferential_single projCocycle.m 0 0 (q := 0) (by simp)]
  simp [Fin.sum_univ_two, op_smul_fst]

end Fst

section Snd

/-- `ℚ` as a right `ℚ × ℚ`-module through the second projection. -/
local instance instModuleSnd : Module (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  Module.compHom ℚ ((RingHom.snd ℚ ℚ).fromOpposite fun _ _ ↦ Commute.all _ _)

private theorem op_smul_snd (a : ℚ × ℚ) (r : ℚ) : op a • r = a.2 * r :=
  rfl

local instance instIsScalarTowerSnd : IsScalarTower ℚ (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  ⟨fun c a r ↦ by
    induction a using MulOpposite.rec' with
    | h a =>
      rw [← op_smul, op_smul_snd, op_smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

/-- With the action through the second projection, `D (1 ⊗ x) = 0`. -/
theorem twistedDifferential_single_snd :
    twistedDifferential projCocycle.m (trivialGrading ℚ ℚ) 0 (Pi.single 0 1) = 0 := by
  rw [twistedDifferential_single projCocycle.m 0 0 (q := 0) (by simp)]
  simp [Fin.sum_univ_two, op_smul_snd]

end Snd

section Upper

/-- `ℚ²` as a left `ℚ × ℚ`-module, coordinatewise: `(a, b) • (u, v) = (a u, b v)`. -/
local instance instModuleDiag : Module (ℚ × ℚ) (Fin 2 → ℚ) :=
  Module.compHom (Fin 2 → ℚ) (RingEquiv.piFinTwo fun _ ↦ ℚ).symm.toRingHom

private theorem smul_diag (a : ℚ × ℚ) (v : Fin 2 → ℚ) : a • v = ![a.1 * v 0, a.2 * v 1] := by
  ext i
  fin_cases i <;> rfl

/-- The right action of `ℚ × ℚ` on `ℚ²` through upper triangular matrices:
`(u, v) · (a, b) = (a u + (b - a) v, b v)`. -/
local instance instSMulUpper : SMul (ℚ × ℚ)ᵐᵒᵖ (Fin 2 → ℚ) :=
  ⟨fun a v ↦ ![a.unop.1 * v 0 + (a.unop.2 - a.unop.1) * v 1, a.unop.2 * v 1]⟩

private theorem smul_upper (a : (ℚ × ℚ)ᵐᵒᵖ) (v : Fin 2 → ℚ) :
    a • v = ![a.unop.1 * v 0 + (a.unop.2 - a.unop.1) * v 1, a.unop.2 * v 1] :=
  rfl

private theorem op_smul_upper (a : ℚ × ℚ) (v : Fin 2 → ℚ) :
    op a • v = ![a.1 * v 0 + (a.2 - a.1) * v 1, a.2 * v 1] :=
  rfl

/-- `ℚ²` as a right `ℚ × ℚ`-module, through upper triangular matrices. -/
local instance instModuleUpper : Module (ℚ × ℚ)ᵐᵒᵖ (Fin 2 → ℚ) :=
  { instSMulUpper with
    one_smul v := by ext i; fin_cases i <;> simp [smul_upper]
    mul_smul a b v := by ext i; fin_cases i <;> simp [smul_upper] <;> ring
    smul_zero a := by ext i; fin_cases i <;> simp [smul_upper]
    smul_add a v w := by ext i; fin_cases i <;> simp [smul_upper] <;> ring
    add_smul a b v := by ext i; fin_cases i <;> simp [smul_upper] <;> ring
    zero_smul v := by ext i; fin_cases i <;> simp [smul_upper] }

/-- **The two actions on `ℚ²` do not commute**: `(1, 0) • ((0, 1) · (0, 1)) = (1, 0)`, while
`((1, 0) • (0, 1)) · (0, 1) = 0`. -/
theorem not_smulCommClass_upper : ¬ SMulCommClass (ℚ × ℚ) (ℚ × ℚ)ᵐᵒᵖ (Fin 2 → ℚ) := by
  intro h
  have := congr_fun (h.smul_comm ((1, 0) : ℚ × ℚ) (op ((0, 1) : ℚ × ℚ)) ![0, 1]) 0
  simp [smul_diag, op_smul_upper] at this

/-- **The commutation hypothesis of the twisted differential cannot be dropped.** For the
noncommuting actions on `ℚ²`, the formula `(D f) y = Σ_x op (m x y) • f x` of the twisted
differential of `projCocycle`, with coefficients in degree `0` and zero differential, is not
`ℚ × ℚ`-linear: the scalar `(1, 0)` kills `(0, 1) ⊗ x`, but fixes its image `(-1, 0) ⊗ y`. -/
theorem not_isLinearMap_sum_op_projCocycle_smul :
    ¬ IsLinearMap (ℚ × ℚ) fun (f : Fin 2 → Fin 2 → ℚ) (y : Fin 2) ↦
      ∑ x, op (projCocycle.m x y) • f x := by
  intro h
  have := congr_fun (congr_fun (h.map_smul ((1, 0) : ℚ × ℚ) (Pi.single 0 ![0, 1])) 1) 0
  simp [Fin.sum_univ_two, smul_diag, op_smul_upper] at this

end Upper

end TwistedExamples

end TauCeti
