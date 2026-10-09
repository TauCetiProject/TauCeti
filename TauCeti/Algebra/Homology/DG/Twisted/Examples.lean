/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

The two actions are declared as local instances in separate sections, so that no instance leaks
out of this file.

## Main results

* `TauCeti.TwistedExamples.projCocycle`: the twisting cocycle `m x y = (1, 0)` over `ℚ × ℚ`.
* `TauCeti.TwistedExamples.twistedDifferential_single_fst`,
  `TauCeti.TwistedExamples.twistedDifferential_single_snd`: the two values of `D (1 ⊗ x)`.

## References

* The DGFloer roadmap, acceptance criterion 2 (`TauCetiRoadmap/DGFloer/README.md`).
-/

public section

open MulOpposite

namespace TauCeti

namespace TwistedExamples

/-- The opposite of a degree-`0` algebra acts on a degree-`0` module compatibly with the
gradings, whatever the action is. -/
instance instGradedSMulTrivialGradingOpposite {R A M : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring M] [Algebra R M] [Module Aᵐᵒᵖ M] :
    SetLike.GradedSMul (InternalGrading.ofDecomposition (trivialGrading R A)).opposite.piece
      (trivialGrading R M) where
  smul_mem {i j a x} ha hx := by
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece,
      mem_trivialGrading_iff] at ha
    rw [mem_trivialGrading_iff] at hx ⊢
    rcases ha with rfl | ha
    · rcases hx with rfl | rfl <;> simp
    · right
      rw [← op_unop a, ha]
      simp

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

@[simp]
theorem projCocycle_m_zero_one : projCocycle.m 0 1 = (1, 0) := by
  simp [projCocycle, projMatrix]

@[simp]
theorem projCocycle_m_one_zero : projCocycle.m 1 0 = 0 := by
  simp [projCocycle, projMatrix]

theorem one_mem_trivialGrading_zero : (1 : ℚ) ∈ trivialGrading ℚ ℚ 0 := by
  simp

section Fst

/-- `ℚ` as a right `ℚ × ℚ`-module through the first projection. -/
local instance instModuleFst : Module (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  Module.compHom ℚ ((RingHom.fst ℚ ℚ).fromOpposite fun _ _ ↦ Commute.all _ _)

theorem op_smul_fst (a : ℚ × ℚ) (r : ℚ) : op a • r = a.1 * r :=
  rfl

local instance instIsScalarTowerFst : IsScalarTower ℚ (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  ⟨fun c a r ↦ by
    induction a using MulOpposite.rec' with
    | h a =>
      rw [← op_smul, op_smul_fst, op_smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

/-- With the action through the first projection, `D (1 ⊗ x) = 1 ⊗ y`. -/
theorem twistedDifferential_single_fst :
    twistedDifferential projCocycle.m (trivialGrading ℚ ℚ) 0 (Pi.single 0 1) = Pi.single 1 1 := by
  rw [twistedDifferential_single projCocycle.m 0 0 one_mem_trivialGrading_zero]
  simp [Fin.sum_univ_two, op_smul_fst]

end Fst

section Snd

/-- `ℚ` as a right `ℚ × ℚ`-module through the second projection. -/
local instance instModuleSnd : Module (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  Module.compHom ℚ ((RingHom.snd ℚ ℚ).fromOpposite fun _ _ ↦ Commute.all _ _)

theorem op_smul_snd (a : ℚ × ℚ) (r : ℚ) : op a • r = a.2 * r :=
  rfl

local instance instIsScalarTowerSnd : IsScalarTower ℚ (ℚ × ℚ)ᵐᵒᵖ ℚ :=
  ⟨fun c a r ↦ by
    induction a using MulOpposite.rec' with
    | h a =>
      rw [← op_smul, op_smul_snd, op_smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

/-- With the action through the second projection, `D (1 ⊗ x) = 0`. -/
theorem twistedDifferential_single_snd :
    twistedDifferential projCocycle.m (trivialGrading ℚ ℚ) 0 (Pi.single 0 1) = 0 := by
  rw [twistedDifferential_single projCocycle.m 0 0 one_mem_trivialGrading_zero]
  simp [Fin.sum_univ_two, op_smul_snd]

end Snd

end TwistedExamples

end TauCeti
