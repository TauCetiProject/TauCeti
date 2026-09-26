/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.GradedModule
public import TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Graded left modules as right modules over the graded opposite

A left module over an internally graded algebra `A` determines a right module over the
Koszul-signed graded opposite of `A`. On homogeneous elements of degrees `p` and `q`, the action is

`x * op(a) = (-1) ^ (p * q) • (a • x)`.

The construction applies to additive commutative monoids and preserves both the ground-ring scalar
tower and the module grading.

## Main definitions

* `GradedOpposite.leftToRightModule`: the right action of the graded opposite associated to a
  graded left module.

## Main results

* `GradedOpposite.leftToRight_smul_of_mem`: the action on homogeneous elements is the Koszul-signed
  original left action.
* `GradedOpposite.leftToRight_isScalarTower` and
  `GradedOpposite.leftToRight_gradedSMul`: compatibility with the ground-ring action and the
  module grading.

The sign convention follows B. Keller, *Introduction to A-infinity algebras and modules*,
Section 3.1.
-/

public section

namespace TauCeti.GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The right action of the graded opposite associated to a graded left `A`-module.

It is obtained by restricting scalars along `(GradedOpposite G)ᵐᵒᵖ ≃ₐ[R] A` and conjugating the
result by the quadratic twist of the module grading. -/
@[instance_reducible]
noncomputable def leftToRightModule (G : InternalGrading R A) (H : InternalGrading R M) :
    Module (GradedOpposite G)ᵐᵒᵖ M := by
  letI : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (opAlgEquiv G).toRingHom
  exact H.quadraticTwistEquiv.toAddEquiv.module (GradedOpposite G)ᵐᵒᵖ

omit [IsScalarTower R A M] in
/-- The graded-opposite action is conjugation of scalar restriction by the quadratic twist. -/
@[simp]
theorem leftToRight_smul (G : InternalGrading R A) (H : InternalGrading R M)
    (s : (GradedOpposite G)ᵐᵒᵖ) (x : M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    s • x = H.quadraticTwist
      (opAlgEquiv G s • H.quadraticTwist x) := by
  unfold leftToRightModule
  -- Normalize the transferred `AddEquiv` action to the corresponding `LinearEquiv` maps.
  change H.quadraticTwistEquiv.symm
      (opAlgEquiv G s • H.quadraticTwistEquiv x) = _
  rw [H.quadraticTwistEquiv_symm_apply, H.quadraticTwistEquiv_apply]

/-- The ground-ring action commutes with the transported graded-opposite action. -/
theorem leftToRight_isScalarTower (G : InternalGrading R A)
    (H : InternalGrading R M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (opAlgEquiv G).toRingHom
  let _ : IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M :=
    ⟨fun r s x ↦ by
      -- Normalize only the action on `M` supplied by `Module.compHom`.
      change opAlgEquiv G (r • s) • x = r • (opAlgEquiv G s • x)
      rw [map_smul, smul_assoc]⟩
  exact H.quadraticTwistEquiv.isScalarTower (GradedOpposite G)ᵐᵒᵖ

/-- A homogeneous scalar of degree `p` acts on a homogeneous module element of degree `q` by the
original left action multiplied by the Koszul sign `(-1) ^ (p * q)`. -/
theorem leftToRight_smul_of_mem (G : InternalGrading R A) (H : InternalGrading R M)
    [SetLike.GradedSMul G.piece H.piece]
    {p q : ℤ} {a : A} (ha : a ∈ G.piece p) {x : M} (hx : x ∈ H.piece q) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    MulOpposite.op (op G a) • x =
      ((((p * q).negOnePow : ℤ) : R) • (a • x)) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  rw [leftToRight_smul G H]
  rw [opAlgEquiv_op_op, G.quadraticTwist_apply_of_mem ha,
    H.quadraticTwist_apply_of_mem hx]
  rw [smul_assoc, smul_comm a, smul_smul]
  have hax : a • x ∈ H.piece (p + q) := SetLike.GradedSMul.smul_mem ha hx
  rw [map_smul, H.quadraticTwist_apply_of_mem hax]
  simp only [smul_smul]
  apply congrArg (· • (a • x))
  simp only [← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    InternalGrading.negOnePow_quadraticExponent_add]
  have hp : (InternalGrading.quadraticExponent p).negOnePow *
      (InternalGrading.quadraticExponent p).negOnePow = (1 : ℤˣ) :=
    Int.units_mul_self _
  have hq : (InternalGrading.quadraticExponent q).negOnePow *
      (InternalGrading.quadraticExponent q).negOnePow = (1 : ℤˣ) :=
    Int.units_mul_self _
  congr 1
  congr 1
  calc
    (InternalGrading.quadraticExponent p).negOnePow *
        (InternalGrading.quadraticExponent q).negOnePow * (p * q).negOnePow *
        (InternalGrading.quadraticExponent p).negOnePow *
        (InternalGrading.quadraticExponent q).negOnePow =
      (p * q).negOnePow *
        ((InternalGrading.quadraticExponent p).negOnePow *
          (InternalGrading.quadraticExponent p).negOnePow) *
        ((InternalGrading.quadraticExponent q).negOnePow *
          (InternalGrading.quadraticExponent q).negOnePow) := by ac_rfl
    _ = (p * q).negOnePow := by simp [hp, hq]

/-- The transported graded-opposite action adds the scalar degree to the module degree. -/
theorem leftToRight_gradedSMul (G : InternalGrading R A) (H : InternalGrading R M)
    [SetLike.GradedSMul G.piece H.piece] :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (grading G).piece).opposite.piece H.piece := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  constructor
  intro p q s x hs hx
  let a := unop G s.unop
  have hs_unop : s.unop ∈ (grading G).piece p :=
    by simpa only [InternalGrading.ofDecomposition_piece] using
      ((InternalGrading.ofDecomposition (grading G).piece).mem_opposite_piece_iff p s).1 hs
  have ha : a ∈ G.piece p := (mem_piece_iff G p s.unop).1 hs_unop
  have hs' : s = MulOpposite.op (op G a) := by simp [a]
  rw [hs', leftToRight_smul_of_mem G H ha hx]
  exact Submodule.smul_mem _ _ (SetLike.GradedSMul.smul_mem ha hx)

end TauCeti.GradedOpposite
