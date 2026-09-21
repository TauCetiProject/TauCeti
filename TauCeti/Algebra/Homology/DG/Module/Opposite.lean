/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Opposite
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs

/-!
# Left DG modules as right modules over the graded opposite

A left module over an internally graded algebra `A` determines a right module over the
Koszul-signed graded opposite of `A`.  On homogeneous elements of degrees `p` and `q`, the action
is

`x * op(a) = (-1) ^ (p * q) • (a • x)`.

The sign is forced by the right Leibniz rule.  It is produced here without choosing degrees for
arbitrary elements: first restrict scalars along the canonical algebra equivalence
`(GradedOpposite G)ᵐᵒᵖ ≃ₐ[R] A`, then conjugate that action by the quadratic twist of the module.
The identity for the quadratic exponent converts this conjugated action into the displayed Koszul
sign on homogeneous elements, while transport supplies the module laws on all elements.

With this action, a DG left module becomes a DG right module over the graded-opposite DG algebra.
The proof first verifies the right Leibniz rule for homogeneous algebra elements and then uses the
internal direct-sum decomposition to remove that homogeneity assumption.

## Main definitions

* `GradedOpposite.leftToRightModule`: the right action of the graded opposite associated to a
  graded left module.

## Main results

* `GradedOpposite.leftToRight_smul_of_mem`: the action on homogeneous elements is the Koszul-signed
  original left action.
* `GradedOpposite.leftToRight_isScalarTower` and
  `GradedOpposite.leftToRight_gradedSMul`: compatibility with the ground-ring action and the
  module grading.
* `IsDGLeftModule.gradedOppositeRight`: a DG left module is a DG right module over the
  Koszul-signed graded opposite.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The right action of the graded opposite associated to a graded left `A`-module.

It is obtained by restricting scalars along `(GradedOpposite G)ᵐᵒᵖ ≃ₐ[R] A` and conjugating the
result by the quadratic twist of the module grading. -/
noncomputable abbrev leftToRightModule (G : InternalGrading R A) (H : InternalGrading R M) :
    Module (GradedOpposite G)ᵐᵒᵖ M := by
  letI : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (rightModuleAlgEquiv G).toRingHom
  exact H.quadraticTwistEquiv.toAddEquiv.module (GradedOpposite G)ᵐᵒᵖ

omit [IsScalarTower R A M] in
/-- The graded-opposite action is conjugation of scalar restriction by the quadratic twist. -/
theorem leftToRight_smul (G : InternalGrading R A) (H : InternalGrading R M)
    (s : (GradedOpposite G)ᵐᵒᵖ) (x : M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    s • x = H.quadraticTwist
      (rightModuleAlgEquiv G s • H.quadraticTwist x) := by
  -- Unfolding the transferred action exposes the linear equivalence and its inverse.
  change H.quadraticTwistEquiv.symm
      (rightModuleAlgEquiv G s • H.quadraticTwistEquiv x) = _
  rw [H.quadraticTwistEquiv_symm_apply, H.quadraticTwistEquiv_apply]

/-- The ground-ring action commutes with the transported graded-opposite action. -/
theorem leftToRight_isScalarTower (G : InternalGrading R A)
    (H : InternalGrading R M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (rightModuleAlgEquiv G).toRingHom
  let _ : IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M :=
    ⟨fun r s x ↦ by
      -- Unfolding scalar restriction reduces compatibility to that of the algebra equivalence.
      change rightModuleAlgEquiv G (r • s) • x = r • (rightModuleAlgEquiv G s • x)
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
  rw [rightModuleAlgEquiv_op_op, G.quadraticTwist_apply_of_mem ha,
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

/-- The right Leibniz rule for a homogeneous algebra element and homogeneous module element. -/
private theorem leftToRight_leibniz_of_mem
    (G : InternalGrading R A) (H : InternalGrading R M)
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} (hA : IsDGAlgebra G.piece d)
    [DirectSum.Decomposition H.piece] {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM)
    {p q : ℤ} {a : A} (ha : a ∈ G.piece p) {x : M} (hx : x ∈ H.piece q) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    dM (MulOpposite.op (op G a) • x) =
      MulOpposite.op (op G a) • dM x +
        q.negOnePow •
          (MulOpposite.op (GradedOpposite.differential G d (op G a)) • x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  have hdx : dM x ∈ H.piece (q + 1) := hM.isHomogeneous.map_mem hx
  rw [GradedOpposite.differential_op]
  rw [leftToRight_smul_of_mem G H ha hx, map_smul, hM.leibniz ha,
    leftToRight_smul_of_mem G H ha hdx,
    leftToRight_smul_of_mem G H (hA.map_mem ha) hx]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_add, smul_smul]
  have hfirst : (p * q).negOnePow * p.negOnePow = (p * (q + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsecond : q.negOnePow * ((p + 1) * q).negOnePow = (p * q).negOnePow := by
    rw [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    use q
    ring
  rw [add_comm]
  congr 1
  · simpa only [Units.val_mul, Int.cast_mul] using
      congrArg (fun z : ℤˣ ↦ (((z : ℤ) : R) • (a • dM x))) hfirst
  · simpa only [Units.val_mul, Int.cast_mul] using
      congrArg (fun z : ℤˣ ↦ (((z : ℤ) : R) • (d a • x))) hsecond.symm

/-- The right Leibniz rule for an arbitrary algebra element and homogeneous module element. -/
private theorem leftToRight_leibniz
    (G : InternalGrading R A) (H : InternalGrading R M)
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} (hA : IsDGAlgebra G.piece d)
    [DirectSum.Decomposition H.piece] {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM)
    {q : ℤ} {x : M} (hx : x ∈ H.piece q) (b : GradedOpposite G) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    dM (MulOpposite.op b • x) =
      MulOpposite.op b • dM x + q.negOnePow •
        (MulOpposite.op (GradedOpposite.differential G d b) • x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  induction b using DirectSum.Decomposition.inductionOn
      (ℳ := (GradedOpposite.grading G).piece) with
  | zero => simp
  | add b c hb hc =>
      simp only [map_add, MulOpposite.op_add, add_smul, smul_add, hb, hc]
      abel
  | homogeneous b =>
      rw [← GradedOpposite.op_unop G b]
      exact leftToRight_leibniz_of_mem G H hA hM
        ((GradedOpposite.mem_piece_iff G _ b).1 b.property) hx

/-- A differential graded left module over `A` is a differential graded right module over the
Koszul-signed graded opposite of `A`, with action `leftToRightModule`. -/
theorem IsDGLeftModule.gradedOppositeRight
    (G : InternalGrading R A) (H : InternalGrading R M)
    [GradedAlgebra G.piece] [SetLike.GradedSMul G.piece H.piece]
    {d : A →ₗ[R] A} {hA : IsDGAlgebra G.piece d}
    [DirectSum.Decomposition H.piece] {dM : M →ₗ[R] M}
    (hM : IsDGLeftModule hA H.piece dM) :
    @IsDGRightModule R (GradedOpposite G) M _ _ _ _ _
      (leftToRightModule G H) (grading G).piece inferInstance _
      (leftToRight_isScalarTower G H) hA.gradedOpposite H.piece
      (leftToRight_gradedSMul G H) inferInstance dM := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  let _ : IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M := leftToRight_isScalarTower G H
  let _ : SetLike.GradedSMul
      (InternalGrading.ofDecomposition (grading G).piece).opposite.piece H.piece :=
    leftToRight_gradedSMul G H
  exact @IsDGRightModule.mk R (GradedOpposite G) M _ _ _ _ _
    (leftToRightModule G H) (grading G).piece inferInstance _
    (leftToRight_isScalarTower G H) hA.gradedOpposite H.piece
    (leftToRight_gradedSMul G H) inferInstance dM hM.isHomogeneous hM.sq_zero
    (fun hx b ↦ leftToRight_leibniz G H hA hM hx b)

end TauCeti.GradedOpposite
