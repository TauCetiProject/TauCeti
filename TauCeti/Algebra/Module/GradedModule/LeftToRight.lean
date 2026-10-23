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
* `GradedOpposite.leftToRight_smul_of_mem_of_even`: a homogeneous scalar of even degree acts by
  the original left action, with no sign.
* `GradedOpposite.leftToRight_isScalarTower` and
  `GradedOpposite.leftToRight_gradedSMul`: compatibility with the ground-ring action and the
  module grading.
* `GradedOpposite.leftToRight_leibniz_iff`: a differential satisfies the right graded Leibniz rule
  for the transported action exactly when it satisfies the left graded Leibniz rule.

The sign convention follows B. Keller, *Introduction to A-infinity algebras and modules*,
Section 3.1.
-/

public section

namespace TauCeti.GradedOpposite

universe uR uA uM

section Action

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

/-- A homogeneous scalar of even degree acts through the graded opposite by the original left
action, on every module element: the Koszul sign `(-1) ^ (p * q)` is trivial on each homogeneous
component. -/
theorem leftToRight_smul_of_mem_of_even (G : InternalGrading R A) (H : InternalGrading R M)
    [SetLike.GradedSMul G.piece H.piece]
    {p : ℤ} {a : A} (ha : a ∈ G.piece p) (hp : Even p) (x : M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    MulOpposite.op (op G a) • x = a • x := by
  classical
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  rw [← DirectSum.sum_support_decompose H.piece x, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [leftToRight_smul_of_mem G H ha (SetLike.coe_mem _),
    Int.negOnePow_even _ (hp.mul_right q), Units.val_one, Int.cast_one, one_smul]

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

end Action

section Differential

/-!
### Differentials

A linear endomorphism `dM` of a graded left module satisfies the left graded Leibniz rule
`dM (a • x) = d a • x + (-1) ^ |a| • (a • dM x)` exactly when it satisfies the right graded Leibniz
rule `dM (x * b) = dM x * b + (-1) ^ |x| • (x * d b)` for the transported action of the graded
opposite. Only the degree laws of `d` and `dM` are used, so the comparison serves differential
graded and curved differential graded modules alike; the square-zero and curvature laws are added
by their respective theories.
-/

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (G : InternalGrading R A) (H : InternalGrading R M) [SetLike.GradedSMul G.piece H.piece]
  {d : A →ₗ[R] A} {dM : M →ₗ[R] M}

/-- The two Leibniz rules agree on a homogeneous scalar and a homogeneous module element. Both
sides of the right-handed rule are the left-handed rule multiplied by the Koszul sign
`(-1) ^ (p * q)`. -/
private theorem leftToRight_leibniz_of_mem_iff
    (hd : ∀ {p : ℤ} {a : A}, a ∈ G.piece p → d a ∈ G.piece (p + 1))
    (hdM : ∀ {q : ℤ} {x : M}, x ∈ H.piece q → dM x ∈ H.piece (q + 1))
    {p q : ℤ} {a : A} (ha : a ∈ G.piece p) {x : M} (hx : x ∈ H.piece q) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    (dM (MulOpposite.op (op G a) • x) =
      MulOpposite.op (op G a) • dM x + q.negOnePow • (MulOpposite.op (op G (d a)) • x)) ↔
    dM (a • x) = d a • x + p.negOnePow • (a • dM x) := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  have hcast (u : ℤˣ) (y : M) : ((u : ℤ) : R) • y = u • y := by
    rw [Int.cast_smul_eq_zsmul, Units.smul_def]
  rw [leftToRight_smul_of_mem G H ha hx, leftToRight_smul_of_mem G H ha (hdM hx),
    leftToRight_smul_of_mem G H (hd ha) hx, map_smul, hcast, hcast, hcast,
    ← smul_left_cancel_iff (p * q).negOnePow (x := dM (a • x)), smul_add, smul_smul, smul_smul]
  have hfirst : (p * q).negOnePow * p.negOnePow = (p * (q + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsecond : q.negOnePow * ((p + 1) * q).negOnePow = (p * q).negOnePow := by
    rw [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    use q
    ring
  rw [hfirst, hsecond, add_comm]

/-- **Left and right graded Leibniz rules.** For degree-raising `d` and `dM`, the differential
`dM` satisfies the right graded Leibniz rule for the action of the graded opposite transported by
`leftToRightModule`, on homogeneous module elements and arbitrary scalars, exactly when it
satisfies the left graded Leibniz rule on homogeneous scalars and arbitrary module elements. -/
theorem leftToRight_leibniz_iff
    (hd : ∀ {p : ℤ} {a : A}, a ∈ G.piece p → d a ∈ G.piece (p + 1))
    (hdM : ∀ {q : ℤ} {x : M}, x ∈ H.piece q → dM x ∈ H.piece (q + 1)) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    (∀ {q : ℤ} {x : M}, x ∈ H.piece q → ∀ b : GradedOpposite G,
      dM (MulOpposite.op b • x) =
        MulOpposite.op b • dM x + q.negOnePow • (MulOpposite.op (differential G d b) • x)) ↔
    ∀ {p : ℤ} {a : A}, a ∈ G.piece p → ∀ x : M,
      dM (a • x) = d a • x + p.negOnePow • (a • dM x) := by
  classical
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
  constructor
  · intro hR p a ha x
    rw [← DirectSum.sum_support_decompose H.piece x]
    simp only [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hq := SetLike.coe_mem (DirectSum.decompose H.piece x q)
    refine (leftToRight_leibniz_of_mem_iff G H hd hdM ha hq).1 ?_
    rw [hR hq, differential_op]
  · intro hL q x hx b
    induction b using DirectSum.Decomposition.inductionOn
        (ℳ := (GradedOpposite.grading G).piece) with
    | zero => simp
    | add b c hb hc =>
        simp only [map_add, MulOpposite.op_add, add_smul, smul_add, hb, hc]
        abel
    | homogeneous b =>
        have hb := (GradedOpposite.mem_piece_iff G _ b).1 b.property
        rw [← GradedOpposite.op_unop G b, differential_op]
        exact (leftToRight_leibniz_of_mem_iff G H hd hdM hb hx).2 (hL hb x)

end Differential

end TauCeti.GradedOpposite
