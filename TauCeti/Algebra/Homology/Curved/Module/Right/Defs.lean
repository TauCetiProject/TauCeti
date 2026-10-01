/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Defs
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs

/-!
# Curved differential graded right modules

A curved differential graded right module over a curved differential graded algebra has a
degree-one differential satisfying the graded Leibniz rule

`dM (x * a) = dM x * a + (-1) ^ |x| * (x * d a)`

and the curvature equation `dM (dM x) = x * w`.  The latter replaces the square-zero axiom of an
ordinary differential graded module.  The algebra curvature convention
`d (d a) = a * w - w * a` is exactly the one compatible with this right-module equation.

In Lean, a right `A`-module is represented as a left module over `Aᵐᵒᵖ`, so `x * a` is written
`MulOpposite.op a • x`.  The grading on `Aᵐᵒᵖ` is transported from the internal grading of `A`;
the module action itself has no extra sign.

Unlike ordinary differential graded modules, curved modules do not generally have cohomology:
the image of their differential need not lie in its kernel.  The zero-curvature comparison below
therefore returns the existing ordinary DG-module structure before any cohomology is formed.

## Main definitions

* `TauCeti.IsCurvedDGRightModule`: the curved differential graded right-module axioms.
* `TauCeti.CurvedDGRightModuleCat`: bundled curved differential graded right modules, the objects
  of the differential graded category of curved modules.

## Main results

* `TauCeti.IsCurvedDGRightModule.map_decompose`: the differential commutes with homogeneous
  projections up to its degree-one shift.
* `TauCeti.IsCurvedDGRightModule.leibniz_of_map_eq_zero`: cycles of the algebra act compatibly
  with the module differential, without a homogeneity assumption on the module element.
* `TauCeti.IsCurvedDGRightModule.toIsDGRightModule_of_curvature_eq_zero`: zero curvature turns a
  curved right module into an ordinary differential graded right module.
* `TauCeti.isCurvedDGRightModule_zero_iff`: the curved and ordinary notions agree at curvature
  zero.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  His curvature is the negative of the right-module curvature used here.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- A **curved differential graded right module** over the curved differential graded algebra
`(𝒜, d, w)`.  Its differential raises degree by one, obeys the right graded Leibniz rule, and
squares to right multiplication by the curvature. -/
structure IsCurvedDGRightModule [IsScalarTower R Aᵐᵒᵖ M]
    (h : IsCurvedDGAlgebra 𝒜 d w) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ]
    (dM : M →ₗ[R] M) : Prop where
  /-- The differential raises degree by one. -/
  isHomogeneous : LinearMap.IsHomogeneous dM ℳ ℳ 1
  /-- The graded right Leibniz rule for a module element of degree `q`. -/
  leibniz : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
    dM (op a • x) = op a • dM x + q.negOnePow • (op (d a) • x)
  /-- The differential squares to right multiplication by the curvature. -/
  sq_eq (x : M) : dM (dM x) = op w • x

variable {h : IsCurvedDGAlgebra 𝒜 d w} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

namespace IsCurvedDGRightModule

/-- The differential of a curved differential graded right module commutes with homogeneous
projections, up to its degree-one shift. -/
@[simp]
theorem map_decompose (hM : IsCurvedDGRightModule h ℳ dM) (q : ℤ) (x : M) :
    dM (decompose ℳ x q : M) = (decompose ℳ (dM x) (q + 1) : M) :=
  DirectSum.map_decompose_shift ℳ ℳ dM (· + 1) (add_left_injective 1)
    (fun _ _ hy ↦ hM.isHomogeneous.map_mem hy) q x

/-- The right Leibniz rule against a cycle of the algebra.  The signed term vanishes, so the
module element need not be homogeneous. -/
theorem leibniz_of_map_eq_zero (hM : IsCurvedDGRightModule h ℳ dM) (x : M) {a : A}
    (ha : d a = 0) : dM (op a • x) = op a • dM x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ x, Finset.smul_sum, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ x, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hM.leibniz (SetLike.coe_mem _) a, ha, op_zero, zero_smul, smul_zero, add_zero]

/-- The curvature action commutes with the module differential. -/
theorem map_op_curvature_smul (hM : IsCurvedDGRightModule h ℳ dM) (x : M) :
    dM (op w • x) = op w • dM x :=
  hM.leibniz_of_map_eq_zero x h.map_curvature

/-- A curved differential graded right module whose curvature is zero is an ordinary differential
graded right module. -/
theorem toIsDGRightModule_of_curvature_eq_zero (hM : IsCurvedDGRightModule h ℳ dM) (hw : w = 0) :
    IsDGRightModule (h.toIsDGAlgebra_of_curvature_eq_zero hw) ℳ dM where
  isHomogeneous := hM.isHomogeneous
  sq_zero x := by rw [hM.sq_eq, hw, op_zero, zero_smul]
  leibniz := hM.leibniz

end IsCurvedDGRightModule

variable {hDG : IsDGAlgebra 𝒜 d}

/-- An ordinary differential graded right module is a curved one with curvature zero. -/
theorem IsDGRightModule.isCurvedDGRightModule_zero
    (hM : IsDGRightModule hDG ℳ dM) :
    IsCurvedDGRightModule hDG.isCurvedDGAlgebra_zero ℳ dM where
  isHomogeneous := hM.isHomogeneous
  leibniz := hM.leibniz
  sq_eq x := by rw [hM.sq_zero, op_zero, zero_smul]

/-- **Zero curvature.** Curved differential graded right modules over an algebra of curvature
zero are exactly ordinary differential graded right modules. -/
theorem isCurvedDGRightModule_zero_iff :
    IsCurvedDGRightModule hDG.isCurvedDGAlgebra_zero ℳ dM ↔ IsDGRightModule hDG ℳ dM := by
  constructor
  · intro hM
    exact hM.toIsDGRightModule_of_curvature_eq_zero rfl
  · exact IsDGRightModule.isCurvedDGRightModule_zero

/-! ### Bundled curved modules -/

/-- A bundled curved differential graded right module over the curved differential graded
algebra `h`. -/
structure CurvedDGRightModuleCat (h : IsCurvedDGAlgebra 𝒜 d w) where
  /-- The underlying module. -/
  carrier : Type uM
  [addCommGroup : AddCommGroup carrier]
  [moduleBase : Module R carrier]
  [moduleOp : Module Aᵐᵒᵖ carrier]
  [scalarTower : IsScalarTower R Aᵐᵒᵖ carrier]
  /-- The internal grading of the module. -/
  grading : ℤ → Submodule R carrier
  [decomposition : DirectSum.Decomposition grading]
  [gradedSMul : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece grading]
  /-- The module differential. -/
  differential : carrier →ₗ[R] carrier
  /-- The differential and action satisfy the curved DG right-module laws. -/
  isCurvedDGRightModule : IsCurvedDGRightModule h grading differential

namespace CurvedDGRightModuleCat

attribute [instance] addCommGroup moduleBase moduleOp scalarTower decomposition gradedSMul

instance : CoeSort (CurvedDGRightModuleCat.{uR, uA, uM} h) (Type uM) := ⟨carrier⟩

/-- Bundle a curved differential graded right module with its existing structures. -/
abbrev of (hM : IsCurvedDGRightModule h ℳ dM) : CurvedDGRightModuleCat h where
  carrier := M
  grading := ℳ
  differential := dM
  isCurvedDGRightModule := hM

end CurvedDGRightModuleCat

end TauCeti
