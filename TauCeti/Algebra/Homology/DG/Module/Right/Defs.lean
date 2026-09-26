/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Defs
public import TauCeti.Algebra.Module.GradedModule.Opposite

/-!
# Differential graded right modules

A differential graded right module over an internally graded differential graded algebra has a
degree-one, square-zero differential satisfying

`dM (x * a) = dM x * a + (-1) ^ |x| * (x * d a)`

for homogeneous `x`.  In Lean a right `A`-module is represented as a left module over `Aᵐᵒᵖ`, so
the action `x * a` is written `MulOpposite.op a • x`.  The source grading on `Aᵐᵒᵖ` is obtained by
transporting the grading of `A` along `MulOpposite.op`; no sign is inserted into the action itself.

The homogeneous Leibniz rule extends to useful statements on arbitrary elements.  In particular,
cycles act on cycles, cycles of the algebra preserve module boundaries, and differentials in the
algebra act by boundaries on module cycles.  These are the facts needed to make the cohomology of
a right DG module into a right module over the cohomology algebra.

## Main definitions

* `TauCeti.IsDGRightModule`: the differential graded right-module axioms on an internally graded
  module over a differential graded algebra.

## Main results

* `TauCeti.IsDGRightModule.leibniz_of_map_eq_zero`: the Leibniz rule against an algebra cycle,
  without a homogeneity assumption on the module element.
* `TauCeti.IsDGRightModule.op_smul_mem_range_of_map_eq_zero`: an algebra cycle preserves module
  boundaries.
* `TauCeti.IsDGRightModule.op_map_smul_mem_range_of_map_eq_zero`: the differential of an algebra
  element acts by a boundary on a module cycle.
* `TauCeti.isDGRightModule_zero`: a graded right module with zero differential is a DG right
  module over a graded algebra with zero differential.
* `TauCeti.IsDGAlgebra.isDGRightModule`: a differential graded algebra is a differential graded
  right module over itself, the free rank-one right module.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- A **differential graded right module** over the differential graded algebra `(𝒜, d)`.  The
right action by `a : A` is written `op a • x`.  The differential raises degree by one, squares to
zero, and obeys the right graded Leibniz rule on homogeneous module elements. -/
structure IsDGRightModule [IsScalarTower R Aᵐᵒᵖ M]
    (h : IsDGAlgebra 𝒜 d) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ]
    (dM : M →ₗ[R] M) : Prop where
  /-- The differential raises the degree by one. -/
  isHomogeneous : LinearMap.IsHomogeneous dM ℳ ℳ 1
  /-- The differential squares to zero. -/
  sq_zero (x : M) : dM (dM x) = 0
  /-- The graded right Leibniz rule for a module element of degree `q`. -/
  leibniz : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
    dM (op a • x) = op a • dM x + q.negOnePow • (op (d a) • x)

variable {h : IsDGAlgebra 𝒜 d} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

namespace IsDGRightModule

/-- The differential of a differential graded right module commutes with homogeneous projections,
up to the shift by one that it applies to degrees. -/
theorem map_decompose (hM : IsDGRightModule h ℳ dM) (q : ℤ) (x : M) :
    dM (decompose ℳ x q : M) = (decompose ℳ (dM x) (q + 1) : M) :=
  DirectSum.map_decompose_shift ℳ ℳ dM (· + 1) (add_left_injective 1)
    (fun _ _ hy ↦ hM.isHomogeneous.map_mem hy) q x

/-- Every homogeneous projection of a boundary is again a boundary. -/
theorem decompose_mem_range (hM : IsDGRightModule h ℳ dM) {x : M}
    (hx : x ∈ LinearMap.range dM) (q : ℤ) :
    (decompose ℳ x q : M) ∈ LinearMap.range dM := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(decompose ℳ y (q - 1) : M), ?_⟩
  have key := hM.map_decompose (q - 1) y
  rw [sub_add_cancel q (1 : ℤ)] at key
  exact key

/-- The homogeneous components of a cycle are cycles. -/
theorem map_decompose_eq_zero (hM : IsDGRightModule h ℳ dM) {x : M} (hx : dM x = 0)
    (q : ℤ) : dM (decompose ℳ x q : M) = 0 := by
  rw [hM.map_decompose, hx, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero]

/-- The right Leibniz rule against a cycle of the algebra.  The sign disappears with the term it
multiplies, so the module element need not be homogeneous. -/
theorem leibniz_of_map_eq_zero (hM : IsDGRightModule h ℳ dM) (x : M) {a : A}
    (ha : d a = 0) : dM (op a • x) = op a • dM x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ x, Finset.smul_sum, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ x, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.leibniz (SetLike.coe_mem _) a, ha, op_zero, zero_smul, smul_zero, add_zero]

/-- A cycle of the algebra acts on a cycle of the right module to give a cycle. -/
theorem map_op_smul_eq_zero_of_map_eq_zero (hM : IsDGRightModule h ℳ dM) {a : A} {x : M}
    (ha : d a = 0) (hx : dM x = 0) : dM (op a • x) = 0 := by
  rw [hM.leibniz_of_map_eq_zero x ha, hx, smul_zero]

/-- A homogeneous module element multiplied by the differential of an algebra element is, up to
the sign of its degree, the difference between the differential of the product and the product of
the module differential. -/
theorem op_map_smul_eq_negOnePow_smul_sub (hM : IsDGRightModule h ℳ dM) {q : ℤ} {x : M}
    (hx : x ∈ ℳ q) (a : A) :
    op (d a) • x = q.negOnePow • (dM (op a • x) - op a • dM x) := by
  rw [hM.leibniz hx a, add_sub_cancel_left, smul_smul, Int.units_mul_self, one_smul]

/-- A cycle of the algebra preserves boundaries of the right module. -/
theorem op_smul_mem_range_of_map_eq_zero (hM : IsDGRightModule h ℳ dM) {a : A}
    (ha : d a = 0) {y : M} (hy : y ∈ LinearMap.range dM) :
    op a • y ∈ LinearMap.range dM := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨op a • x, hM.leibniz_of_map_eq_zero x ha⟩

/-- The differential of an algebra element acts by a boundary on every cycle of the right module.
The witness is assembled degreewise because the sign depends on the degree of the module element.
-/
theorem op_map_smul_mem_range_of_map_eq_zero (hM : IsDGRightModule h ℳ dM) (a : A) {x : M}
    (hx : dM x = 0) : op (d a) • x ∈ LinearMap.range dM := by
  classical
  rw [← DirectSum.sum_support_decompose ℳ x, Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ =>
    ⟨q.negOnePow • (op a • (decompose ℳ x q : M)), ?_⟩
  rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  have hcycle := hM.map_decompose_eq_zero hx q
  have key := (hM.op_map_smul_eq_negOnePow_smul_sub
    (x := (decompose ℳ x q : M)) (SetLike.coe_mem _) a).symm
  rw [hcycle, smul_zero, sub_zero] at key
  exact key

end IsDGRightModule

/-- A differential graded algebra is a differential graded right module over itself, the **free
rank-one** right module.  Its Leibniz rule is the algebra Leibniz rule, whose sign is carried by
the module element because that is the left-hand factor of the product. -/
theorem IsDGAlgebra.isDGRightModule (h : IsDGAlgebra 𝒜 d) : IsDGRightModule h 𝒜 d where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha
  sq_zero := h.sq_zero
  leibniz {_ _} hx a := by
    simp only [op_smul_eq_mul]
    exact h.leibniz hx a

/-- A graded right module with zero differential over a graded algebra with zero differential is a
differential graded right module. -/
theorem isDGRightModule_zero (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] :
    IsDGRightModule (isDGAlgebra_zero 𝒜) ℳ (0 : M →ₗ[R] M) where
  isHomogeneous := LinearMap.isHomogeneous_zero ℳ ℳ 1
  sq_zero _ := rfl
  leibniz := fun _ _ => by simp

end TauCeti
