/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# An integral-basis presentation of the complementary module

Let `A` have fraction field `K`, and let the finite free `A`-algebra `B` become the
finite separable field extension `L / K` after inverting the nonzero elements of `A`.
The trace-dual basis of an `A`-basis of `B` is an `A`-basis of the complementary
module `Bᵛ = {x ∈ L | Tr(x B) ⊆ A}`, constructed as
`Module.Basis.traceDualIntegralBasis`.

The inclusion `B → Bᵛ` is represented by the trace Gram matrix, including when `B`
is a nonmaximal order. The equivalence
`Module.Basis.traceDualQuotientEquiv` presents `Bᵛ / B` as its cokernel. In particular
it reduces computation of the complementary-module quotient to linear algebra over `A`, without any
separability assumption on residue fields or a monogenicity assumption on `B`.

The construction uses Mathlib's `Module.Basis.traceDual`,
`Submodule.traceDual_span_of_basis`, and localization of bases.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §3 (the complementary module and discriminant).
-/

public section

open Module
open scoped nonZeroDivisors

namespace Module.Basis

variable {A K B L ι : Type*} [CommRing A] [IsDomain A] [Field K]
  [CommRing B] [Field L] [Algebra A K] [Algebra A B] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Finite ι] [DecidableEq ι]

variable (b : Basis ι A B)

omit [IsDomain A] in
/-- The complementary module is spanned over the base ring by the field trace-dual basis. -/
theorem dualSubmodule_one_eq_span_traceDual :
    (Algebra.traceForm K L).dualSubmodule ((1 : Submodule B L).restrictScalars A) =
      Submodule.span A (Set.range (b.localizationLocalization K A⁰ L).traceDual) := by
  have hspan : (1 : Submodule B L).restrictScalars A =
      Submodule.span A (Set.range (b.localizationLocalization K A⁰ L)) := by
    rw [Basis.localizationLocalization_span]
    ext x
    simp [Submodule.one_eq_range]
  simpa only [Submodule.restrictScalars_traceDual] using
    Submodule.traceDual_span_of_basis A (1 : Submodule B L)
      (b.localizationLocalization K A⁰ L) hspan

/-- The trace-dual basis of an integral lattice, as a basis of its complementary module. -/
noncomputable def traceDualIntegralBasis :
    Basis ι A ((Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars A)) :=
  ((b.localizationLocalization K A⁰ L).traceDual.restrictScalars A).map
    (LinearEquiv.ofEq _ _ b.dualSubmodule_one_eq_span_traceDual.symm)

/-- The vectors of the complementary-module basis are the field trace-dual vectors. -/
@[simp]
theorem coe_traceDualIntegralBasis (i : ι) :
    (b.traceDualIntegralBasis (K := K) (L := L) i : L) =
      (b.localizationLocalization K A⁰ L).traceDual i := by
  rw [traceDualIntegralBasis, Basis.map_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (Basis.restrictScalars_apply _ _ _)

/-- Coordinates in the complementary-module basis are the traces against the original basis. -/
@[simp]
theorem algebraMap_traceDualIntegralBasis_repr
    (x : (Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars A)) (i : ι) :
    algebraMap A K ((b.traceDualIntegralBasis (K := K) (L := L)).repr x i) =
      Algebra.trace K L ((x : L) * algebraMap B L (b i)) := by
  classical
  simp only [traceDualIntegralBasis, Basis.map_repr, LinearEquiv.trans_apply,
    Basis.restrictScalars_repr_apply, Basis.traceDual_repr_apply,
    Algebra.traceForm_apply, Basis.localizationLocalization_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]

omit [DecidableEq ι] in
/-- The inclusion of the finite free algebra `B` into its complementary module inside `L`.
The image lies in the trace dual because localization identifies traces of products in `B`
with images of their traces in `A`. -/
noncomputable def algebraToTraceDual :
    B →ₗ[A] (Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars A) := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  refine (IsScalarTower.toAlgHom A B L).toLinearMap.codRestrict _ fun x ↦ ?_
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hy
  rw [Algebra.traceForm_apply, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
    ← map_mul, Algebra.trace_localization A A⁰]
  exact Submodule.mem_one.mpr ⟨Algebra.trace A B (x * y), rfl⟩

omit [IsDomain A] [FiniteDimensional K L] [Algebra.IsSeparable K L] [DecidableEq ι] in
/-- The inclusion into the complementary module is the usual embedding in `L`. -/
@[simp]
theorem coe_algebraToTraceDual (x : B) :
    (b.algebraToTraceDual (K := K) (L := L) x : L) = algebraMap B L x :=
  (rfl)

omit [IsDomain A] [FiniteDimensional K L] [Algebra.IsSeparable K L] [DecidableEq ι] in
/-- The inclusion of a finite free algebra in its trace dual is injective. -/
theorem algebraToTraceDual_injective :
    Function.Injective (b.algebraToTraceDual (K := K) (L := L)) := by
  intro x y h
  apply b.repr.injective
  ext i
  apply IsFractionRing.injective A K
  simpa only [coe_algebraToTraceDual, Basis.localizationLocalization_repr_algebraMap] using
    congrArg (fun z : L ↦ (b.localizationLocalization K A⁰ L).repr z i)
      (congrArg Subtype.val h)

/-- In trace-dual coordinates, the inclusion of an integral basis is its trace Gram matrix. -/
@[simp]
theorem traceDualIntegralBasis_repr_algebraToTraceDual (x : B) (i : ι) :
    (b.traceDualIntegralBasis (K := K) (L := L)).repr
      (b.algebraToTraceDual (K := K) (L := L) x) i =
        Algebra.trace A B (x * b i) := by
  apply IsFractionRing.injective A K
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  rw [b.algebraMap_traceDualIntegralBasis_repr, coe_algebraToTraceDual,
    ← map_mul, Algebra.trace_localization A A⁰]

variable [Fintype ι]

/-- The matrix of the algebra inclusion, with the trace-dual basis in the target,
is the trace matrix of the original integral basis. -/
theorem toMatrix_algebraToTraceDual :
    LinearMap.toMatrix b (b.traceDualIntegralBasis (K := K) (L := L))
      (b.algebraToTraceDual (K := K) (L := L)) = Algebra.traceMatrix A b := by
  ext i j
  rw [LinearMap.toMatrix_apply, traceDualIntegralBasis_repr_algebraToTraceDual,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]

/-- The trace-dual coordinate map intertwines the algebra inclusion and its trace Gram matrix. -/
theorem traceDualIntegralBasis_equivFun_comp_algebraToTraceDual :
    (b.traceDualIntegralBasis (K := K) (L := L)).equivFun.toLinearMap ∘ₗ
        b.algebraToTraceDual (K := K) (L := L) =
      Matrix.mulVecLin (Algebra.traceMatrix A b) ∘ₗ b.equivFun.toLinearMap := by
  ext x : 1
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_apply,
    Matrix.mulVecLin_apply, b.toMatrix_algebraToTraceDual] using
    (LinearMap.toMatrix_mulVec_repr b
      (b.traceDualIntegralBasis (K := K) (L := L))
      (b.algebraToTraceDual (K := K) (L := L)) x).symm

/-- The complementary-module quotient by the algebra is the cokernel of the trace
Gram matrix, over the original coefficient ring. -/
noncomputable def traceDualQuotientEquiv :
    (((Algebra.traceForm K L).dualSubmodule ((1 : Submodule B L).restrictScalars A)) ⧸
        LinearMap.range (b.algebraToTraceDual (K := K) (L := L))) ≃ₗ[A]
      ((ι → A) ⧸ LinearMap.range (Matrix.mulVecLin (Algebra.traceMatrix A b))) := by
  apply Submodule.Quotient.equiv _ _
    (b.traceDualIntegralBasis (K := K) (L := L)).equivFun
  rw [← LinearMap.range_comp, b.traceDualIntegralBasis_equivFun_comp_algebraToTraceDual,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

/-- On representatives, the cokernel presentation sends `x` to its trace-pairing coordinates. -/
@[simp]
theorem traceDualQuotientEquiv_mk
    (x : (Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars A)) :
    b.traceDualQuotientEquiv (K := K) (L := L) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((b.traceDualIntegralBasis (K := K) (L := L)).equivFun x) :=
  (rfl)

/-- The inverse cokernel presentation reconstructs a complementary-module element from its
trace-pairing coordinates. -/
@[simp]
theorem traceDualQuotientEquiv_symm_mk (v : ι → A) :
    (b.traceDualQuotientEquiv (K := K) (L := L)).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((b.traceDualIntegralBasis (K := K) (L := L)).equivFun.symm v) :=
  (rfl)

end Module.Basis
