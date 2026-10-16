/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Components
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# Cohomology of a right A-infinity module

The unary operation of a right `A∞` module squares to zero.  This file packages its cycles,
boundaries, and total cohomology as modules over the ground ring.  The quotient interface is
stated using cycle representatives so morphisms can descend their linear parts without exposing
the implementation of the quotient.

The higher module operations are not used to define the underlying cohomology module.  Their
arity-two identity will subsequently equip it with a right action of the cohomology algebra.

## Main definitions

* `TauCeti.AInfinityRightModule.differential`: the unary module operation as a linear map.
* `TauCeti.AInfinityRightModule.cochainComplex`: the underlying cochain complex of the module.
* `TauCeti.AInfinityRightModule.cycles` and `TauCeti.AInfinityRightModule.boundaries`: its kernel
  and range.
* `TauCeti.AInfinityRightModule.Cohomology`: unary cycles modulo unary boundaries.
* `TauCeti.AInfinityRightModule.cohomologyClass`: the class represented by a cycle.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A} {M : Type uM} [AddCommGroup M] [Module R M]

namespace AInfinityRightModule

/-- The differential of a right `A∞` module, namely its unary operation. -/
noncomputable def differential (MM : AInfinityRightModule AA M) : M →ₗ[R] M :=
  MM.taylor ∘ₗ (TensorProduct.mk R M (TensorWords R A)).flip 1

/-- The module differential evaluates to the unary operation. -/
@[simp]
theorem differential_apply (MM : AInfinityRightModule AA M) (x : M) :
    MM.differential x = MM.m 1 x (fun i ↦ i.elim0) := by
  rw [differential, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    MM.taylor_tmul_one]

/-- The unary operation of a right `A∞` module squares to zero. -/
@[simp]
theorem differential_comp_self_eq_zero (MM : AInfinityRightModule AA M) :
    MM.differential ∘ₗ MM.differential = 0 := by
  ext x
  simp only [LinearMap.comp_apply, differential_apply, LinearMap.zero_apply]
  exact MM.stasheff_arity_one x _ _

/-- The Taylor map on the empty algebra word is the differential. -/
theorem taylor_tmul_one_eq_differential (MM : AInfinityRightModule AA M) (x : M) :
    MM.taylor (x ⊗ₜ[R] (1 : TensorWords R A)) = MM.differential x := by
  rw [differential_apply, taylor_tmul_one]

/-- The differential of a right `A∞` module raises the degree by one. -/
theorem differential_mem_piece (MM : AInfinityRightModule AA M) {p : ℤ} {x : M}
    (hx : x ∈ MM.grading.piece p) : MM.differential x ∈ MM.grading.piece (p + 1) := by
  rw [differential_apply]
  simpa using MM.m_mem_piece 0 hx (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)

/-- The differential of a right `A∞` module is homogeneous of degree one. -/
theorem isHomogeneous_differential (MM : AInfinityRightModule AA M) :
    LinearMap.IsHomogeneous MM.differential MM.grading.piece MM.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ MM.differential_mem_piece hx

/-- The underlying cochain complex of a right `A∞` module: its degree-`p` term is the degree-`p`
part of the module and its differential is the unary operation. -/
abbrev cochainComplex (MM : AInfinityRightModule AA M) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex MM.grading.piece MM.differential MM.isHomogeneous_differential
    fun _ x ↦ LinearMap.congr_fun MM.differential_comp_self_eq_zero x

/-- The cycles of a right `A∞` module are the kernel of its unary operation. -/
def cycles (MM : AInfinityRightModule AA M) : Submodule R M :=
  LinearMap.ker MM.differential

/-- The cycles are the kernel of the module differential. -/
theorem cycles_def (MM : AInfinityRightModule AA M) :
    MM.cycles = LinearMap.ker MM.differential := (rfl)

/-- An element is a cycle exactly when its unary operation vanishes. -/
@[simp]
theorem mem_cycles (MM : AInfinityRightModule AA M) {x : M} :
    x ∈ MM.cycles ↔ MM.differential x = 0 := by
  rw [cycles, LinearMap.mem_ker]

/-- The boundaries of a right `A∞` module are the range of its unary operation. -/
def boundaries (MM : AInfinityRightModule AA M) : Submodule R M :=
  LinearMap.range MM.differential

/-- The boundaries are the range of the module differential. -/
theorem boundaries_def (MM : AInfinityRightModule AA M) :
    MM.boundaries = LinearMap.range MM.differential := (rfl)

/-- An element is a boundary exactly when it is the unary operation of some element. -/
@[simp]
theorem mem_boundaries (MM : AInfinityRightModule AA M) {x : M} :
    x ∈ MM.boundaries ↔ ∃ y : M, MM.differential y = x := by
  rw [boundaries, LinearMap.mem_range]

/-- Every boundary is a cycle. -/
theorem boundaries_le_cycles (MM : AInfinityRightModule AA M) : MM.boundaries ≤ MM.cycles := by
  rintro _ ⟨y, rfl⟩
  rw [mem_cycles]
  exact LinearMap.congr_fun MM.differential_comp_self_eq_zero y

/-- The differential of every element is a boundary. -/
theorem differential_mem_boundaries (MM : AInfinityRightModule AA M) (x : M) :
    MM.differential x ∈ MM.boundaries :=
  ⟨x, rfl⟩

/-- The differential of every element is a cycle. -/
theorem differential_mem_cycles (MM : AInfinityRightModule AA M) (x : M) :
    MM.differential x ∈ MM.cycles :=
  MM.boundaries_le_cycles (MM.differential_mem_boundaries x)

/-- The unary operation of every element is a boundary. -/
theorem m_one_mem_boundaries (MM : AInfinityRightModule AA M) (x : M) :
    MM.m 1 x (fun i ↦ i.elim0) ∈ MM.boundaries := by
  simpa only [differential_apply] using MM.differential_mem_boundaries x

/-- The unary operation of every element is a cycle. -/
theorem m_one_mem_cycles (MM : AInfinityRightModule AA M) (x : M) :
    MM.m 1 x (fun i ↦ i.elim0) ∈ MM.cycles :=
  MM.boundaries_le_cycles (MM.m_one_mem_boundaries x)

/-- The boundaries, viewed as a submodule of the cycles. -/
def boundariesInCycles (MM : AInfinityRightModule AA M) : Submodule R MM.cycles :=
  MM.boundaries.submoduleOf MM.cycles

/-- A cycle lies in `boundariesInCycles` exactly when its underlying element is a boundary. -/
@[simp]
theorem mem_boundariesInCycles (MM : AInfinityRightModule AA M) {x : MM.cycles} :
    x ∈ MM.boundariesInCycles ↔ (x : M) ∈ MM.boundaries := by
  rw [boundariesInCycles, Submodule.submoduleOf, Submodule.mem_comap]
  rfl

/-- The total cohomology module of a right `A∞` module: unary cycles modulo unary boundaries. -/
abbrev Cohomology (MM : AInfinityRightModule AA M) := MM.cycles ⧸ MM.boundariesInCycles

/-- The linear quotient map from cycles to module cohomology. -/
def cohomologyClassLinearMap (MM : AInfinityRightModule AA M) :
    MM.cycles →ₗ[R] MM.Cohomology :=
  MM.boundariesInCycles.mkQ

/-- The cohomology class represented by a module cycle. -/
def cohomologyClass (MM : AInfinityRightModule AA M) {x : M} (hx : x ∈ MM.cycles) :
    MM.Cohomology :=
  MM.cohomologyClassLinearMap ⟨x, hx⟩

/-- A cohomology class is the quotient class of its cycle representative. -/
theorem cohomologyClass_eq_mk (MM : AInfinityRightModule AA M) {x : M} (hx : x ∈ MM.cycles) :
    MM.cohomologyClass hx = Submodule.Quotient.mk ⟨x, hx⟩ := (rfl)

/-- Zero represents zero in module cohomology. -/
@[simp]
theorem cohomologyClass_zero (MM : AInfinityRightModule AA M) :
    MM.cohomologyClass MM.cycles.zero_mem = 0 :=
  MM.cohomologyClassLinearMap.map_zero

/-- The class of a sum of module cycles is the sum of their classes. -/
@[simp]
theorem cohomologyClass_add (MM : AInfinityRightModule AA M) {x y : M}
    (hx : x ∈ MM.cycles) (hy : y ∈ MM.cycles) :
    MM.cohomologyClass (MM.cycles.add_mem hx hy) =
      MM.cohomologyClass hx + MM.cohomologyClass hy :=
  MM.cohomologyClassLinearMap.map_add ⟨x, hx⟩ ⟨y, hy⟩

/-- The class of a scalar multiple of a module cycle is the scalar multiple of its class. -/
@[simp]
theorem cohomologyClass_smul (MM : AInfinityRightModule AA M) (r : R) {x : M}
    (hx : x ∈ MM.cycles) :
    MM.cohomologyClass (MM.cycles.smul_mem r hx) = r • MM.cohomologyClass hx :=
  MM.cohomologyClassLinearMap.map_smul r ⟨x, hx⟩

/-- Every module cohomology class has a cycle representative. -/
theorem exists_cohomologyClass_eq (MM : AInfinityRightModule AA M) (c : MM.Cohomology) :
    ∃ (x : M) (hx : x ∈ MM.cycles), MM.cohomologyClass hx = c := by
  induction c using Submodule.Quotient.induction_on with
  | H x => exact ⟨x, x.2, rfl⟩

/-- Two module cycles represent the same cohomology class exactly when their difference is a
boundary. -/
@[simp]
theorem cohomologyClass_eq_iff (MM : AInfinityRightModule AA M) {x y : M}
    (hx : x ∈ MM.cycles) (hy : y ∈ MM.cycles) :
    MM.cohomologyClass hx = MM.cohomologyClass hy ↔ x - y ∈ MM.boundaries := by
  simp only [cohomologyClass, cohomologyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, mem_boundariesInCycles]
  rfl

/-- A module cycle represents zero in cohomology exactly when it is a boundary. -/
@[simp]
theorem cohomologyClass_eq_zero_iff (MM : AInfinityRightModule AA M) {x : M}
    (hx : x ∈ MM.cycles) : MM.cohomologyClass hx = 0 ↔ x ∈ MM.boundaries := by
  simp only [cohomologyClass, cohomologyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, mem_boundariesInCycles]

/-- The cohomology class of a unary operation is zero. -/
@[simp]
theorem cohomologyClass_m_one_eq_zero (MM : AInfinityRightModule AA M) (x : M) :
    MM.cohomologyClass (MM.m_one_mem_cycles x) = 0 :=
  (MM.cohomologyClass_eq_zero_iff _).2 (MM.m_one_mem_boundaries x)

end AInfinityRightModule

end TauCeti
