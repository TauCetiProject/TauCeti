/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs

/-!
# The cohomology of a differential graded right module

Let `M` be a differential graded right module over a differential graded algebra `A`. Its cycles
are the kernel of the module differential and its boundaries are the image. The cycles form a
right module over the algebra cycles, the boundaries form a right submodule, and the resulting
quotient `H(M)` is a right module over the cohomology algebra `H(A)`.

Right modules are represented as left modules over the opposite ring. Thus the scalar ring of the
cycle module is `cycles(A)ᵐᵒᵖ`, while that of the cohomology module is `H(A)ᵐᵒᵖ`. The latter action
is obtained by descending the former through the boundary ideal. This keeps the handedness visible
in types and ensures that multiplication in the opposite ring encodes the usual right-module
associativity law.

The cycles inherit the grading of `M`. Their homogeneous pieces form an internal direct sum and
make them a graded right module over the graded algebra of cycles.

This development adapts the left-module construction in
`TauCeti.Algebra.Homology.DG.Module.Cohomology` to right modules via opposite rings.

## Main definitions

* `TauCeti.IsDGRightModule.cycles`: module cycles, as a right module over algebra cycles.
* `TauCeti.IsDGRightModule.boundaries`: module boundaries inside the cycles.
* `TauCeti.IsDGRightModule.Cohomology`: cycles modulo boundaries.
* `TauCeti.IsDGRightModule.cyclesDeg`: the homogeneous cycles of a fixed degree.

## Main results

* `TauCeti.IsDGRightModule.instModuleCohomology`: `H(M)` is a right module over `H(A)`.
* `TauCeti.IsDGRightModule.op_quotientMk_smul`: the descended action is computed on cycle
  representatives.
* `TauCeti.IsDGRightModule.instGradedSMulCyclesDeg`: the cycles are a graded right module over the
  graded algebra of cycles.
* `TauCeti.IsDGRightModule.isInternal_cyclesDeg`: the homogeneous cycle spaces form an internal
  direct sum.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 4.1.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

namespace IsDGAlgebra

/-- Restriction of the right `A`-action to the opposite of the algebra of cycles. -/
noncomputable instance instModuleOppositeCycles (h : IsDGAlgebra 𝒜 d) :
    Module (h.cycles)ᵐᵒᵖ M :=
  Module.compHom M h.cycles.val.op.toRingHom

/-- The restricted cycle action is compatible with the action of the ground ring. -/
noncomputable instance instIsScalarTowerOppositeCycles (h : IsDGAlgebra 𝒜 d) :
    IsScalarTower R (h.cycles)ᵐᵒᵖ M :=
  ⟨fun r a x => by
    rw [Algebra.smul_def]
    -- Expose the restricted scalar action to apply the ambient scalar-tower equation.
    change h.cycles.val.op.toRingHom ((algebraMap R (h.cycles)ᵐᵒᵖ) r * a) • x = _
    rw [map_mul, mul_smul]
    change (algebraMap R Aᵐᵒᵖ) r • op (a.unop : A) • x =
      r • op (a.unop : A) • x
    rw [algebraMap_smul]⟩

end IsDGAlgebra

namespace IsDGRightModule

/-- The cycles of a differential graded right module, as a right module over the algebra cycles. -/
def cycles (hM : IsDGRightModule h ℳ dM) : Submodule (h.cycles)ᵐᵒᵖ M :=
  { (LinearMap.ker dM).toAddSubmonoid with
    smul_mem' := fun z _ hx =>
      hM.map_op_smul_eq_zero_of_map_eq_zero (h.mem_cycles.mp z.unop.2) hx }

/-- An element is a module cycle exactly when its differential vanishes. -/
@[simp]
lemma mem_cycles (hM : IsDGRightModule h ℳ dM) {x : M} :
    x ∈ hM.cycles ↔ dM x = 0 :=
  Iff.rfl

/-- The differential of every module element is a cycle. -/
theorem map_mem_cycles (hM : IsDGRightModule h ℳ dM) (x : M) : dM x ∈ hM.cycles :=
  hM.sq_zero x

/-- The boundaries of a differential graded right module, as a right submodule of its cycles. -/
noncomputable def boundaries (hM : IsDGRightModule h ℳ dM) :
    Submodule (h.cycles)ᵐᵒᵖ hM.cycles :=
  { (LinearMap.range dM).toAddSubmonoid.comap hM.cycles.subtype.toAddMonoidHom with
    smul_mem' := fun z _ hx =>
      hM.op_smul_mem_range_of_map_eq_zero (h.mem_cycles.mp z.unop.2) hx }

/-- A module cycle is a boundary exactly when its underlying element lies in the differential's
range. -/
@[simp]
lemma mem_boundaries (hM : IsDGRightModule h ℳ dM) {z : hM.cycles} :
    z ∈ hM.boundaries ↔ (z : M) ∈ LinearMap.range dM :=
  Iff.rfl

/-- The cycle represented by a differential is a boundary. -/
theorem map_mem_boundaries (hM : IsDGRightModule h ℳ dM) (x : M) :
    (⟨dM x, hM.map_mem_cycles x⟩ : hM.cycles) ∈ hM.boundaries :=
  hM.mem_boundaries.mpr ⟨x, rfl⟩

/-- The cohomology `H(M)` of a differential graded right module: cycles modulo boundaries. -/
abbrev Cohomology (hM : IsDGRightModule h ℳ dM) := hM.cycles ⧸ hM.boundaries

/-- A module cohomology class vanishes exactly when its cycle representative is a boundary. -/
theorem quotientMk_eq_zero_iff (hM : IsDGRightModule h ℳ dM) {z : hM.cycles} :
    (Submodule.Quotient.mk z : hM.Cohomology) = 0 ↔ z ∈ hM.boundaries :=
  Submodule.Quotient.mk_eq_zero _

/-- The class of a differential vanishes in module cohomology. -/
@[simp]
theorem quotientMk_map_eq_zero (hM : IsDGRightModule h ℳ dM) (x : M) :
    (Submodule.Quotient.mk (⟨dM x, hM.map_mem_cycles x⟩ : hM.cycles) : hM.Cohomology) = 0 :=
  hM.quotientMk_eq_zero_iff.mpr (hM.map_mem_boundaries x)

/-- The opposite boundary ideal of the algebra annihilates module cohomology. -/
theorem isTorsionBySet_boundaries (hM : IsDGRightModule h ℳ dM) :
    Module.IsTorsionBySet (h.cycles)ᵐᵒᵖ hM.Cohomology
      (h.boundaries.op.asIdeal : Set (h.cycles)ᵐᵒᵖ) := by
  intro x a
  refine Submodule.Quotient.induction_on _ x fun z => ?_
  rw [← Submodule.Quotient.mk_smul, hM.quotientMk_eq_zero_iff, mem_boundaries]
  have ha : a.1.unop ∈ h.boundaries := TwoSidedIdeal.mem_asIdealOpposite.mp a.2
  obtain ⟨b, hb⟩ := h.mem_boundaries.mp ha
  have hz : dM (z : M) = 0 := hM.mem_cycles.mp z.2
  have hrange := hM.op_map_smul_mem_range_of_map_eq_zero b hz
  rw [hb] at hrange
  exact hrange

/-- Module cohomology is a module over the opposite algebra of cycles modulo the opposite boundary
ideal, since by `isTorsionBySet_boundaries` that ideal annihilates it.  This is the intermediate
scalar ring through which the action of the cohomology algebra is defined. -/
noncomputable instance instModuleQuotientOpBoundaries (hM : IsDGRightModule h ℳ dM) :
    Module ((h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal) hM.Cohomology :=
  hM.isTorsionBySet_boundaries.module

/-- The cohomology of a differential graded right module is a right module over the cohomology
algebra. -/
noncomputable instance instModuleCohomology (hM : IsDGRightModule h ℳ dM) :
    Module (h.Cohomology)ᵐᵒᵖ hM.Cohomology := by
  let quotientMkDouble : (h.cycles)ᵐᵒᵖ →+*
      ((h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal)ᵐᵒᵖᵐᵒᵖ :=
    (RingEquiv.opOp ((h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal)).toRingHom.comp
      (Ideal.Quotient.mk h.boundaries.op.asIdeal)
  let lift : h.Cohomology →+* ((h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal)ᵐᵒᵖ :=
    Ideal.Quotient.lift h.boundaries.asIdeal quotientMkDouble.unop (by
      intro a ha
      apply unop_injective
      rw [unop_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
        TwoSidedIdeal.mem_asIdealOpposite.mpr <| TwoSidedIdeal.mem_asIdeal.mp ha)
  let opToQuotientOp : (h.Cohomology)ᵐᵒᵖ →+*
      (h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal :=
    (RingEquiv.opOp ((h.cycles)ᵐᵒᵖ ⧸ h.boundaries.op.asIdeal)).symm.toRingHom.comp lift.op
  exact Module.compHom hM.Cohomology opToQuotientOp

/-- The defining equation of `instModuleCohomology`: an opposite cohomology class acts as the
corresponding class of the opposite algebra of cycles modulo the opposite boundary ideal.  Stating
it separately keeps later computations from unfolding the instance. -/
theorem op_quotientMk_smul_eq_quotientMk_op_smul (hM : IsDGRightModule h ℳ dM)
    (z : h.cycles) (x : hM.Cohomology) :
    op (Ideal.Quotient.mk h.boundaries.asIdeal z) • x =
      Ideal.Quotient.mk h.boundaries.op.asIdeal (op z) • x :=
  rfl

/-- The action on module cohomology is computed by acting with a cycle representative. -/
@[simp]
theorem op_quotientMk_smul (hM : IsDGRightModule h ℳ dM)
    (z : h.cycles) (x : hM.Cohomology) :
    op (Ideal.Quotient.mk h.boundaries.asIdeal z) • x = op z • x := by
  rw [hM.op_quotientMk_smul_eq_quotientMk_op_smul]
  exact hM.isTorsionBySet_boundaries.mk_smul (op z) x

section Grading

/-- The degree-`p` homogeneous module cycles. -/
noncomputable def cyclesDeg (hM : IsDGRightModule h ℳ dM) (p : ℤ) :
    Submodule R hM.cycles :=
  (ℳ p).comap ((hM.cycles.subtype).restrictScalars R)

/-- A cycle belongs to degree `p` exactly when its underlying module element does. -/
@[simp]
lemma mem_cyclesDeg (hM : IsDGRightModule h ℳ dM) {p : ℤ} {z : hM.cycles} :
    z ∈ hM.cyclesDeg p ↔ (z : M) ∈ ℳ p :=
  Iff.rfl

/-- Module cycles are closed under every homogeneous projection of the ambient grading. -/
theorem isHomogeneous_cycles (hM : IsDGRightModule h ℳ dM) :
    SetLike.IsHomogeneous ℳ hM.cycles :=
  fun p _ hz => hM.mem_cycles.mpr (hM.map_decompose_eq_zero (hM.mem_cycles.mp hz) p)

/-- Module cycles inherit the grading of the ambient differential graded right module. -/
noncomputable instance instDecompositionCyclesDeg (hM : IsDGRightModule h ℳ dM) :
    DirectSum.Decomposition hM.cyclesDeg :=
  DirectSum.Decomposition.restrict ℳ hM.cyclesDeg
    ((hM.cycles.subtype).restrictScalars R) Subtype.val_injective
    (fun _ _ => hM.mem_cyclesDeg) fun p z =>
      ⟨⟨(decompose ℳ (z : M) p : M), hM.isHomogeneous_cycles p z.2⟩, rfl⟩

/-- Every module cycle is a sum of homogeneous module cycles. -/
theorem iSup_cyclesDeg_eq_top (hM : IsDGRightModule h ℳ dM) :
    ⨆ p : ℤ, hM.cyclesDeg p = ⊤ :=
  (DirectSum.Decomposition.isInternal hM.cyclesDeg).submodule_iSup_eq_top

/-- The homogeneous module cycle spaces are independent. -/
theorem iSupIndep_cyclesDeg (hM : IsDGRightModule h ℳ dM) : iSupIndep hM.cyclesDeg :=
  (DirectSum.Decomposition.isInternal hM.cyclesDeg).submodule_iSupIndep

/-- The homogeneous module cycle spaces form an internal direct sum. -/
theorem isInternal_cyclesDeg (hM : IsDGRightModule h ℳ dM) :
    DirectSum.IsInternal hM.cyclesDeg :=
  DirectSum.Decomposition.isInternal hM.cyclesDeg

/-- Homogeneous projection of a module cycle agrees with projection in the ambient module. -/
@[simp]
theorem coe_decompose_cyclesDeg (hM : IsDGRightModule h ℳ dM) (p : ℤ)
    (z : hM.cycles) :
    ((decompose hM.cyclesDeg z p : hM.cycles) : M) =
      (decompose ℳ (z : M) p : M) := by
  simpa only [LinearMap.coe_restrictScalars, Submodule.coe_subtype] using
    DirectSum.map_decompose_restrict ℳ hM.cyclesDeg
      ((hM.cycles.subtype).restrictScalars R) (fun _ _ => hM.mem_cyclesDeg) p z

/-- The cycles of a differential graded right module are a graded right module over the graded
algebra of cycles. -/
instance instGradedSMulCyclesDeg (hM : IsDGRightModule h ℳ dM) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition h.cyclesDeg).opposite.piece hM.cyclesDeg where
  smul_mem := by
    intro i j a x ha hx
    rw [InternalGrading.mem_opposite_piece_iff] at ha
    have ha' : (a.unop : h.cycles) ∈ h.cyclesDeg i := by
      simpa using ha
    have hsource : op (a.unop : A) ∈
        (InternalGrading.ofDecomposition 𝒜).opposite.piece i :=
      (InternalGrading.op_mem_opposite_piece_iff _ _ _).mpr <| by
        simpa only [InternalGrading.ofDecomposition_piece] using h.mem_cyclesDeg.mp ha'
    exact SetLike.GradedSMul.smul_mem
      (A := (InternalGrading.ofDecomposition 𝒜).opposite.piece) (B := ℳ) hsource
      (hM.mem_cyclesDeg.mp hx)

end Grading

end IsDGRightModule

end TauCeti
