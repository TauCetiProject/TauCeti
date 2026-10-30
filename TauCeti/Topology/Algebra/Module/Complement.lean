/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Transport of complemented submodules

Topological complementedness is preserved by continuous semilinear equivalences, allowing
continuous projections to be transported between different presentations of a module. It is also
preserved by restriction of scalars.
-/

public section

namespace Submodule

section Map

variable {R S M N : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [AddCommGroup N] [TopologicalSpace M] [TopologicalSpace N]
  [Module R M] [Module S N] {σ : R →+* S} {τ : S →+* R}
  [RingHomInvPair σ τ] [RingHomInvPair τ σ]

/-- A continuous semilinear equivalence carries a complemented submodule to a complemented
submodule. -/
theorem ClosedComplemented.map {p : Submodule R M} (hp : p.ClosedComplemented)
    (e : M ≃SL[σ] N) : (p.map e.toLinearMap).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  let ep := e.submoduleMap p
  refine ⟨ep.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap), ?_⟩
  intro y
  have h := congrArg ep (hP (ep.symm y))
  simpa only [ep, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.submoduleMap_apply,
    ContinuousLinearEquiv.submoduleMap_symm_apply, ep.apply_symm_apply] using h

/-- Complementedness is invariant under a continuous semilinear equivalence. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.closedComplemented_map_iff (e : M ≃SL[σ] N)
    (p : Submodule R M) : (p.map e.toLinearMap).ClosedComplemented ↔ p.ClosedComplemented := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map e⟩
  have hmap : (p.map e.toLinearMap).map e.symm.toLinearMap = p := by
    ext x
    simp
  exact hmap ▸ h.map e.symm

end Map

section RestrictScalars

variable (R : Type*) {A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [TopologicalSpace M]
  [Module R M] [Module A M] [SMul R A] [IsScalarTower R A M]

/-- A complemented submodule stays complemented after restricting scalars: a continuous
`A`-linear projection onto `p` is in particular a continuous `R`-linear one. -/
theorem ClosedComplemented.restrictScalars {p : Submodule A M} (hp : p.ClosedComplemented) :
    (p.restrictScalars R).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  exact ⟨ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.restrictScalars R (p.subtypeL.comp P)) (p.restrictScalars R)
    fun x ↦ (P x).2, fun x ↦ Subtype.ext (congrArg Subtype.val (hP ⟨x, x.2⟩))⟩

end RestrictScalars

end Submodule
