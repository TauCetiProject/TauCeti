/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Complemented submodules and continuous linear sections

Topological complementedness is preserved by continuous semilinear equivalences, allowing
continuous projections to be transported between different presentations of a module. It is also
preserved by restriction of scalars.
A continuous linear quotient map with continuously complemented kernel admits a continuous
linear section, obtained by descending the complementary projection through the quotient.
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

namespace ContinuousLinearMap

open Topology

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- A continuous linear quotient map with continuously complemented kernel admits
a continuous linear right inverse. -/
theorem exists_rightInverse_of_isQuotientMap_of_closedComplemented_ker
    (f : E →L[R] F) (hf : IsQuotientMap f) (h : f.ker.ClosedComplemented) :
    ∃ s : F →L[R] E, Function.RightInverse s f := by
  obtain ⟨r, hr⟩ := h
  let P : E →L[R] E := f.ker.subtypeL.comp r
  have hP (x : E) (hx : x ∈ f.ker) : P x = x := by
    simpa [P] using congrArg Subtype.val (hr ⟨x, hx⟩)
  have hfP (x : E) : f (P x) = 0 := by
    simp only [P, comp_apply, Submodule.subtypeL_apply]
    exact LinearMap.mem_ker.mp (r x).property
  have hker : f.ker ≤ (LinearMap.id - P.toLinearMap).ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    simp [hP x hx]
  let s : F →ₗ[R] E := f.toLinearMap.liftOfSurjective hf.surjective
    ⟨LinearMap.id - P.toLinearMap, hker⟩
  have hs (x : E) : s (f x) = x - P x := by
    simpa only [s, LinearMap.sub_apply, LinearMap.id_apply, coe_coe] using
      (LinearMap.equivOfSurjective_apply (f := f.toLinearMap) hf.surjective hker (m := x))
  have hscont : Continuous s := by
    apply hf.continuous_iff.mpr
    exact (continuous_id.sub P.continuous).congr (fun x ↦ (hs x).symm)
  refine ⟨⟨s, hscont⟩, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf.surjective y
  simp [hs, hfP]

end ContinuousLinearMap
