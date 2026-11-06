/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

/-!
# Complemented submodules and continuous linear sections

Topological complementedness is preserved by continuous semilinear equivalences, allowing
continuous projections to be transported between different presentations of a module. It is also
preserved by restriction of scalars.
A continuous linear quotient map with continuously complemented kernel admits a continuous
linear section, obtained by descending the complementary projection through the quotient.
A continuous linear functional taking a nonzero value on a vector `u` splits the space as the
product of the scalars and the kernel (`TauCeti.exists_homeomorph_prod_ker`).
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

namespace TauCeti

section KerProd

variable {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

/-- **Coordinates along a vector** `u` on which a continuous linear functional `φ` takes the value
`L ≠ 0`, based at `p`: a homeomorphism `E ≃ₜ 𝕜 × ker φ` sending `x` to
`(φ (x - p), (x - p) - (φ (x - p) / L) • u)`, with inverse `y ↦ p + (y.1 / L) • u + y.2`. -/
theorem exists_homeomorph_prod_ker {φ : StrongDual 𝕜 E} {u : E} {L : 𝕜} (hu : φ u = L)
    (hL : L ≠ 0) (p : E) :
    ∃ e : E ≃ₜ 𝕜 × LinearMap.ker (φ : E →ₗ[𝕜] 𝕜), (∀ x, (e x).1 = φ (x - p)) ∧
      (∀ x, ((e x).2 : E) = (x - p) - (φ (x - p) / L) • u) ∧
      ∀ y, e.symm y = p + (y.1 / L) • u + y.2 := by
  let ψ : 𝕜 →L[𝕜] E := ContinuousLinearMap.toSpanSingleton 𝕜 (L⁻¹ • u)
  have hψ (r : 𝕜) : ψ r = (r / L) • u := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_smul, div_eq_mul_inv]
  have hψφ : Function.RightInverse ψ φ := fun r ↦ by
    rw [hψ, map_smul, hu, smul_eq_mul, div_mul_cancel₀ _ hL]
  refine ⟨(Homeomorph.subRight p).trans
    (ContinuousLinearEquiv.equivOfRightInverse φ ψ hψφ).toHomeomorph, fun x ↦ ?_, fun x ↦ ?_,
    fun y ↦ ?_⟩
  · simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.fst_equivOfRightInverse, Homeomorph.coe_subRight]
  · simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.snd_equivOfRightInverse, Homeomorph.coe_subRight, hψ]
  · simp only [Homeomorph.symm_trans_apply, ContinuousLinearEquiv.coe_symm_toHomeomorph,
      ContinuousLinearEquiv.equivOfRightInverse_symm_apply, hψ, Homeomorph.subRight_symm_apply]
    abel

end KerProd

end TauCeti
