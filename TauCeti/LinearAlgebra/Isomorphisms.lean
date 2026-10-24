/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Inverses up to a scalar

If an element `γ` of a commutative ring kills both the kernel and the cokernel of a linear map
`f : M → N`, then `f` has an inverse up to `γ²`: there is a linear map `g : N → M` with
`g ∘ f = γ² •`. The map is `g n = γ • m`, where `f m = γ • n`, built from the first isomorphism
theorem `LinearMap.quotKerEquivRange`.
-/

public section

namespace LinearMap

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- If `γ` kills the kernel and the cokernel of `f : M → N`, then `f` has an inverse up to `γ²`:
some `g : N → M` satisfies `g ∘ f = (γ * γ) •`. -/
theorem exists_comp_eq_lsmul_of_mem_annihilator (f : M →ₗ[A] N) {γ : A}
    (hker : γ ∈ Module.annihilator A (ker f)) (hcoker : γ ∈ Module.annihilator A (N ⧸ range f)) :
    ∃ g : N →ₗ[A] M, g ∘ₗ f = lsmul A M (γ * γ) := by
  have hrange (n : N) : γ • n ∈ range f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.mp hcoker _
  have hle : ker f ≤ ker (γ • LinearMap.id : M →ₗ[A] M) := fun m hm ↦ by
    simpa using Module.mem_annihilator.mp hker ⟨m, hm⟩
  refine ⟨(ker f).liftQ _ hle ∘ₗ (f.quotKerEquivRange.symm : range f →ₗ[A] M ⧸ ker f) ∘ₗ
    (γ • LinearMap.id : N →ₗ[A] N).codRestrict _ hrange, ?_⟩
  ext m
  have : (γ • LinearMap.id : N →ₗ[A] N).codRestrict _ hrange (f m) =
      ⟨f (γ • m), mem_range_self f _⟩ :=
    Subtype.ext (by simp)
  simp only [comp_apply, LinearEquiv.coe_coe, this, quotKerEquivRange_symm_apply_image]
  simp [mul_smul]

end LinearMap
