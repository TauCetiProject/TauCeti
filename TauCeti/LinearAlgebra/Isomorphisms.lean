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

If an element `c` of a commutative ring kills the kernel of a linear map `f : M → N` and `b`
kills its cokernel, then `f` has an inverse up to `b * c`: there is a linear map `g : N → M` with
`f ∘ g = (b * c) •` and `g ∘ f = (b * c) •`. The map is `g n = c • m`, where `f m = b • n`, built
from the first isomorphism theorem `LinearMap.quotKerEquivRange`.
-/

public section

namespace LinearMap

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- If `c` kills the kernel and `b` kills the cokernel of `f : M → N`, then `f` has an inverse up
to `b * c`: some `g : N → M` satisfies `f ∘ g = (b * c) •` and `g ∘ f = (b * c) •`. -/
theorem exists_comp_eq_lsmul_of_mem_annihilator (f : M →ₗ[A] N) {b c : A}
    (hker : c ∈ Module.annihilator A (ker f)) (hcoker : b ∈ Module.annihilator A (N ⧸ range f)) :
    ∃ g : N →ₗ[A] M, f ∘ₗ g = lsmul A N (b * c) ∧ g ∘ₗ f = lsmul A M (b * c) := by
  have hrange (n : N) : b • n ∈ range f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.mp hcoker _
  have hle : ker f ≤ ker (c • LinearMap.id : M →ₗ[A] M) := fun m hm ↦ by
    simpa using Module.mem_annihilator.mp hker ⟨m, hm⟩
  let g := (ker f).liftQ _ hle ∘ₗ (f.quotKerEquivRange.symm : range f →ₗ[A] M ⧸ ker f) ∘ₗ
    (b • LinearMap.id : N →ₗ[A] N).codRestrict _ hrange
  -- `g` sends `n` to `c • m` whenever `f m = b • n`.
  have hg {m : M} {n : N} (h : f m = b • n) : g n = c • m := by
    have : (b • LinearMap.id : N →ₗ[A] N).codRestrict _ hrange n = ⟨f m, mem_range_self f _⟩ :=
      Subtype.ext (by simp [h])
    simp [g, this]
  refine ⟨g, ext fun n ↦ ?_, ext fun m ↦ ?_⟩
  · obtain ⟨m, hm⟩ := hrange n
    simp [hg hm, hm, smul_smul, mul_comm]
  · simp [hg (map_smul f b m), smul_smul, mul_comm]

end LinearMap
