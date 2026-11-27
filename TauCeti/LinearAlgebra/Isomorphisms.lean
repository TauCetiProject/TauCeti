/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Colon

/-!
# Inverses up to a scalar

If an element `c` of a commutative ring kills the kernel of a linear map `f : M → N` and `b`
kills its cokernel, then `f` has an inverse up to `b * c`: there is a linear map `g : N → M` with
`f ∘ g = (b * c) •` and `g ∘ f = (b * c) •`. The map is `g n = c • m`, where `f m = b • n`, built
from the first isomorphism theorem `LinearMap.quotKerEquivRange`.

Such bounds compose: if `a` kills the kernel (or the cokernel) of `f : M → N` and `b` kills that of
`g : N → P`, then `a * b` kills the kernel (or the cokernel) of `g ∘ f`
(`LinearMap.mul_mem_annihilator_ker_comp`, `LinearMap.mul_mem_annihilator_range_comp`).

The file also records the value of Mathlib's third isomorphism theorem
`Submodule.quotientQuotientEquivQuotientSup` on representatives
(`Submodule.quotientQuotientEquivQuotientSup_mk_mk`).
-/

public section

namespace LinearMap

variable {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

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

/-- If `a` kills the kernel of `f` and `b` kills the kernel of `g`, then `a * b` kills the kernel
of `g ∘ f`. -/
theorem mul_mem_annihilator_ker_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) {a b : A}
    (ha : a ∈ Module.annihilator A (ker f)) (hb : b ∈ Module.annihilator A (ker g)) :
    a * b ∈ Module.annihilator A (ker (g ∘ₗ f)) := by
  refine Module.mem_annihilator.mpr fun ⟨m, hm⟩ ↦ Subtype.ext ?_
  have hbm : b • m ∈ ker f := by
    simpa using congrArg Subtype.val (Module.mem_annihilator.mp hb ⟨f m, hm⟩)
  simpa [mul_smul] using congrArg Subtype.val (Module.mem_annihilator.mp ha ⟨b • m, hbm⟩)

/-- If `a` kills the cokernel of `f` and `b` kills the cokernel of `g`, then `a * b` kills the
cokernel of `g ∘ f`. -/
theorem mul_mem_annihilator_range_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) {a b : A}
    (ha : a ∈ Module.annihilator A (N ⧸ range f)) (hb : b ∈ Module.annihilator A (P ⧸ range g)) :
    a * b ∈ Module.annihilator A (P ⧸ range (g ∘ₗ f)) := by
  rw [Submodule.annihilator_quotient, Submodule.mem_colon] at ha hb ⊢
  intro y _
  obtain ⟨n, hn⟩ := hb y trivial
  obtain ⟨m, hm⟩ := ha n trivial
  exact ⟨m, by rw [comp_apply, hm, map_smul, hn, mul_smul]⟩

end LinearMap

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The third isomorphism theorem `(M ⧸ S) ⧸ (T ⧸ S) ≃ M ⧸ (S ⊔ T)` sends the class of the class
of `x` to the class of `x`. -/
@[simp]
theorem quotientQuotientEquivQuotientSup_mk_mk (S T : Submodule R M) (x : M) :
    quotientQuotientEquivQuotientSup S T (Quotient.mk (Quotient.mk x)) = Quotient.mk x := by
  rw [quotientQuotientEquivQuotientSup, LinearEquiv.trans_apply, quotEquivOfEq_mk]
  exact quotientQuotientEquivQuotientAux_mk_mk _ _ _ _

end Submodule
