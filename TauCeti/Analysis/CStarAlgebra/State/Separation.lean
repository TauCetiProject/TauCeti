/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.CStarAlgebra.State.Unitization
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Separation of points, self-adjointness, and positivity by states

Using spectral and norm attainment from `TauCeti.Analysis.CStarAlgebra.State.Spectrum` together
with unitization of states (`TauCeti.Analysis.CStarAlgebra.State.Unitization`), states of a
possibly nonunital C⋆-algebra `A` separate points and detect self-adjointness, positivity, and the
C⋆-order without assuming `[Nontrivial A]`:

* `TauCeti.eq_zero_of_forall_mem_stateSpace_apply_eq_zero`,
  `TauCeti.eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero`,
  `TauCeti.forall_mem_stateSpace_apply_eq_zero_iff`,
  `TauCeti.eq_of_forall_mem_stateSpace_apply_eq`, and `TauCeti.forall_mem_stateSpace_apply_eq_iff`:
  states separate all elements of `A`.
* `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace` and
  `TauCeti.forall_mem_stateSpace_isSelfAdjoint_apply_iff`: an element is self-adjoint if and only
  if every state maps it to a real scalar.
* `TauCeti.nonneg_iff_forall_mem_stateSpace`, `TauCeti.forall_mem_stateSpace_apply_nonneg_iff`,
  `TauCeti.le_iff_forall_mem_stateSpace`, `TauCeti.le_of_forall_mem_stateSpace_apply_le`, and
  `TauCeti.forall_mem_stateSpace_apply_le_iff`: positivity and the C⋆-order are detected pointwise
  by states.

## References

* J. Peterson, *Notes on von Neumann algebras* (2013), Proposition 4.1.5, p. 56.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.6.
-/

public section

open WeakDual
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **State separation of zero.** If `φ a = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ a = 0) : a = 0 := by
  have hsa (x : selfAdjoint A) (hx : ∀ φ : stateSpace A, φ.val x = 0) : (x : A) = 0 := by
    have : IsStarNormal (x : A) := x.property.isStarNormal
    exact norm_eq_zero.1 <| by
      simp [norm_eq_iSup_norm_apply_stateSpace_of_isStarNormal (x : A), hx, Real.iSup_const_zero]
  rw [← realPart_add_I_smul_imaginaryPart a,
    hsa (realPart a) fun φ => by
      simpa [h φ.val φ.property] using map_realPart (StateSpace.toPositiveLinearMap φ) a,
    hsa (imaginaryPart a) fun φ => by
      simpa [h φ.val φ.property] using map_imaginaryPart (StateSpace.toPositiveLinearMap φ) a,
    smul_zero, add_zero]

/-- If `φ (star a * a) = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ (star a * a) = 0) : a = 0 :=
  star_mul_self_eq_zero.1 (eq_zero_of_forall_mem_stateSpace_apply_eq_zero h)

/-- An element `a` of a C⋆-algebra is zero if and only if every state vanishes on `a`. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_zero_iff {a : A} :
    (∀ φ ∈ stateSpace A, φ a = 0) ↔ a = 0 :=
  ⟨eq_zero_of_forall_mem_stateSpace_apply_eq_zero, by rintro rfl φ _; simp⟩

/-- **States separate points.** Two elements of a C⋆-algebra are equal if every state takes the
same value on them. -/
theorem eq_of_forall_mem_stateSpace_apply_eq {a b : A}
    (h : ∀ φ ∈ stateSpace A, φ a = φ b) : a = b :=
  sub_eq_zero.1 <| eq_zero_of_forall_mem_stateSpace_apply_eq_zero fun φ hφ => by
    rw [map_sub, h φ hφ, sub_self]

/-- Two elements of a C⋆-algebra are equal if and only if every state takes the same value on
them. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_iff {a b : A} :
    (∀ φ ∈ stateSpace A, φ a = φ b) ↔ a = b :=
  ⟨eq_of_forall_mem_stateSpace_apply_eq, fun h _ _ => h ▸ rfl⟩

/-- **Detection of self-adjointness by states.** An element `a` of a C⋆-algebra is self-adjoint if
and only if `φ a` is self-adjoint (real) for every state `φ`. -/
theorem isSelfAdjoint_iff_forall_mem_stateSpace {a : A} :
    IsSelfAdjoint a ↔ ∀ φ ∈ stateSpace A, IsSelfAdjoint (φ a) := by
  refine ⟨fun ha φ hφ => isSelfAdjoint_apply_of_mem_stateSpace hφ ha, fun h => ?_⟩
  rw [isSelfAdjoint_iff]
  refine eq_of_forall_mem_stateSpace_apply_eq fun φ hφ => ?_
  rw [map_star_of_mem_stateSpace hφ, (h φ hφ).star_eq]

/-- Every state sends `a` to a self-adjoint (real) scalar if and only if `a` is self-adjoint. -/
@[simp]
theorem forall_mem_stateSpace_isSelfAdjoint_apply_iff {a : A} :
    (∀ φ ∈ stateSpace A, IsSelfAdjoint (φ a)) ↔ IsSelfAdjoint a :=
  isSelfAdjoint_iff_forall_mem_stateSpace.symm

/-- **Detection of positivity by states.** An element `a` of a C⋆-algebra is nonnegative (`0 ≤ a`)
if and only if `0 ≤ φ a` for every state `φ`. No self-adjointness hypothesis on `a` is needed. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have ha_sa : IsSelfAdjoint a :=
    isSelfAdjoint_iff_forall_mem_stateSpace.2 fun φ hφ => (h φ hφ).isSelfAdjoint
  -- Pass to `A⁺¹`: any state `ψ` of `A⁺¹` restricts to a multiple of a state of `A` (or to `0`),
  -- so `0 ≤ ψ a` holds on all of `stateSpace A⁺¹`, making the real spectrum of `(a : A⁺¹)`
  -- nonnegative.
  have hunit (ψ : WeakDual ℂ A⁺¹) (hψ : ψ ∈ stateSpace A⁺¹) : 0 ≤ ψ (a : A⁺¹) := by
    set φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
    by_cases hφ0 : φ = 0
    · have hzero : ψ (a : A⁺¹) = 0 := by
        calc ψ (a : A⁺¹)
            = φ a := (pullbackFunctional_apply (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a).symm
          _ = 0 := by rw [hφ0, ← toStrongDual_apply]; simp
      simp [hzero]
    · have hpos : 0 < ‖toStrongDual φ‖ := by simp [hφ0]
      have hcφ := h _ (inv_norm_toStrongDual_smul_mem_stateSpace_of_map_nonneg_of_ne_zero
        (fun _ => map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ) hφ0)
      simpa [-Complex.real_smul, φ, smul_smul, mul_inv_cancel₀ hpos.ne'] using
        smul_nonneg hpos.le hcφ
  rw [← Unitization.inr_nonneg_iff ℂ]
  have ha_inr_sa : IsSelfAdjoint (a : A⁺¹) := ha_sa.inr ℂ
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A⁺¹) ha_inr_sa]
  intro r hr
  have hrc : (r : ℂ) ∈ spectrum ℂ (a : A⁺¹) := by simpa using spectrum.algebraMap_mem ℂ hr
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : A⁺¹) hrc
  exact Complex.zero_le_real.1 (hψa ▸ hunit ψ hψ)

/-- Every state is nonnegative at `a` if and only if `0 ≤ a`. -/
@[simp]
theorem forall_mem_stateSpace_apply_nonneg_iff {a : A} :
    (∀ φ ∈ stateSpace A, 0 ≤ φ a) ↔ 0 ≤ a :=
  nonneg_iff_forall_mem_stateSpace.symm

/-- **Detection of order by states.** In a C⋆-algebra, `a ≤ b` if and only if `φ a ≤ φ b` for every
state `φ`. -/
theorem le_iff_forall_mem_stateSpace {a b : A} :
    a ≤ b ↔ ∀ φ ∈ stateSpace A, φ a ≤ φ b := by
  simpa only [map_sub, sub_nonneg] using nonneg_iff_forall_mem_stateSpace (a := b - a)

/-- If `φ a ≤ φ b` for every state `φ` of `A`, then `a ≤ b`. -/
theorem le_of_forall_mem_stateSpace_apply_le {a b : A}
    (h : ∀ φ ∈ stateSpace A, φ a ≤ φ b) : a ≤ b :=
  le_iff_forall_mem_stateSpace.2 h

/-- Every state satisfies `φ a ≤ φ b` if and only if `a ≤ b`. -/
@[simp]
theorem forall_mem_stateSpace_apply_le_iff {a b : A} :
    (∀ φ ∈ stateSpace A, φ a ≤ φ b) ↔ a ≤ b :=
  le_iff_forall_mem_stateSpace.symm

end TauCeti
