/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Determinant.PositivePairing
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# The cokernel of `ε - Q` for a map preserving the form `⟪J ·, ·⟫`

Let `V` be a real inner product space, `J` an injective linear endomorphism, and `Q` a linear
endomorphism preserving the bilinear form `ω(x, y) = ⟪J x, y⟫`, that is
`⟪J (Q x), Q y⟫ = ⟪J x, y⟫`. For an orthogonal complex structure `J`, `ω` is the symplectic form
and `Q` is a linear symplectic map, such as the linearized return map of a periodic orbit of a
Hamiltonian flow. For a sign `ε` with `ε ^ 2 = 1`, put `f = ε - Q`.

If `x` lies in the `ε`-eigenspace `ker f`, then `J x` is orthogonal to the range of `f`
(`TauCeti.inner_apply_apply_eq_zero_of_inner_apply_eq_of_mem_ker`), because
`⟪J x, y⟫ = ⟪J (Q x), Q y⟫ = ε ⟪J x, Q y⟫`. Hence `J x` lies in the range only if it vanishes,
and `x ↦ [J x]` is injective from `ker f` to the cokernel `V ⧸ range f`. In finite dimension the
two spaces have the same dimension, so this is a linear equivalence
(`TauCeti.kerEquivQuotientRangeOfInnerApplyEq`).

Unlike the dimension count alone, this gives a specific isomorphism between the kernel and the
cokernel of `ε - Q`, determined by `J`. It identifies the determinant line
`det (ker f) ⊗ (det (coker f))^*` of `f` with `det (ker f) ⊗ (det (ker f))^*`, which is how the
kernel of a formal adjoint, computed through the same eigenspace, is compared with the cokernel.

**Orientations.** The same orthogonality makes `β(x, [z]) = ⟪J x, z⟫` a well-defined pairing of
`ker f` with `V ⧸ range f` (`TauCeti.kerQuotientRangePairing`), and the isomorphism above is
positive for it: `β(x, [J x]) = ‖J x‖² > 0` for `x ≠ 0`. Any other linear map
`φ : ker f → V ⧸ range f` with `0 < β(x, φ x)` for every `x ≠ 0` is then an isomorphism as well,
differing from `x ↦ [J x]` by an automorphism of `ker f` of positive determinant
(`TauCeti.det_pos_kerEquivQuotientRangeOfInnerApplyEq_symm_comp`,
`TauCeti.bijective_of_forall_pos_kerQuotientRangePairing`). So both identify the determinant line
of `f` with `det (ker f) ⊗ (det (ker f))^*` compatibly with orientations. For the return map of a
periodic linear Hamiltonian equation, `ε` times the endpoint map of variation of constants gives
such a map (`TauCeti.kerQuotientRangePairing_smul_kerTwistedLinearOperatorToQuotientRange_pos`).

## Main definitions

* `TauCeti.kerEquivQuotientRangeOfInnerApplyEq`: the isomorphism `x ↦ [J x]` from the kernel of
  `ε - Q` onto its cokernel.
* `TauCeti.kerQuotientRangePairing`: the pairing `β(x, [z]) = ⟪J x, z⟫` of the kernel with the
  cokernel.

## Main results

* `TauCeti.det_pos_kerEquivQuotientRangeOfInnerApplyEq_symm_comp`: a map from the kernel to the
  cokernel positive for `β` differs from `x ↦ [J x]` by an automorphism of positive determinant.
-/

public section

noncomputable section

open Module LinearMap
open scoped RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {J Q f : V →ₗ[ℝ] V} {ε : ℝ}

/-- If `Q` preserves `⟪J ·, ·⟫` and `ε ^ 2 = 1`, then for every `x` in the kernel of
`f = ε - Q`, the vector `J x` is orthogonal to the range of `f`. -/
theorem inner_apply_apply_eq_zero_of_inner_apply_eq_of_mem_ker
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    {x : V} (hx : x ∈ ker f) (y : V) :
    ⟪J x, f y⟫ = 0 := by
  have hQx : Q x = ε • x := by
    rw [mem_ker, hf, sub_eq_zero] at hx
    exact hx.symm
  have h := hQ x y
  rw [hQx, map_smul, real_inner_smul_left] at h
  rw [hf, inner_sub_right, real_inner_smul_right, ← h]
  linear_combination ⟪J x, Q y⟫ * hε

variable [FiniteDimensional ℝ V]

/-- **The kernel and the cokernel of `ε - Q`.** Let `J` be injective, `Q` preserve
`⟪J ·, ·⟫` and `ε ^ 2 = 1`. For `f = ε - Q` on a finite-dimensional space, `x ↦ [J x]` is a linear
equivalence from the kernel of `f` onto its cokernel `V ⧸ range f`. -/
def kerEquivQuotientRangeOfInnerApplyEq (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x) :
    ker f ≃ₗ[ℝ] V ⧸ range f :=
  linearEquivOfInjective ((range f).mkQ ∘ₗ J ∘ₗ (ker f).subtype)
    (by
      rw [← ker_eq_bot, eq_bot_iff]
      rintro ⟨x, hx⟩ h
      obtain ⟨y, hy⟩ : J x ∈ range f := by simpa [Submodule.Quotient.mk_eq_zero] using h
      have h0 : ⟪J x, J x⟫ = 0 := by
        calc ⟪J x, J x⟫ = ⟪J x, f y⟫ := by rw [hy]
          _ = 0 := inner_apply_apply_eq_zero_of_inner_apply_eq_of_mem_ker hQ hε hf hx y
      have hx0 : x = 0 := hJ (by rw [inner_self_eq_zero.1 h0, map_zero])
      simp [hx0])
    (finrank_quotient_range_eq_finrank_ker f).symm

@[simp]
theorem kerEquivQuotientRangeOfInnerApplyEq_apply (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    (x : ker f) :
    kerEquivQuotientRangeOfInnerApplyEq hJ hQ hε hf x = Submodule.Quotient.mk (J x) :=
  (rfl)

omit [FiniteDimensional ℝ V] in
variable (J f) in
/-- The pairing `β(x, [z]) = ⟪J x, z⟫` of the kernel of `f = ε - Q` with its cokernel
`V ⧸ range f`, for `Q` preserving `⟪J ·, ·⟫` and `ε ^ 2 = 1`. It is well defined because `J x` is
orthogonal to the range of `f` for `x ∈ ker f`. -/
def kerQuotientRangePairing (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1)
    (hf : ∀ x, f x = ε • x - Q x) : ker f →ₗ[ℝ] (V ⧸ range f) →ₗ[ℝ] ℝ :=
  ((range f).liftQ (innerₗ V ∘ₗ J ∘ₗ (ker f).subtype).flip (by
    rintro _ ⟨y, rfl⟩
    rw [mem_ker]
    ext x
    exact inner_apply_apply_eq_zero_of_inner_apply_eq_of_mem_ker hQ hε hf x.property y)).flip

omit [FiniteDimensional ℝ V] in
@[simp]
theorem kerQuotientRangePairing_mk (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1)
    (hf : ∀ x, f x = ε • x - Q x) (x : ker f) (z : V) :
    kerQuotientRangePairing J f hQ hε hf x (Submodule.Quotient.mk z) = ⟪J x, z⟫ :=
  (rfl)

omit [FiniteDimensional ℝ V] in
/-- The pairing `β(x, [J x]) = ‖J x‖²` is positive for `x ≠ 0` in the kernel of `ε - Q`. -/
theorem kerQuotientRangePairing_mk_apply_pos (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    {x : ker f} (hx : x ≠ 0) :
    0 < kerQuotientRangePairing J f hQ hε hf x (Submodule.Quotient.mk (J x)) := by
  rw [kerQuotientRangePairing_mk, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.2 fun h =>
    hx (Submodule.coe_eq_zero.1 ((injective_iff_map_eq_zero J).1 hJ _ h))) 2

/-- **Positive maps from the kernel to the cokernel induce the orientation of `x ↦ [J x]`.** Let
`J` be injective, `Q` preserve `⟪J ·, ·⟫` and `ε ^ 2 = 1`, and put `f = ε - Q`. A linear map
`φ : ker f → V ⧸ range f` with `0 < ⟪J x, φ x⟫` for every `x ≠ 0` differs from the isomorphism
`x ↦ [J x]` by an automorphism of `ker f` of positive determinant. -/
theorem det_pos_kerEquivQuotientRangeOfInnerApplyEq_symm_comp (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    {φ : ker f →ₗ[ℝ] V ⧸ range f}
    (hφ : ∀ x, x ≠ 0 → 0 < kerQuotientRangePairing J f hQ hε hf x (φ x)) :
    0 < ((kerEquivQuotientRangeOfInnerApplyEq hJ hQ hε hf).symm.toLinearMap ∘ₗ φ).det :=
  det_pos_of_forall_pos_of_forall_pos (kerQuotientRangePairing J f hQ hε hf)
    (kerEquivQuotientRangeOfInnerApplyEq hJ hQ hε hf)
    (fun _ hx => kerQuotientRangePairing_mk_apply_pos hJ hQ hε hf hx) hφ

/-- A linear map `φ : ker f → V ⧸ range f` with `0 < ⟪J x, φ x⟫` for every `x ≠ 0` is bijective,
for `f = ε - Q` as in `TauCeti.kerEquivQuotientRangeOfInnerApplyEq`. -/
theorem bijective_of_forall_pos_kerQuotientRangePairing (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    {φ : ker f →ₗ[ℝ] V ⧸ range f}
    (hφ : ∀ x, x ≠ 0 → 0 < kerQuotientRangePairing J f hQ hε hf x (φ x)) :
    Function.Bijective φ := by
  set e := kerEquivQuotientRangeOfInnerApplyEq hJ hQ hε hf
  have hT : Function.Bijective (e.symm.toLinearMap ∘ₗ φ) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2
      (det_pos_kerEquivQuotientRangeOfInnerApplyEq_symm_comp hJ hQ hε hf hφ).ne'))
  have hφe : (φ : ker f → V ⧸ range f) = e ∘ (e.symm.toLinearMap ∘ₗ φ) := by
    ext x
    simp
  rw [hφe]
  exact e.bijective.comp hT

end TauCeti
