/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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
    (by
      have h₁ := Submodule.finrank_quotient_add_finrank (range f)
      have h₂ := finrank_range_add_finrank_ker f
      omega)

@[simp]
theorem kerEquivQuotientRangeOfInnerApplyEq_apply (hJ : Function.Injective J)
    (hQ : ∀ x y, ⟪J (Q x), Q y⟫ = ⟪J x, y⟫) (hε : ε ^ 2 = 1) (hf : ∀ x, f x = ε • x - Q x)
    (x : ker f) :
    kerEquivQuotientRangeOfInnerApplyEq hJ hQ hε hf x = Submodule.Quotient.mk (J x) :=
  (rfl)

end TauCeti
