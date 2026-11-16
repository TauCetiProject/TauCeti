/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# Comparing two splittings by projection

Let `E = p₁ ⊕ q₁` and `E = p₂ ⊕ q₂` be two splittings of a module into complementary submodules,
and suppose that the two splittings are in general position: `p₁` is a complement of `q₂` and
`q₁` is a complement of `p₂`. Then projecting `p₁` onto `p₂` along `q₂`, and `q₁` onto `q₂` along
`p₂`, are linear equivalences, and together they give a linear automorphism of `E` carrying the
first splitting onto the second (`Submodule.splittingEquiv`). It is the identity when the two
splittings agree (`Submodule.splittingEquiv_self`).

For instance, a nondegenerate symmetric bilinear form on a finite-dimensional real vector space
splits it into a negative definite and a positive definite part, and two such splittings are always
in general position, since a vector in a negative definite and a positive definite subspace is `0`.
This is how the negative and positive normal bundles of a Morse–Bott critical submanifold relative
to two fibre metrics are compared.

## Main definitions

* `Submodule.splittingEquiv`: the automorphism of `E` carrying the splitting `p₁ ⊕ q₁` onto
  `p₂ ⊕ q₂` by projecting each summand along the other summand of the second splitting.

## Main results

* `Submodule.splittingEquiv_apply`: the formula `x ↦ π₂ (π₁ x) + π₂' (π₁' x)` in terms of the
  projections `π` onto the first summands and `π'` onto the second summands.
* `Submodule.splittingEquiv_symm_apply`: the inverse is `y ↦ π₁₂ (π₂ y) + π₁₂' (π₂' y)`, where
  `π₁₂` projects onto `p₁` along `q₂` and `π₁₂'` onto `q₁` along `p₂`.
* `Submodule.map_splittingEquiv_left` and `Submodule.map_splittingEquiv_right`: the automorphism
  carries `p₁` onto `p₂` and `q₁` onto `q₂`.
* `Submodule.splittingEquiv_self`: comparing a splitting with itself gives the identity.
-/

public section

namespace Submodule

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {p₁ q₁ p₂ q₂ : Submodule R E}

/-- The automorphism of `E` comparing two splittings `E = p₁ ⊕ q₁` and `E = p₂ ⊕ q₂` in general
position, that is, with `p₁` complementary to `q₂` and `q₁` complementary to `p₂`. It maps `p₁`
onto `p₂` by the projection along `q₂`, and `q₁` onto `q₂` by the projection along `p₂`. Each of
these restrictions is an equivalence because both its source and its target are complements of its
kernel. -/
noncomputable def splittingEquiv (h₁ : IsCompl p₁ q₁) (h₂ : IsCompl p₂ q₂) (hp : IsCompl p₁ q₂)
    (hq : IsCompl q₁ p₂) : E ≃ₗ[R] E :=
  (prodEquivOfIsCompl p₁ q₁ h₁).symm ≪≫ₗ
    (((quotientEquivOfIsCompl q₂ p₁ hp.symm).symm ≪≫ₗ
        quotientEquivOfIsCompl q₂ p₂ h₂.symm).prodCongr
      ((quotientEquivOfIsCompl p₂ q₁ hq.symm).symm ≪≫ₗ quotientEquivOfIsCompl p₂ q₂ h₂)) ≪≫ₗ
    prodEquivOfIsCompl p₂ q₂ h₂

variable (h₁ : IsCompl p₁ q₁) (h₂ : IsCompl p₂ q₂) (hp : IsCompl p₁ q₂) (hq : IsCompl q₁ p₂)

/-- The comparison of two splittings projects the `p₁`-component of `x` onto `p₂` along `q₂` and
its `q₁`-component onto `q₂` along `p₂`. -/
@[simp]
theorem splittingEquiv_apply (x : E) :
    splittingEquiv h₁ h₂ hp hq x =
      p₂.projection q₂ h₂ (p₁.projection q₁ h₁ x) +
        q₂.projection p₂ h₂.symm (q₁.projection p₁ h₁.symm x) := by
  simp [splittingEquiv]

/-- On `p₁`, the comparison of two splittings is the projection onto `p₂` along `q₂`. -/
theorem splittingEquiv_apply_of_mem_left {x : E} (hx : x ∈ p₁) :
    splittingEquiv h₁ h₂ hp hq x = p₂.projection q₂ h₂ x := by
  rw [splittingEquiv_apply, projection_apply_of_mem_left h₁ hx,
    (projection_apply_eq_zero_iff h₁.symm).2 hx, map_zero, add_zero]

/-- On `q₁`, the comparison of two splittings is the projection onto `q₂` along `p₂`. -/
theorem splittingEquiv_apply_of_mem_right {x : E} (hx : x ∈ q₁) :
    splittingEquiv h₁ h₂ hp hq x = q₂.projection p₂ h₂.symm x := by
  rw [splittingEquiv_apply, projection_apply_of_mem_left h₁.symm hx,
    (projection_apply_eq_zero_iff h₁).2 hx, map_zero, zero_add]

/-- Exchanging the roles of the two summands in both splittings gives the same comparison. -/
theorem splittingEquiv_swap :
    splittingEquiv h₁.symm h₂.symm hq hp = splittingEquiv h₁ h₂ hp hq := by
  ext x
  rw [splittingEquiv_apply, splittingEquiv_apply, add_comm]

/-- On `p₂`, the inverse of the comparison of two splittings is the projection onto `p₁` along
`q₂`. -/
theorem splittingEquiv_symm_apply_of_mem_left {y : E} (hy : y ∈ p₂) :
    (splittingEquiv h₁ h₂ hp hq).symm y = p₁.projection q₂ hp y := by
  rw [LinearEquiv.symm_apply_eq,
    splittingEquiv_apply_of_mem_left h₁ h₂ hp hq (projection_apply_mem hp y),
    -- The projection of `y` onto `p₁` along `q₂` differs from `y` by an element of `q₂`.
    projection_eq_self_sub_projection hp.symm, map_sub, projection_apply_of_mem_left h₂ hy,
    (projection_apply_eq_zero_iff h₂).2 (projection_apply_mem hp.symm y), sub_zero]

/-- On `q₂`, the inverse of the comparison of two splittings is the projection onto `q₁` along
`p₂`. -/
theorem splittingEquiv_symm_apply_of_mem_right {y : E} (hy : y ∈ q₂) :
    (splittingEquiv h₁ h₂ hp hq).symm y = q₁.projection p₂ hq y := by
  rw [← splittingEquiv_swap]
  exact splittingEquiv_symm_apply_of_mem_left h₁.symm h₂.symm hq hp hy

/-- The inverse of the comparison of two splittings projects the `p₂`-component of `y` onto `p₁`
along `q₂` and its `q₂`-component onto `q₁` along `p₂`. -/
@[simp]
theorem splittingEquiv_symm_apply (y : E) :
    (splittingEquiv h₁ h₂ hp hq).symm y =
      p₁.projection q₂ hp (p₂.projection q₂ h₂ y) +
        q₁.projection p₂ hq (q₂.projection p₂ h₂.symm y) := by
  conv_lhs => rw [← projection_add_projection_eq_self h₂ y]
  rw [map_add, splittingEquiv_symm_apply_of_mem_left h₁ h₂ hp hq (projection_apply_mem h₂ y),
    splittingEquiv_symm_apply_of_mem_right h₁ h₂ hp hq (projection_apply_mem h₂.symm y)]

/-- **The comparison of two splittings carries `p₁` onto `p₂`.** -/
theorem map_splittingEquiv_left : p₁.map (splittingEquiv h₁ h₂ hp hq : E →ₗ[R] E) = p₂ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, splittingEquiv_apply_of_mem_left h₁ h₂ hp hq hx]
    exact projection_apply_mem h₂ x
  · intro y hy
    refine ⟨p₁.projection q₂ hp y, projection_apply_mem hp y, ?_⟩
    rw [LinearEquiv.coe_coe, ← splittingEquiv_symm_apply_of_mem_left h₁ h₂ hp hq hy,
      LinearEquiv.apply_symm_apply]

/-- **The comparison of two splittings carries `q₁` onto `q₂`.** -/
theorem map_splittingEquiv_right : q₁.map (splittingEquiv h₁ h₂ hp hq : E →ₗ[R] E) = q₂ := by
  rw [← splittingEquiv_swap]
  exact map_splittingEquiv_left h₁.symm h₂.symm hq hp

/-- **Comparing a splitting with itself gives the identity.** -/
@[simp]
theorem splittingEquiv_self : splittingEquiv h₁ h₁ h₁ h₁.symm = LinearEquiv.refl R E := by
  ext x
  rw [splittingEquiv_apply, projection_apply_of_mem_left h₁ (projection_apply_mem h₁ x),
    projection_apply_of_mem_left h₁.symm (projection_apply_mem h₁.symm x),
    projection_add_projection_eq_self, LinearEquiv.refl_apply]

end Submodule
