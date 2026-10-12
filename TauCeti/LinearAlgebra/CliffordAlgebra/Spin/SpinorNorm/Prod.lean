/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

/-!
# Spinor norms of orthogonal sums

Let `Q₁` and `Q₂` be nondegenerate quadratic forms on finite-dimensional vector spaces over a
field in which `2` is invertible. An orthogonal automorphism `g₁` of `Q₁` and an orthogonal
automorphism `g₂` of `Q₂` combine into the orthogonal automorphism `g₁ ⊕ g₂` of the orthogonal
sum `Q₁.prod Q₂`. This file proves that the spinor norm is multiplicative along this
construction: `θ(g₁ ⊕ g₂) = θ(g₁) θ(g₂)`.

The reflection of `Q₁.prod Q₂` in a vector of either summand is the orthogonal sum of the
corresponding reflection with the identity, and has the same norm. Since reflections generate
each orthogonal group, the two sides agree. Restricting to determinant one gives the same formula
for the spinor norm on the special orthogonal groups.

## Main results

* `CliffordAlgebra.orthogonalSpinorNorm_orthogonalGroupProd`: the spinor norm of an orthogonal
  sum is the product of the spinor norms.
* `CliffordAlgebra.spinorNorm_specialOrthogonalGroupProd`: the same on the special orthogonal
  groups.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §55.
-/

public section

namespace CliffordAlgebra

open TauCeti

universe u v w

variable {K : Type u} {V₁ : Type v} {V₂ : Type w} [Field K] [Invertible (2 : K)]
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

/-- The spinor norm of the orthogonal sum `g₁ ⊕ g₂` is the product of the spinor norms of `g₁`
and `g₂`. -/
@[simp]
theorem orthogonalSpinorNorm_orthogonalGroupProd (hQ₁ : Q₁.Nondegenerate)
    (hQ₂ : Q₂.Nondegenerate)
    (g : QuadraticMap.orthogonalGroup Q₁ × QuadraticMap.orthogonalGroup Q₂) :
    orthogonalSpinorNorm (Q₁.prod Q₂) (hQ₁.prod hQ₂) (QuadraticMap.orthogonalGroupProd Q₁ Q₂ g) =
      orthogonalSpinorNorm Q₁ hQ₁ g.1 * orthogonalSpinorNorm Q₂ hQ₂ g.2 := by
  -- On each summand, both sides are homomorphisms agreeing on reflections.
  have h₁ : ((orthogonalSpinorNorm (Q₁.prod Q₂) (hQ₁.prod hQ₂)).comp
      (QuadraticMap.orthogonalGroupProd Q₁ Q₂)).comp (MonoidHom.inl _ _) =
        orthogonalSpinorNorm Q₁ hQ₁ := by
    refine QuadraticMap.orthogonalGroup_hom_ext Q₁ hQ₁ fun v _ ↦ ?_
    have hv : (Q₁.prod Q₂) (v, 0) = Q₁ v := by simp
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply,
      QuadraticMap.orthogonalGroupProd_reflectionOrthogonal_one,
      orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
    exact congrArg squareClassHom (Units.ext hv)
  have h₂ : ((orthogonalSpinorNorm (Q₁.prod Q₂) (hQ₁.prod hQ₂)).comp
      (QuadraticMap.orthogonalGroupProd Q₁ Q₂)).comp (MonoidHom.inr _ _) =
        orthogonalSpinorNorm Q₂ hQ₂ := by
    refine QuadraticMap.orthogonalGroup_hom_ext Q₂ hQ₂ fun w _ ↦ ?_
    have hw : (Q₁.prod Q₂) (0, w) = Q₂ w := by simp
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inr_apply,
      QuadraticMap.orthogonalGroupProd_one_reflectionOrthogonal,
      orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
    exact congrArg squareClassHom (Units.ext hw)
  have hg : g = (g.1, 1) * (1, g.2) := by simp
  rw [← h₁, ← h₂, hg, map_mul, map_mul]
  simp

/-- The spinor norm of the orthogonal sum of two special orthogonal automorphisms is the product
of their spinor norms. -/
-- `spinorNorm_apply` already simplifies the left-hand side, so this is not a simp-normal form.
theorem spinorNorm_specialOrthogonalGroupProd (hQ₁ : Q₁.Nondegenerate)
    (hQ₂ : Q₂.Nondegenerate)
    (g : QuadraticMap.specialOrthogonalGroup Q₁ × QuadraticMap.specialOrthogonalGroup Q₂) :
    spinorNorm (Q₁.prod Q₂) (hQ₁.prod hQ₂) (QuadraticMap.specialOrthogonalGroupProd Q₁ Q₂ g) =
      spinorNorm Q₁ hQ₁ g.1 * spinorNorm Q₂ hQ₂ g.2 := by
  have hg : QuadraticMap.specialOrthogonalToOrthogonal (Q₁.prod Q₂)
      (QuadraticMap.specialOrthogonalGroupProd Q₁ Q₂ g) =
      QuadraticMap.orthogonalGroupProd Q₁ Q₂ (QuadraticMap.specialOrthogonalToOrthogonal Q₁ g.1,
        QuadraticMap.specialOrthogonalToOrthogonal Q₂ g.2) := by
    apply Subtype.ext
    rw [QuadraticMap.coe_specialOrthogonalToOrthogonal, QuadraticMap.coe_orthogonalGroupProd,
      QuadraticMap.coe_specialOrthogonalGroupProd, QuadraticMap.coe_specialOrthogonalToOrthogonal,
      QuadraticMap.coe_specialOrthogonalToOrthogonal]
  rw [spinorNorm_apply, spinorNorm_apply, spinorNorm_apply, hg,
    orthogonalSpinorNorm_orthogonalGroupProd]

end CliffordAlgebra
