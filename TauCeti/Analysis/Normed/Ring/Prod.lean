/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
import Mathlib.Algebra.Group.Prod

/-!
# Multiplicative pseudo-uniformisers of product rings

In a product `R₁ × R₂` of seminormed rings with the maximum norm, a pair `(ϖ₁, ϖ₂)` of
multiplicative pseudo-uniformisers is again a multiplicative pseudo-uniformiser whenever the two
factors have equal norm, `‖ϖ₁‖ = ‖ϖ₂‖` (`TauCeti.NormedRing.PseudoUniformizer.prod`):
multiplication by `(ϖ₁, ϖ₂)` scales both coordinates by the same factor, hence scales their
maximum by that factor. Equal norms are essential: if `‖ϖ₁‖ < ‖ϖ₂‖`, multiplying `(1, 0)` by
`(ϖ₁, ϖ₂)` has norm `‖ϖ₁‖` rather than `‖(ϖ₁, ϖ₂)‖ * ‖(1, 0)‖ = ‖ϖ₂‖`.
-/

public section

namespace TauCeti.NormedRing

namespace PseudoUniformizer

variable {R₁ R₂ : Type*} [SeminormedRing R₁] [SeminormedRing R₂]

/-- **Product of multiplicative pseudo-uniformisers of equal norm.** If `ϖ₁` and `ϖ₂` are
multiplicative pseudo-uniformisers of `R₁` and `R₂` with `‖ϖ₁‖ = ‖ϖ₂‖`, then `(ϖ₁, ϖ₂)` is a
multiplicative pseudo-uniformiser of `R₁ × R₂` for the maximum norm. -/
def prod (ϖ₁ : PseudoUniformizer R₁) (ϖ₂ : PseudoUniformizer R₂)
    (h : ‖(ϖ₁.unit : R₁)‖ = ‖(ϖ₂.unit : R₂)‖) : PseudoUniformizer (R₁ × R₂) where
  unit :=
    { val := ((ϖ₁.unit : R₁), (ϖ₂.unit : R₂))
      inv := ((↑ϖ₁.unit⁻¹ : R₁), (↑ϖ₂.unit⁻¹ : R₂))
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  norm_mul x := by
    simp only [Prod.norm_def, Prod.fst_mul, Prod.snd_mul, ϖ₁.norm_mul, ϖ₂.norm_mul, ← h, max_self,
      mul_max_of_nonneg _ _ ϖ₁.norm_pos.le]
  norm_pos := by
    simp only [Prod.norm_def, ← h, max_self, ϖ₁.norm_pos]
  norm_lt_one := by
    simp only [Prod.norm_def, ← h, max_self, ϖ₁.norm_lt_one]

/-- The underlying element of `ϖ₁.prod ϖ₂ h` is `(ϖ₁, ϖ₂)`. -/
@[simp]
theorem coe_unit_prod (ϖ₁ : PseudoUniformizer R₁) (ϖ₂ : PseudoUniformizer R₂)
    (h : ‖(ϖ₁.unit : R₁)‖ = ‖(ϖ₂.unit : R₂)‖) :
    (((ϖ₁.prod ϖ₂ h).unit : (R₁ × R₂)ˣ) : R₁ × R₂) = ((ϖ₁.unit : R₁), (ϖ₂.unit : R₂)) :=
  (rfl)

/-- The norm of `ϖ₁.prod ϖ₂ h` is the common norm `‖ϖ₁‖`. -/
theorem norm_prod (ϖ₁ : PseudoUniformizer R₁) (ϖ₂ : PseudoUniformizer R₂)
    (h : ‖(ϖ₁.unit : R₁)‖ = ‖(ϖ₂.unit : R₂)‖) :
    ‖(((ϖ₁.prod ϖ₂ h).unit : (R₁ × R₂)ˣ) : R₁ × R₂)‖ = ‖(ϖ₁.unit : R₁)‖ := by
  simp [Prod.norm_def, ← h]

end PseudoUniformizer

/-- A product of two seminormed rings is Tate if they admit multiplicative pseudo-uniformisers of
equal norm. -/
theorem IsTate.of_prod {R₁ R₂ : Type*} [SeminormedRing R₁] [SeminormedRing R₂]
    (ϖ₁ : PseudoUniformizer R₁) (ϖ₂ : PseudoUniformizer R₂)
    (h : ‖(ϖ₁.unit : R₁)‖ = ‖(ϖ₂.unit : R₂)‖) : IsTate (R₁ × R₂) :=
  ⟨⟨ϖ₁.prod ϖ₂ h⟩⟩

end TauCeti.NormedRing
