/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Representation
public import TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct

/-!
# Cartier divisors and the Picard group

The Cartier divisor tensor-product isomorphism makes the class map additive. Negation of Cartier
divisors corresponds to inversion in the Picard group.

## Main declarations

* `Scheme.CartierDivisor.toLineBundleClass_add` and `toLineBundleClassHom`: the additive
  comparison from Cartier divisors to line-bundle classes;
* `Scheme.CartierDivisor.toLineBundleClass_neg`: negation corresponds to the inverse class.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace

namespace TauCeti
namespace AlgebraicGeometry
namespace Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

section TensorProduct

variable (D E : CartierDivisor X)

/-- The class of the sheaf of `D + E` is the tensor product of the two divisor classes. -/
@[simp]
theorem toLineBundleClass_add :
    (D + E).toLineBundleClass = D.toLineBundleClass * E.toLineBundleClass := by
  have h (F : CartierDivisor X) :
      F.toLineBundleClass = LineBundleClass.mk F.toInvertibleSheaf := by
    apply toLineBundleClass_eq_mk_iff.mpr
    simpa only [toInvertibleSheaf_obj] using
      (⟨Iso.refl _⟩ : Nonempty (F.sheaf ≅ F.sheaf))
  rw [h (D + E), h D, h E, ← LineBundleClass.mk_tensorProduct,
    LineBundleClass.mk_eq_mk_iff]
  refine ⟨?_⟩
  simp only [toInvertibleSheaf_obj, InvertibleSheaf.tensorProduct_obj]
  exact (tensorProductSheafIso D E).symm

end TensorProduct

end
end CartierDivisor
end Scheme

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Negating a Cartier divisor gives the inverse line-bundle class. -/
@[simp]
theorem toLineBundleClass_neg (D : CartierDivisor X) :
    (-D).toLineBundleClass = D.toLineBundleClass⁻¹ := by
  apply mul_eq_one_iff_eq_inv'.mp
  rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero]

/-- The Cartier divisor map to the tensor-product Picard group, as an additive homomorphism. -/
noncomputable def toLineBundleClassHom : CartierDivisor X →+ Additive (LineBundleClass X) where
  toFun D := Additive.ofMul D.toLineBundleClass
  map_zero' := congrArg Additive.ofMul toLineBundleClass_zero
  map_add' D E := congrArg Additive.ofMul (toLineBundleClass_add D E)

/-- The bundled Cartier divisor comparison sends `D` to the class of `𝒪_X(D)`. -/
@[simp]
lemma toLineBundleClassHom_apply (D : CartierDivisor X) :
    toLineBundleClassHom D = Additive.ofMul D.toLineBundleClass := by
  rw [toLineBundleClassHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

end Scheme.CartierDivisor

end AlgebraicGeometry
end TauCeti
