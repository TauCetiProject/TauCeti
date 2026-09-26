/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Representation
public import TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct

/-!
# The Picard group of an integral scheme

The Cartier divisor tensor-product isomorphism makes the class map additive. Since every
line-bundle class on an integral scheme is represented by a Cartier divisor, the class of
`𝒪_X(-D)` provides its inverse.

## Main declarations

* `Scheme.CartierDivisor.toLineBundleClass_add` and `toLineBundleClassHom`: the additive
  comparison from Cartier divisors to line-bundle classes;
* `LineBundleClass.isUnit` and its `CommGroup` instance: the Picard group of an integral scheme.
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

/-- The line-bundle class of `-D` inverts the class of `D`. -/
theorem isUnit_toLineBundleClass : IsUnit D.toLineBundleClass :=
  ⟨⟨D.toLineBundleClass, (-D).toLineBundleClass,
    by rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero],
    by rw [← toLineBundleClass_add, neg_add_cancel, toLineBundleClass_zero]⟩, rfl⟩

end TensorProduct

end
end CartierDivisor
end Scheme

namespace LineBundleClass

variable {X : Scheme.{u}} [IsIntegral X]

/-- Every line-bundle class on an integral scheme is invertible under tensor product. -/
theorem isUnit (a : LineBundleClass X) : IsUnit a := by
  obtain ⟨D, rfl⟩ := Scheme.CartierDivisor.toLineBundleClass_surjective a
  exact Scheme.CartierDivisor.isUnit_toLineBundleClass D

/-- Tensor product gives the Picard group of any integral scheme. -/
noncomputable instance : CommGroup (LineBundleClass X) :=
  commGroupOfIsUnit isUnit

end LineBundleClass

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
