/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.CategoryTheory.Monoidal.CommMon
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Relative spectra of tensor products

For quasi-coherent commutative algebras `A` and `B` on a scheme `X`, the tensor product
`A ⊗ B` is again quasi-coherent, and it is the coproduct of `A` and `B` among quasi-coherent
algebras. Since relative Spec is an anti-equivalence onto affine schemes over `X`, it turns
this coproduct into a product of affine `X`-schemes, which is the fibre product over `X`:

`Spec_X (A ⊗ B) ≅ Spec_X A ×_X Spec_X B`,

with projections the relative spectra of the inclusions `A ⟶ A ⊗ B ⟵ B`. This identification
is how fibrewise operations on affine schemes over `X`, such as the addition map of a linear
scheme `Spec_X A ×_X Spec_X A ⟶ Spec_X A`, are encoded by comultiplications `A ⟶ A ⊗ A`.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.binaryCofanIsColimit`: the tensor product of
  quasi-coherent algebras is their coproduct;
* `TauCeti.AlgebraicGeometry.relativeSpecBinaryFanIsLimit`: the relative spectrum of a tensor
  product is the product of the relative spectra in affine schemes over `X`;
* `CategoryTheory.CommMon.isPullback_relativeSpecMap_inl_inr`: the relative spectrum of
  `A ⊗ B` is the fibre product of the relative spectra of `A` and `B` over `X`.

## References

* The Stacks Project, Tag 01LQ (relative spectrum as a functor).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.5.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace QuasicoherentAlgebra

/-- The tensor product of two quasi-coherent commutative algebras. -/
abbrev tensorObj (A B : QuasicoherentAlgebra X) : QuasicoherentAlgebra X :=
  ⟨CommMon.tensorObj A.obj B.obj, inferInstanceAs ((A.obj.X ⊗ B.obj.X).IsQuasicoherent)⟩

/-- The binary cofan `A ⟶ A ⊗ B ⟵ B` of quasi-coherent algebras. -/
abbrev binaryCofan (A B : QuasicoherentAlgebra X) : BinaryCofan A B :=
  BinaryCofan.mk (P := tensorObj A B) (ObjectProperty.homMk (CommMon.inl A.obj B.obj))
    (ObjectProperty.homMk (CommMon.inr A.obj B.obj))

/-- The tensor product of quasi-coherent algebras is their coproduct. -/
def binaryCofanIsColimit (A B : QuasicoherentAlgebra X) : IsColimit (binaryCofan A B) :=
  isColimitOfReflectsOfMapIsColimit (ObjectProperty.ι _) _ _
    (CommMon.binaryCofanIsColimit A.obj B.obj)

instance : HasBinaryCoproducts (QuasicoherentAlgebra X) :=
  @hasBinaryCoproducts_of_hasColimit_pair _ _ fun {A B} ↦
    ⟨⟨⟨_, binaryCofanIsColimit A B⟩⟩⟩

end QuasicoherentAlgebra

/-- The relative spectrum of a tensor product `A ⊗ B` of quasi-coherent algebras, with the
relative spectra of the two inclusions, is the product of `Spec_X A` and `Spec_X B` in affine
schemes over `X`. -/
def relativeSpecBinaryFanIsLimit (A B : QuasicoherentAlgebra X) :
    IsLimit (BinaryFan.mk ((relativeSpec X).map (QuasicoherentAlgebra.binaryCofan A B).inl.op)
      ((relativeSpec X).map (QuasicoherentAlgebra.binaryCofan A B).inr.op)) :=
  mapIsLimitOfPreservesOfIsLimit (relativeSpec X) _ _
    (BinaryCofan.IsColimit.op (QuasicoherentAlgebra.binaryCofanIsColimit A B))

/-- The relative spectrum of the tensor product `A ⊗ B` of quasi-coherent algebras is the
fibre product `Spec_X A ×_X Spec_X B`, with projections the relative spectra of the
inclusions `A ⟶ A ⊗ B ⟵ B`. -/
theorem _root_.CategoryTheory.CommMon.isPullback_relativeSpecMap_inl_inr
    (A B : CommMon X.Modules) [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] :
    IsPullback (CommMon.relativeSpecMap (CommMon.inl A B))
      (CommMon.relativeSpecMap (CommMon.inr A B)) A.relativeSpecToBase B.relativeSpecToBase :=
  have : PreservesFiniteLimits (MorphismProperty.Over.forget @IsAffineHom ⊤ X) := by
    -- Mathlib's instance for `MorphismProperty.Over.forget` does not unify with this goal at
    -- instance transparency, so it is applied directly.
    apply MorphismProperty.Over.instPreservesFiniteLimitsTopOverForget
  Over.isPullback_of_binaryFan_isLimit _
    (mapIsLimitOfPreservesOfIsLimit (MorphismProperty.Over.forget _ _ X) _ _
      (relativeSpecBinaryFanIsLimit ⟨A, inferInstance⟩ ⟨B, inferInstance⟩))

end

end TauCeti.AlgebraicGeometry
