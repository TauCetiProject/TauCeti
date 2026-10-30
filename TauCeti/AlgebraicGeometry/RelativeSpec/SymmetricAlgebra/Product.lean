/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Product
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of a coproduct

For quasicoherent sheaves `F` and `G` on a scheme `X`, the linear scheme `𝕍(F ⊕ G)` of their
coproduct is the fibre product `𝕍(F) ×_X 𝕍(G)`, where `𝕍(F) = Spec_X (Sym F)`
(Stacks Project, Tag 01M1, and EGA II, 1.7). Indeed the symmetric algebra is the free
quasicoherent algebra (`symmetricAlgebraAdjunction`), so it sends the coproduct `F ⊕ G` to the
coproduct `Sym F ⊗ Sym G` of quasicoherent algebras, and relative Spec, an anti-equivalence onto
affine schemes over `X`, sends that coproduct to the fibre product over `X`.

On points this is the bijection between module maps `F ⊕ G ⟶ q_* 𝒪_T` and pairs of module maps
`F ⟶ q_* 𝒪_T`, `G ⟶ q_* 𝒪_T` (`relativeSpecSymmetricAlgebraHomEquiv`).

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraBinaryFanIsLimit`: for a coproduct
  `F ⟶ P ⟵ G` of quasicoherent sheaves, `Spec_X (Sym P)` is the product of `Spec_X (Sym F)` and
  `Spec_X (Sym G)` in affine schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_relativeSpec_map_symmetricAlgebra_map`: the same
  statement as a fibre product of schemes over `X`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} {F G P : QuasicoherentSheaf X} {i₁ : F ⟶ P} {i₂ : G ⟶ P}

/-- **`Spec_X (Sym -)` turns coproducts into products.** If `i₁ : F ⟶ P ⟵ G : i₂` is a coproduct
of quasicoherent sheaves, then `Spec_X (Sym P)`, with the relative-spectrum maps of `Sym i₁` and
`Sym i₂`, is the product of `Spec_X (Sym F)` and `Spec_X (Sym G)` in affine schemes over `X`. -/
def relativeSpecSymmetricAlgebraBinaryFanIsLimit (hc : IsColimit (BinaryCofan.mk i₁ i₂)) :
    IsLimit (BinaryFan.mk ((relativeSpec X).map ((symmetricAlgebra X).map i₁).op)
      ((relativeSpec X).map ((symmetricAlgebra X).map i₂).op)) :=
  mapIsLimitOfPreservesOfIsLimit (relativeSpec X) _ _
    (BinaryCofan.IsColimit.op (mapIsColimitOfPreservesOfIsColimit (symmetricAlgebra X) _ _ hc))

/-- **The linear scheme of a coproduct is the fibre product.** If `i₁ : F ⟶ P ⟵ G : i₂` is a
coproduct of quasicoherent sheaves, then `Spec_X (Sym P)`, with the relative-spectrum maps of
`Sym i₁` and `Sym i₂`, is the fibre product `Spec_X (Sym F) ×_X Spec_X (Sym G)` of schemes. -/
theorem isPullback_relativeSpec_map_symmetricAlgebra_map
    (hc : IsColimit (BinaryCofan.mk i₁ i₂)) :
    IsPullback ((relativeSpec X).map ((symmetricAlgebra X).map i₁).op).left
      ((relativeSpec X).map ((symmetricAlgebra X).map i₂).op).left
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))).hom
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj G))).hom :=
  AffineSchemeOver.isPullback_of_binaryFan_isLimit _
    (relativeSpecSymmetricAlgebraBinaryFanIsLimit hc)

end

end TauCeti.AlgebraicGeometry
