/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Product
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# The total space of a direct sum of vector bundles

The geometric total space `𝕍(E) = Spec_X (Sym E^∨)` of finite locally free sheaves on a scheme `X`
sends direct sums to fibre products: the total space of `E ⊕ F` is `𝕍(E) ×_X 𝕍(F)`, with
projections the maps of total spaces induced by the projections `E ⊕ F ⟶ E` and `E ⊕ F ⟶ F`
(Stacks Project, Tag 01M1, and EGA II, 1.7).

More generally, the functor `totalSpaceScheme X` preserves finite products
(`preservesFiniteProducts_totalSpaceScheme`); in particular the total space of the zero bundle is
`X`. The functor `totalSpaceScheme X` is the composite of
dualization, an anti-equivalence sending direct sums to direct sums; of the inclusion into
quasicoherent sheaves, which is additive; of the symmetric algebra, a left adjoint
(`symmetricAlgebraAdjunction`); and of relative Spec, an anti-equivalence onto affine schemes
over `X`.

On points over a scheme `q : T ⟶ X`, this says that a section of `q^* (E ⊕ F)` is a pair of
sections of `q^* E` and `q^* F` (`totalSpaceHomEquiv`).

## Main declarations

* `TauCeti.AlgebraicGeometry.preservesFiniteProducts_totalSpaceScheme`: the total space functor
  preserves finite products;
* `TauCeti.AlgebraicGeometry.totalSpaceSchemeBinaryFanIsLimit`: the total space of `E ⊞ F`, with
  the maps induced by the two projections, is the product of the total spaces of `E` and `F` in
  affine schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_totalSpaceScheme_map_fst_snd`: the same statement as a
  fibre product of schemes over `X`.

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

/-- **The total space of a vector bundle preserves finite products.** In particular the total
space of a direct sum of finite locally free sheaves is the fibre product of their total spaces
(`totalSpaceSchemeBinaryFanIsLimit`), and the total space of the zero bundle is `X`. -/
instance preservesFiniteProducts_totalSpaceScheme (X : Scheme.{u}) :
    PreservesFiniteProducts (totalSpaceScheme X) :=
  have : (dualFunctor (X := X)).rightOp.IsEquivalence := dualEquiv.isEquivalence_functor
  have := preservesFiniteProducts_op (toQuasicoherent X)
  have := preservesFiniteProducts_op (symmetricAlgebra X)
  inferInstanceAs (PreservesFiniteProducts (dualFunctor.rightOp ⋙
    (toQuasicoherent X).op ⋙ (symmetricAlgebra X).op ⋙ relativeSpec X))

variable {X : Scheme.{u}}

-- As for `FiniteLocallyFreeSheaf.rank_biprod_apply`, binary biproducts `E ⊞ F` are obtained from
-- the finite biproducts of `FiniteLocallyFreeSheaf X`.
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **The total space of a direct sum is the product of the total spaces.** For finite locally
free sheaves `E` and `F`, the total space of `E ⊞ F`, with the maps of total spaces induced by the
projections `E ⊞ F ⟶ E` and `E ⊞ F ⟶ F`, is the product of the total spaces of `E` and `F` in
affine schemes over `X`. -/
def totalSpaceSchemeBinaryFanIsLimit (E F : FiniteLocallyFreeSheaf X) :
    IsLimit (BinaryFan.mk ((totalSpaceScheme X).map (biprod.fst : E ⊞ F ⟶ E))
      ((totalSpaceScheme X).map (biprod.snd : E ⊞ F ⟶ F))) :=
  mapIsLimitOfPreservesOfIsLimit (totalSpaceScheme X) _ _ (BinaryBiproduct.isLimit E F)

/-- **The total space of a direct sum is the fibre product of the total spaces.** For finite
locally free sheaves `E` and `F`, the total space `𝕍(E ⊞ F)` is the fibre product
`𝕍(E) ×_X 𝕍(F)` of schemes, with projections the maps of total spaces induced by the
projections `E ⊞ F ⟶ E` and `E ⊞ F ⟶ F`. -/
theorem isPullback_totalSpaceScheme_map_fst_snd (E F : FiniteLocallyFreeSheaf X) :
    IsPullback ((totalSpaceScheme X).map (biprod.fst : E ⊞ F ⟶ E)).left
      ((totalSpaceScheme X).map (biprod.snd : E ⊞ F ⟶ F)).left
      ((totalSpaceScheme X).obj E).hom ((totalSpaceScheme X).obj F).hom :=
  AffineSchemeOver.isPullback_of_binaryFan_isLimit _ (totalSpaceSchemeBinaryFanIsLimit E F)

end

end TauCeti.AlgebraicGeometry
