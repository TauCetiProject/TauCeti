/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of a direct sum

For quasicoherent sheaves `F` and `G` on a scheme `X`, the relative spectrum of the symmetric
algebra of the direct sum `F ⊞ G` is the fibre product of those of `F` and `G`:

`Spec_X (Sym (F ⊞ G)) ≅ Spec_X (Sym F) ×_X Spec_X (Sym G)`,

with projections the relative spectra of the symmetric algebras of the inclusions
`F ⟶ F ⊞ G ⟵ G`. By the universal property of `Spec_X (Sym F)`, a morphism
`T ⟶ Spec_X (Sym (F ⊞ G))` over `X` is a module map `F ⊞ G ⟶ q_* 𝒪_T`, and such a map is a pair
of module maps `F ⟶ q_* 𝒪_T` and `G ⟶ q_* 𝒪_T`, so the statement follows from the Yoneda lemma
in `Over X`. Equivalently, the contravariant linear scheme `𝕍(F) = Spec_X (Sym F)` turns direct
sums of quasicoherent sheaves into fibre products over `X` (Stacks Project, Tag 01M1).

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraBiprodFanIsLimit`: `Spec_X (Sym (F ⊞ G))`
  is the product of `Spec_X (Sym F)` and `Spec_X (Sym G)` in schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_relativeSpecSymmetricAlgebra_biprod`: it is the fibre
  product `Spec_X (Sym F) ×_X Spec_X (Sym G)`.

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

variable {X : Scheme.{u}}

/-- The binary fan in schemes over `X` whose cone point is `Spec_X (Sym (F ⊞ G))` and whose
projections are the relative spectra of the symmetric algebras of the inclusions
`F ⟶ F ⊞ G ⟵ G`. -/
abbrev relativeSpecSymmetricAlgebraBiprodFan (F G : QuasicoherentSheaf X) :
    BinaryFan ((MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))))
      ((MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj G)))) :=
  BinaryFan.mk
    ((MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map ((symmetricAlgebra X).map biprod.inl).op))
    ((MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map ((symmetricAlgebra X).map biprod.inr).op))

/-- **The relative spectrum of the symmetric algebra of a direct sum is a product.** For
quasicoherent sheaves `F` and `G` on `X`, `Spec_X (Sym (F ⊞ G))`, with the relative spectra of the
symmetric algebras of the inclusions `F ⟶ F ⊞ G ⟵ G`, is the product of `Spec_X (Sym F)` and
`Spec_X (Sym G)` in schemes over `X`. On points, the lift of a pair of module maps
`φ : F ⟶ q_* 𝒪_T` and `ψ : G ⟶ q_* 𝒪_T` is the point of `F ⊞ G ⟶ q_* 𝒪_T` restricting to `φ`
and `ψ`. -/
def relativeSpecSymmetricAlgebraBiprodFanIsLimit (F G : QuasicoherentSheaf X) :
    IsLimit (relativeSpecSymmetricAlgebraBiprodFan F G) :=
  -- The inclusion into `X.Modules` is additive, so it sends `F ⊞ G` to a biproduct there: module
  -- maps out of `F ⊞ G` are pairs of module maps out of `F` and `G`.
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules)
  let hc := (isBinaryBilimitOfPreserves (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules)
    (BinaryBiproduct.isBilimit F G)).isColimit
  BinaryFan.IsLimit.mk _
    (fun {T} f g ↦ (relativeSpecSymmetricAlgebraHomEquiv (F ⊞ G) T).symm
      (hc.desc (BinaryCofan.mk (relativeSpecSymmetricAlgebraHomEquiv F T f)
        (relativeSpecSymmetricAlgebraHomEquiv G T g))))
    (fun {T} _ _ ↦ (relativeSpecSymmetricAlgebraHomEquiv F T).injective <|
      (relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map _ T _).trans <|
        (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)).trans (hc.fac _ ⟨.left⟩))
    (fun {T} _ _ ↦ (relativeSpecSymmetricAlgebraHomEquiv G T).injective <|
      (relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map _ T _).trans <|
        (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)).trans (hc.fac _ ⟨.right⟩))
    (fun {T} _ _ m hf hg ↦ (relativeSpecSymmetricAlgebraHomEquiv (F ⊞ G) T).injective <|
      (BinaryCofan.IsColimit.hom_ext hc
        (((relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map _ T m).symm.trans
          (congrArg _ hf)).trans (hc.fac (BinaryCofan.mk _ _) ⟨.left⟩).symm)
        (((relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map _ T m).symm.trans
          (congrArg _ hg)).trans (hc.fac (BinaryCofan.mk _ _) ⟨.right⟩).symm)).trans
        (Equiv.apply_symm_apply _ _).symm)

/-- **The relative spectrum of the symmetric algebra of a direct sum is a fibre product.** For
quasicoherent sheaves `F` and `G` on `X`, `Spec_X (Sym (F ⊞ G))` is the fibre product
`Spec_X (Sym F) ×_X Spec_X (Sym G)`, with projections the relative spectra of the symmetric
algebras of the inclusions `F ⟶ F ⊞ G ⟵ G`. -/
theorem isPullback_relativeSpecSymmetricAlgebra_biprod (F G : QuasicoherentSheaf X) :
    IsPullback ((relativeSpec X).map ((symmetricAlgebra X).map (biprod.inl : F ⟶ F ⊞ G)).op).left
      ((relativeSpec X).map ((symmetricAlgebra X).map (biprod.inr : G ⟶ F ⊞ G)).op).left
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))).hom
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj G))).hom :=
  Over.isPullback_of_binaryFan_isLimit _ (relativeSpecSymmetricAlgebraBiprodFanIsLimit F G)

end

end TauCeti.AlgebraicGeometry
