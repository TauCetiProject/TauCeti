/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of a direct sum

For quasicoherent sheaves `F` and `G` on a scheme `X`, the linear scheme
`𝕍(F ⊕ G) = Spec_X (Sym (F ⊕ G))` is the fibre product `𝕍(F) ×_X 𝕍(G)`, with projections the
relative spectra of the symmetric algebras of the inclusions `F ⟶ F ⊕ G ⟵ G` (Stacks Project,
Tag 01M1, and EGA II, 1.7). On points this is the statement that a module map
`F ⊕ G ⟶ q_* 𝒪_T` is the same as a pair of module maps `F ⟶ q_* 𝒪_T` and `G ⟶ q_* 𝒪_T`: by the
universal property `relativeSpecSymmetricAlgebraHomEquiv`, these are the points of `𝕍(F ⊕ G)`,
`𝕍(F)` and `𝕍(G)` over a scheme `q : T ⟶ X`. The direct sum is given by any bilimit bicone in
the category of quasicoherent sheaves, for instance the chosen biproduct `F ⊞ G`.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraBinaryFanIsLimit`: `Spec_X (Sym (F ⊕ G))`
  is the product of `Spec_X (Sym F)` and `Spec_X (Sym G)` in schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_relativeSpec_map_symmetricAlgebra_map_inl_inr`: the same
  statement as a pullback square of schemes.

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

variable {X : Scheme.{u}} {F G : QuasicoherentSheaf X} {b : BinaryBicone F G}

/-- **The relative spectrum of the symmetric algebra of a direct sum is a fibre product.** For a
direct sum `F ⊕ G` of quasicoherent sheaves on `X`, given by a bilimit bicone `b`,
`Spec_X (Sym (F ⊕ G))` is the product of `Spec_X (Sym F)` and `Spec_X (Sym G)` in schemes over `X`,
with projections the relative spectra of the symmetric algebras of the inclusions
`F ⟶ F ⊕ G ⟵ G`. A pair of points of `Spec_X (Sym F)` and `Spec_X (Sym G)` over `T` lifts to the
point of `Spec_X (Sym (F ⊕ G))` whose module map `F ⊕ G ⟶ q_* 𝒪_T` restricts to their module
maps on `F` and `G`. -/
def relativeSpecSymmetricAlgebraBinaryFanIsLimit (hb : b.IsBilimit) :
    IsLimit (BinaryFan.mk
      ((MorphismProperty.Over.forget _ _ X).map
        ((relativeSpec X).map ((symmetricAlgebra X).map b.inl).op))
      ((MorphismProperty.Over.forget _ _ X).map
        ((relativeSpec X).map ((symmetricAlgebra X).map b.inr).op))) :=
  -- The inclusion of quasicoherent sheaves into all `𝒪_X`-modules is additive, so `b` is also a
  -- coproduct of `𝒪_X`-modules, which are the targets of the universal property of `Sym`.
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  have hc := (isBinaryBilimitOfPreserves
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) hb).isColimit
  BinaryFan.IsLimit.mk _
    (fun {T} t₁ t₂ ↦ (relativeSpecSymmetricAlgebraHomEquiv b.pt T).symm
      (hc.desc (BinaryCofan.mk (relativeSpecSymmetricAlgebraHomEquiv F T t₁)
        (relativeSpecSymmetricAlgebraHomEquiv G T t₂))))
    (fun {T} _ _ ↦ (relativeSpecSymmetricAlgebraHomEquiv F T).injective <|
      (relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map b.inl T _).trans
        ((congrArg (b.inl.hom ≫ ·) (Equiv.apply_symm_apply _ _)).trans (hc.fac _ ⟨.left⟩)))
    (fun {T} _ _ ↦ (relativeSpecSymmetricAlgebraHomEquiv G T).injective <|
      (relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map b.inr T _).trans
        ((congrArg (b.inr.hom ≫ ·) (Equiv.apply_symm_apply _ _)).trans (hc.fac _ ⟨.right⟩)))
    (fun {T} t₁ t₂ m h₁ h₂ ↦ (relativeSpecSymmetricAlgebraHomEquiv b.pt T).eq_symm_apply.2 <|
      BinaryCofan.IsColimit.hom_ext hc
        (((relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map b.inl T m).symm.trans
            (congrArg _ h₁)).trans
          (hc.fac (BinaryCofan.mk (relativeSpecSymmetricAlgebraHomEquiv F T t₁)
            (relativeSpecSymmetricAlgebraHomEquiv G T t₂)) ⟨.left⟩).symm)
        (((relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map b.inr T m).symm.trans
            (congrArg _ h₂)).trans
          (hc.fac (BinaryCofan.mk (relativeSpecSymmetricAlgebraHomEquiv F T t₁)
            (relativeSpecSymmetricAlgebraHomEquiv G T t₂)) ⟨.right⟩).symm))

/-- For a direct sum `F ⊕ G` of quasicoherent sheaves on `X`, given by a bilimit bicone `b`, the
square of schemes formed by `Spec_X (Sym (F ⊕ G))`, `Spec_X (Sym F)`, `Spec_X (Sym G)` and `X` is a
pullback square: `Spec_X (Sym (F ⊕ G)) ≅ Spec_X (Sym F) ×_X Spec_X (Sym G)`. -/
theorem isPullback_relativeSpec_map_symmetricAlgebra_map_inl_inr (hb : b.IsBilimit) :
    IsPullback ((relativeSpec X).map ((symmetricAlgebra X).map b.inl).op).left
      ((relativeSpec X).map ((symmetricAlgebra X).map b.inr).op).left
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))).hom
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj G))).hom :=
  Over.isPullback_of_binaryFan_isLimit _ (relativeSpecSymmetricAlgebraBinaryFanIsLimit hb)

end

end TauCeti.AlgebraicGeometry
