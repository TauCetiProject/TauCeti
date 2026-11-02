/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# The total space of a direct sum of vector bundles

For finite locally free sheaves `E` and `F` on a scheme `X`, the geometric total space
`𝕍(E ⊕ F) = Spec_X (Sym (E ⊕ F)^∨)` of their direct sum is the fibre product `𝕍(E) ×_X 𝕍(F)`, with
projections the maps of total spaces induced by the projections `E ⟵ E ⊕ F ⟶ F` (Stacks Project,
Tag 01M1, and EGA II, 1.7). On points this is the statement that a section of `q^* (E ⊕ F)` is a
pair of sections of `q^* E` and `q^* F`: by `totalSpaceHomEquiv`, these are the points of
`𝕍(E ⊕ F)`, `𝕍(E)` and `𝕍(F)` over a scheme `q : T ⟶ X`, and pullback of modules preserves direct
sums. The direct sum is given by any bilimit bicone of finite locally free sheaves; for the chosen
biproduct `E ⊞ F` this gives an isomorphism `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` of schemes over `X`,
natural in `E` and `F` (`totalSpaceSchemeBiprodIso`).

More generally, the functor `totalSpaceScheme X` preserves finite products
(`preservesFiniteProducts_totalSpaceScheme`); in particular the total space of the zero bundle is
`X`. Indeed `totalSpaceScheme X` is the composite of dualization, an anti-equivalence; of the
inclusion into quasicoherent sheaves, which is additive; of the symmetric algebra, a left adjoint
(`symmetricAlgebraAdjunction`); and of relative Spec, an anti-equivalence onto affine schemes
over `X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceSchemeBinaryFanIsLimit`: the total space of a direct sum is
  the product of the total spaces in schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_totalSpaceScheme_map_fst_snd`: the same statement as a
  pullback square of schemes;
* `TauCeti.AlgebraicGeometry.totalSpaceSchemeBiprodIso`: the isomorphism `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)`
  over `X`, with naturality `totalSpaceSchemeBiprodIso_hom_naturality`;
* `TauCeti.AlgebraicGeometry.preservesFiniteProducts_totalSpaceScheme`: the total space functor
  preserves finite products.

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

/-- **The total space of a vector bundle preserves finite products.** In particular the total
space of a direct sum of finite locally free sheaves is the product of their total spaces in affine
schemes over `X`, and the total space of the zero bundle is `X`. -/
instance preservesFiniteProducts_totalSpaceScheme (X : Scheme.{u}) :
    PreservesFiniteProducts (totalSpaceScheme X) :=
  have : (dualFunctor (X := X)).rightOp.IsEquivalence := dualEquiv.isEquivalence_functor
  have := preservesFiniteProducts_op (toQuasicoherent X)
  have := preservesFiniteProducts_op (symmetricAlgebra X)
  inferInstanceAs (PreservesFiniteProducts (dualFunctor.rightOp ⋙
    (toQuasicoherent X).op ⋙ (symmetricAlgebra X).op ⋙ relativeSpec X))

variable {X : Scheme.{u}}

/-- **The total space of a direct sum of vector bundles is a fibre product.** For a direct sum
`E ⊕ F` of finite locally free sheaves on `X`, given by a bilimit bicone `b`, the total space
`𝕍(E ⊕ F)` is the product of `𝕍(E)` and `𝕍(F)` in schemes over `X`, with projections the maps of
total spaces induced by the projections `E ⟵ E ⊕ F ⟶ F`. A pair of points of `𝕍(E)` and `𝕍(F)`
over `q : T ⟶ X` lifts to the point of `𝕍(E ⊕ F)` whose section of `q^* (E ⊕ F)` projects to
their sections of `q^* E` and `q^* F`. -/
def totalSpaceSchemeBinaryFanIsLimit {E F : FiniteLocallyFreeSheaf X} {b : BinaryBicone E F}
    (hb : b.IsBilimit) :
    IsLimit (BinaryFan.mk
      ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map b.fst))
      ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map b.snd))) :=
  -- Pullback of modules along `q : T ⟶ X` is additive, so `q^* b` is a product of `𝒪_T`-modules,
  -- whose sections are the points of the total spaces over `T`.
  have hl (T : Over X) :=
    haveI := preservesBinaryBiproducts_of_preservesBiproducts
      (ObjectProperty.ι (Scheme.Modules.isFiniteLocallyFree X) ⋙ Scheme.Modules.pullback T.hom)
    (isBinaryBilimitOfPreserves
      (ObjectProperty.ι (Scheme.Modules.isFiniteLocallyFree X) ⋙ Scheme.Modules.pullback T.hom)
      hb).isLimit
  BinaryFan.IsLimit.mk _
    (fun {T} t₁ t₂ ↦ (totalSpaceHomEquiv b.pt T).symm
      ((hl T).lift (BinaryFan.mk (totalSpaceHomEquiv E T t₁) (totalSpaceHomEquiv F T t₂))))
    (fun {T} _ _ ↦ (totalSpaceHomEquiv E T).injective <|
      (totalSpaceHomEquiv_comp_map b.fst T _).trans
        ((congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ((hl T).fac _ ⟨.left⟩)))
    (fun {T} _ _ ↦ (totalSpaceHomEquiv F T).injective <|
      (totalSpaceHomEquiv_comp_map b.snd T _).trans
        ((congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ((hl T).fac _ ⟨.right⟩)))
    (fun {T} t₁ t₂ m h₁ h₂ ↦ (totalSpaceHomEquiv b.pt T).eq_symm_apply.2 <|
      BinaryFan.IsLimit.hom_ext (hl T)
        (((totalSpaceHomEquiv_comp_map b.fst T m).symm.trans (congrArg _ h₁)).trans
          ((hl T).fac (BinaryFan.mk (totalSpaceHomEquiv E T t₁) (totalSpaceHomEquiv F T t₂))
            ⟨.left⟩).symm)
        (((totalSpaceHomEquiv_comp_map b.snd T m).symm.trans (congrArg _ h₂)).trans
          ((hl T).fac (BinaryFan.mk (totalSpaceHomEquiv E T t₁) (totalSpaceHomEquiv F T t₂))
            ⟨.right⟩).symm))

/-- For a direct sum `E ⊕ F` of finite locally free sheaves on `X`, given by a bilimit bicone `b`,
the square of schemes formed by `𝕍(E ⊕ F)`, `𝕍(E)`, `𝕍(F)` and `X` is a pullback square:
`𝕍(E ⊕ F) ≅ 𝕍(E) ×_X 𝕍(F)`. -/
theorem isPullback_totalSpaceScheme_map_fst_snd {E F : FiniteLocallyFreeSheaf X}
    {b : BinaryBicone E F} (hb : b.IsBilimit) :
    IsPullback ((totalSpaceScheme X).map b.fst).left ((totalSpaceScheme X).map b.snd).left
      ((totalSpaceScheme X).obj E).hom ((totalSpaceScheme X).obj F).hom :=
  Over.isPullback_of_binaryFan_isLimit _ (totalSpaceSchemeBinaryFanIsLimit hb)

variable (E F : FiniteLocallyFreeSheaf X)

/-- **The total space of a direct sum of vector bundles.** The total space `𝕍(E ⊞ F)` of the
biproduct of finite locally free sheaves `E` and `F` is isomorphic over `X` to the fibre product
`𝕍(E) ×_X 𝕍(F)`, the cartesian product in schemes over `X`. Its components are the maps of total
spaces induced by the projections `E ⟵ E ⊞ F ⟶ F` (`totalSpaceSchemeBiprodIso_hom`). -/
def totalSpaceSchemeBiprodIso :
    (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (E ⊞ F)) ≅
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E) ⊗
        (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj F) :=
  (totalSpaceSchemeBinaryFanIsLimit (BinaryBiproduct.isBilimit E F)).conePointUniqueUpToIso
    (tensorProductIsBinaryProduct _ _)

/-- The isomorphism `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` is the pair of maps of total spaces induced by the
projections `E ⟵ E ⊞ F ⟶ F`. -/
@[simp]
lemma totalSpaceSchemeBiprodIso_hom :
    (totalSpaceSchemeBiprodIso E F).hom =
      lift ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.fst))
        ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.snd)) := by
  refine hom_ext _ _ ?_ ?_
  · rw [lift_fst]
    exact (totalSpaceSchemeBinaryFanIsLimit _).conePointUniqueUpToIso_hom_comp _ ⟨.left⟩
  · rw [lift_snd]
    exact (totalSpaceSchemeBinaryFanIsLimit _).conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

/-- The inverse of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` followed by the map of total spaces induced by the
first projection `E ⊞ F ⟶ E` is the first projection of the fibre product. Not a `simp` lemma:
`simp` unfolds the map of total spaces by `totalSpaceScheme_map`. -/
@[reassoc]
lemma totalSpaceSchemeBiprodIso_inv_comp_map_fst :
    (totalSpaceSchemeBiprodIso E F).inv ≫
        (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.fst) =
      fst _ _ := by
  rw [Iso.inv_comp_eq, totalSpaceSchemeBiprodIso_hom, lift_fst]

/-- The inverse of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` followed by the map of total spaces induced by the
second projection `E ⊞ F ⟶ F` is the second projection of the fibre product. Not a `simp` lemma:
`simp` unfolds the map of total spaces by `totalSpaceScheme_map`. -/
@[reassoc]
lemma totalSpaceSchemeBiprodIso_inv_comp_map_snd :
    (totalSpaceSchemeBiprodIso E F).inv ≫
        (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.snd) =
      snd _ _ := by
  rw [Iso.inv_comp_eq, totalSpaceSchemeBiprodIso_hom, lift_snd]

variable {E F} in
/-- **Naturality of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)`.** For morphisms `a : E ⟶ E'` and `c : F ⟶ F'` of
finite locally free sheaves, the map of total spaces induced by `a ⊞ c` corresponds to the
product of the maps of total spaces induced by `a` and `c`. -/
@[reassoc]
lemma totalSpaceSchemeBiprodIso_hom_naturality {E' F' : FiniteLocallyFreeSheaf X} (a : E ⟶ E')
    (c : F ⟶ F') :
    (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map (biprod.map a c)) ≫
        (totalSpaceSchemeBiprodIso E' F').hom =
      (totalSpaceSchemeBiprodIso E F).hom ≫
        ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map a) ⊗ₘ
          (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map c)) := by
  refine hom_ext _ _ ?_ ?_ <;>
    simp only [Category.assoc, totalSpaceSchemeBiprodIso_hom, lift_fst, lift_snd, tensorHom_fst,
      tensorHom_snd, lift_fst_assoc, lift_snd_assoc, ← Functor.map_comp, biprod.map_fst,
      biprod.map_snd]

end

end TauCeti.AlgebraicGeometry
