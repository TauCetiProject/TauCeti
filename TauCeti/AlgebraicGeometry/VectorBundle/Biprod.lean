/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# The total space of a direct sum of vector bundles

For finite locally free sheaves `E` and `F` on a scheme `X`, the geometric total space of the
direct sum is the fibre product of the total spaces:

`𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)`,

with projections the maps of total spaces induced by the projections `E ⟵ E ⊞ F ⟶ F`. This is
the direct-sum row of the dictionary between finite locally free sheaves and geometric vector
bundles (Stacks Project, Tag 01M1; Hartshorne, Exercise II.5.18).

The proof is the Yoneda lemma in `Over X`. For a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(E)` over `X` are global sections of `q^* E` (`totalSpaceHomEquiv`), naturally in `E`
(`totalSpaceHomEquiv_comp_map`). Pullback of modules is additive, so `q^* (E ⊞ F)` is the direct
sum of `q^* E` and `q^* F`, and a section of `q^* (E ⊞ F)` is a pair of sections of `q^* E` and
`q^* F`.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceBiprodFanIsLimit`: `𝕍(E ⊞ F)` is the product of `𝕍(E)` and
  `𝕍(F)` in schemes over `X`;
* `TauCeti.AlgebraicGeometry.isPullback_totalSpaceScheme_biprod`: it is the fibre product
  `𝕍(E) ×_X 𝕍(F)`;
* `TauCeti.AlgebraicGeometry.totalSpaceBiprodIso`: the resulting isomorphism
  `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)`, natural in `E` and `F`
  (`totalSpaceBiprodIso_hom_naturality`).

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The binary fan in schemes over `X` whose cone point is the total space `𝕍(E ⊞ F)` and whose
projections are the maps of total spaces induced by the projections `E ⟵ E ⊞ F ⟶ F`. -/
abbrev totalSpaceBiprodFan (E F : FiniteLocallyFreeSheaf X) :
    BinaryFan ((MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
      ((MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj F)) :=
  BinaryFan.mk ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.fst))
    ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map biprod.snd))

/-- For a scheme `q : T ⟶ X` over `X`, pullback of modules is additive, so `q^* (E ⊞ F)`, with
the pullbacks of the projections, is a product of `q^* E` and `q^* F`. -/
private def pullbackBiprodIsLimit (E F : FiniteLocallyFreeSheaf X) (T : Over X) :
    IsLimit ((ObjectProperty.ι _ ⋙ Scheme.Modules.pullback T.hom).mapBinaryBicone
      (BinaryBiproduct.bicone E F)).toCone :=
  have := preservesBinaryBiproducts_of_preservesBiproducts
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pullback T.hom)
  (isBinaryBilimitOfPreserves _ (BinaryBiproduct.isBilimit E F)).isLimit

/-- **The total space of a direct sum is a product.** For finite locally free sheaves `E` and `F`
on `X`, the total space `𝕍(E ⊞ F)`, with the maps induced by the projections
`E ⟵ E ⊞ F ⟶ F`, is the product of `𝕍(E)` and `𝕍(F)` in schemes over `X`. On points, the lift of
a pair of sections `s` of `q^* E` and `t` of `q^* F` is the point of the section of
`q^* (E ⊞ F)` whose projections are `s` and `t`. -/
def totalSpaceBiprodFanIsLimit (E F : FiniteLocallyFreeSheaf X) :
    IsLimit (totalSpaceBiprodFan E F) :=
  BinaryFan.IsLimit.mk _
    (fun {T} f g ↦ (totalSpaceHomEquiv (E ⊞ F) T).symm
      ((pullbackBiprodIsLimit E F T).lift
        (BinaryFan.mk (totalSpaceHomEquiv E T f) (totalSpaceHomEquiv F T g))))
    (fun {T} _ _ ↦ (totalSpaceHomEquiv E T).injective <|
      (totalSpaceHomEquiv_comp_map _ T _).trans <|
        (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans
          ((pullbackBiprodIsLimit E F T).fac _ ⟨.left⟩))
    (fun {T} _ _ ↦ (totalSpaceHomEquiv F T).injective <|
      (totalSpaceHomEquiv_comp_map _ T _).trans <|
        (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans
          ((pullbackBiprodIsLimit E F T).fac _ ⟨.right⟩))
    (fun {T} _ _ m hf hg ↦ (totalSpaceHomEquiv (E ⊞ F) T).injective <|
      (BinaryFan.IsLimit.hom_ext (pullbackBiprodIsLimit E F T)
        (((totalSpaceHomEquiv_comp_map _ T m).symm.trans (congrArg _ hf)).trans
          ((pullbackBiprodIsLimit E F T).fac (BinaryFan.mk _ _) ⟨.left⟩).symm)
        (((totalSpaceHomEquiv_comp_map _ T m).symm.trans (congrArg _ hg)).trans
          ((pullbackBiprodIsLimit E F T).fac (BinaryFan.mk _ _) ⟨.right⟩).symm)).trans
        (Equiv.apply_symm_apply _ _).symm)

/-- **The total space of a direct sum is a fibre product.** For finite locally free sheaves `E`
and `F` on `X`, the total space `𝕍(E ⊞ F)` is the fibre product `𝕍(E) ×_X 𝕍(F)`, with projections
the maps induced by the projections `E ⟵ E ⊞ F ⟶ F`. -/
theorem isPullback_totalSpaceScheme_biprod (E F : FiniteLocallyFreeSheaf X) :
    IsPullback ((totalSpaceScheme X).map (biprod.fst : E ⊞ F ⟶ E)).left
      ((totalSpaceScheme X).map (biprod.snd : E ⊞ F ⟶ F)).left
      ((totalSpaceScheme X).obj E).hom ((totalSpaceScheme X).obj F).hom :=
  Over.isPullback_of_binaryFan_isLimit _ (totalSpaceBiprodFanIsLimit E F)

/-- The isomorphism `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` between the total space of a direct sum and the
fibre product of the total spaces. -/
def totalSpaceBiprodIso (E F : FiniteLocallyFreeSheaf X) :
    ((totalSpaceScheme X).obj (E ⊞ F)).left ≅
      pullback ((totalSpaceScheme X).obj E).hom ((totalSpaceScheme X).obj F).hom :=
  (isPullback_totalSpaceScheme_biprod E F).isoPullback

/-- The first projection of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` is the map of total spaces induced by
the projection `E ⊞ F ⟶ E`. -/
@[reassoc (attr := simp)]
theorem totalSpaceBiprodIso_hom_fst (E F : FiniteLocallyFreeSheaf X) :
    (totalSpaceBiprodIso E F).hom ≫ pullback.fst _ _ =
      ((totalSpaceScheme X).map (biprod.fst : E ⊞ F ⟶ E)).left :=
  IsPullback.isoPullback_hom_fst _

/-- The second projection of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` is the map of total spaces induced
by the projection `E ⊞ F ⟶ F`. -/
@[reassoc (attr := simp)]
theorem totalSpaceBiprodIso_hom_snd (E F : FiniteLocallyFreeSheaf X) :
    (totalSpaceBiprodIso E F).hom ≫ pullback.snd _ _ =
      ((totalSpaceScheme X).map (biprod.snd : E ⊞ F ⟶ F)).left :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` followed by the map of total spaces induced by
the projection `E ⊞ F ⟶ E` is the first projection of the fibre product. -/
@[reassoc]
theorem totalSpaceBiprodIso_inv_fst (E F : FiniteLocallyFreeSheaf X) :
    (totalSpaceBiprodIso E F).inv ≫ ((totalSpaceScheme X).map (biprod.fst : E ⊞ F ⟶ E)).left =
      pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

/-- The inverse of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)` followed by the map of total spaces induced by
the projection `E ⊞ F ⟶ F` is the second projection of the fibre product. -/
@[reassoc]
theorem totalSpaceBiprodIso_inv_snd (E F : FiniteLocallyFreeSheaf X) :
    (totalSpaceBiprodIso E F).inv ≫ ((totalSpaceScheme X).map (biprod.snd : E ⊞ F ⟶ F)).left =
      pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

/-- **Naturality of `𝕍(E ⊞ F) ≅ 𝕍(E) ×_X 𝕍(F)`.** For morphisms `a : E ⟶ E'` and `b : F ⟶ F'`,
the map of total spaces induced by `a ⊞ b` corresponds to the map of fibre products induced by
the maps of total spaces of `a` and `b`. -/
@[reassoc]
theorem totalSpaceBiprodIso_hom_naturality {E E' F F' : FiniteLocallyFreeSheaf X} (a : E ⟶ E')
    (b : F ⟶ F') :
    ((totalSpaceScheme X).map (biprod.map a b)).left ≫ (totalSpaceBiprodIso E' F').hom =
      (totalSpaceBiprodIso E F).hom ≫
        pullback.map _ _ _ _ ((totalSpaceScheme X).map a).left ((totalSpaceScheme X).map b).left
          (𝟙 X) ((Category.comp_id ((totalSpaceScheme X).obj E).hom).trans
            (MorphismProperty.Over.w ((totalSpaceScheme X).map a)).symm)
          ((Category.comp_id ((totalSpaceScheme X).obj F).hom).trans
            (MorphismProperty.Over.w ((totalSpaceScheme X).map b)).symm) := by
  -- The underlying morphism of schemes of a composite in `AffineSchemeOver X` is by definition
  -- the composite of the underlying morphisms, so each component is `.left` of an equation in
  -- `AffineSchemeOver X` given by functoriality of `totalSpaceScheme X` and `biprod.map_fst`,
  -- `biprod.map_snd`. (`rw` and `simp` cannot use `MorphismProperty.Comma.comp_left` here:
  -- `AffineSchemeOver X` passes the class `IsAffineHom` as a `MorphismProperty`, which only
  -- typechecks after unfolding.)
  apply pullback.hom_ext <;>
    simp only [Category.assoc, totalSpaceBiprodIso_hom_fst, totalSpaceBiprodIso_hom_snd,
      pullback.lift_fst, pullback.lift_snd, totalSpaceBiprodIso_hom_fst_assoc,
      totalSpaceBiprodIso_hom_snd_assoc]
  · exact congrArg (fun φ ↦ φ.left) (show (totalSpaceScheme X).map (biprod.map a b) ≫
      (totalSpaceScheme X).map biprod.fst = (totalSpaceScheme X).map biprod.fst ≫
        (totalSpaceScheme X).map a by simp only [← Functor.map_comp, biprod.map_fst])
  · exact congrArg (fun φ ↦ φ.left) (show (totalSpaceScheme X).map (biprod.map a b) ≫
      (totalSpaceScheme X).map biprod.snd = (totalSpaceScheme X).map biprod.snd ≫
        (totalSpaceScheme X).map b by simp only [← Functor.map_comp, biprod.map_snd])

end

end TauCeti.AlgebraicGeometry
