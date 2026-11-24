/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.OpenImmersion

import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Affinoid charts of a fibre product of adic spaces

Let `IsPullback p q f g` be a pullback square in `AdicSpace` with vertex `Z`, and let
`W ≅ Spa(A, A⁺)`, `U ≅ Spa(B, B⁺)` and `V ≅ Spa(C, C⁺)` be open subspaces of `S`, `X` and `Y`,
on which `f` and `g` are given by adic morphisms of Huber pairs `A → B` and `A → C`. If the
completed tensor product `(B, B⁺) ⊗̂_A (C, C⁺)` is sheafy, the open subspace
`p⁻¹(U) ∩ q⁻¹(V)` of `Z` is canonically `Spa((B, B⁺) ⊗̂_A (C, C⁺))`, compatibly with the
projections: both are pullbacks of `U ⟶ S ⟵ V`
(`TauCeti.AdicSpace.isPullback_restrict_inf_of_isPullback` and
`TauCeti.AdicSpace.affinoid_isPullback`). The identification uses only the square and the three
charts, so it does not depend on how `Z` was glued from affinoid charts.

## Main declarations

* `TauCeti.AdicSpace.isPullback_comapOfPair_completedTensor_of_iso`: the completed tensor product
  of the charts is a pullback of `U ⟶ S ⟵ V`.
* `TauCeti.AdicSpace.restrictInfIsoCompletedTensor`: the isomorphism
  `Z|_{p⁻¹(U) ∩ q⁻¹(V)} ≅ Spa((B, B⁺) ⊗̂_A (C, C⁺))`.
* `TauCeti.AdicSpace.restrictInfIsoCompletedTensor_hom_inl`,
  `TauCeti.AdicSpace.restrictInfIsoCompletedTensor_hom_inr`,
  `TauCeti.AdicSpace.restrictInfIsoCompletedTensor_inv_inl`,
  `TauCeti.AdicSpace.restrictInfIsoCompletedTensor_inv_inr`: its compatibility with the
  projections.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.56, the affinoid
  fibre product used here through `TauCeti.AdicSpace.affinoid_isPullback`.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace TauCeti.AdicSpace

open Huber

universe u

variable {A B C : Type u}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] [IsHuberRing C]
  [Algebra A B] [Algebra A C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  {Z X Y S : AdicSpace.{u}}
  {SA : Pair A} {TB : Pair B} {UC : Pair C}
  {hSA : IsSheafyForEveryPresentation SA.plus} {hTB : IsSheafyForEveryPresentation TB.plus}
  {hUC : IsSheafyForEveryPresentation UC.plus}
  {φ : Pair.Hom SA TB} {ψ : Pair.Hom SA UC}
  {W : Opens S.obj} {U : Opens X.obj} {V : Opens Y.obj}
  {eW : S.restrict W ≅ ofPair SA hSA} {eU : X.restrict U ≅ ofPair TB hTB}
  {eV : Y.restrict V ≅ ofPair UC hUC}

/-- **The completed tensor product of affinoid charts is a fibre product of the charts over
`S`**: if `f : X ⟶ S` and `g : Y ⟶ S` are given on charts `U ≅ Spa(B, B⁺)`, `V ≅ Spa(C, C⁺)`
over a chart `W ≅ Spa(A, A⁺)` by adic morphisms of Huber pairs, and `(B, B⁺) ⊗̂_A (C, C⁺)` is
sheafy, then `Spa((B, B⁺) ⊗̂_A (C, C⁺))` is a pullback of `U ⟶ S` and `V ⟶ S`. -/
theorem isPullback_comapOfPair_completedTensor_of_iso {f : X ⟶ S} {g : Y ⟶ S}
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    IsPullback (comapOfPair hTB hTU (Pair.completedTensor.inl A TB UC) ≫ eU.inv)
      (comapOfPair hUC hTU (Pair.completedTensor.inr A TB UC) ≫ eV.inv)
      (X.ofRestrict U ≫ f) (Y.ofRestrict V ≫ g) := by
  have hpull : IsPullback (comapOfPair hTB hTU (Pair.completedTensor.inl A TB UC) ≫ eU.inv)
      (comapOfPair hUC hTU (Pair.completedTensor.inr A TB UC) ≫ eV.inv)
      (eU.hom ≫ comapOfPair hSA hTB φ ≫ eW.inv) (eV.hom ≫ comapOfPair hSA hUC ψ ≫ eW.inv) :=
    (affinoid_isPullback hSA hTB hUC hTU φ ψ hφ hψ).of_iso' (Iso.refl _) eU eV eW
      (by simp) (by simp) (by simp) (by simp)
  simpa only [Category.assoc, ← hf, ← hg, Iso.hom_inv_id_assoc] using
    hpull.comp_mono (S.ofRestrict W)

variable {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- **Affinoid chart of a fibre product**: for a pullback square
`IsPullback p q f g` and charts `W ≅ Spa(A, A⁺)` of `S`, `U ≅ Spa(B, B⁺)` of `X` and
`V ≅ Spa(C, C⁺)` of `Y` on which `f` and `g` are given by adic morphisms of Huber pairs, with
`(B, B⁺) ⊗̂_A (C, C⁺)` sheafy, the open subspace `p⁻¹(U) ∩ q⁻¹(V)` of `Z` is
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
noncomputable def restrictInfIsoCompletedTensor (hs : IsPullback p q f g)
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    Z.restrict ((Opens.map p.hom.base).obj U ⊓ (Opens.map q.hom.base).obj V) ≅
      ofPair (TB.completedTensor A UC) hTU :=
  (isPullback_restrict_inf_of_isPullback hs U V).isoIsPullback _ _
    (isPullback_comapOfPair_completedTensor_of_iso hTU hφ hψ hf hg)

/-- The isomorphism `restrictInfIsoCompletedTensor` is compatible with the first projections:
it carries the restriction of `p` to `Spa(inl)`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoCompletedTensor_hom_inl (hs : IsPullback p q f g)
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    (restrictInfIsoCompletedTensor hs hTU hφ hψ hf hg).hom ≫
        comapOfPair hTB hTU (Pair.completedTensor.inl A TB UC) ≫ eU.inv =
      liftRestrict p inf_le_left :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `restrictInfIsoCompletedTensor` is compatible with the second projections:
it carries the restriction of `q` to `Spa(inr)`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoCompletedTensor_hom_inr (hs : IsPullback p q f g)
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    (restrictInfIsoCompletedTensor hs hTU hφ hψ hf hg).hom ≫
        comapOfPair hUC hTU (Pair.completedTensor.inr A TB UC) ≫ eV.inv =
      liftRestrict q inf_le_right :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The inverse of `restrictInfIsoCompletedTensor` is compatible with the first projections:
it carries `Spa(inl)` to the restriction of `p`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoCompletedTensor_inv_inl (hs : IsPullback p q f g)
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    (restrictInfIsoCompletedTensor hs hTU hφ hψ hf hg).inv ≫ liftRestrict p inf_le_left =
      comapOfPair hTB hTU (Pair.completedTensor.inl A TB UC) ≫ eU.inv :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- The inverse of `restrictInfIsoCompletedTensor` is compatible with the second projections:
it carries `Spa(inr)` to the restriction of `q`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoCompletedTensor_inv_inr (hs : IsPullback p q f g)
    (hTU : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus)
    (hφ : φ.toRingHom = algebraMap A B) (hψ : ψ.toRingHom = algebraMap A C)
    (hf : eU.inv ≫ X.ofRestrict U ≫ f = comapOfPair hSA hTB φ ≫ eW.inv ≫ S.ofRestrict W)
    (hg : eV.inv ≫ Y.ofRestrict V ≫ g = comapOfPair hSA hUC ψ ≫ eW.inv ≫ S.ofRestrict W) :
    (restrictInfIsoCompletedTensor hs hTU hφ hψ hf hg).inv ≫ liftRestrict q inf_le_right =
      comapOfPair hUC hTU (Pair.completedTensor.inr A TB UC) ≫ eV.inv :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

end TauCeti.AdicSpace
