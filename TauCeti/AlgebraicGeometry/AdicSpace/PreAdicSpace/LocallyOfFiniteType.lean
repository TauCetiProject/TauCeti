/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

/-!
# Morphisms of pre-adic spaces locally of finite type

A morphism `f : X ⟶ Y` of pre-adic spaces is *locally of finite type* (Wedhorn, Definition 8.48)
when every point of `X` has an open neighbourhood `U` mapped by `f` into an open `V ⊆ Y` such that
`U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and Hausdorff, under which
`f` restricted to `U → V` is the morphism induced by a morphism of Huber pairs
`(A, A⁺) → (B, B⁺)` topologically of finite type (Wedhorn, Definition 8.42,
`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`). Wedhorn states the definition for morphisms
of adic spaces; it makes sense for every morphism of `𝒱^pre`, and is stated at that generality.
The name follows Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` for schemes.

The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs needs the structure
presheaf of `Spa(B, B⁺)` to be a sheaf, and the underlying ring homomorphism to carry open ideals
to ideals generating open ideals. The first is part of the data of the definition; the second
holds for every homomorphism topologically of finite type
(`TauCeti.Huber.IsTopologicallyFiniteType.isOpen_map`).

## Main definitions

* `TauCeti.PreAdicSpace.LocallyOfFiniteType`: Wedhorn Definition 8.48(1).

## Main results

* `TauCeti.ValuationSpectrum.locallyOfFiniteType_presentationLimitPreAdicSpaceComap`: the
  morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs topologically of finite
  type is locally of finite type; in particular, so is the identity of the adic spectrum of a
  complete Hausdorff Huber pair with sheafy structure presheaf
  (`TauCeti.ValuationSpectrum.locallyOfFiniteType_id_presentationLimitPreAdicSpace`).
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.respectsIso`: being locally of finite type is
  invariant under isomorphisms of the source and of the target.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top`: being locally of finite type can be
  checked on an open cover of the source.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.comp_of_isOpenImmersion`: composing with an open
  immersion into a larger target preserves being locally of finite type.

## Implementation notes

The definition through presentations by adic spectra, and the isomorphism-invariance results
`iso_hom_comp`, `comp_iso_hom` and `respectsIso`, are modelled on
`TauCeti.PreAdicSpace.IsClosedImmersion`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

open ValuationSpectrum

variable {X Y Z : PreAdicSpace.{u}}

/-- **Wedhorn Definition 8.48(1)**: a morphism `f : X ⟶ Y` of pre-adic spaces is *locally of
finite type* when every point `x` of `X` has an open neighbourhood `U`, mapped by `f` into an open
`V` of `Y`, together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and Hausdorff with
`Spa(B, B⁺)` having a sheaf as structure presheaf, a morphism `φ : (A, A⁺) → (B, B⁺)` topologically
of finite type, and isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y`
restricted to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def LocallyOfFiniteType (f : X ⟶ Y) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.ofRestrict _ ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.ofRestrict _

/-- Unfolding lemma for `TauCeti.PreAdicSpace.LocallyOfFiniteType`. -/
theorem locallyOfFiniteType_iff (f : X ⟶ Y) : LocallyOfFiniteType f ↔
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.ofRestrict _ ≫ f =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.ofRestrict _ :=
  Iff.rfl

/-- Precomposing a morphism locally of finite type with an isomorphism gives one locally of finite
type: over the same opens of the target, `e` identifies the restrictions of the two sources. -/
private theorem LocallyOfFiniteType.iso_hom_comp {X' : PreAdicSpace.{u}} (e : X' ≅ X)
    {f : X ⟶ Y} (hf : LocallyOfFiniteType f) : LocallyOfFiniteType (e.hom ≫ f) := by
  intro x
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf (e.hom.base x)
  refine ⟨(Opens.map e.hom.base).obj U, hx, V, fun y hy ↦ hUV hy, A, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, (restrictIso e.symm U).symm ≪≫ eU, eV, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hfac, restrictIso_inv_ofRestrict_assoc]
  -- `e.symm.inv` is `e.hom` (`Iso.symm_inv`, a `rfl`-lemma); it also occurs in the open restricted
  -- to, so `rw` cannot rewrite it on one side only
  rfl

/-- Postcomposing a morphism locally of finite type with an isomorphism `e : Y ≅ Y'` gives one
locally of finite type: `e` carries the opens of the definition to opens of `Y'`, identifying the
restrictions of `Y` and `Y'` to them. -/
private theorem LocallyOfFiniteType.comp_iso_hom {Y' : PreAdicSpace.{u}} (e : Y ≅ Y')
    {f : X ⟶ Y} (hf : LocallyOfFiniteType f) : LocallyOfFiniteType (f ≫ e.hom) := by
  intro x
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x
  -- `e⁻¹(e(V)) = V`
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e) V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  refine ⟨U, hx, (Opens.map e.inv.base).obj V, fun y hy ↦ ?_, A, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eU,
    (restrictIso e V).symm ≪≫ eV, ?_⟩
  · have hy' : f.base y ∈ ((Opens.map e.hom.base).obj ((Opens.map e.inv.base).obj V)) :=
      key.symm ▸ hUV hy
    exact hy'
  · rw [reassoc_of% hfac]
    simp

/-- **Being locally of finite type is invariant under isomorphisms** of the source and of the
target. -/
instance LocallyOfFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ hf.iso_hom_comp e)
    (fun e _ hf ↦ hf.comp_iso_hom e)

/-- **Being locally of finite type can be checked on an open cover of the source**: if `X` is
covered by opens `Uᵢ` such that every restriction `Uᵢ → X → Y` of `f` is locally of finite type,
then so is `f`. An open of a restriction is an open of `X`, by `restrictRestrictIso`. -/
theorem LocallyOfFiniteType.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (U : ι → Opens X)
    (hU : iSup U = ⊤) (h : ∀ i, LocallyOfFiniteType (X.ofRestrict (U i).isOpenEmbedding ≫ f)) :
    LocallyOfFiniteType f := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ Set.mem_univ x : x ∈ iSup U)
  obtain ⟨W, hx, V, hWV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eW, eV, hfac⟩ := h i ⟨x, hi⟩
  refine ⟨(U i).isOpenEmbedding.isOpenMap.functor.obj W, ⟨⟨x, hi⟩, hx, rfl⟩, V,
    fun _ ⟨y, hy, hxy⟩ ↦ hxy ▸ hWV hy, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf,
    (restrictRestrictIso X (U i).isOpenEmbedding W).symm ≪≫ eW, eV, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hfac, Iso.eq_inv_comp,
    restrictRestrictIso_hom_ofRestrict_assoc]

/-- **Composing with an open immersion into a larger target preserves being locally of finite
type**: an open `V` of `Y` over which `f` is induced by a morphism of Huber pairs is identified,
by the open immersion `g : Y ⟶ Z`, with the open `g(V)` of `Z`. -/
theorem LocallyOfFiniteType.comp_of_isOpenImmersion {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (g : Y ⟶ Z) [IsOpenImmersion g] : LocallyOfFiniteType (f ≫ g) := by
  intro x
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x
  -- the open `g(V)` of `Z`, and the identification of the two restrictions
  let V' : Opens Z := g.isOpenEmbedding.isOpenMap.functor.obj V
  have hr : Set.range (Y.ofRestrict V.isOpenEmbedding ≫ g).base =
      Set.range (Z.ofRestrict V'.isOpenEmbedding).base := by
    ext z
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩
      exact ⟨⟨g.base v, v, hv, rfl⟩, rfl⟩
    · rintro ⟨⟨_, v, hv, rfl⟩, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq _ _ hr
  refine ⟨U, hx, V', fun y hy ↦ ⟨f.base y, hUV hy, rfl⟩, A, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eU,
    e.symm ≪≫ eV, ?_⟩
  rw [reassoc_of% hfac]
  simp [e]

end PreAdicSpace

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B]
  {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus))

/-- **The morphism of adic spectra induced by a morphism of Huber pairs topologically of finite
type is locally of finite type**, witnessed over the whole of `Spa(B, B⁺)` and `Spa(A, A⁺)`, for
`B` complete and Hausdorff with sheafy structure presheaf. -/
theorem locallyOfFiniteType_presentationLimitPreAdicSpaceComap (φ : Pair.Hom S T)
    (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf) := by
  refine fun _ ↦ ⟨⊤, trivial, ⊤, le_top, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, restrictTopIso _,
    restrictTopIso _, ?_⟩
  rw [← restrictTopIso_hom, ← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id]

include hsheaf in
/-- **The identity of the adic spectrum of a complete Hausdorff Huber pair with sheafy structure
presheaf is locally of finite type**: it is induced by the identity of the pair, which is
topologically of finite type. -/
theorem locallyOfFiniteType_id_presentationLimitPreAdicSpace :
    LocallyOfFiniteType (𝟙 (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP')) := by
  simpa using locallyOfFiniteType_presentationLimitPreAdicSpaceComap P' P' hP' hP' hsheaf
    (Pair.Hom.id T) (Pair.Hom.isTopologicallyFiniteType_id T)

end ValuationSpectrum

end TauCeti

end
