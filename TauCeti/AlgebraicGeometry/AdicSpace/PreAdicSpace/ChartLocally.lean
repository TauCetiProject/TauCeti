/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap

/-!
# Morphisms of pre-adic spaces chart-locally induced by morphisms of Huber pairs

Given a property `Q` of morphisms of Huber pairs, a morphism `f : X ⟶ Y` of pre-adic spaces is
*chart-locally `Q`* when every point of `X` has an open neighbourhood `U` mapped by `f` into an
open `V ⊆ Y` such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and
Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of Huber
pairs `(A, A⁺) → (B, B⁺)` satisfying `Q`. This is the shape of Wedhorn's Definition 8.48 and of
Huber's definition of adic morphisms (Huber 1994, §3); the name follows Mathlib's
`AlgebraicGeometry.affineLocally` for schemes.

The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs needs the structure
presheaf of `Spa(B, B⁺)` to be a sheaf, which is part of the data of the definition.

## Main definitions

* `TauCeti.PreAdicSpace.chartLocally`: the morphisms chart-locally induced by morphisms of Huber
  pairs satisfying a given property.

## Main results

* `TauCeti.PreAdicSpace.chartLocally_mono`: a weaker property of morphisms of Huber pairs gives a
  weaker chart-local property, with the same charts.
* `TauCeti.PreAdicSpace.chartLocally_respectsIso`: every chart-local property is invariant under
  isomorphisms of the source and of the target.
* `TauCeti.ValuationSpectrum.chartLocally_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs satisfying `Q` is chart-locally
  `Q`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.48.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

open ValuationSpectrum

/-- A morphism `f : X ⟶ Y` of pre-adic spaces is *chart-locally `Q`*, for a property `Q` of
morphisms of Huber pairs, when every point `x` of `X` has an open neighbourhood `U`, mapped by `f`
into an open `V` of `Y`, together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and
Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf, a morphism
`φ : (A, A⁺) → (B, B⁺)` satisfying `Q`, and isomorphisms identifying `X` restricted to `U` with
`Spa(B, B⁺)` and `Y` restricted to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism
induced by `φ`. -/
def chartLocally
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop) :
    MorphismProperty PreAdicSpace.{u} := fun X Y f ↦
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : Q φ)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.ofRestrict _ ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.ofRestrict _

/-- Unfolding lemma for `TauCeti.PreAdicSpace.chartLocally`. -/
theorem chartLocally_iff
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    {X Y : PreAdicSpace.{u}} (f : X ⟶ Y) : chartLocally Q f ↔
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
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
          φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.ofRestrict _ :=
  Iff.rfl

section

variable {Q Q' : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}

/-- **Monotonicity**: if every morphism of Huber pairs satisfying `Q` satisfies `Q'`, then every
chart-locally `Q` morphism is chart-locally `Q'`, with the same charts. -/
theorem chartLocally_mono
    (h : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B} (φ : Pair.Hom S T), Q φ → Q' φ)
    {X Y : PreAdicSpace.{u}} {f : X ⟶ Y} (hf : chartLocally Q f) : chartLocally Q' f := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf x
  exact ⟨U, hx, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, h φ hφ, hsheaf, eU, eV, hfac⟩

variable {X Y : PreAdicSpace.{u}}

/-- Precomposing a chart-locally `Q` morphism with an isomorphism gives a chart-locally `Q`
morphism: over the same opens of the target, `e` identifies the restrictions of the two sources. -/
private theorem chartLocally_iso_hom_comp {X' : PreAdicSpace.{u}} (e : X' ≅ X) {f : X ⟶ Y}
    (hf : chartLocally Q f) : chartLocally Q (e.hom ≫ f) := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf (e.hom.base x)
  refine ⟨(Opens.map e.hom.base).obj U, hx, V, fun y hy ↦ hUV hy, A, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, (restrictIso e.symm U).symm ≪≫ eU, eV, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hfac, restrictIso_inv_ofRestrict_assoc]
  -- `e.symm.inv` is `e.hom` (`Iso.symm_inv`, a `rfl`-lemma); it also occurs in the open restricted
  -- to, so `rw` cannot rewrite it on one side only
  rfl

/-- Postcomposing a chart-locally `Q` morphism with an isomorphism `e : Y ≅ Y'` gives a
chart-locally `Q` morphism: `e` carries the opens of the definition to opens of `Y'`, identifying
the restrictions of `Y` and `Y'` to them. -/
private theorem chartLocally_comp_iso_hom {Y' : PreAdicSpace.{u}} (e : Y ≅ Y') {f : X ⟶ Y}
    (hf : chartLocally Q f) : chartLocally Q (f ≫ e.hom) := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf x
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

/-- **Being chart-locally `Q` is invariant under isomorphisms** of the source and of the target,
for every property `Q` of morphisms of Huber pairs. -/
instance chartLocally_respectsIso : MorphismProperty.RespectsIso (chartLocally.{u} Q) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ chartLocally_iso_hom_comp e hf)
    (fun e _ hf ↦ chartLocally_comp_iso_hom e hf)

end

end PreAdicSpace

namespace ValuationSpectrum

open PreAdicSpace

variable {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B]
  {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus))

/-- **The morphism of adic spectra induced by a morphism of Huber pairs satisfying `Q` is
chart-locally `Q`**, witnessed over the whole of `Spa(B, B⁺)` and `Spa(A, A⁺)`, for `B` complete
and Hausdorff with sheafy structure presheaf. -/
theorem chartLocally_presentationLimitPreAdicSpaceComap (φ : Pair.Hom S T) (hφ : Q φ) :
    chartLocally Q (presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf) := by
  refine (chartLocally_iff _).mpr fun _ ↦ ⟨⊤, trivial, ⊤, le_top, A, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, restrictTopIso _, restrictTopIso _, ?_⟩
  rw [← restrictTopIso_hom, ← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id]

end ValuationSpectrum

end TauCeti

end
