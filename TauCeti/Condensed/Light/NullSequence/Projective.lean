/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Condensed.Light.NullSequence.Basic
public import Mathlib.Condensed.Light.InternallyProjective

import all Mathlib.Condensed.Light.Sequence

/-!
# Internal projectivity of the lifted convergent sequence

This is the universe-polymorphic version of the sequence projectivity argument in
`Mathlib.Condensed.Light.Sequence`, by Jonas van der Schaaf and Dagur Asgeirsson.
We reuse its generic topological helpers and adapt the categorical descent argument
from `OnePoint ℕ` to `OnePoint (ULift ℕ)`.
-/

public section

universe u

open CategoryTheory Category Functor LightProfinite OnePoint LightCondensed
  MonoidalCategory CartesianMonoidalCategory CompHausLike InternalProjectivityProof

namespace TauCeti

-- The one-point construction does not infer these transported instances, and countability
-- is needed for the product of fibres. Keep this alternative presentation local.
private instance : SecondCountableTopology (OnePoint (ULift.{u} ℕ)) :=
  (Homeomorph.ulift.onePointCongr).secondCountableTopology

private instance : T2Space (OnePoint (ULift.{u} ℕ)) :=
  Homeomorph.ulift.onePointCongr.symm.t2Space

private instance : Countable (OnePoint (ULift.{u} ℕ)) :=
  Homeomorph.ulift.onePointCongr.injective.countable

private abbrev sequence : LightProfinite.{u} := LightProfinite.of (OnePoint (ULift.{u} ℕ))

variable (R : Type u) [CommRing R]

/-- The diagonal together with the fibre at infinity covers the kernel pair. -/
private def kernelPairCover {S T : LightProfinite} (π : T ⟶ S ⊗ sequence) :
    (of _ (T ⊕ (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd S sequence) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd S sequence) ≫ π)))) ⟶
        CompHausLike.pullback π π := ⟨TopCat.ofHom {
  toFun := coverToFun _ _
  continuous_toFun := by dsimp [coverToFun]; fun_prop }⟩

open Limits in
/-- Correct a map on the fibre at infinity so that it descends along the cover. -/
private noncomputable def descentCocone {X : LightCondMod R} {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence)
    [Epi ((lightProfiniteToLightCondSet ⋙ free R).map <| kernelPairCover π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (σ : S ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (hr : LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r_inf =
      𝟙 (LightProfinite.fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
      (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π))) ⋙ free R) := by
  refine Cocone.ofCofork (Cofork.ofπ (g -
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g) ?_)
  rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map <| kernelPairCover π)]
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ free R)
      (coproductIsColimit _ _)).hom_ext
  -- Expose only the mapped coproduct carrier, so the additive laws match its arrows.
  dsimp only [Functor.mapCocone, Cocone.functoriality, coproductCocone, BinaryCofan.mk]
  rintro ⟨⟨⟩ | ⟨⟩⟩
  · simp only [Functor.comp_map,
      parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left, parallelPair_map_right,
      Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc, ← Functor.map_comp]
    rfl
  · simp only [pair_obj_right, Functor.comp_map, parallelPair_obj_zero,
      parallelPair_obj_one, parallelPair_map_left,
      Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc, parallelPair_map_right]
    simp only [← Functor.map_comp]
    have hf : (coproductCocone T (CompHausLike.pullback
        (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
        (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.right⟩ ≫
        kernelPairCover π ≫ CompHausLike.pullback.fst π π =
        CompHausLike.pullback.fst _ _ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) := rfl
    have hs : (coproductCocone T (CompHausLike.pullback
        (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
        (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.right⟩ ≫
        kernelPairCover π ≫ CompHausLike.pullback.snd π π =
        CompHausLike.pullback.snd _ _ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) := rfl
    dsimp only [coproductCocone, BinaryCofan.mk] at hf hs
    erw [hf, hs]
    simp only [assoc]
    repeat' erw [reassoc_of% hr]
    simp only [sub_self, zero_add]
    apply congrArg (fun k ↦ k ≫ g)
    apply congrArg (free R).map
    apply congrArg lightProfiniteToLightCondSet.map
    ext x
    exact congrArg (fun z : S × sequence ↦ (σ z.1).val) x.prop

/-- Refine a cover so its fibre at infinity splits and its kernel pair has the needed cover. -/
private lemma refineSequenceCover {S T : LightProfinite} (π : T ⟶ S ⊗ sequence) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ sequence) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ sequence) = g' ≫ π ∧
        IsSplitEpi
          (LightProfinite.fibreIncl ∞ (π' ≫ snd S' sequence) ≫ π' ≫ fst S' sequence) ∧
          Epi (kernelPairCover π') := by
  have := S'_compactSpace π π.hom.hom.continuous
  let S'π (n : sequence) : ↧(S' π) ⟶ LightProfinite.fibre n (π ≫ snd _ _) :=
    ⟨TopCat.ofHom {
      toFun x := x.val n,
      continuous_toFun := by refine (continuous_apply _).comp ?_; fun_prop }⟩
  let y' : ↧(S' π) ⟶ S :=
    ConcreteCategory.ofHom ⟨y π, y_continuous π π.hom.hom.continuous⟩
  let π' := CompHausLike.pullback.snd π (y' ▷ sequence)
  let σ' : sequence → LightProfinite.of (S' π) →
      CompHausLike.pullback π (y' ▷ sequence) := fun n ↦
    CompHausLike.pullback.lift _ _ (S'π n ≫ LightProfinite.fibreIncl _ _)
      (lift (𝟙 _) (const _ n)) <| by
      apply CartesianMonoidalCategory.hom_ext<;> ext x; exacts [x.prop n ∞, (x.val n).prop]
  have hσ (x : sequence) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).1 = s := rfl
  have hσ' (x : sequence) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).2 = x := rfl
  have : CompactSpace (fibres π' σ') := isCompact_iff_compactSpace.mp
    (fibres_closed π' π'.hom.hom.continuous σ' (by fun_prop) hσ').isCompact
  refine ⟨↧(S' π), ↧(fibres π' σ'), y',
    ⟨TopCat.ofHom ⟨Subtype.val, by fun_prop⟩⟩ ≫ π',
    ⟨TopCat.ofHom ⟨Subtype.val, by fun_prop⟩⟩ ≫ CompHausLike.pullback.fst _ _,
      ?_, ?_, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    refine fibres_surjective _ ?_ _ hσ hσ'
    exact (LightProfinite.epi_iff_surjective π').mp inferInstance
  · rw [LightProfinite.epi_iff_surjective]
    apply y_surjective
    exact (LightProfinite.epi_iff_surjective π).mp inferInstance
  · simp [π', CompHausLike.pullback.condition]
  · exact ⟨ConcreteCategory.ofHom ⟨(sectionOfFibreIncl π' σ' hσ'),
      (.subtype_mk (by fun_prop) _)⟩, rfl⟩
  · rw [LightProfinite.epi_iff_surjective]
    exact coverToFun_surjective _ _ hσ hσ'

/-- The fibre at infinity of a nonempty cover is injective, so its inclusion retracts. -/
private lemma inftyFibre_retraction {S T : LightProfinite} (π : T ⟶ S ⊗ sequence)
    [Epi π] [Nonempty S] :
    ∃ r : T ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _),
      LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r = 𝟙 _ := by
  have : Mono (LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) := by
    rw [CompHausLike.mono_iff_injective]
    exact Subtype.val_injective
  have : Nonempty (LightProfinite.fibre ∞ (π ≫ snd _ _)) := by
    obtain ⟨x, hx⟩ := (.comp ((fun y ↦ ⟨(Nonempty.some inferInstance, y), rfl⟩))
      ((LightProfinite.epi_iff_surjective _).mp inferInstance) :
        ((snd S sequence) ∘ π).Surjective) ∞
    exact ⟨x, by simpa using hx⟩
  exact Injective.factors (𝟙 _) (LightProfinite.fibreIncl ∞ (π ≫ snd _ _))

private theorem internallyProjective_free_onePointSequence :
    InternallyProjective ((free R).obj sequence.toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R sequence]
  intro X Y p hp S f
  obtain ⟨T, π, g, hπ, comm⟩ := LightCondMod.factorsThru_lightProfinite_epi_of_epi R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ :=
    refineSequenceCover π
  refine ⟨S', y', (LightProfinite.epi_iff_surjective _).mp inferInstance, ?_⟩
  by_cases hS' : Nonempty S'
  · obtain ⟨r_inf, hr⟩ := inftyFibre_retraction π'
    have : EffectiveEpi π' := by
      rw [LightProfinite.effectiveEpi_iff_surjective, ← LightProfinite.epi_iff_surjective]
      infer_instance
    let hπ' : RegularEpi <| lightProfiniteToLightCondSet.map π' :=
      regularEpiOfPreserves π' _ (CompHausLike.pullback.cone _ _)
        (CompHausLike.pullback.isLimit _ _)
    have hc := Limits.isColimitOfPreserves (free R) hπ'.isColimit
    refine ⟨hc.desc (descentCocone R π' ((lightProfiniteToLightCondSet ⋙ free R).map g' ≫ g)
      r_inf split.section_ hr), ?_⟩
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map π'),
      ← Functor.comp_map, ← map_comp_assoc]
    -- This is the same free map, presented as the colimit cocone leg.
    change _ = (((free R).mapCocone _).ι.app .one ≫
      hc.desc (descentCocone R π' _ r_inf split.section_ hr)) ≫ p
    rw [show ((free R).mapCocone _).ι.app .one ≫
      hc.desc (descentCocone R π' _ r_inf split.section_ hr) = _ from
        hc.fac (descentCocone R π' _ r_inf split.section_ hr) .one]
    dsimp only [descentCocone, Limits.Cocone.ofCofork, Limits.Cofork.ofπ]
    simp only [Limits.parallelPair_obj_one, Functor.comp_map, Functor.map_comp,
      assoc, eqToHom_refl, Preadditive.comp_add, Preadditive.comp_sub,
      id_comp, Preadditive.add_comp, Preadditive.sub_comp, ← comm]
    simp only [← Functor.map_comp, ← Functor.comp_map, ← assoc, ← comp]
    symm
    rw [sub_add, sub_eq_self, sub_eq_zero]
    simp only [Category.assoc]
    have : LightProfinite.fibreIncl ∞ (π' ≫ snd _ _) ≫ π' =
        LightProfinite.fibreIncl ∞ (π' ≫ snd _ _) ≫ π' ≫ fst _ _ ≫
          lift (𝟙 _) (const S' (∞ : sequence)) :=
      CartesianMonoidalCategory.hom_ext _ _ rfl (by ext a; exact a.prop)
    rw [reassoc_of% this, reassoc_of% split.id]
  · have h : IsEmpty (S' ⊗ sequence) := isEmpty_prod.mpr <| Or.inl <| by simpa using hS'
    have : IsIso π' :=
      ⟨ConcreteCategory.ofHom ⟨(h.elim ·), continuous_of_const <| by aesop⟩,
      by ext x; exact h.elim (π' x), by ext x; all_goals exact h.elim x⟩
    exact ⟨(lightProfiniteToLightCondSet ⋙ free R).map (inv π' ≫ g') ≫ g, by grind⟩

/-- The free light condensed module on the universe-lifted convergent sequence is internally
projective, as in Rodríguez Camargo, *Notes on Solid Geometry*, Theorem 2.3.3(3).
The proof adapts `LightCondensed.internallyProjective_free_natUnionInfty`
to the caller's universe. -/
theorem internallyProjective_free_liftedSequence :
    InternallyProjective ((free R).obj liftedSequence.{u}.toCondensed) := by
  have : InternallyProjective ((lightProfiniteToLightCondSet ⋙ free R).obj sequence) :=
    internallyProjective_free_onePointSequence R
  exact InternallyProjective.ofRetract
    ((Retract.ofIso (CompHausLike.isoOfHomeo (Y := sequence) liftedSequenceHomeomorph)).map
      (lightProfiniteToLightCondSet ⋙ free R))

/-- The null-sequence module is internally projective as a retract of the free module on
its marked convergent sequence. -/
theorem internallyProjective_nullSeq : InternallyProjective (nullSeq R) := by
  have : InternallyProjective
      ((lightProfiniteToLightCondSet ⋙ free R).obj (Under.mk inftyPoint.{u}).right) :=
    internallyProjective_free_liftedSequence R
  exact InternallyProjective.ofRetract (reducedLightFreeRetract R (Under.mk inftyPoint))

end TauCeti
