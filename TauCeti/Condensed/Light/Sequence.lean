/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.LightProfinite.Sequence
public import Mathlib.Condensed.Light.InternallyProjective
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.AlexandrovDiscrete
public import TauCeti.Topology.Compactification.OnePoint.Card
public import TauCeti.Topology.Compactification.OnePoint.SecondCountable

import all Mathlib.Condensed.Light.Sequence

/-!
# Internal projectivity of countable discrete one-point compactifications

For a commutative ring in any site universe, internal Hom out of the free light condensed
module on a countable discrete one-point compactification preserves epimorphisms.
In particular this applies to the native lifted convergent sequence.

The proof generalizes the categorical descent argument of Jonas van der Schaaf and Dagur
Asgeirsson in `Mathlib.Condensed.Light.Sequence`, reusing its generic topological helpers.
The mathematical reference is Rodríguez Camargo, *Notes on Solid Geometry*,
Theorem 2.3.3(3).
-/

public section

universe u

open CategoryTheory Category Functor LightProfinite OnePoint LightCondensed
  MonoidalCategory CartesianMonoidalCategory CompHausLike InternalProjectivityProof

namespace TauCeti

section

variable {α : Type u} [TopologicalSpace α] [DiscreteTopology α] [Countable α]

private abbrev sequence (α : Type u) [TopologicalSpace α] [DiscreteTopology α]
    [Countable α] : LightProfinite.{u} :=
  LightProfinite.of (OnePoint α)

variable (R : Type u) [CommRing R]

/-- The map from the diagonal and the kernel pair restricted to the infinity fibre.
It is a cover after `refineSequenceCover`, when each fibre over a pair `(s, n)` with
finite `n` is a singleton. -/
private def kernelPairCover {S T : LightProfinite} (π : T ⟶ S ⊗ (sequence α)) :
    (of _ (T ⊕ (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd S (sequence α)) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd S (sequence α)) ≫ π)))) ⟶
        CompHausLike.pullback π π := ⟨TopCat.ofHom {
  toFun := coverToFun _ _
  continuous_toFun := by dsimp [coverToFun]; fun_prop }⟩

/-- On the diagonal summand, the first kernel-pair projection is the identity. -/
private lemma kernelPairCover_left_fst {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α) :
    (coproductCocone T (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.left⟩ ≫
      kernelPairCover π ≫ CompHausLike.pullback.fst π π = 𝟙 T := rfl

/-- On the diagonal summand, the second kernel-pair projection is the identity. -/
private lemma kernelPairCover_left_snd {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α) :
    (coproductCocone T (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.left⟩ ≫
      kernelPairCover π ≫ CompHausLike.pullback.snd π π = 𝟙 T := rfl

/-- On the infinity summand, the first projection is the first fibre projection. -/
private lemma kernelPairCover_right_fst {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α) :
    (coproductCocone T (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.right⟩ ≫
      kernelPairCover π ≫ CompHausLike.pullback.fst π π =
        CompHausLike.pullback.fst _ _ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) := rfl

/-- On the infinity summand, the second projection is the second fibre projection. -/
private lemma kernelPairCover_right_snd {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α) :
    (coproductCocone T (CompHausLike.pullback
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π))).ι.app ⟨.right⟩ ≫
      kernelPairCover π ≫ CompHausLike.pullback.snd π π =
        CompHausLike.pullback.snd _ _ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) := rfl

/-- Correct a free map by subtracting its restriction to infinity and adding the chosen
section over the base. -/
private noncomputable def correctedMap {X : LightCondMod R} {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α)
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _))
    (σ : S ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _)) :
    ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X :=
  g - (lightProfiniteToLightCondSet ⋙ free R).map
    (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g

open Limits in
/-- Correct a map on the fibre at infinity so that it descends along the cover. -/
private noncomputable def descentCocone {X : LightCondMod R} {S T : LightProfinite}
    (π : T ⟶ S ⊗ (sequence α))
    [Epi ((lightProfiniteToLightCondSet ⋙ free R).map <| kernelPairCover π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (σ : S ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (hr : LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r_inf =
      𝟙 (LightProfinite.fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
      (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π))) ⋙ free R) := by
  refine Cocone.ofCofork (Cofork.ofπ (correctedMap R π g r_inf σ) ?_)
  dsimp only [correctedMap]
  rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map <| kernelPairCover π)]
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ free R)
      (coproductIsColimit _ _)).hom_ext
  dsimp only [Functor.mapCocone, Limits.Cocone.functoriality, coproductCocone,
    Limits.BinaryCofan.mk]
  rintro ⟨⟨⟩ | ⟨⟩⟩
  case' left =>
    have hf := kernelPairCover_left_fst π
    have hs := kernelPairCover_left_snd π
  case' right =>
    have hf := kernelPairCover_right_fst π
    have hs := kernelPairCover_right_snd π
  all_goals
    dsimp only [coproductCocone, Limits.BinaryCofan.mk] at hf hs
    simp only [Functor.comp_map,
      parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left, parallelPair_map_right,
      Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc, ← Functor.map_comp,
      hf, hs, reassoc_of% hf, reassoc_of% hs]
  simp only [reassoc_of% hr, sub_self, zero_add]
  apply congrArg (fun k ↦ k ≫ g)
  apply congrArg (free R).map
  apply congrArg lightProfiniteToLightCondSet.map
  ext x
  exact congrArg (fun z : S × (sequence α) ↦ (σ z.1).val) x.prop

/-- The leg at the target of the kernel-pair diagram is the corrected free map. -/
private lemma descentCocone_ι_one {X : LightCondMod R} {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α)
    [Epi ((lightProfiniteToLightCondSet ⋙ free R).map (kernelPairCover π))]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _))
    (σ : S ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _))
    (hr : LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r_inf = 𝟙 _) :
    (descentCocone R π g r_inf σ hr).ι.app .one = correctedMap R π g r_inf σ := rfl

/-- Refine a cover so its fibre at infinity splits and its kernel pair has the needed cover. -/
private lemma refineSequenceCover {S T : LightProfinite} (π : T ⟶ S ⊗ (sequence α)) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ (sequence α)) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ (sequence α)) = g' ≫ π ∧
        IsSplitEpi
          (LightProfinite.fibreIncl ∞ (π' ≫ snd S' (sequence α)) ≫ π' ≫ fst S' (sequence α)) ∧
          Epi (kernelPairCover π') := by
  have := S'_compactSpace π π.hom.hom.continuous
  let S'π (n : (sequence α)) : ↧(S' π) ⟶ LightProfinite.fibre n (π ≫ snd _ _) :=
    ⟨TopCat.ofHom {
      toFun x := x.val n,
      continuous_toFun := by refine (continuous_apply _).comp ?_; fun_prop }⟩
  let y' : ↧(S' π) ⟶ S :=
    ConcreteCategory.ofHom ⟨y π, y_continuous π π.hom.hom.continuous⟩
  let π' := CompHausLike.pullback.snd π (y' ▷ (sequence α))
  let σHom : sequence α → (LightProfinite.of (S' π) ⟶
      CompHausLike.pullback π (y' ▷ sequence α)) := fun n ↦
    CompHausLike.pullback.lift _ _ (S'π n ≫ LightProfinite.fibreIncl _ _)
      (lift (𝟙 _) (const _ n)) <| by
      apply CartesianMonoidalCategory.hom_ext<;> ext x; exacts [x.prop n ∞, (x.val n).prop]
  let σ' : sequence α → LightProfinite.of (S' π) →
      CompHausLike.pullback π (y' ▷ sequence α) := fun x ↦ σHom x
  have hπσ (x : sequence α) : σHom x ≫ π' = lift (𝟙 _) (const _ x) :=
    CompHausLike.pullback.lift_snd _ _ _ _ _
  have hσ (x : sequence α) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).1 = s :=
    congrArg Prod.fst (ConcreteCategory.congr_hom (hπσ x) s)
  have hσ' (x : sequence α) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).2 = x :=
    congrArg Prod.snd (ConcreteCategory.congr_hom (hπσ x) s)
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
private lemma inftyFibre_retraction {S T : LightProfinite} (π : T ⟶ S ⊗ (sequence α))
    [Epi π] [Nonempty S] :
    ∃ r : T ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _),
      LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r = 𝟙 _ := by
  have : Mono (LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) := by
    rw [CompHausLike.mono_iff_injective]
    exact Subtype.val_injective
  have : Nonempty (LightProfinite.fibre ∞ (π ≫ snd _ _)) := by
    obtain ⟨x, hx⟩ := (.comp ((fun y ↦ ⟨(Nonempty.some inferInstance, y), rfl⟩))
      ((LightProfinite.epi_iff_surjective _).mp inferInstance) :
        ((snd S (sequence α)) ∘ π).Surjective) ∞
    exact ⟨x, by simpa using hx⟩
  exact Injective.factors (𝟙 _) (LightProfinite.fibreIncl ∞ (π ≫ snd _ _))

/-- Mapping a cofork sends its target leg to the map of its projection. -/
private lemma free_mapCofork_ι_one {A B Z : LightCondSet.{u}} {a b : A ⟶ B}
    (q : B ⟶ Z) (w : a ≫ q = b ≫ q) :
    ((free R).mapCocone (Limits.Cofork.ofπ q w)).ι.app .one = (free R).map q := rfl

/-- On the infinity fibre, passing through the chosen section preserves the cover map. -/
private lemma inftyFibre_comp_section {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α)
    (σ : S ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _))
    (hσ : σ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ = 𝟙 S) :
    LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π =
      LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π := by
  have hi : LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π =
      LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫
        lift (𝟙 _) (const S (∞ : sequence α)) :=
    CartesianMonoidalCategory.hom_ext _ _ rfl (by ext a; exact a.prop)
  have hσπ : σ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π =
      lift (𝟙 S) (const S (∞ : sequence α)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [assoc, lift_fst] using hσ
    · ext x; exact (σ x).prop
  rw [hσπ]
  exact hi

/-- Descend the corrected free map when the infinity fibre splits over the base. -/
private lemma descendSequenceCover {X Y : LightCondMod R} {S T : LightProfinite}
    (π : T ⟶ S ⊗ sequence α) [Epi π] [Nonempty S]
    [Epi ((lightProfiniteToLightCondSet ⋙ free R).map (kernelPairCover π))]
    (σ : S ⟶ LightProfinite.fibre ∞ (π ≫ snd _ _))
    (hσ : σ ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ = 𝟙 S)
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (f : ((lightProfiniteToLightCondSet ⋙ free R).obj (S ⊗ sequence α)) ⟶ Y)
    (p : X ⟶ Y) (comm : (lightProfiniteToLightCondSet ⋙ free R).map π ≫ f = g ≫ p) :
    ∃ d, f = d ≫ p := by
  obtain ⟨r_inf, hr⟩ := inftyFibre_retraction π
  have : EffectiveEpi π := by
    rw [LightProfinite.effectiveEpi_iff_surjective, ← LightProfinite.epi_iff_surjective]
    infer_instance
  have hcoeq : lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π) ≫
      lightProfiniteToLightCondSet.map π =
      lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π) ≫
        lightProfiniteToLightCondSet.map π := by
    simp only [← Functor.map_comp, CompHausLike.pullback.condition]
  have hc : Limits.IsColimit ((free R).mapCocone
      (Limits.Cofork.ofπ (lightProfiniteToLightCondSet.map π) hcoeq)) :=
    Limits.isColimitOfPreserves (free R)
      (regularEpiOfPreserves π lightProfiniteToLightCondSet
        (CompHausLike.pullback.cone _ _) (CompHausLike.pullback.isLimit _ _)).isColimit
  let d : ((lightProfiniteToLightCondSet ⋙ free R).obj (S ⊗ sequence α)) ⟶ X :=
    hc.desc (descentCocone R π g r_inf σ hr)
  refine ⟨d, ?_⟩
  have hdesc : (lightProfiniteToLightCondSet ⋙ free R).map π ≫ d =
      correctedMap R π g r_inf σ := by
    have hfac := hc.fac (descentCocone R π g r_inf σ hr) .one
    simp only [free_mapCofork_ι_one, descentCocone_ι_one] at hfac
    exact hfac
  rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map π),
    ← Category.assoc, hdesc]
  dsimp only [correctedMap]
  simp only [Functor.comp_map, Functor.map_comp, assoc,
    Preadditive.add_comp, Preadditive.sub_comp, ← comm]
  simp only [← Functor.map_comp, ← Functor.comp_map, ← assoc]
  symm
  rw [sub_add, sub_eq_self, sub_eq_zero]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ (lightProfiniteToLightCondSet ⋙ free R).map (r_inf ≫ k) ≫ f)
    (inftyFibre_comp_section π σ hσ)

/-- Internal Hom out of the free module on a countable discrete one-point compactification
preserves epimorphisms. -/
theorem internallyProjective_free_onePoint :
    InternallyProjective ((free R).obj (LightProfinite.of (OnePoint α)).toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R (sequence α)]
  intro X Y p hp S f
  obtain ⟨T, π, g, hπ, comm⟩ := LightCondMod.factorsThru_lightProfinite_epi_of_epi R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ :=
    refineSequenceCover π
  refine ⟨S', y', (LightProfinite.epi_iff_surjective _).mp inferInstance, ?_⟩
  by_cases hS' : Nonempty S'
  · apply descendSequenceCover R π' split.section_ split.id
      ((lightProfiniteToLightCondSet ⋙ free R).map g' ≫ g)
    simp only [← map_comp_assoc, ← Functor.comp_map, comp, assoc]
    simp only [Functor.map_comp, assoc, comm]
  · have h : IsEmpty (S' ⊗ (sequence α)) := isEmpty_prod.mpr <| Or.inl <| by simpa using hS'
    have : IsIso π' :=
      ⟨ConcreteCategory.ofHom ⟨(h.elim ·), continuous_of_const <| by aesop⟩,
      by ext x; exact h.elim (π' x), by ext x; all_goals exact h.elim x⟩
    exact ⟨(lightProfiniteToLightCondSet ⋙ free R).map (inv π' ≫ g') ≫ g, by grind⟩

end

variable (R : Type u) [CommRing R]

/-- Internal Hom out of the free module on the lifted convergent sequence preserves
epimorphisms in every site universe. -/
theorem internallyProjective_free_liftedSequence :
    InternallyProjective ((free R).obj liftedSequence.{u}.toCondensed) := by
  have : InternallyProjective
      ((lightProfiniteToLightCondSet ⋙ free R).obj (sequence (ULift.{u} ℕ))) :=
    internallyProjective_free_onePoint (α := ULift.{u} ℕ) R
  exact InternallyProjective.ofRetract
    ((Retract.ofIso (CompHausLike.isoOfHomeo (Y := sequence (ULift.{u} ℕ))
      liftedSequenceHomeomorph)).map (lightProfiniteToLightCondSet ⋙ free R))

end TauCeti
