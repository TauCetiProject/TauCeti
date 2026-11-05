/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.MappingSpace

/-!
# Point-set suspension spectra

The suspension spectrum of a pointed simplicial set `K` is the existing free spectrum
`(SymmetricSpectrum.free 0).obj K`. Its adjunction with level-zero evaluation is
`SymmetricSpectrum.freeEvaluationAdjunction 0`; no separate spectrum carrier is needed.

The isomorphism `SymmetricSpectrum.suspensionLevelIso` identifies its levels with `Sⁿ ∧ K`,
with the symmetric group permuting the sphere coordinates. Its iterated structure maps
concatenate sphere coordinates on the left. The suspension spectrum of `S⁰` is the sphere
spectrum, the unit of the balanced smash product.

These are point-set constructions. No derived adjunction or stable-equivalence assertion is
made here.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.SymmetricSpectrum

open scoped DayFunctor

/-- The level formula `(Σ∞ K)ₙ ≅ Sⁿ ∧ K`, oriented from sphere coordinates to the free-spectrum
carrier. The comparison includes the identity shuffle in Day convolution. -/
noncomputable def suspensionLevelIso (K : PointedSSet.{0}) (n : ℕ) :
    PointedSSet.circle.smashPow (Fin n) ⊗ K ≅ (evaluation n).obj ((free 0).obj K) :=
  asIso (SymmetricSequence.tensorFreeZeroι SymmetricSequence.sphere K n)

/-- The suspension level comparison is the identity-shuffle inclusion. -/
lemma suspensionLevelIso_hom (K : PointedSSet.{0}) (n : ℕ) :
    (suspensionLevelIso K n).hom =
      SymmetricSequence.tensorFreeZeroι SymmetricSequence.sphere K n := (rfl)

/-- The level formula is natural in the pointed simplicial set. -/
@[reassoc (attr := simp)]
lemma suspensionLevelIso_hom_naturality {K L : PointedSSet.{0}} (f : K ⟶ L) (n : ℕ) :
    PointedSSet.circle.smashPow (Fin n) ◁ f ≫ (suspensionLevelIso L n).hom =
      (suspensionLevelIso K n).hom ≫ (evaluation n).map ((free 0).map f) :=
  SymmetricSequence.tensorFreeZeroι_naturality_right SymmetricSequence.sphere f n

/-- The level formula intertwines the action of a bijection with the permutation of sphere
coordinates, leaving the input pointed simplicial set fixed. -/
@[simp↓, reassoc (attr := simp↓)]
lemma smashPowReindex_comp_suspensionLevelIso_hom (K : PointedSSet.{0}) {n m : ℕ}
    (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk m) :
    PointedSSet.circle.smashPowReindex σ.toEquiv ▷ K ≫ (suspensionLevelIso K m).hom =
      (suspensionLevelIso K n).hom ≫ ((free 0).obj K).X.functor.map σ :=
  SymmetricSequence.map_whiskerRight_comp_tensorFreeZeroι SymmetricSequence.sphere K σ

/-- Under the level formula, the iterated structure map concatenates the sphere coordinates
on the left and retains the pointed simplicial set coordinate. -/
@[simp↓, reassoc (attr := simp↓)]
lemma suspensionLevelIso_hom_dayStructureMap (K : PointedSSet.{0}) (p q : ℕ) :
    PointedSSet.circle.smashPow (Fin p) ◁ (suspensionLevelIso K q).hom ≫
      ((free 0).obj K).dayStructureMap (FiniteBijection.mk p) (FiniteBijection.mk q) =
        (α_ _ _ K).inv ≫
          Functor.LaxMonoidal.μ (PointedSSet.smashPowFunctor PointedSSet.circle)
            (FiniteBijection.mk p) (FiniteBijection.mk q) ▷ K ≫
          (suspensionLevelIso K (p + q)).hom := by
  apply (cancel_epi (α_ (PointedSSet.circle.smashPow (Fin p))
    (PointedSSet.circle.smashPow (Fin q)) K).hom).1
  simp only [Iso.hom_inv_id_assoc]
  simp only [suspensionLevelIso_hom, SymmetricSequence.tensorFreeZeroι_def,
    Mod.dayStructureMap_def, freeMod_smul, DayFunctor.comp_natTrans, NatTrans.comp_app,
    whiskerLeft_comp, Category.assoc]
  -- Move the generator out of the triple smash and cancel its isomorphism.
  -- Here `erw` identifies sphere powers with the corresponding functor objects.
  erw [← associator_naturality_right_assoc, ← whisker_exchange_assoc]
  rw [cancel_epi]
  have hρ := (DayFunctor.η SymmetricSequence.sphere
    (SymmetricSequence.sphere ⊗ (SymmetricSequence.free 0).obj K)).naturality
      ((𝟙 (FiniteBijection.mk p), (ρ_ (FiniteBijection.mk q)).hom) :
        (FiniteBijection.mk p, FiniteBijection.mk q ⊗ FiniteBijection.mk 0) ⟶
          (FiniteBijection.mk p, FiniteBijection.mk q))
  simp only [Functor.comp_map, tensor_map, externalProductBifunctor_obj_map,
    FiniteBijection.toEquiv_id, PointedSSet.smashPowReindex_refl, id_whiskerRight,
    Category.id_comp, id_tensorHom] at hρ
  -- Identify the underlying free-module object before rewriting naturality components.
  dsimp only [free, freeMod, Functor.comp_obj]
  rw [reassoc_of% hρ]
  -- Move the right unitor through the Day unit and the inverse associator.
  erw [NatTrans.naturality_assoc]
  erw [reassoc_of% DayFunctor.whiskerLeft_η_app_comp_η_app_comp_associator_inv_natTrans_app
    SymmetricSequence.sphere SymmetricSequence.sphere ((SymmetricSequence.free 0).obj K)
      (FiniteBijection.mk p) (FiniteBijection.mk q) (𝟙_ FiniteBijection),
    Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, ← rightUnitor_tensor_hom]
  -- Multiplication restricts to the sphere functor's block-concatenation tensorator.
  erw [NatTrans.naturality, DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc,
    ← comp_whiskerRight_assoc, DayFunctor.η_app_comp_mul_natTrans_app]
  -- The sphere functor is the circle's smash-power functor, and the block sum has length p + q.
  rfl

/-- The suspension spectrum of the pointed zero-sphere is the sphere spectrum. -/
noncomputable def suspensionUnitIso : (free 0).obj (𝟙_ PointedSSet.{0}) ≅ 𝟙_ SymmetricSpectrum :=
  (freeMod SymmetricSequence.sphere).mapIso SymmetricSequence.freeZeroUnitIso ≪≫
    -- The two opaque action instances agree by their public characteristic equations.
    eqToIso (by
      dsimp only [freeMod, Mod.tensorLeft, Mod.regular_X]
      congr 1
      apply ModObj.ext
      exact (freeMod_smul SymmetricSequence.sphere _).trans
        (Mod.tensorLeft_smul (Mod.regular SymmetricSequence.sphere) _).symm) ≪≫
    Mod.tensorLeftUnitIso (Mod.regular SymmetricSequence.sphere)

/-- In sphere coordinates the comparison `Σ∞ S⁰ ≅ S` is the right unitor. -/
@[simp↓, reassoc (attr := simp↓)]
lemma suspensionLevelIso_hom_comp_suspensionUnitIso_hom (n : ℕ) :
    (suspensionLevelIso (𝟙_ PointedSSet.{0}) n).hom ≫
      (evaluation n).map suspensionUnitIso.hom =
        (ρ_ (PointedSSet.circle.smashPow (Fin n))).hom := by
  have h (M N : SymmetricSpectrum) (e : M = N) :
      (eqToIso e).hom.hom = eqToHom (congrArg (fun X : SymmetricSpectrum => X.X) e) :=
    eqToHom_map (Mod.forget SymmetricSequence.sphere) e
  simp only [suspensionUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Mod.comp_hom', Mod.tensorLeftUnitIso_hom_hom, suspensionLevelIso_hom, h,
    Mod.Hom.mk'_hom]
  exact SymmetricSequence.tensorFreeZeroι_comp_whiskerLeft_freeZeroUnitIso_hom
    SymmetricSequence.sphere n

end TauCeti.SymmetricSpectrum
