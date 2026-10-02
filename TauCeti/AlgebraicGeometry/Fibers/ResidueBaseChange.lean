/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.SpecialFiber.Basic

/-!
# Special fibres and local base change

For a local homomorphism of local rings, taking the special fibre after base change agrees
canonically with extending the original special fibre along the induced extension of residue
fields. The isomorphism compares two iterated pullbacks of schemes and preserves their maps to
the original total space and to the new residue-field spectrum. It is the comparison used when
changing the chosen DVR in a model of a curve.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

-- The special-fibre projections are the corresponding scalar-extension projections at the
-- residue field. Keeping these identifications explicit makes the tower calculations readable.
private lemma specialFiberι_eq_genericFiberι (T : Type u) [CommRing T] [IsLocalRing T]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of T)) :
    specialFiberι T g = genericFiberι T (ResidueField T) g := rfl

private lemma specialFiber_hom_eq_genericFiber_hom (T : Type u) [CommRing T] [IsLocalRing T]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of T)) :
    (specialFiber T g).hom = (genericFiber T (ResidueField T) g).hom := rfl

/-- Base change to a local ring followed by passage to its special fibre is the same as
extending the original special fibre to the larger residue field. -/
noncomputable def specialFiberBaseChangeIso :
    (specialFiber S (genericFiber R S f).hom).left ≅
      (genericFiber (ResidueField R) (ResidueField S) (specialFiber R f).hom).left :=
  genericFiberTowerIso R S (ResidueField S) f ≪≫
    (genericFiberTowerIso R (ResidueField R) (ResidueField S) f).symm

/-- The special-fibre base-change isomorphism preserves projection to the original scheme. -/
@[reassoc (attr := simp)]
theorem specialFiberBaseChangeIso_hom_fst :
    (specialFiberBaseChangeIso f).hom ≫
        genericFiberι (ResidueField R) (ResidueField S)
          (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R)))) ≫
          specialFiberι R f =
      specialFiberι S (genericFiber R S f).hom ≫ genericFiberι R S f := by
  simp only [specialFiberι_eq_genericFiberι]
  -- The remaining `pullback.snd` is the generic-fibre structure map.
  change (specialFiberBaseChangeIso f).hom ≫
      genericFiberι (ResidueField R) (ResidueField S) (genericFiber R (ResidueField R) f).hom ≫
        genericFiberι R (ResidueField R) f =
    genericFiberι S (ResidueField S) (genericFiber R S f).hom ≫ genericFiberι R S f
  calc
    _ = (genericFiberTowerIso R S (ResidueField S) f).hom ≫
          genericFiberι R (ResidueField S) f := by
        simp only [specialFiberBaseChangeIso, Iso.trans_hom, Iso.symm_hom]
        simp only [genericFiber_hom]
        simpa only [Category.assoc] using
          congrArg (fun h ↦ (genericFiberTowerIso R S (ResidueField S) f).hom ≫ h)
            (genericFiberTowerIso_inv_genericFiberι R (ResidueField R) (ResidueField S) f)
    _ = _ := genericFiberTowerIso_hom_genericFiberι R S (ResidueField S) f

/-- The special-fibre base-change isomorphism preserves projection to the new residue-field
spectrum. -/
@[reassoc]
theorem specialFiberBaseChangeIso_hom_snd :
    (specialFiberBaseChangeIso f).hom ≫
      pullback.snd
        (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R))))
        (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) (ResidueField S)))) =
      (specialFiber S (genericFiber R S f).hom).hom := by
  simp only [specialFiber_hom_eq_genericFiber_hom]
  -- The remaining `pullback.snd` is the generic-fibre structure map.
  change (specialFiberBaseChangeIso f).hom ≫
      (genericFiber (ResidueField R) (ResidueField S)
        (genericFiber R (ResidueField R) f).hom).hom =
    (genericFiber S (ResidueField S) (genericFiber R S f).hom).hom
  calc
    _ = (genericFiberTowerIso R S (ResidueField S) f).hom ≫
          (genericFiber R (ResidueField S) f).hom := by
        simp only [specialFiberBaseChangeIso, Iso.trans_hom, Iso.symm_hom]
        simp only [genericFiber_hom]
        rw [Category.assoc]
        rw [genericFiberTowerIso_inv_hom]
        rfl
    _ = _ := by
      simpa only [genericFiber_hom] using
        genericFiberTowerIso_hom_hom R S (ResidueField S) f

attribute [simp] specialFiberBaseChangeIso_hom_snd

/-- The inverse special-fibre base-change isomorphism preserves projection to the original
scheme. -/
@[reassoc (attr := simp)]
theorem specialFiberBaseChangeIso_inv_fst :
    (specialFiberBaseChangeIso f).inv ≫
        specialFiberι S
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ≫
          genericFiberι R S f =
      genericFiberι (ResidueField R) (ResidueField S)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R)))) ≫
        specialFiberι R f := by
  simp only [specialFiberι_eq_genericFiberι]
  -- The nested projection is the structure map of the first scalar extension.
  change (specialFiberBaseChangeIso f).inv ≫
      genericFiberι S (ResidueField S) (genericFiber R S f).hom ≫ genericFiberι R S f =
    genericFiberι (ResidueField R) (ResidueField S)
      (genericFiber R (ResidueField R) f).hom ≫ genericFiberι R (ResidueField R) f
  rw [← specialFiberBaseChangeIso_hom_fst f, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- The inverse special-fibre base-change isomorphism preserves projection to the new
residue-field spectrum. -/
@[reassoc]
theorem specialFiberBaseChangeIso_inv_snd :
    (specialFiberBaseChangeIso f).inv ≫
        pullback.snd
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
          (Spec.map (CommRingCat.ofHom (residue S))) =
      pullback.snd
        (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R))))
        (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) (ResidueField S)))) := by
  simp only [specialFiber_hom_eq_genericFiber_hom]
  -- Both nested projections are generic-fibre structure maps at residue fields.
  change (specialFiberBaseChangeIso f).inv ≫
      (genericFiber S (ResidueField S) (genericFiber R S f).hom).hom =
    (genericFiber (ResidueField R) (ResidueField S)
      (genericFiber R (ResidueField R) f).hom).hom
  have h := specialFiberBaseChangeIso_hom_snd (R := R) (S := S) f
  change (specialFiberBaseChangeIso f).hom ≫
      (genericFiber (ResidueField R) (ResidueField S)
        (genericFiber R (ResidueField R) f).hom).hom =
    (genericFiber S (ResidueField S) (genericFiber R S f).hom).hom at h
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

attribute [simp] specialFiberBaseChangeIso_inv_snd

end TauCeti
