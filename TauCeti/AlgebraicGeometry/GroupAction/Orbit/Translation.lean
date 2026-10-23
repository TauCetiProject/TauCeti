/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Closure

/-!
# Translations of scheme-theoretic orbit closures

Every section of an acting group induces an automorphism of the scheme-theoretic
orbit closure. The inclusion intertwines it with ambient translation, and the
orbit factorization intertwines it with left translation on the group. These
identities preserve the full scheme structure, including nilpotents, and hold
over any base when the orbit morphism is quasi-compact.

For a closed orbit over an algebraically closed field, these automorphisms act
transitively on its closed points. This supplies the homogeneity needed to
spread local geometric properties over a closed orbit scheme.

The construction uses Mathlib's `IsClosedImmersion.lift` and the schematic
dominance of `Scheme.Hom.toImage`. It parallels the immersion lifting used for
`TauCeti.Comodule.projectiveOrbitTranslation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {S : Scheme.{u}} (G : Over S) {X : Over S} [GrpObj G] [ModObj G X]
  (x : 𝟙_ (Over S) ⟶ X) [QuasiCompact (orbitMap G x).left]

private theorem ker_orbitClosureι_le_translation (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureι G x).ker ≤
      (orbitClosureι G x ≫ (translation X g).hom.left).ker := by
  -- Schematic dominance detects the ideal after precomposition by the orbit factorization.
  -- Equivariance then replaces ambient translation by an isomorphism on the group.
  have h (f : orbitClosureScheme G x ⟶ X.left) :
      (toOrbitClosure G x ≫ f).ker = f.ker := by
    rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have heq : toOrbitClosure G x ≫ orbitClosureι G x ≫ (translation X g).hom.left =
      (leftTranslation g).hom.left ≫ (orbitMap G x).left := by
    simpa only [Over.comp_left, toOrbitClosure_ι_assoc] using
      congrArg Over.Hom.left (leftTranslation_hom_orbitMap g x).symm
  rw [← h (orbitClosureι G x ≫ (translation X g).hom.left), heq,
    Scheme.Hom.ker_comp_of_isIso, ← toOrbitClosure_ι, h]

/-- The lift of ambient translation along the closed orbit-closure inclusion. -/
private def orbitClosureTranslationHom (g : 𝟙_ (Over S) ⟶ G) :
    orbitClosureScheme G x ⟶ orbitClosureScheme G x :=
  IsClosedImmersion.lift (orbitClosureι G x)
    (orbitClosureι G x ≫ (translation X g).hom.left)
    (ker_orbitClosureι_le_translation G x g)

@[reassoc]
private theorem orbitClosureTranslationHom_ι (g : 𝟙_ (Over S) ⟶ G) :
    orbitClosureTranslationHom G x g ≫ orbitClosureι G x =
      orbitClosureι G x ≫ (translation X g).hom.left :=
  IsClosedImmersion.lift_fac _ _ _

/-- Translation on the full scheme-theoretic orbit closure induced by a group section. -/
def orbitClosureTranslation (g : 𝟙_ (Over S) ⟶ G) :
    orbitClosureScheme G x ≅ orbitClosureScheme G x where
  hom := orbitClosureTranslationHom G x g
  inv := orbitClosureTranslationHom G x g⁻¹
  hom_inv_id := by
    apply (cancel_mono (orbitClosureι G x)).mp
    simp only [Category.assoc, orbitClosureTranslationHom_ι,
      orbitClosureTranslationHom_ι_assoc, translation_inv, Iso.symm_hom,
      ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (orbitClosureι G x)).mp
    simp only [Category.assoc, orbitClosureTranslationHom_ι,
      orbitClosureTranslationHom_ι_assoc, translation_inv, Iso.symm_hom,
      ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id, Category.id_comp]

/-- The inclusion of the orbit closure commutes with translation. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_hom_ι (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).hom ≫ orbitClosureι G x =
      orbitClosureι G x ≫ (translation X g).hom.left :=
  orbitClosureTranslationHom_ι G x g

/-- The orbit factorization intertwines left translation and orbit-closure translation. -/
@[reassoc]
theorem toOrbitClosure_orbitClosureTranslation_hom (g : 𝟙_ (Over S) ⟶ G) :
    toOrbitClosure G x ≫ (orbitClosureTranslation G x g).hom =
      (leftTranslation g).hom.left ≫ toOrbitClosure G x := by
  apply (cancel_mono (orbitClosureι G x)).mp
  simp only [Category.assoc, orbitClosureTranslation_hom_ι, toOrbitClosure_ι,
    toOrbitClosure_ι_assoc]
  exact congrArg Over.Hom.left (leftTranslation_hom_orbitMap g x).symm

/-- Translation by the identity fixes the orbit closure scheme. -/
@[simp]
theorem orbitClosureTranslation_one :
    orbitClosureTranslation G x 1 = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono (orbitClosureι G x)).mp
  simp

/-- Group multiplication composes orbit-closure translations in action order. -/
@[simp]
theorem orbitClosureTranslation_mul (g h : 𝟙_ (Over S) ⟶ G) :
    orbitClosureTranslation G x (g * h) =
      orbitClosureTranslation G x h ≪≫ orbitClosureTranslation G x g := by
  apply Iso.ext
  apply (cancel_mono (orbitClosureι G x)).mp
  simp only [Iso.trans_hom, Category.assoc, orbitClosureTranslation_hom_ι,
    orbitClosureTranslation_hom_ι_assoc, translation_mul, Over.comp_left]

/-- Inverse group sections give inverse orbit-closure translations. -/
@[simp]
theorem orbitClosureTranslation_inv_eq_symm (g : 𝟙_ (Over S) ⟶ G) :
    orbitClosureTranslation G x g⁻¹ = (orbitClosureTranslation G x g).symm := by
  apply Iso.ext
  rfl

/-- Inverse orbit-closure translation restricts inverse ambient translation. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_inv_ι (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).inv ≫ orbitClosureι G x =
      orbitClosureι G x ≫ (translation X g).inv.left := by
  rw [Iso.inv_comp_eq, orbitClosureTranslation_hom_ι_assoc,
    ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]

/-- Orbit-closure translations preserve the original base morphism. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_hom_toBase (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).hom ≫ orbitClosureToBase G x =
      orbitClosureToBase G x := by
  rw [orbitClosureToBase_def, orbitClosureTranslation_hom_ι_assoc, Over.w]

/-- Inverse orbit-closure translations preserve the original base morphism. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_inv_toBase (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).inv ≫ orbitClosureToBase G x =
      orbitClosureToBase G x := by
  rw [Iso.inv_comp_eq, orbitClosureTranslation_hom_toBase]

section FiniteType

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) [QuasiCompact (orbitMap G x).left]

/-- On a closed orbit, group sections act transitively on the closed points of its
scheme model. No reducedness or smoothness assumption is needed. -/
theorem exists_orbitClosureTranslation_eq_of_isClosed (hc : IsClosed (orbit G x))
    {y z : orbitClosureScheme G x} (hy : y ∈ closedPoints _) (hz : z ∈ closedPoints _) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      (orbitClosureTranslation G x g).hom y = z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hp (p : orbitClosureScheme G x) (hp : p ∈ closedPoints _) :
      orbitClosureι G x p ∈ orbit G x ∩ closedPoints X.left := by
    have h : orbitClosureι G x p ∈
        (orbitClosureι G x) '' closedPoints (orbitClosureScheme G x) := ⟨p, hp, rfl⟩
    rwa [Scheme.Hom.image_closedPoints_eq_range_inter_closedPoints,
      range_orbitClosureι, orbitClosure_def, hc.closure_eq] at h
  have hy' := hp y hy
  have hz' := hp z hz
  rw [orbit_inter_closedPoints] at hy' hz'
  obtain ⟨g, a, ha⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨h, b, hb⟩ := Set.mem_iUnion.mp hz'
  rw [Subsingleton.elim (α := Spec (.of k)) b a] at hb
  refine ⟨h * g⁻¹, (orbitClosureι G x).isEmbedding.injective ?_⟩
  have heq : (g • x) ≫ (translation X (h * g⁻¹)).hom = h • x := by
    simp only [comp_translation_hom, toUnit_unit, Category.id_comp, mul_smul,
      inv_smul_smul]
  have ht := congrArg (fun f : orbitClosureScheme G x ⟶ X.left ↦ f y)
    (orbitClosureTranslation_hom_ι G x (h * g⁻¹))
  simp only [Scheme.Hom.comp_apply] at ht
  rw [ht, ← ha, ← hb]
  exact congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ X ↦ f.left a) heq

end FiniteType

end TauCeti.SchemeAction
