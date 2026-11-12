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
    rw [toOrbitClosure_ι_assoc, orbitMap_left_translation]
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
    orbitClosureScheme G x ≅ orbitClosureScheme G x :=
  liftTranslation (orbitClosureι G x) (orbitClosureTranslationHom G x)
    (orbitClosureTranslationHom_ι G x) g

/-- The inclusion of the orbit closure commutes with translation. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_hom_ι (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).hom ≫ orbitClosureι G x =
      orbitClosureι G x ≫ (translation X g).hom.left :=
  liftTranslation_hom_ι _ _ _ g

/-- The orbit factorization intertwines left translation and orbit-closure translation. -/
@[reassoc]
theorem toOrbitClosure_orbitClosureTranslation_hom (g : 𝟙_ (Over S) ⟶ G) :
    toOrbitClosure G x ≫ (orbitClosureTranslation G x g).hom =
      (leftTranslation g).hom.left ≫ toOrbitClosure G x :=
  comp_liftTranslation_hom _ _ _ x (toOrbitClosure G x) (toOrbitClosure_ι G x) g

/-- Translation by the identity fixes the orbit closure scheme. -/
@[simp]
theorem orbitClosureTranslation_one :
    orbitClosureTranslation G x 1 = Iso.refl _ := liftTranslation_one _ _ _

/-- Group multiplication composes orbit-closure translations in action order. -/
@[simp]
theorem orbitClosureTranslation_mul (g h : 𝟙_ (Over S) ⟶ G) :
    orbitClosureTranslation G x (g * h) =
      orbitClosureTranslation G x h ≪≫ orbitClosureTranslation G x g :=
  liftTranslation_mul _ _ _ g h

/-- Inverse group sections give inverse orbit-closure translations. -/
@[simp]
theorem orbitClosureTranslation_inv_eq_symm (g : 𝟙_ (Over S) ⟶ G) :
    orbitClosureTranslation G x g⁻¹ = (orbitClosureTranslation G x g).symm :=
  liftTranslation_inv_eq_symm _ _ _ g

/-- Inverse orbit-closure translation restricts inverse ambient translation. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_inv_ι (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).inv ≫ orbitClosureι G x =
      orbitClosureι G x ≫ (translation X g).inv.left := liftTranslation_inv_ι _ _ _ g

/-- Orbit-closure translations preserve the original base morphism. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_hom_toBase (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).hom ≫ orbitClosureToBase G x =
      orbitClosureToBase G x := by
  rw [orbitClosureToBase_def]
  exact liftTranslation_hom_toBase _ _ _ g

/-- Inverse orbit-closure translations preserve the original base morphism. -/
@[reassoc (attr := simp)]
theorem orbitClosureTranslation_inv_toBase (g : 𝟙_ (Over S) ⟶ G) :
    (orbitClosureTranslation G x g).inv ≫ orbitClosureToBase G x =
      orbitClosureToBase G x := by
  rw [orbitClosureToBase_def]
  exact liftTranslation_inv_toBase _ _ _ g

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
  exact exists_eq_of_equivariant_of_range_subset_orbit G x (orbitClosureι G x)
    (range_orbitClosureι_of_isClosed G x hc).le (orbitClosureTranslation G x)
    (orbitClosureTranslation_hom_ι G x) hy hz

end FiniteType

end TauCeti.SchemeAction
