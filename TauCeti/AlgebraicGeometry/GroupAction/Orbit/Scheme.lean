/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.LocallyClosed
public import TauCeti.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.LocallyClosed

/-!
# Scheme models of locally closed orbits

For a finite-type group scheme acting on a finite-type scheme over an algebraically
closed field, use the scheme-theoretic image of the orbit morphism inside the
coborder of its image. This gives a locally closed immersion with exactly the geometric
orbit as its image and a surjective factorization of the orbit morphism. If the group
is reduced, this orbit scheme is reduced, even when the ambient scheme is not.
Translation by rational group points restricts to automorphisms of the orbit scheme,
transitive on its closed points.

This construction uses `Scheme.Hom.locallyClosedImage` and the lifting property of
immersions after surjective, scheme-theoretically dominant morphisms, paralleling
`TauCeti.Comodule.projectiveOrbitTranslation`.
It does not assume that a quotient by the stabilizer is represented, and does not
assert that the orbit morphism is smooth. Smoothness of the orbit scheme is proved
in `TauCeti.AlgebraicGeometry.GroupAction.Orbit.Smooth`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The range of the orbit morphism is locally closed. -/
theorem isLocallyClosed_range_orbitMap : IsLocallyClosed (Set.range (orbitMap G x).left) :=
  orbit_def G x ▸ isLocallyClosed_orbit G x

/-- The orbit scheme is the locally closed scheme image of the orbit morphism.
For a reduced acting group it is the reduced orbit model. -/
abbrev orbitScheme : Scheme.{u} :=
  (orbitMap G x).left.locallyClosedImage
    (isLocallyClosed_range_orbitMap G x)

/-- The locally closed inclusion of the orbit scheme into the acted-on scheme. -/
def orbitι : orbitScheme G x ⟶ X.left :=
  (orbitMap G x).left.locallyClosedImageι
    (isLocallyClosed_range_orbitMap G x)

/-- The orbit scheme's structure morphism to the ground field. -/
def orbitToBase : orbitScheme G x ⟶ Spec (.of k) := orbitι G x ≫ X.hom

/-- The orbit inclusion is the inclusion of the locally closed scheme image. -/
theorem orbitι_def : orbitι G x =
    (orbitMap G x).left.locallyClosedImageι
      (isLocallyClosed_range_orbitMap G x) := (rfl)

/-- The orbit scheme inherits its structure morphism from the acted-on scheme. -/
theorem orbitToBase_def : orbitToBase G x = orbitι G x ≫ X.hom := (rfl)

instance : IsImmersion (orbitι G x) := by
  rw [orbitι_def]
  infer_instance

/-- The orbit scheme has the full geometric orbit, including nonclosed points, as its image. -/
@[simp]
theorem range_orbitι : Set.range (orbitι G x) = orbit G x := by
  rw [orbitι_def, Scheme.Hom.range_locallyClosedImageι, orbit_def]

/-- The orbit morphism factors through its locally closed scheme image. -/
def toOrbit : G.left ⟶ orbitScheme G x :=
  (orbitMap G x).left.toLocallyClosedImage
    (isLocallyClosed_range_orbitMap G x)

/-- The orbit factorization is the canonical map onto the locally closed scheme image. -/
theorem toOrbit_def : toOrbit G x =
    (orbitMap G x).left.toLocallyClosedImage
      (isLocallyClosed_range_orbitMap G x) := (rfl)

/-- The orbit factorization recovers the original orbit morphism. -/
@[reassoc (attr := simp)]
theorem toOrbit_ι : toOrbit G x ≫ orbitι G x = (orbitMap G x).left := by
  rw [toOrbit_def, orbitι_def]
  exact Scheme.Hom.toLocallyClosedImage_locallyClosedImageι _ _

/-- The factorization is a morphism over the ground field. -/
@[reassoc (attr := simp)]
theorem toOrbit_toBase : toOrbit G x ≫ orbitToBase G x = G.hom := by
  rw [orbitToBase_def, toOrbit_ι_assoc, Over.w]

/-- The map from the group onto its orbit scheme is surjective on all scheme points. -/
instance : Surjective (toOrbit G x) := by
  rw [toOrbit_def]
  infer_instance

instance : QuasiCompact (toOrbit G x) := by
  rw [toOrbit_def]
  infer_instance

/-- The orbit morphism is scheme-theoretically dominant onto its orbit scheme. -/
instance : IsSchemeTheoreticallyDominant (toOrbit G x) := by
  rw [toOrbit_def]
  infer_instance

instance : LocallyOfFiniteType (orbitToBase G x) := by
  rw [orbitToBase_def]
  infer_instance

instance : CompactSpace (orbitScheme G x) :=
  Function.Surjective.compactSpace (toOrbit G x).continuous (toOrbit G x).surjective

/-- A reduced acting group gives a reduced orbit scheme. No reducedness of the
acted-on scheme is required. -/
instance [IsReduced G.left] : IsReduced (orbitScheme G x) :=
  IsSchemeTheoreticallyDominant.isReduced (toOrbit G x)

private theorem exists_orbitTranslationHom (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ∃! l : orbitScheme G x ⟶ orbitScheme G x,
      l ≫ orbitι G x = orbitι G x ≫ (translation X g).hom.left :=
  (orbitι G x).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (orbitι G x ≫ (translation X g).hom.left) (toOrbit G x)
    ((leftTranslation g).hom.left ≫ toOrbit G x)
    (by simpa only [Category.assoc, toOrbit_ι, toOrbit_ι_assoc, Over.comp_left] using
      congrArg Over.Hom.left (leftTranslation_hom_orbitMap g x))

/-- The unique lift of ambient translation to the locally closed orbit scheme. -/
private def orbitTranslationHom (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitScheme G x ⟶ orbitScheme G x :=
  (exists_orbitTranslationHom G x g).exists.choose

@[reassoc]
private theorem orbitTranslationHom_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitTranslationHom G x g ≫ orbitι G x = orbitι G x ≫ (translation X g).hom.left :=
  (exists_orbitTranslationHom G x g).exists.choose_spec

/-- Translation by a rational group point on the locally closed orbit scheme. -/
def orbitTranslation (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitScheme G x ≅ orbitScheme G x where
  hom := orbitTranslationHom G x g
  inv := orbitTranslationHom G x g⁻¹
  hom_inv_id := by
    apply (cancel_mono (orbitι G x)).mp
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      translation_inv, Iso.symm_hom, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (orbitι G x)).mp
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      translation_inv, Iso.symm_hom, ← Over.comp_left, Iso.inv_hom_id,
      Over.id_left, Category.comp_id, Category.id_comp]

/-- The orbit immersion intertwines orbit translations with ambient translations. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_hom_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).hom ≫ orbitι G x =
      orbitι G x ≫ (translation X g).hom.left :=
  orbitTranslationHom_ι G x g

/-- The orbit factorization intertwines left translation on the group and orbit translation. -/
@[reassoc]
theorem toOrbit_orbitTranslation_hom (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    toOrbit G x ≫ (orbitTranslation G x g).hom =
      (leftTranslation g).hom.left ≫ toOrbit G x := by
  apply (cancel_mono (orbitι G x)).mp
  simp only [Category.assoc, orbitTranslation_hom_ι, toOrbit_ι, toOrbit_ι_assoc]
  exact congrArg Over.Hom.left (leftTranslation_hom_orbitMap g x).symm

/-- Translation on the orbit scheme preserves its ground-field structure. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_hom_toBase (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).hom ≫ orbitToBase G x = orbitToBase G x := by
  rw [orbitToBase_def, orbitTranslation_hom_ι_assoc, Over.w]

/-- Translation by the identity is the identity on the orbit scheme. -/
@[simp]
theorem orbitTranslation_one : orbitTranslation G x 1 = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono (orbitι G x)).mp
  simp

/-- Multiplication of group points composes translations in action order. -/
@[simp]
theorem orbitTranslation_mul (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitTranslation G x (g * h) = orbitTranslation G x h ≪≫ orbitTranslation G x g := by
  apply Iso.ext
  apply (cancel_mono (orbitι G x)).mp
  simp only [Iso.trans_hom, Category.assoc, orbitTranslation_hom_ι,
    orbitTranslation_hom_ι_assoc, translation_mul, Over.comp_left]

/-- Inverse group points induce inverse orbit translations. -/
@[simp]
theorem orbitTranslation_inv_eq_symm (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitTranslation G x g⁻¹ = (orbitTranslation G x g).symm := by
  apply Iso.ext
  rfl

/-- Inverse orbit translation intertwines the immersions into the ambient scheme. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_inv_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).inv ≫ orbitι G x =
      orbitι G x ≫ (translation X g).inv.left := by
  rw [← Iso.symm_hom, ← orbitTranslation_inv_eq_symm, orbitTranslation_hom_ι,
    translation_inv, Iso.symm_hom]

/-- Inverse orbit translation also preserves the ground-field structure. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_inv_toBase (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).inv ≫ orbitToBase G x = orbitToBase G x := by
  rw [Iso.inv_comp_eq, orbitTranslation_hom_toBase]

/-- Rational group points act transitively on the closed points of the orbit scheme. -/
theorem exists_orbitTranslation_eq {y z : orbitScheme G x}
    (hy : y ∈ closedPoints _) (hz : z ∈ closedPoints _) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (orbitTranslation G x g).hom y = z := by
  exact exists_eq_of_equivariant_of_range_subset_orbit G x (orbitι G x)
    (range_orbitι G x).le (orbitTranslation G x) (orbitTranslation_hom_ι G x) hy hz

end TauCeti.SchemeAction
