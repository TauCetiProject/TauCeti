/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Translation

/-!
# Scheme models of locally closed orbits

For a finite-type group scheme acting on a finite-type scheme over an algebraically
closed field, restrict the scheme-theoretic orbit closure to the open complement of
the orbit boundary. This gives a locally closed immersion with exactly the geometric
orbit as its image and a surjective factorization of the orbit morphism. If the group
is reduced, this orbit scheme is reduced, even when the ambient scheme is not.
Translation by rational group points restricts to automorphisms of the orbit scheme,
transitive on its closed points.

This construction uses the full scheme-theoretic image and Mathlib's open subschemes.
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

/-- The open part of the scheme-theoretic orbit closure lying in the geometric orbit. -/
def orbitOpen : (orbitClosureScheme G x).Opens :=
  (orbitClosureι G x) ⁻¹ᵁ
    ⟨coborder (orbit G x), (isLocallyClosed_orbit G x).isOpen_coborder⟩

/-- Membership in the orbit open is detected by the original geometric orbit. -/
@[simp]
theorem mem_orbitOpen (p : orbitClosureScheme G x) :
    p ∈ orbitOpen G x ↔ orbitClosureι G x p ∈ orbit G x := by
  have hp : orbitClosureι G x p ∈ closure (orbit G x) := by
    rw [← orbitClosure_def, ← range_orbitClosureι]
    exact ⟨p, rfl⟩
  rw [orbitOpen, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_mk,
    mem_coborder_iff_imp]
  exact imp_iff_right hp

/-- The orbit scheme is the open subscheme of its scheme-theoretic closure obtained
by removing the boundary. For a reduced acting group it is the reduced orbit model. -/
abbrev orbitScheme : Scheme.{u} := (orbitOpen G x).toScheme

/-- The open immersion of the orbit scheme into its scheme-theoretic closure. -/
def orbitToClosure : orbitScheme G x ⟶ orbitClosureScheme G x := (orbitOpen G x).ι

/-- The locally closed inclusion of the orbit scheme into the acted-on scheme. -/
def orbitι : orbitScheme G x ⟶ X.left := orbitToClosure G x ≫ orbitClosureι G x

/-- The orbit scheme's structure morphism to the ground field. -/
def orbitToBase : orbitScheme G x ⟶ Spec (.of k) := orbitι G x ≫ X.hom

/-- The inclusion into the orbit closure is its defining open-subscheme inclusion. -/
theorem orbitToClosure_def : orbitToClosure G x = (orbitOpen G x).ι := (rfl)

/-- The orbit inclusion factors through the scheme-theoretic orbit closure. -/
theorem orbitι_def : orbitι G x = orbitToClosure G x ≫ orbitClosureι G x := (rfl)

/-- The orbit scheme inherits its structure morphism from the acted-on scheme. -/
theorem orbitToBase_def : orbitToBase G x = orbitι G x ≫ X.hom := (rfl)

instance : IsOpenImmersion (orbitToClosure G x) := by
  rw [orbitToClosure_def]
  infer_instance

instance : IsImmersion (orbitι G x) := by
  rw [orbitι_def]
  infer_instance

/-- The orbit scheme has the full geometric orbit, including nonclosed points, as its image. -/
@[simp]
theorem range_orbitι : Set.range (orbitι G x) = orbit G x := by
  rw [orbitι_def, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    orbitToClosure_def, Scheme.Opens.range_ι]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_orbitOpen G x q).mp hq
  · intro hp
    obtain ⟨q, rfl⟩ := (range_orbitClosureι G x).ge ((orbit_subset_orbitClosure G x) hp)
    exact ⟨q, (mem_orbitOpen G x q).mpr hp, rfl⟩

/-- The orbit morphism factors through the orbit scheme. -/
def toOrbit : G.left ⟶ orbitScheme G x :=
  IsOpenImmersion.lift (orbitToClosure G x) (toOrbitClosure G x) (by
    rw [orbitToClosure_def, Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    apply (mem_orbitOpen G x _).mpr
    rw [← Scheme.Hom.comp_apply, toOrbitClosure_ι]
    exact (mem_orbit G x _).mpr ⟨p, rfl⟩)

/-- The orbit factorization agrees with the map to the scheme-theoretic closure. -/
@[reassoc (attr := simp)]
theorem toOrbit_toClosure : toOrbit G x ≫ orbitToClosure G x = toOrbitClosure G x :=
  IsOpenImmersion.lift_fac _ _ _

/-- The orbit factorization recovers the original orbit morphism. -/
@[reassoc (attr := simp)]
theorem toOrbit_ι : toOrbit G x ≫ orbitι G x = (orbitMap G x).left := by
  rw [orbitι_def, ← Category.assoc, toOrbit_toClosure, toOrbitClosure_ι]

/-- The factorization is a morphism over the ground field. -/
@[reassoc (attr := simp)]
theorem toOrbit_toBase : toOrbit G x ≫ orbitToBase G x = G.hom := by
  rw [orbitToBase_def, toOrbit_ι_assoc, Over.w]

/-- The map from the group onto its orbit scheme is surjective on all scheme points. -/
instance : Surjective (toOrbit G x) := by
  rw [surjective_iff]
  intro p
  obtain ⟨q, hq⟩ := (mem_orbit G x _).mp ((range_orbitι G x).le ⟨p, rfl⟩)
  refine ⟨q, (orbitι G x).isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, toOrbit_ι]
  exact hq

instance : LocallyOfFiniteType (orbitToBase G x) := by
  rw [orbitToBase_def]
  infer_instance

instance : CompactSpace (orbitScheme G x) :=
  Function.Surjective.compactSpace (toOrbit G x).continuous (toOrbit G x).surjective

/-- A reduced acting group gives a reduced orbit scheme. No reducedness of the
acted-on scheme is required. -/
instance [IsReduced G.left] : IsReduced (orbitScheme G x) := by
  have : IsReduced (orbitClosureScheme G x) := inferInstance
  exact isReduced_of_isOpenImmersion (orbitToClosure G x)

/-- Orbit-closure translations preserve the open orbit subscheme. -/
@[simp]
theorem preimage_orbitOpen (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitClosureTranslation G x g).hom ⁻¹ᵁ orbitOpen G x = orbitOpen G x := by
  let := translationMulAction G X
  ext p
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, mem_orbitOpen]
  rw [← Scheme.Hom.comp_apply, orbitClosureTranslation_hom_ι, Scheme.Hom.comp_apply]
  simpa only [Set.mem_preimage, translationMulAction_smul] using
    Set.ext_iff.mp (preimage_smul_orbit g x) (orbitClosureι G x p)

/-- Translation by a rational group point on the locally closed orbit scheme. -/
def orbitTranslation (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitScheme G x ≅ orbitScheme G x :=
  Scheme.isoOfEq _ (preimage_orbitOpen G x g).symm ≪≫
    (orbitClosureTranslation G x g).hom.preimageIso (orbitOpen G x)

/-- The open inclusion into the closure intertwines orbit translations. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_hom_toClosure (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).hom ≫ orbitToClosure G x =
      orbitToClosure G x ≫ (orbitClosureTranslation G x g).hom := by
  simp [orbitTranslation, orbitToClosure_def]

/-- The orbit immersion intertwines orbit translations with ambient translations. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_hom_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).hom ≫ orbitι G x =
      orbitι G x ≫ (translation X g).hom.left := by
  rw [orbitι_def, orbitTranslation_hom_toClosure_assoc,
    Category.assoc, orbitClosureTranslation_hom_ι, ← Category.assoc]

/-- The orbit factorization intertwines left translation on the group and orbit translation. -/
@[reassoc]
theorem toOrbit_orbitTranslation_hom (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    toOrbit G x ≫ (orbitTranslation G x g).hom =
      (leftTranslation g).hom.left ≫ toOrbit G x := by
  apply (cancel_mono (orbitToClosure G x)).mp
  simp only [Category.assoc, orbitTranslation_hom_toClosure, toOrbit_toClosure,
    toOrbit_toClosure_assoc]
  exact toOrbitClosure_orbitClosureTranslation_hom G x g

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
  apply (cancel_mono (orbitToClosure G x)).mp
  rw [orbitTranslation_hom_toClosure, Iso.symm_hom, eq_comm, Iso.inv_comp_eq,
    orbitTranslation_hom_toClosure_assoc, orbitClosureTranslation_inv_eq_symm,
    Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- Inverse orbit translation intertwines the open inclusions into the closure. -/
@[reassoc (attr := simp)]
theorem orbitTranslation_inv_toClosure (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).inv ≫ orbitToClosure G x =
      orbitToClosure G x ≫ (orbitClosureTranslation G x g).inv := by
  rw [← Iso.symm_hom, ← orbitTranslation_inv_eq_symm, orbitTranslation_hom_toClosure,
    orbitClosureTranslation_inv_eq_symm, Iso.symm_hom]

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
