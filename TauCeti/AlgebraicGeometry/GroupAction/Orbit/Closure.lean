/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.ClosedOrbit
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Scheme-theoretic orbit closures and closed orbit schemes

The scheme-theoretic image of an orbit morphism gives a closed subscheme of the
acted-on scheme. For a finite-type group acting on a finite-type scheme over an
algebraically closed field, its underlying space is the full geometric orbit closure.
The orbit morphism factors through it, and this factorization is surjective exactly
when the orbit is closed. If the group is reduced, the orbit closure scheme is reduced.
No reducedness assumption on the acted-on scheme is needed.

Every orbit closure contains a closed orbit with this scheme structure. In a proper
ambient scheme the resulting closed orbit scheme is proper. These schemes and maps
supply algebraic carriers for subsequent comparisons with homogeneous spaces and,
over the complex numbers, compact analytic orbits. Changing the rational base point
by a group element gives a canonical isomorphism over the acted-on scheme.

The construction uses Mathlib's `Scheme.Hom.image`, rather than a second subscheme
construction. It also retains the scheme-theoretic image for a nonreduced group;
reducedness is asserted only with a reduced group as source.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., §1.8 (the closed-orbit lemma).
* The Stacks Project, Tag 01R5 (scheme-theoretic images).
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {S : Scheme.{u}} (G : Over S) {X : Over S}

section Monoid

variable [MonObj G] [ModObj G X]

/-- The scheme-theoretic closure of the orbit of a section. -/
abbrev orbitClosureScheme (x : 𝟙_ (Over S) ⟶ X) : Scheme.{u} :=
  (orbitMap G x).left.image

/-- The inclusion of the scheme-theoretic orbit closure in the acted-on scheme. -/
def orbitClosureι (x : 𝟙_ (Over S) ⟶ X) : orbitClosureScheme G x ⟶ X.left :=
  (orbitMap G x).left.imageι

/-- The orbit morphism with target restricted to its scheme-theoretic image. -/
def toOrbitClosure (x : 𝟙_ (Over S) ⟶ X) : G.left ⟶ orbitClosureScheme G x :=
  (orbitMap G x).left.toImage

/-- The inclusion is Mathlib's scheme-theoretic image inclusion. -/
theorem orbitClosureι_def (x : 𝟙_ (Over S) ⟶ X) :
    orbitClosureι G x = (orbitMap G x).left.imageι := (rfl)

/-- The factorization is Mathlib's map to the scheme-theoretic image. -/
theorem toOrbitClosure_def (x : 𝟙_ (Over S) ⟶ X) :
    toOrbitClosure G x = (orbitMap G x).left.toImage := (rfl)

/-- The factorization recovers the actual orbit morphism. -/
@[reassoc (attr := simp)]
theorem toOrbitClosure_ι (x : 𝟙_ (Over S) ⟶ X) :
    toOrbitClosure G x ≫ orbitClosureι G x = (orbitMap G x).left := by
  rw [toOrbitClosure_def, orbitClosureι_def, Scheme.Hom.toImage_imageι]

/-- The structural morphism of the orbit closure over the original base. -/
def orbitClosureToBase (x : 𝟙_ (Over S) ⟶ X) : orbitClosureScheme G x ⟶ S :=
  orbitClosureι G x ≫ X.hom

/-- The structure map is inherited from the acted-on scheme. -/
theorem orbitClosureToBase_def (x : 𝟙_ (Over S) ⟶ X) :
    orbitClosureToBase G x = orbitClosureι G x ≫ X.hom := (rfl)

/-- The orbit factorization is over the base. -/
@[reassoc (attr := simp)]
theorem toOrbitClosure_toBase (x : 𝟙_ (Over S) ⟶ X) :
    toOrbitClosure G x ≫ orbitClosureToBase G x = G.hom := by
  simp [orbitClosureToBase_def, ← Category.assoc]

section QuasiCompact

variable (x : 𝟙_ (Over S) ⟶ X) [QuasiCompact (orbitMap G x).left]

/-- The scheme-theoretic orbit closure is a closed subscheme. -/
instance : IsClosedImmersion (orbitClosureι G x) := by
  rw [orbitClosureι_def]
  infer_instance

/-- The orbit factorization is quasi-compact. -/
instance : QuasiCompact (toOrbitClosure G x) := by
  rw [toOrbitClosure_def]
  infer_instance

/-- The orbit factorization is scheme-theoretically dominant. -/
instance : IsSchemeTheoreticallyDominant (toOrbitClosure G x) := by
  rw [toOrbitClosure_def]
  infer_instance

/-- The inclusion has precisely the full geometric orbit closure as its range. -/
@[simp]
theorem range_orbitClosureι : Set.range (orbitClosureι G x) = orbitClosure G x := by
  rw [orbitClosureι_def, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    orbitClosure_def, orbit_def]

/-- The orbit morphism covers its scheme-theoretic closure exactly when the orbit is closed. -/
theorem surjective_toOrbitClosure_iff :
    Surjective (toOrbitClosure G x) ↔ IsClosed (orbit G x) := by
  constructor
  · intro h
    have hr := congrArg (fun f : G.left ⟶ X.left ↦ Set.range f) (toOrbitClosure_ι G x)
    have heq : orbit G x = orbitClosure G x := by
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (toOrbitClosure G x).surjective, Set.image_univ,
        range_orbitClosureι, orbit_def] using hr.symm
    rw [heq]
    exact isClosed_orbitClosure G x
  · intro h
    exact ⟨(orbitMap G x).left.toImage_surjective_of_isClosed_range
      (by simpa only [orbit_def] using h)⟩

/-- The orbit closure is locally of finite type over the base whenever the ambient
scheme is. -/
instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (orbitClosureToBase G x) := by
  rw [orbitClosureToBase_def]
  infer_instance

/-- A quasi-compact acted-on scheme has quasi-compact scheme-theoretic orbit closures. -/
instance [CompactSpace X.left] : CompactSpace (orbitClosureScheme G x) :=
  QuasiCompact.compactSpace_of_compactSpace (orbitClosureι G x)

/-- A proper ambient scheme gives a proper scheme-theoretic orbit closure over the base. -/
instance [IsProper X.hom] : IsProper (orbitClosureToBase G x) := by
  rw [orbitClosureToBase_def]
  infer_instance

end QuasiCompact

end Monoid

variable [GrpObj G] [ModObj G X]

/-- Translating the rational base point does not change the defining ideal of the orbit image. -/
theorem ker_orbitMap_smul (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (orbitMap G (g • x)).left.ker = (orbitMap G x).left.ker := by
  rw [orbitMap_smul, Over.comp_left, Scheme.Hom.ker_comp_of_isIso]

/-- Changing the base point by a group section canonically identifies the orbit closure
schemes over the acted-on scheme, including their nonreduced structures. -/
def orbitClosureIsoSmul (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    orbitClosureScheme G (g • x) ≅ orbitClosureScheme G x where
  hom := Scheme.IdealSheafData.inclusion (ker_orbitMap_smul G g x).ge
  inv := Scheme.IdealSheafData.inclusion (ker_orbitMap_smul G g x).le
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The change-of-base-point isomorphism respects the inclusion into the acted-on scheme. -/
@[reassoc (attr := simp)]
theorem orbitClosureIsoSmul_hom_ι (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (orbitClosureIsoSmul G g x).hom ≫ orbitClosureι G x = orbitClosureι G (g • x) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The inverse change-of-base-point map also respects the ambient inclusion. -/
@[reassoc (attr := simp)]
theorem orbitClosureIsoSmul_inv_ι (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    (orbitClosureIsoSmul G g x).inv ≫ orbitClosureι G (g • x) = orbitClosureι G x := by
  rw [Iso.inv_comp_eq, orbitClosureIsoSmul_hom_ι]

/-- On the orbit factorization, changing base point corresponds to right translation
on the group. -/
@[reassoc]
theorem toOrbitClosure_isoSmul_hom (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    toOrbitClosure G (g • x) ≫ (orbitClosureIsoSmul G g x).hom =
      (rightTranslation g).hom.left ≫ toOrbitClosure G x := by
  apply (cancel_mono (orbitClosureι G x)).mp
  simp only [Category.assoc, orbitClosureIsoSmul_hom_ι, toOrbitClosure_ι]
  rw [← Over.comp_left, ← orbitMap_smul]

section FiniteType

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
  [CompactSpace X.left]

/-- The closure of every orbit contains the scheme-theoretic image of a closed orbit,
and the corresponding map from the group is surjective. For a reduced group this
is a reduced closed orbit scheme. -/
theorem exists_surjective_toOrbitClosure_subset (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      Surjective (toOrbitClosure G y) ∧
        Set.range (orbitClosureι G y) ⊆ orbitClosure G x := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨y, hy, hsub⟩ := exists_isClosed_orbit_subset_orbitClosure G x
  refine ⟨y, (surjective_toOrbitClosure_iff G y).mpr hy, ?_⟩
  rw [range_orbitClosureι, orbitClosure_def, hy.closure_eq]
  exact hsub

/-- A nonempty finite-type scheme with a finite-type group action has a closed orbit
scheme covered by the group. If the ambient scheme is proper, this scheme is proper. -/
theorem exists_surjective_toOrbitClosure [Nonempty X.left] :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X, Surjective (toOrbitClosure G y) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨y, hy⟩ := exists_isClosed_orbit G (X := X)
  exact ⟨y, (surjective_toOrbitClosure_iff G y).mpr hy⟩

end FiniteType

end TauCeti.SchemeAction
