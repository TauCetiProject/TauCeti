/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# K-injective replacements in the derived category

Let `C` be an abelian category. A K-injective replacement of a cochain complex `K` is a
quasi-isomorphism `K ⟶ I` into a K-injective complex. Such replacements are unique up to
homotopy equivalence (`CochainComplex.IsKInjective.exists_homotopyEquiv`), and the comparison
map is unique up to homotopy (`CochainComplex.IsKInjective.nonempty_homotopy_of_comp`).

When every complex, bounded or not, has a K-injective replacement
(`TauCeti.HasKInjectiveResolutions`), the replacements assemble into a functor
`TauCeti.kInjectiveReplacement C : DerivedCategory C ⥤ HomotopyCategory C (.up ℤ)`. It is right
adjoint to the localization functor `DerivedCategory.Qh`
(`TauCeti.kInjectiveReplacementAdjunction`) and fully faithful, its values are K-injective, its
essential image consists exactly of the K-injective complexes, and the unit `K ⟶ I(K)` of the
adjunction is a quasi-isomorphism, natural in `K` up to homotopy. Thus morphisms into an object
of the derived category are computed as homotopy classes of chain maps into its replacement,
which is how unbounded right derived functors and derived `Hom` are constructed.

The adjunction is built from Mathlib's `CochainComplex.IsKInjective.Qh_map_bijective`: maps in
the homotopy category into a K-injective complex are the maps in the derived category.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154,
  §1.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex.IsKInjective

/-- Precomposition with a quasi-isomorphism is injective on homotopy classes of maps into a
K-injective complex. -/
theorem nonempty_homotopy_of_comp {K K' I : CochainComplex C ℤ} [I.IsKInjective]
    (f : K ⟶ K') [QuasiIso f] (g₁ g₂ : K' ⟶ I) (h : Homotopy (f ≫ g₁) (f ≫ g₂)) :
    Nonempty (Homotopy g₁ g₂) := by
  let := HasDerivedCategory.standard C
  have hf : IsIso (Qh.map ((HomotopyCategory.quotient _ _).map f)) := by
    rw [isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact HomologicalComplex.mem_quasiIso_iff _ |>.2 inferInstance
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ((Qh_map_bijective _ I).injective ?_)⟩
  rw [← cancel_epi (Qh.map ((HomotopyCategory.quotient _ _).map f))]
  simp only [← Functor.map_comp, HomotopyCategory.eq_of_homotopy _ _ h]

/-- K-injective replacements are unique up to homotopy equivalence: if `f₁ : K ⟶ I₁` and
`f₂ : K ⟶ I₂` are quasi-isomorphisms into K-injective complexes, there is a homotopy equivalence
`I₁ ≃ I₂` whose composition with `f₁` is homotopic to `f₂`. -/
theorem exists_homotopyEquiv {K I₁ I₂ : CochainComplex C ℤ} [I₁.IsKInjective] [I₂.IsKInjective]
    (f₁ : K ⟶ I₁) (f₂ : K ⟶ I₂) [QuasiIso f₁] [QuasiIso f₂] :
    ∃ e : HomotopyEquiv I₁ I₂, Nonempty (Homotopy (f₁ ≫ e.hom) f₂) := by
  let := HasDerivedCategory.standard C
  obtain ⟨g, hg⟩ := (Qh_map_bijective ((HomotopyCategory.quotient _ _).obj I₁) I₂).surjective
    ((quotientCompQhIso C).hom.app I₁ ≫ inv (Q.map f₁) ≫ Q.map f₂ ≫
      (quotientCompQhIso C).inv.app I₂)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  have hQ : Q.map g = inv (Q.map f₁) ≫ Q.map f₂ := by
    rw [← cancel_epi ((quotientCompQhIso C).hom.app I₁), ← quotientCompQhIso_hom_naturality, hg]
    simp
  have : QuasiIso g := by
    rw [← isIso_Q_map_iff_quasiIso, hQ]
    infer_instance
  obtain ⟨e, he⟩ := (quasiIso_iff g).1 this
  refine ⟨e, ⟨HomotopyCategory.homotopyOfEq _ _ ((Qh_map_bijective _ I₂).injective ?_)⟩⟩
  rw [← cancel_mono ((quotientCompQhIso C).hom.app I₂)]
  simp [he, hQ]

end CochainComplex.IsKInjective

namespace TauCeti

variable (C) in
/-- An abelian category has K-injective resolutions if every cochain complex, with no
boundedness assumption, admits a quasi-isomorphism into a K-injective complex. -/
class HasKInjectiveResolutions : Prop where
  /-- Every cochain complex has a quasi-isomorphism into a K-injective complex. -/
  exists_quasiIso_isKInjective (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (i : K ⟶ I), QuasiIso i ∧ I.IsKInjective

variable [HasKInjectiveResolutions C] [HasDerivedCategory.{w} C]

namespace KInjectiveReplacement

/-- The chosen K-injective replacement of a complex representing an object of `D(C)`. -/
private def complex (X : DerivedCategory C) : CochainComplex C ℤ :=
  (HasKInjectiveResolutions.exists_quasiIso_isKInjective (Q.objPreimage X)).choose

/-- The chosen quasi-isomorphism into the replacement. -/
private def ι (X : DerivedCategory C) : Q.objPreimage X ⟶ complex X :=
  (HasKInjectiveResolutions.exists_quasiIso_isKInjective (Q.objPreimage X)).choose_spec.choose

private instance quasiIso_ι (X : DerivedCategory C) : QuasiIso (ι X) :=
  (HasKInjectiveResolutions.exists_quasiIso_isKInjective
    (Q.objPreimage X)).choose_spec.choose_spec.1

private instance isKInjective_complex (X : DerivedCategory C) : (complex X).IsKInjective :=
  (HasKInjectiveResolutions.exists_quasiIso_isKInjective
    (Q.objPreimage X)).choose_spec.choose_spec.2

/-- The replacement represents the object it replaces. -/
private def iso (X : DerivedCategory C) :
    Qh.obj ((HomotopyCategory.quotient _ _).obj (complex X)) ≅ X :=
  (quotientCompQhIso C).app _ ≪≫ (asIso (Q.map (ι X))).symm ≪≫ Q.objObjPreimageIso X

/-- Maps in the derived category into `X` are homotopy classes of maps into its replacement. -/
private def homEquiv (Y : HomotopyCategory C (.up ℤ)) (X : DerivedCategory C) :
    (Qh.obj Y ⟶ X) ≃ (Y ⟶ (HomotopyCategory.quotient _ _).obj (complex X)) :=
  ((Iso.refl _).homCongr (iso X).symm).trans
    (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective Y (complex X))).symm

private theorem Qh_map_homEquiv (Y : HomotopyCategory C (.up ℤ)) (X : DerivedCategory C)
    (g : Qh.obj Y ⟶ X) : Qh.map (homEquiv Y X g) = g ≫ (iso X).inv := by
  simp [homEquiv, Iso.homCongr_apply, Equiv.ofBijective_apply_symm_apply]

private theorem homEquiv_naturality (Y' Y : HomotopyCategory C (.up ℤ)) (X : DerivedCategory C)
    (f : Y' ⟶ Y) (g : Qh.obj Y ⟶ X) :
    homEquiv Y' X (Qh.map f ≫ g) = f ≫ homEquiv Y X g :=
  (CochainComplex.IsKInjective.Qh_map_bijective Y' (complex X)).injective (by
    simp [Qh_map_homEquiv])

private theorem homEquiv_symm_apply (Y : HomotopyCategory C (.up ℤ)) (X : DerivedCategory C)
    (h : Y ⟶ (HomotopyCategory.quotient _ _).obj (complex X)) :
    (homEquiv Y X).symm h = Qh.map h ≫ (iso X).hom := by
  rw [Equiv.symm_apply_eq]
  exact (CochainComplex.IsKInjective.Qh_map_bijective Y (complex X)).injective (by
    simp [Qh_map_homEquiv])

end KInjectiveReplacement

open KInjectiveReplacement

variable (C) in
/-- The K-injective replacement functor `D(C) ⥤ K(C)`. It sends an object of the derived category
to a K-injective complex representing it, viewed in the homotopy category. On morphisms it uses
that maps in the derived category into a K-injective complex are homotopy classes of chain
maps. -/
def kInjectiveReplacement : DerivedCategory C ⥤ HomotopyCategory C (.up ℤ) :=
  Adjunction.rightAdjointOfEquiv homEquiv homEquiv_naturality

variable (C) in
/-- The K-injective replacement functor is right adjoint to the localization functor
`DerivedCategory.Qh : K(C) ⥤ D(C)`. -/
def kInjectiveReplacementAdjunction : Qh ⊣ kInjectiveReplacement C :=
  Adjunction.adjunctionOfEquivRight homEquiv homEquiv_naturality

/-- The K-injective replacement functor sends `X` to its chosen replacement `complex X`. -/
private theorem kInjectiveReplacement_obj (X : DerivedCategory C) :
    (kInjectiveReplacement C).obj X = (HomotopyCategory.quotient _ _).obj (complex X) :=
  rfl

/-- The values of the K-injective replacement functor are K-injective complexes. -/
instance isKInjective_kInjectiveReplacement_obj_as (X : DerivedCategory C) :
    CochainComplex.IsKInjective ((kInjectiveReplacement C).obj X).as := by
  rw [kInjectiveReplacement_obj]
  exact isKInjective_complex X

private theorem kInjectiveReplacementAdjunction_counit_app (X : DerivedCategory C) :
    (kInjectiveReplacementAdjunction C).counit.app X = (iso X).hom := by
  rw [kInjectiveReplacementAdjunction, Adjunction.adjunctionOfEquivRight_counit_app,
    homEquiv_symm_apply, Qh.map_id, Category.id_comp]

instance : IsIso (kInjectiveReplacementAdjunction C).counit := by
  have (X : DerivedCategory C) : IsIso ((kInjectiveReplacementAdjunction C).counit.app X) := by
    rw [kInjectiveReplacementAdjunction_counit_app]
    exact (inferInstance : IsIso (iso X).hom)
  exact NatIso.isIso_of_isIso_app _

variable (C) in
/-- The K-injective replacement functor is fully faithful. -/
def fullyFaithfulKInjectiveReplacement : (kInjectiveReplacement C).FullyFaithful :=
  (kInjectiveReplacementAdjunction C).fullyFaithfulROfIsIsoCounit

instance : (kInjectiveReplacement C).Full :=
  (fullyFaithfulKInjectiveReplacement C).full

instance : (kInjectiveReplacement C).Faithful :=
  (fullyFaithfulKInjectiveReplacement C).faithful

/-- The unit `K ⟶ I(K)` of the adjunction, from a complex to the K-injective replacement of its
image in the derived category, is a quasi-isomorphism. -/
theorem quasiIso_kInjectiveReplacementAdjunction_unit_app (K : HomotopyCategory C (.up ℤ)) :
    HomotopyCategory.quasiIso C _ ((kInjectiveReplacementAdjunction C).unit.app K) :=
  (isIso_Qh_map_iff _).1 inferInstance

/-- A chain map `K ⟶ I(K)` representing the unit of the adjunction is a quasi-isomorphism of
complexes into the K-injective replacement of `K`. -/
theorem quasiIso_of_quotient_map_eq_kInjectiveReplacementAdjunction_unit_app
    {K : CochainComplex C ℤ}
    (f : K ⟶ ((kInjectiveReplacement C).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj K))).as)
    (hf : (HomotopyCategory.quotient _ _).map f =
      (kInjectiveReplacementAdjunction C).unit.app ((HomotopyCategory.quotient _ _).obj K)) :
    QuasiIso f := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff, hf]
  exact quasiIso_kInjectiveReplacementAdjunction_unit_app _

/-- The essential image of the K-injective replacement functor consists exactly of the
K-injective complexes. -/
theorem mem_essImage_kInjectiveReplacement_iff (K : HomotopyCategory C (.up ℤ)) :
    (kInjectiveReplacement C).essImage K ↔ CochainComplex.IsKInjective K.as := by
  refine ⟨fun ⟨X, ⟨e⟩⟩ ↦ (HomotopyCategory.homotopyEquivOfIso e).isKInjective, fun _ ↦ ?_⟩
  rw [← (kInjectiveReplacementAdjunction C).isIso_unit_app_iff_mem_essImage]
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient _ _).map_surjective
    ((kInjectiveReplacementAdjunction C).unit.app K)
  have := quasiIso_of_quotient_map_eq_kInjectiveReplacementAdjunction_unit_app f hf
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).1 this
  rw [← hf]
  exact (HomotopyCategory.isoOfHomotopyEquiv e).isIso_hom

end TauCeti
