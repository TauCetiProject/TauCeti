/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MaximalIdealPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.AddCommGrp
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Site
public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic
public import TauCeti.RingTheory.Affinoid.TopologicallyFiniteType
import Mathlib.CategoryTheory.Limits.Preserves.Lattice
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

/-!
# Classical and adic Čech complexes of rational covers

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, with a complete
ultrametric algebra norm. Its maximal ideals are the classical points of the adic spectrum
`X = Spa(A, A°)` (`TauCeti.ValuationSpectrum.maximalSpectrumToSpa`). The classical points of a
rational open `R(T/s) ⊆ X` form the classical rational domain
`{x | |s(x)| ≠ 0, |t(x)| ≤ |s(x)| for t ∈ T}`
(`TauCeti.ValuationSpectrum.maximalSpectrumToSpa_mem_spaBasicOpen_iff`). So every rational open
`V` has a classical trace `AffinoidSubdomain.ofSpaRationalOpen`, an affinoid subdomain of `Sp A`.

This file compares the coordinate presheaf of the classical affinoid subdomains,
`TauCeti.AffinoidSubdomain.presheaf`, with the structure presheaf of `X`. On the rational opens,
regarded as a meet-semilattice with top, both are presheaves of abelian groups, and they are
naturally isomorphic: on `V = R(T/s)`, both are identified with the rational fraction algebra
`A⟨T/s⟩`, by the universal property of affinoid subdomains on the classical side and by
`TauCeti.RationalFraction.completionLocEquiv` and
`TauCeti.ValuationSpectrum.presentationLimitRationalIso` on the adic side. These identifications
commute with the maps from `A`, and on the classical side maps out of `A⟨T/s⟩` are determined by
their restrictions to `A`; this gives naturality.

Taking traces of rational opens preserves finite intersections and the whole space, so it
preserves the finite products in the Čech complexes. Hence the classical Čech complex of the
traces of a family of rational opens is exact exactly when the adic Čech complex of the family
is (`TauCeti.AffinoidSubdomain.quasiIso_cechAugmentation_ofSpaRationalOpen_iff`). This transports
acyclicity theorems for rational covers of `X` to classical affinoid covers. No covering
hypothesis is involved in the comparison itself.

## Main definitions

* `TauCeti.AffinoidSubdomain.ofSpaRationalOpen`: the classical points of a rational open of
  `Spa(A, A°)`, as an affinoid subdomain of `Sp A`.

## Main results

* `TauCeti.AffinoidSubdomain.quasiIso_cechAugmentation_ofSpaRationalOpen_iff`: the augmented
  Čech complex of the classical coordinate presheaf for the traces of a family of rational opens
  is exact if and only if the augmented Čech complex of the adic structure presheaf for the family
  is.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.2.2 and 8.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.38, Example 7.58,
  §8.1 and Lemma 8.34.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition
  TauCeti.CategoryTheory

namespace TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]

open ValuationSpectrum

namespace AffinoidSubdomain

/-! ### Classical traces of rational opens -/

/-- An enumeration of the elements of a finite set, used as the numerators of a rational fraction
algebra. -/
private noncomputable def enum (T : Finset A) : Fin T.card → A := fun i ↦ (T.equivFin.symm i : A)

omit [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] in
private theorem range_enum (T : Finset A) : Set.range (enum T) = T := by
  ext a
  refine ⟨?_, fun ha ↦ ⟨T.equivFin ⟨a, ha⟩, by simp [enum]⟩⟩
  rintro ⟨i, rfl⟩
  exact (T.equivFin.symm i).property

omit [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] in
private theorem insert_range_enum {T : Finset A} {s : A} (hs : s ∈ T) :
    insert s (Set.range (enum T)) = T := by
  rw [range_enum]
  exact Set.insert_eq_of_mem hs

/-! ### The sections over a rational open

For each rational open `V` choose a presentation `V = R(T/s)` with `s ∈ T` and `T` generating the
unit ideal. The sections of both presheaves over `V` are identified with `A⟨T/s⟩`. -/

section Presentation

omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace A]

variable (K) in
include K in
private theorem exists_pres {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    ∃ T : Finset A, ∃ s ∈ T, Ideal.span (T : Set A) = ⊤ ∧
      V = spaBasicOpen (powerBoundedSubring A) T s :=
  have := IsTateRing.of_normedAlgebra K A
  exists_spaBasicOpen_of_mem_spaRationalOpens hV

variable (K) in
include K in
/-- The chosen numerators of a rational open. -/
private noncomputable def num {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) : Finset A :=
  (exists_pres K hV).choose

variable (K) in
include K in
/-- The chosen denominator of a rational open. -/
private noncomputable def den {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) : A :=
  (exists_pres K hV).choose_spec.choose

private theorem den_mem {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) : den K hV ∈ num K hV :=
  (exists_pres K hV).choose_spec.choose_spec.1

private theorem span_num {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    Ideal.span (num K hV : Set A) = ⊤ :=
  (exists_pres K hV).choose_spec.choose_spec.2.1

private theorem eq_spaBasicOpen {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    V = spaBasicOpen (powerBoundedSubring A) (num K hV) (den K hV) :=
  (exists_pres K hV).choose_spec.choose_spec.2.2

private theorem isOpen_span_num {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    IsOpen (Ideal.span (num K hV : Set A) : Set A) := by
  rw [span_num]
  exact isOpen_univ

private theorem hasDenominatorPower_num (P : PairOfDefinition A)
    {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    P.HasDenominatorPower (num K hV) (den K hV) (Localization.Away (den K hV)) :=
  hasDenominatorPower_of_isOpen_span P _ _ _ (isOpen_span_num hV)

variable (K) in
include K in
/-- The chosen presentation of a rational open. -/
private noncomputable abbrev pres (P : PairOfDefinition A)
    {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) : Presentation P :=
  ⟨num K hV, den K hV, hasDenominatorPower_num P hV⟩

end Presentation

variable [hA : Fact (IsAffinoidAlgebra K A)]

/-- The classical points of `R(T/s)` form the classical rational domain with denominator `s` and
the elements of `T` as numerators. -/
private theorem preimage_spaBasicOpen (T : Finset A) (s : A) :
    maximalSpectrumToSpa K hA.out.isTopologicallyFiniteType ⁻¹'
        (spaBasicOpen (powerBoundedSubring A) T s : Set (spa (powerBoundedSubring A))) =
      rationalDomain K s (enum T) := by
  ext x
  rw [Set.mem_preimage, SetLike.mem_coe, maximalSpectrumToSpa_mem_spaBasicOpen_iff,
    mem_rationalDomain]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ h _ (T.equivFin.symm i).property, fun h t ht ↦ ?_⟩
  simpa [enum] using h (T.equivFin ⟨t, ht⟩)

/-- **The classical trace of a rational open.** The classical points of a rational open `V` of
`Spa(A, A°)`, regarded as a set of maximal ideals of the affinoid algebra `A`. If `V = R(T/s)`,
this is the classical rational domain `{x | |s(x)| ≠ 0, |t(x)| ≤ |s(x)| for t ∈ T}`, represented
by the rational fraction algebra `A⟨T/s⟩`, so it is an affinoid subdomain. -/
noncomputable def ofSpaRationalOpen {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) : AffinoidSubdomain K A where
  carrier := maximalSpectrumToSpa K hA.out.isTopologicallyFiniteType ⁻¹' V
  exists_representation := by
    have := IsTateRing.of_normedAlgebra K A
    obtain ⟨T, s, hs, hT, rfl⟩ := exists_spaBasicOpen_of_mem_spaRationalOpens hV
    refine ⟨CommAlgCat.of K (RationalFraction s (enum T)), IsScalarTower.toAlgHom K A _, ?_⟩
    rw [preimage_spaBasicOpen]
    exact RationalFraction.isAffinoidSubdomainMap hA.out (by rwa [insert_range_enum hs])

/-- A maximal ideal lies in the classical trace of `V` exactly when its classical point lies
in `V`. -/
@[simp]
theorem mem_ofSpaRationalOpen {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) (x : MaximalSpectrum A) :
    x ∈ ofSpaRationalOpen (K := K) hV ↔
      maximalSpectrumToSpa K hA.out.isTopologicallyFiniteType x ∈ V :=
  Iff.rfl

/-- Taking classical traces is monotone. -/
theorem ofSpaRationalOpen_mono {V W : Opens (spa (powerBoundedSubring A))}
    {hV : V ∈ spaRationalOpens (powerBoundedSubring A)}
    {hW : W ∈ spaRationalOpens (powerBoundedSubring A)} (h : W ≤ V) :
    ofSpaRationalOpen (K := K) hW ≤ ofSpaRationalOpen (K := K) hV :=
  fun _ hx ↦ h hx

/-- The classical trace of an intersection of rational opens is the intersection of the
classical traces. -/
@[simp]
theorem ofSpaRationalOpen_inf {V W : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A))
    (hW : W ∈ spaRationalOpens (powerBoundedSubring A))
    (hVW : V ⊓ W ∈ spaRationalOpens (powerBoundedSubring A)) :
    ofSpaRationalOpen (K := K) hVW = ofSpaRationalOpen hV ⊓ ofSpaRationalOpen hW :=
  SetLike.coe_injective <| by
    rw [coe_inf]
    ext
    simp

/-- The classical trace of the whole adic spectrum is the whole classical spectrum. -/
@[simp]
theorem ofSpaRationalOpen_top (h : ⊤ ∈ spaRationalOpens (powerBoundedSubring A)) :
    ofSpaRationalOpen (K := K) h = ⊤ := by
  refine SetLike.coe_injective ?_
  rw [coe_top]
  ext
  simp

private theorem isAffinoidSubdomainMap_pres {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    IsAffinoidSubdomainMap
      (IsScalarTower.toAlgHom K A (RationalFraction (den K hV) (enum (num K hV))))
      (ofSpaRationalOpen (K := K) hV : Set (MaximalSpectrum A)) := by
  have h := RationalFraction.isAffinoidSubdomainMap hA.out (g := den K hV)
    (f := enum (num K hV)) (by rw [insert_range_enum (den_mem hV)]; exact span_num hV)
  rwa [← preimage_spaBasicOpen, ← eq_spaBasicOpen hV] at h

/-- `TauCeti.RationalFraction.completionLocEquiv` for a numerator set which is only
propositionally of the form `insert g (Set.range f)`. -/
private noncomputable def completionLocEquivOfEq (P : PairOfDefinition A) {g : A} {m : ℕ}
    {f : Fin m → A} {T : Set A} (hT : insert g (Set.range f) = T)
    (hden : P.HasDenominatorPower T g (Localization.Away g)) (h : Ideal.span T = ⊤) :
    letI := locUniformSpace P T g _ hden
    letI := isUniformAddGroup_locUniformSpace P T g _ hden
    letI := isTopologicalRing_locUniformSpace P T g _ hden
    RationalFraction g f ≃+* UniformSpace.Completion (Localization.Away g) := by
  subst hT
  exact RationalFraction.completionLocEquiv hA.out P _ hden h

private theorem completionLocEquivOfEq_algebraMap (P : PairOfDefinition A) {g : A} {m : ℕ}
    {f : Fin m → A} {T : Set A} (hT : insert g (Set.range f) = T)
    (hden : P.HasDenominatorPower T g (Localization.Away g)) (h : Ideal.span T = ⊤) (a : A) :
    letI := locUniformSpace P T g _ hden
    letI := isUniformAddGroup_locUniformSpace P T g _ hden
    letI := isTopologicalRing_locUniformSpace P T g _ hden
    completionLocEquivOfEq (K := K) P hT hden h (algebraMap A _ a) =
      toCompletionLoc P T g _ hden a := by
  subst hT
  exact RationalFraction.completionLocEquiv_algebraMap hA.out P _ hden h a

local notation "F" => TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat
local notation "Ab" => forget₂ (CommAlgCat K) CommRingCat ⋙ forget₂ CommRingCat RingCat ⋙
  forget₂ RingCat AddCommGrpCat
local notation "Ab'" => forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

variable (P : PairOfDefinition A)

/-- The classical and adic sections over a rational open `V = R(T/s)`, as commutative rings:
both are identified with `A⟨T/s⟩`. -/
private noncomputable def sectionsIso {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    CommRingCat.of (ofSpaRationalOpen (K := K) hV).sections ≅
      (F).obj (presentationLimit (P := P) (powerBoundedSubring A) V) :=
  letI := locUniformSpace P (num K hV) (den K hV) _ (hasDenominatorPower_num (K := K) P hV)
  letI := isUniformAddGroup_locUniformSpace P (num K hV) (den K hV) _
    (hasDenominatorPower_num (K := K) P hV)
  letI := isTopologicalRing_locUniformSpace P (num K hV) (den K hV) _
    (hasDenominatorPower_num (K := K) P hV)
  (((ofSpaRationalOpen (K := K) hV).sectionsAlgEquiv
      (isAffinoidSubdomainMap_pres (K := K) hV)).toRingEquiv.trans
    (completionLocEquivOfEq (K := K) P (insert_range_enum (den_mem (K := K) hV))
      (hasDenominatorPower_num (K := K) P hV) (span_num (K := K) hV))).toCommRingCatIso ≪≫
    (pres K P hV).completionLocObjCommRingCatIso.symm ≪≫
    (F).mapIso (presentationLimitRationalIso (powerBoundedSubring A)
      (fun _ ha ↦ mem_powerBoundedSubring.mp ha) (pres K P hV)
      (isOpen_span_num (K := K) hV)).symm ≪≫
    (F).mapIso (eqToIso (congrArg (presentationLimit (P := P) (powerBoundedSubring A))
      (eq_spaBasicOpen (K := K) hV).symm))

/-- The structure map from `A` to the sections of the presentation limit over `V`, as a morphism
of commutative rings. -/
private noncomputable def toSectionsAdic (V : Opens (spa (powerBoundedSubring A))) :
    CommRingCat.of A ⟶ (F).obj (presentationLimit (P := P) (powerBoundedSubring A) V) :=
  (forget₂ _root_.TopCommRingCat CommRingCat).map
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm) ≫
    (F).map (toPresentationLimit (P := P) (powerBoundedSubring A) V)

private theorem toSectionsAdic_comp_map {V W : Opens (spa (powerBoundedSubring A))}
    (h : W ≤ V) :
    toSectionsAdic P V ≫ (F).map (presentationLimitMap (P := P) h) = toSectionsAdic P W := by
  unfold toSectionsAdic
  -- The source `CommRingCat.of A` is only definitionally the image of `TopCommRingCat.of A`, so
  -- `rw [Category.assoc]` finds no instance of its pattern; the composites are reassociated by
  -- `exact` instead.
  exact (Category.assoc _ _ _).trans <| congrArg _ (((F).map_comp _ _).symm.trans
    (congrArg (F).map (toPresentationLimit_comp_presentationLimitMap _ h)))

/-- The identification of sections over a rational open commutes with the maps from `A`. -/
private theorem toSections_comp_sectionsIso_hom {V : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A)) :
    CommRingCat.ofHom (ofSpaRationalOpen (K := K) hV).toSections.toRingHom ≫
        (sectionsIso P hV).hom = toSectionsAdic P V := by
  let _ := locUniformSpace P (num K hV) (den K hV) _ (hasDenominatorPower_num (K := K) P hV)
  have _ := isUniformAddGroup_locUniformSpace P (num K hV) (den K hV) _
    (hasDenominatorPower_num (K := K) P hV)
  have _ := isTopologicalRing_locUniformSpace P (num K hV) (den K hV) _
    (hasDenominatorPower_num (K := K) P hV)
  -- The classical half of the identification sends `a` to its image in the completion.
  have h₁ : CommRingCat.ofHom (ofSpaRationalOpen (K := K) hV).toSections.toRingHom ≫
      (((ofSpaRationalOpen (K := K) hV).sectionsAlgEquiv
        (isAffinoidSubdomainMap_pres (K := K) hV)).toRingEquiv.trans
        (completionLocEquivOfEq (K := K) P (insert_range_enum (den_mem (K := K) hV))
          (hasDenominatorPower_num (K := K) P hV) (span_num (K := K) hV))).toCommRingCatIso.hom =
      CommRingCat.ofHom (toCompletionLoc P (num K hV) (den K hV) _
        (hasDenominatorPower_num (K := K) P hV)) := by
    ext a
    simp [completionLocEquivOfEq_algebraMap]
  -- The adic half sends the image in the completion to the canonical section.
  have h₂ : (F).map (pres K P hV).toCompletionLocObjHom ≫
      (F).map (presentationLimitRationalIso (powerBoundedSubring A)
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) (pres K P hV)
        (isOpen_span_num (K := K) hV)).inv ≫
      (F).map (eqToHom (congrArg (presentationLimit (P := P) (powerBoundedSubring A))
        (eq_spaBasicOpen (K := K) hV).symm)) =
      (F).map (toPresentationLimit (P := P) (powerBoundedSubring A) V) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      toCompletionLocObjHom_comp_presentationLimitRationalIso_inv_assoc,
      toPresentationLimit_comp_eqToHom _ (eq_spaBasicOpen (K := K) hV).symm]
  simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, eqToIso.hom]
  rw [reassoc_of% h₁,
    reassoc_of% (Presentation.ofHom_toCompletionLoc_comp_completionLocObjCommRingCatIso_inv
      (pres K P hV))]
  -- As in `toSectionsAdic_comp_map`, the objects agree only definitionally, so `Category.assoc`
  -- is applied by `exact` rather than by rewriting.
  exact (Category.assoc _ _ _).trans (congrArg _ h₂)

/-- **Naturality of the identification of sections.** Under the identifications of sections
over rational opens, classical restriction is adic restriction. -/
private theorem sectionsIso_hom_naturality {V W : Opens (spa (powerBoundedSubring A))}
    (hV : V ∈ spaRationalOpens (powerBoundedSubring A))
    (hW : W ∈ spaRationalOpens (powerBoundedSubring A)) (h : W ≤ V) :
    (sectionsIso (K := K) P hV).hom ≫ (F).map (presentationLimitMap (P := P) h) =
      CommRingCat.ofHom (restrict (ofSpaRationalOpen_mono (K := K) h)).toRingHom ≫
        (sectionsIso (K := K) P hW).hom := by
  rw [← Iso.comp_inv_eq, Category.assoc]
  set φ := (sectionsIso (K := K) P hV).hom ≫ (F).map (presentationLimitMap (P := P) h) ≫
    (sectionsIso (K := K) P hW).inv
  -- `φ` commutes with the maps from `A`, since both identifications and both restrictions do.
  have hφ (a : A) : φ ((ofSpaRationalOpen (K := K) hV).toSections a) =
      (ofSpaRationalOpen (K := K) hW).toSections a := by
    have e := toSections_comp_sectionsIso_hom (K := K) P hV
    have e' := toSections_comp_sectionsIso_hom (K := K) P hW
    rw [← Iso.eq_comp_inv] at e'
    have hcomp : CommRingCat.ofHom (ofSpaRationalOpen (K := K) hV).toSections.toRingHom ≫ φ =
        CommRingCat.ofHom (ofSpaRationalOpen (K := K) hW).toSections.toRingHom := by
      rw [e', ← toSectionsAdic_comp_map P h, ← e]
      simp [φ]
    exact congrArg (fun f ↦ f.hom a) hcomp
  -- So `φ` is a `K`-algebra map out of a representing algebra, determined on `A`.
  let ψ : (ofSpaRationalOpen (K := K) hV).sections →ₐ[K]
      (ofSpaRationalOpen (K := K) hW).sections :=
    { φ.hom with commutes' := fun c ↦ by simpa using hφ (algebraMap K A c) }
  have hψ : ψ = restrict (ofSpaRationalOpen_mono (K := K) h) := by
    apply (ofSpaRationalOpen (K := K) hV).isAffinoidSubdomainMap.algHom_ext
      (ofSpaRationalOpen (K := K) hW).isAffinoidAlgebra
    ext a
    simpa [ψ] using hφ a
  ext x
  exact (congrArg (fun χ : _ →ₐ[K] _ ↦ χ x) hψ :)

/-! ### The comparison of presheaves on rational opens -/

variable (A) in
/-- The rational opens of `Spa(A, A°)`. -/
private def RatOpen : Type u :=
  {V : Opens (spa (powerBoundedSubring A)) // V ∈ spaRationalOpens (powerBoundedSubring A)}

private noncomputable instance [IsHuberRing A] : SemilatticeInf (RatOpen A) :=
  Subtype.semilatticeInf fun _ _ ↦ inf_mem_spaRationalOpens

private noncomputable instance [IsHuberRing A] : OrderTop (RatOpen A) :=
  Subtype.orderTop (top_mem_spaRationalOpens _)

/-- The sections of the presentation limit, as an abelian group, are the values of
`presentationLimitAddCommGrpPresheaf`. -/
private noncomputable def adicIso (V : Set.Iic (⊤ : Opens (spa (powerBoundedSubring A)))) :
    (Ab').obj ((F).obj (presentationLimit (P := P) (powerBoundedSubring A) V.val)) ≅
      (presentationLimitAddCommGrpPresheaf P (powerBoundedSubring A) ⊤).obj (Opposite.op V) :=
  eqToIso (presentationLimitAddCommGrpPresheaf_obj_eq_forget₂ P (powerBoundedSubring A) V).symm

omit [CompleteSpace A] in
private theorem adicIso_naturality
    {V W : Set.Iic (⊤ : Opens (spa (powerBoundedSubring A)))} (h : W ⟶ V) :
    (Ab').map ((F).map (presentationLimitMap (P := P) (leOfHom h))) ≫ (adicIso P W).hom =
      (adicIso P V).hom ≫
        (presentationLimitAddCommGrpPresheaf P (powerBoundedSubring A) ⊤).map h.op := by
  simp [adicIso, presentationLimitAddCommGrpPresheaf_map_eq_forget₂]

section Huber

variable [IsHuberRing A]

variable (K) in
/-- Taking classical traces preserves finite intersections and the whole space. -/
private noncomputable def traceHom : InfTopHom (RatOpen A) (AffinoidSubdomain K A) where
  toFun V := ofSpaRationalOpen V.property
  map_inf' V W := ofSpaRationalOpen_inf V.property W.property _
  map_top' := ofSpaRationalOpen_top _

/-- The inclusion of the rational opens into all opens. -/
private noncomputable def inclHom :
    InfTopHom (RatOpen A) (Set.Iic (⊤ : Opens (spa (powerBoundedSubring A)))) where
  toFun V := ⟨V.val, Set.mem_Iic.2 le_top⟩
  map_inf' _ _ := rfl
  map_top' := rfl

/-- **The classical and adic presheaves agree on rational opens.** On the rational opens of
`Spa(A, A°)`, the classical coordinate presheaf of the traces and the adic structure presheaf
are naturally isomorphic as presheaves of abelian groups. -/
private noncomputable def addCommGrpIso :
    (OrderHom.ofClass (traceHom K (A := A))).toFunctor.op ⋙ presheaf ⋙ Ab ≅
      (OrderHom.ofClass (inclHom (A := A))).toFunctor.op ⋙
        presentationLimitAddCommGrpPresheaf P (powerBoundedSubring A) ⊤ :=
  NatIso.ofComponents (fun V ↦ (Ab').mapIso (sectionsIso (K := K) P V.unop.property) ≪≫
      adicIso P (inclHom V.unop))
    fun {V W} f ↦ by
      have hcl : ((OrderHom.ofClass (traceHom K (A := A))).toFunctor.op ⋙ presheaf ⋙ Ab).map f =
          (Ab').map (CommRingCat.ofHom (restrict (ofSpaRationalOpen_mono (K := K)
            (hV := V.unop.property) (hW := W.unop.property) (leOfHom f.unop))).toRingHom) := by
        -- `presheaf ⋙ Ab` acts on `f` by `restrict` between the traces. This is definitional
        -- but not available by rewriting: `presheaf_map_hom` is stated for `homOfLE` rather than
        -- for the image of `f` under `traceHom`, and the traces `traceHom K V` unfold to
        -- `ofSpaRationalOpen V.property` only through the definition of `traceHom`.
        rfl
      have N₁ := congrArg (Ab').map
        (sectionsIso_hom_naturality (K := K) P V.unop.property W.unop.property (leOfHom f.unop))
      rw [Functor.map_comp, Functor.map_comp] at N₁
      have N₂ := adicIso_naturality P
        ((OrderHom.ofClass (inclHom (A := A))).toFunctor.map f.unop)
      rw [hcl]
      -- The objects of the two composites agree only definitionally, so the associativity moves
      -- are made by `exact` through the reassociated forms of `N₁` and `N₂`.
      exact ((reassoc_of% N₁) _).symm.trans
        ((congrArg (_ ≫ ·) N₂).trans (Category.assoc _ _ _).symm)

end Huber

/-- **Classical and adic Čech complexes of rational opens agree.** Let `A` be an affinoid algebra
with a complete ultrametric algebra norm, `P` a pair of definition of `A` and `V` a family of
rational opens of `Spa(A, A°)`. The augmented Čech complex of the classical coordinate presheaf,
as a presheaf of abelian groups on the affinoid subdomains of `Sp A`, for the classical traces of
the `V i` is exact if and only if the augmented Čech complex of the adic structure presheaf, on
the opens of `Spa(A, A°)`, for the `V i` is exact. The family need not cover. -/
theorem quasiIso_cechAugmentation_ofSpaRationalOpen_iff {ι : Type u}
    {V : ι → Opens (spa (powerBoundedSubring A))}
    (hV : ∀ i, V i ∈ spaRationalOpens (powerBoundedSubring A)) :
    QuasiIso (cechAugmentation (fun i ↦ ofSpaRationalOpen (K := K) (hV i)) isTerminalTop
        (presheaf ⋙ Ab)) ↔
      QuasiIso (cechAugmentation
        (fun i ↦ (⟨V i, Set.mem_Iic.2 le_top⟩ :
          Set.Iic (⊤ : Opens (spa (powerBoundedSubring A)))))
        isTerminalTop (presentationLimitAddCommGrpPresheaf P (powerBoundedSubring A) ⊤)) := by
  have := IsTateRing.of_normedAlgebra K A
  let U : ι → RatOpen A := fun i ↦ ⟨V i, hV i⟩
  have htop : (OrderHom.ofClass (traceHom K (A := A))).toFunctor.obj ⊤ = ⊤ :=
    map_top (traceHom K (A := A))
  -- The classical complex is taken for the terminal object `⊤`, the transport along
  -- `traceHom` for its value at `⊤`; these agree, and terminality is a proposition.
  have hterm {T T' : AffinoidSubdomain K A} (e : T = T') (hT : IsTerminal T)
      (hT' : IsTerminal T') :
      QuasiIso (cechAugmentation (fun i ↦ ofSpaRationalOpen (K := K) (hV i)) hT (presheaf ⋙ Ab)) ↔
        QuasiIso (cechAugmentation (fun i ↦ ofSpaRationalOpen (K := K) (hV i)) hT'
          (presheaf ⋙ Ab)) := by
    subst e
    rw [Subsingleton.elim hT hT']
  refine (hterm htop.symm isTerminalTop (isTerminalTop.ofIso (eqToIso htop.symm))).trans ?_
  refine (quasiIso_cechAugmentation_op_comp_iff
    (OrderHom.ofClass (traceHom K (A := A))).toFunctor U (presheaf ⋙ Ab)
    (fun _ _ ↦ inferInstance) isTerminalTop _).symm.trans ?_
  refine (quasiIso_cechAugmentation_iff_of_iso U isTerminalTop _
    (addCommGrpIso (K := K) P)).trans ?_
  exact quasiIso_cechAugmentation_op_comp_iff (OrderHom.ofClass (inclHom (A := A))).toFunctor U
    _ (fun _ _ ↦ inferInstance) isTerminalTop isTerminalTop

end AffinoidSubdomain

end TauCeti
