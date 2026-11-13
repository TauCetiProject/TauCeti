/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Triangulated
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence

/-!
# The stable and singularity categories of Gorenstein-projective modules over a Noetherian ring

Over a left Noetherian ring `A`, a finitely generated `A`-module is Gorenstein-projective in the
module sense (`TauCeti.IsGorensteinProjective`) if and only if it is a Gorenstein-projective object
of the abelian category `FGModuleCat A` (`FGModuleCat.isGorensteinProjective_iff`). This upgrades
that objectwise identification to an exact equivalence of Frobenius categories
`GorensteinProjectiveModuleCat A ≌ CategoryTheory.GorensteinProjective (FGModuleCat A)`.

Since both directions preserve conflations, they preserve projective-injective objects and induce
a triangulated equivalence between the two projective stable categories for Happel's
triangulations (`GorensteinProjectiveModuleCat.stableEquivalenceFGModuleCat`). Composing with
Chen's fully faithful triangle functor
`CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat A)` yields a fully
faithful triangle functor
`GorensteinProjectiveModuleCat.toSingularityCategory A` from the stable category of finitely
generated Gorenstein-projective `A`-modules to the singularity category
`SingularityCategory (FGModuleCat A)`.

## Main definitions

In the namespace `TauCeti.GorensteinProjectiveModuleCat`:

* `toFGModuleCat` and `ofFGModuleCat`: the functors identifying Gorenstein-projective modules with
  Gorenstein-projective objects of `FGModuleCat A`, packaged as `equivalenceFGModuleCat`.
* `stableEquivalenceFGModuleCat`: the induced equivalence between the projective stable categories
  of `GorensteinProjectiveModuleCat A` and `CategoryTheory.GorensteinProjective (FGModuleCat A)`,
  with shift compatibilities `stableEquivalenceFGModuleCatFunctorCommShift` and
  `stableEquivalenceFGModuleCatInverseCommShift`.
* `toSingularityCategory`: Chen's fully faithful functor from the projective stable category of
  `GorensteinProjectiveModuleCat A` to `SingularityCategory (FGModuleCat A)`, with shift
  compatibility `toSingularityCategoryCommShift`.

## Main results

In the namespace `TauCeti.GorensteinProjectiveModuleCat`:

* `stableConflationExact_toFGModuleCat` and `stableConflationExact_ofFGModuleCat`: both directions
  of `equivalenceFGModuleCat` preserve conflations and projective-injective objects.
* `stableEquivalenceFGModuleCat_isTriangulated`: the stable comparison equivalence is triangulated.
* `toSingularityCategory_isTriangulated`: Chen's functor on `GorensteinProjectiveModuleCat A` is a
  triangle functor.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris Sér. I
  Math. **305** (1987), 225–228, Example 2.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace TauCeti.GorensteinProjectiveModuleCat

section Equivalence

variable (A : Type u) [Ring A] [IsNoetherianRing A] [Small.{v} A]

/-- The functor viewing a finitely generated Gorenstein-projective `A`-module as a
Gorenstein-projective object of the abelian category `FGModuleCat A`. -/
def toFGModuleCat :
    GorensteinProjectiveModuleCat.{v} A ⥤
      CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) :=
  ObjectProperty.lift (isGorensteinProjective (FGModuleCat.{v} A))
    (ObjectProperty.ιOfLE fun X hX ↦ (ModuleCat.isFG_iff X).2 hX.finite)
    fun X ↦ (FGModuleCat.isGorensteinProjective_iff _).2 X.property

/-- The functor viewing a Gorenstein-projective object of `FGModuleCat A` as a finitely generated
Gorenstein-projective `A`-module. -/
def ofFGModuleCat :
    CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) ⥤
      GorensteinProjectiveModuleCat.{v} A :=
  ObjectProperty.lift (IsGorensteinProjective.{v} A)
    ((isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
      forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))
    fun X ↦ (FGModuleCat.isGorensteinProjective_iff X.obj).1 X.property

instance : (toFGModuleCat.{v} A).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    rfl

instance : (ofFGModuleCat.{v} A).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    rfl

/-- Forgetting Gorenstein-projectivity after `toFGModuleCat` gives the inclusion into
`FGModuleCat A`. -/
theorem toFGModuleCat_comp_ι :
    toFGModuleCat.{v} A ⋙ (isGorensteinProjective (FGModuleCat.{v} A)).ι =
      ObjectProperty.ιOfLE fun X hX ↦ (ModuleCat.isFG_iff X).2 hX.finite :=
  (rfl)

/-- Forgetting both Gorenstein-projectivity and finite generation after `toFGModuleCat` recovers
the underlying module inclusion. -/
theorem toFGModuleCat_comp_ι_comp_forget₂ :
    toFGModuleCat.{v} A ⋙ (isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) =
      (IsGorensteinProjective.{v} A).ι :=
  (rfl)

/-- Forgetting Gorenstein-projectivity after `ofFGModuleCat` forgets Gorenstein-projectivity and
finite generation on `FGModuleCat A`. -/
theorem ofFGModuleCat_comp_ι :
    ofFGModuleCat.{v} A ⋙ (IsGorensteinProjective.{v} A).ι =
      (isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) :=
  (rfl)

variable {A} in
/-- The underlying finitely generated module of `(toFGModuleCat A).obj X`. -/
@[simp]
theorem toFGModuleCat_obj_obj (X : GorensteinProjectiveModuleCat.{v} A) :
    ((toFGModuleCat.{v} A).obj X).obj = ⟨X.obj, (ModuleCat.isFG_iff X.obj).2 X.property.finite⟩ :=
  (rfl)

variable {A} in
/-- The underlying module of `(ofFGModuleCat A).obj X`. -/
@[simp]
theorem ofFGModuleCat_obj_obj (X : CategoryTheory.GorensteinProjective (FGModuleCat.{v} A)) :
    ((ofFGModuleCat.{v} A).obj X).obj = X.obj.obj :=
  (rfl)

/-- **Equivalence between Gorenstein-projective modules and Gorenstein-projective objects of
`mod-A`** over a left Noetherian ring. -/
def equivalenceFGModuleCat :
    GorensteinProjectiveModuleCat.{v} A ≌
      CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) where
  functor := toFGModuleCat.{v} A
  inverse := ofFGModuleCat.{v} A
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    apply ObjectProperty.hom_ext
    exact (Category.id_comp f.hom).trans (Category.comp_id f.hom).symm
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (Category.id_comp f.hom.hom).trans (Category.comp_id f.hom.hom).symm
  functor_unitIso_comp _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _

/-- The forward functor of `equivalenceFGModuleCat` is `toFGModuleCat`. -/
@[simp]
theorem equivalenceFGModuleCat_functor :
    (equivalenceFGModuleCat.{v} A).functor = toFGModuleCat.{v} A :=
  (rfl)

/-- The inverse functor of `equivalenceFGModuleCat` is `ofFGModuleCat`. -/
@[simp]
theorem equivalenceFGModuleCat_inverse :
    (equivalenceFGModuleCat.{v} A).inverse = ofFGModuleCat.{v} A :=
  (rfl)

instance : (equivalenceFGModuleCat.{v} A).functor.Additive :=
  inferInstanceAs (toFGModuleCat.{v} A).Additive

instance : (equivalenceFGModuleCat.{v} A).symm.functor.Additive :=
  inferInstanceAs (ofFGModuleCat.{v} A).Additive

variable {A}

/-- `toFGModuleCat` preserves conflations: short exactness in `ModuleCat A` and in `FGModuleCat A`
coincide along the faithful exact forgetful functor. -/
theorem isConflationExact_toFGModuleCat :
    (exactStructure.{v} A).IsConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (toFGModuleCat.{v} A) where
  map_conflation {S} hS := by
    rw [exactStructure_conflation_iff] at hS
    rw [CategoryTheory.GorensteinProjective.exactStructure_conflation_iff]
    let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
    have hmap : ((S.map (toFGModuleCat.{v} A)).map
        (isGorensteinProjective (FGModuleCat.{v} A)).ι).map F =
          S.map (IsGorensteinProjective.{v} A).ι := rfl
    have hSF : (((S.map (toFGModuleCat.{v} A)).map
        (isGorensteinProjective (FGModuleCat.{v} A)).ι).map F).ShortExact := by
      rwa [hmap]
    refine
      { exact := (ShortComplex.exact_map_iff_of_faithful _ F).1 hSF.exact
        mono_f := F.mono_of_mono_map hSF.mono_f
        epi_g := F.epi_of_epi_map hSF.epi_g }

/-- `ofFGModuleCat` preserves conflations: `forget₂ (FGModuleCat A) (ModuleCat A)` is exact. -/
theorem isConflationExact_ofFGModuleCat :
    (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A)).IsConflationExact
      (exactStructure.{v} A) (ofFGModuleCat.{v} A) where
  map_conflation {S} hS := by
    rw [CategoryTheory.GorensteinProjective.exactStructure_conflation_iff] at hS
    rw [exactStructure_conflation_iff]
    have hmap : (S.map (ofFGModuleCat.{v} A)).map (IsGorensteinProjective.{v} A).ι =
        (S.map (isGorensteinProjective (FGModuleCat.{v} A)).ι).map
          (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)) := rfl
    rw [hmap]
    exact hS.map_of_exact (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))

/-- `toFGModuleCat` preserves conflations and projective-injective objects. -/
theorem stableConflationExact_toFGModuleCat :
    StableConflationExact (exactStructure.{v} A)
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (toFGModuleCat.{v} A) :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := equivalenceFGModuleCat.{v} A)
    isConflationExact_toFGModuleCat isConflationExact_ofFGModuleCat

/-- `ofFGModuleCat` preserves conflations and projective-injective objects. -/
theorem stableConflationExact_ofFGModuleCat :
    StableConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (exactStructure.{v} A) (ofFGModuleCat.{v} A) :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (equivalenceFGModuleCat.{v} A).symm)
    isConflationExact_ofFGModuleCat isConflationExact_toFGModuleCat

variable (A)

/-- **Equivalence of stable categories of Gorenstein-projective modules** over a left Noetherian
ring, comparing the projective stable category of `GorensteinProjectiveModuleCat A` with that of
`CategoryTheory.GorensteinProjective (FGModuleCat A)`. -/
def stableEquivalenceFGModuleCat :
    (exactStructure.{v} A).ProjectiveStableCategory ≌
      (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (equivalenceFGModuleCat.{v} A)
    stableConflationExact_toFGModuleCat stableConflationExact_ofFGModuleCat
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

/-- The forward functor of `stableEquivalenceFGModuleCat` is the stable descent of
`toFGModuleCat`. -/
theorem stableEquivalenceFGModuleCat_functor :
    (stableEquivalenceFGModuleCat.{v} A).functor =
      stableConflationExact_toFGModuleCat.stableFunctor exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_functor (equivalenceFGModuleCat.{v} A)
    stableConflationExact_toFGModuleCat stableConflationExact_ofFGModuleCat
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

instance : (stableEquivalenceFGModuleCat.{v} A).functor.Additive := by
  rw [stableEquivalenceFGModuleCat_functor, StableConflationExact.stableFunctor_eq_map]
  infer_instance

/-- Along the stable quotient functors, `stableEquivalenceFGModuleCat` is induced by
`toFGModuleCat`. -/
theorem projectiveStableFunctor_comp_stableEquivalenceFGModuleCat_functor :
    (exactStructure.{v} A).projectiveStableFunctor ⋙
        (stableEquivalenceFGModuleCat.{v} A).functor =
      toFGModuleCat.{v} A ⋙
        (CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor := by
  rw [stableEquivalenceFGModuleCat_functor, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.quotientFunctor_comp_map]

/-- Compatibility of the forward functor of `stableEquivalenceFGModuleCat` with the integral
shifts generated by stable suspension. -/
@[instance_reducible]
def stableEquivalenceFGModuleCatFunctorCommShift :
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableEquivalenceFGModuleCat.{v} A).functor.CommShift ℤ :=
  StableConflationExact.stableEquivalenceFunctorCommShift
    stableConflationExact_toFGModuleCat stableConflationExact_ofFGModuleCat
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

/-- Compatibility of the inverse functor of `stableEquivalenceFGModuleCat` with the integral
shifts generated by stable suspension. -/
@[instance_reducible]
def stableEquivalenceFGModuleCatInverseCommShift :
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableEquivalenceFGModuleCat.{v} A).inverse.CommShift ℤ :=
  StableConflationExact.stableEquivalenceInverseCommShift
    stableConflationExact_toFGModuleCat stableConflationExact_ofFGModuleCat
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

/-- **The stable comparison equivalence is triangulated** for Happel's triangulations on
`GorensteinProjectiveModuleCat A` and `CategoryTheory.GorensteinProjective (FGModuleCat A)`. -/
theorem stableEquivalenceFGModuleCat_isTriangulated :
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableShiftFunctor_additive
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stablePretriangulated
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stablePretriangulated
    letI := stableEquivalenceFGModuleCatFunctorCommShift.{v} A
    letI := stableEquivalenceFGModuleCatInverseCommShift.{v} A
    letI := (stableEquivalenceFGModuleCat.{v} A).commShift_of_functor ℤ
    (stableEquivalenceFGModuleCat.{v} A).IsTriangulated :=
  StableConflationExact.stableEquivalenceIsTriangulated
    stableConflationExact_toFGModuleCat stableConflationExact_ofFGModuleCat
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

end Equivalence

section Singularity

variable (A : Type u) [Ring A] [IsNoetherianRing A] [Small.{v} A]
  [HasDerivedCategory.{w} (FGModuleCat.{v} A)]

/-- **Chen's functor** from the projective stable category of finitely generated
Gorenstein-projective `A`-modules to the singularity category `SingularityCategory (FGModuleCat A)`,
placing a module in degree zero. -/
def toSingularityCategory :
    (exactStructure.{v} A).ProjectiveStableCategory ⥤
      SingularityCategory (FGModuleCat.{v} A) :=
  (stableEquivalenceFGModuleCat.{v} A).functor ⋙
    CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)

/-- `toSingularityCategory` is the stable comparison equivalence followed by Chen's functor on
`FGModuleCat A`. -/
theorem toSingularityCategory_def :
    toSingularityCategory.{w, v} A =
      (stableEquivalenceFGModuleCat.{v} A).functor ⋙
        CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A) :=
  (rfl)

instance : (toSingularityCategory.{w, v} A).Additive := by
  unfold toSingularityCategory
  infer_instance

instance : (toSingularityCategory.{w, v} A).Full := by
  unfold toSingularityCategory
  infer_instance

instance : (toSingularityCategory.{w, v} A).Faithful := by
  unfold toSingularityCategory
  infer_instance

/-- **Chen's theorem** for `GorensteinProjectiveModuleCat`: the functor from the projective stable
category of finitely generated Gorenstein-projective `A`-modules to
`SingularityCategory (FGModuleCat A)` is fully faithful. -/
def fullyFaithfulToSingularityCategory :
    (toSingularityCategory.{w, v} A).FullyFaithful :=
  .ofFullyFaithful _

/-- Along the stable quotient functor, Chen's functor places the underlying finitely generated
module in degree zero in the singularity category. -/
theorem projectiveStableFunctor_comp_toSingularityCategory :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ toSingularityCategory.{w, v} A =
      (ObjectProperty.ιOfLE fun X hX ↦ (ModuleCat.isFG_iff X).2 hX.finite) ⋙
        DerivedCategory.Bounded.singleFunctor (FGModuleCat.{v} A) 0 ⋙
        SingularityCategory.Q (FGModuleCat.{v} A) := by
  rw [toSingularityCategory_def, ← Functor.assoc,
    projectiveStableFunctor_comp_stableEquivalenceFGModuleCat_functor, Functor.assoc,
    CategoryTheory.GorensteinProjective.projectiveStableFunctor_comp_toSingularityCategory]
  rfl

/-- Compatibility of `toSingularityCategory` with the integral shifts, obtained by composing the
shift compatibilities of `stableEquivalenceFGModuleCat` and Chen's functor on `FGModuleCat A`. -/
@[instance_reducible]
def toSingularityCategoryCommShift :
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
    (toSingularityCategory.{w, v} A).CommShift ℤ := by
  letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
  letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  letI := stableEquivalenceFGModuleCatFunctorCommShift.{v} A
  letI := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  unfold toSingularityCategory
  infer_instance

/-- **Chen's functor on `GorensteinProjectiveModuleCat` is a triangle functor** for Happel's
triangulation of the stable category and the Verdier-quotient triangulation of the singularity
category. -/
theorem toSingularityCategory_isTriangulated :
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableHasShift
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius.{v, u} (A := A)).stablePretriangulated
    letI := toSingularityCategoryCommShift.{w, v} A
    (toSingularityCategory.{w, v} A).IsTriangulated := by
  have hE := exactStructure_isFrobenius.{v, u} (A := A)
  have hE' := CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE'.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := stableEquivalenceFGModuleCatFunctorCommShift.{v} A
  let := stableEquivalenceFGModuleCatInverseCommShift.{v} A
  let := (stableEquivalenceFGModuleCat.{v} A).commShift_of_functor ℤ
  let := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  have := stableEquivalenceFGModuleCat_isTriangulated.{v} A
  have := CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated
    (C := FGModuleCat.{v} A)
  -- `toSingularityCategory` is the composite of two triangle functors, with the composite shift
  -- compatibility (`toSingularityCategoryCommShift`).
  exact inferInstanceAs
    (((stableEquivalenceFGModuleCat.{v} A).functor ⋙
      CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)).IsTriangulated)

end Singularity

end TauCeti.GorensteinProjectiveModuleCat
