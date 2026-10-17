/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.RingTheory.GradedAlgebra.Trivial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Opposite

/-!
# Ordinary modules as DG modules concentrated in degree zero

For an ordinary `R`-algebra `A`, viewed as a DG algebra with trivial grading and zero
differential, ordinary right `A`-modules are exactly the DG right modules concentrated in
degree zero. The functor `DGRightModuleCat.degreeZero` is fully faithful, and
`DGRightModuleCat.degreeZeroEquivalence` identifies its source with that full subcategory.
Concentration forces the differential to vanish, so no extra differential data survive in
this comparison.

Ordinary left `A`-modules give right modules over `Aᵐᵒᵖ` by restriction along
`(RingEquiv.opOp A).symm`. The equivalence `DGRightModuleCat.leftDegreeZeroEquivalence`
makes this handedness bridge explicit; the right action of `op a` is the original left
action of `a`. There is no Koszul correction in degree zero.

The constructions use Mathlib's scalar restriction and its equivalence for a ring
isomorphism, and Tau Ceti's existing trivial grading and concentration API.

## References

* B. Keller, *Deriving DG categories*, Sections 1--2, for right DG modules and ordinary
  algebras as DG algebras concentrated in degree zero.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGRightModuleCat

universe uR uA uM

variable (R : Type uR) (A : Type uA) [CommRing R] [Ring A] [Algebra R A]

/-- Include ordinary right modules among DG right modules by placing them in degree zero. -/
-- The object carrier must reduce to the scalar-restriction carrier in the pointwise API.
@[expose]
def degreeZero : ModuleCat.{uM} Aᵐᵒᵖ ⥤
    DGRightModuleCat.{uR, uA, uM} (isDGAlgebra_zero (trivialGrading R A)) where
  obj M := by
    letI := Module.restrictScalars R Aᵐᵒᵖ M
    letI := IsScalarTower.restrictScalars R Aᵐᵒᵖ M
    exact of (isDGRightModule_zero (𝒜 := trivialGrading R A) (trivialGrading R M))
  map {M N} f := by
    letI := Module.restrictScalars R Aᵐᵒᵖ M
    letI := Module.restrictScalars R Aᵐᵒᵖ N
    letI := IsScalarTower.restrictScalars R Aᵐᵒᵖ M
    letI := IsScalarTower.restrictScalars R Aᵐᵒᵖ N
    exact
      { toLinearMap := f.hom
        map_mem' := fun hx ↦ by
          rw [mem_trivialGrading_iff] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (map_zero _)
        map_d' := fun _ ↦ (map_zero f.hom).symm }
  map_id M := hom_ext fun x ↦ by rw [id_apply]; rfl
  map_comp f g := hom_ext fun x ↦ by rw [comp_apply]; rfl

/-- The grading of an included ordinary module is the trivial grading. -/
@[simp]
theorem degreeZero_obj_grading (M : ModuleCat.{uM} Aᵐᵒᵖ) :
    ((degreeZero R A).obj M).grading =
      trivialGrading R ((degreeZero R A).obj M) := (rfl)

/-- The differential of an included ordinary module is zero. -/
@[simp]
theorem degreeZero_obj_differential (M : ModuleCat.{uM} Aᵐᵒᵖ) :
    ((degreeZero R A).obj M).differential = 0 := (rfl)

/-- Including a module homomorphism keeps its values. -/
@[simp]
theorem degreeZero_map_apply {M N : ModuleCat.{uM} Aᵐᵒᵖ} (f : M ⟶ N)
    (x : (degreeZero R A).obj M) : (degreeZero R A).map f x = f.hom x := (rfl)

/-- Every included ordinary module is concentrated in degree zero. -/
theorem isConcentratedInDegreeZero_degreeZero_obj (M : ModuleCat.{uM} Aᵐᵒᵖ) :
    ((degreeZero R A).obj M).IsConcentratedInDegreeZero :=
  isConcentratedInDegreeZero_iff.2 fun _ hq ↦
    trivialGrading_eq_bot R ((degreeZero R A).obj M) hq

/-- A DG map between modules in the image is exactly an ordinary right-module map. -/
def fullyFaithfulDegreeZero : (degreeZero.{uR, uA, uM} R A).FullyFaithful where
  preimage f := ModuleCat.ofHom f.toLinearMap
  map_preimage _f := hom_ext fun _ ↦ rfl
  preimage_map _f := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

instance : (degreeZero.{uR, uA, uM} R A).Full := (fullyFaithfulDegreeZero R A).full

instance : (degreeZero.{uR, uA, uM} R A).Faithful := (fullyFaithfulDegreeZero R A).faithful

instance : (degreeZero.{uR, uA, uM} R A).Additive where
  map_add := hom_ext fun _ ↦ by simp only [degreeZero_map_apply, add_apply]; rfl

/-- Forgetting an included module recovers the original ordinary module, naturally. -/
def degreeZeroCompForgetIso : degreeZero.{uR, uA, uM} R A ⋙ forgetToRightModuleCat ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ LinearEquiv.toModuleIso (LinearEquiv.refl _ _))
    (fun f ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ degreeZero_map_apply R A f x))

/-- The comparison after forgetting acts identically on elements. -/
@[simp]
theorem degreeZeroCompForgetIso_hom_app_apply (M : ModuleCat.{uM} Aᵐᵒᵖ)
    (x : (degreeZero R A).obj M) :
    ModuleCat.Hom.hom (A := forgetToRightModuleCat.obj ((degreeZero R A).obj M))
      (B := M) ((degreeZeroCompForgetIso R A).hom.app M) x = x := (rfl)

/-- The inverse comparison after forgetting also acts identically on elements. -/
@[simp]
theorem degreeZeroCompForgetIso_inv_app_apply (M : ModuleCat.{uM} Aᵐᵒᵖ) (x : M) :
    ModuleCat.Hom.hom (A := M)
      (B := forgetToRightModuleCat.obj ((degreeZero R A).obj M))
      ((degreeZeroCompForgetIso R A).inv.app M) x = x := (rfl)

variable {R A}

/-- Replacing a DG module concentrated in degree zero by the included underlying ordinary
module preserves both its grading and its differential. -/
def degreeZeroIso (M : DGRightModuleCat.{uR, uA, uM}
    (isDGAlgebra_zero (trivialGrading R A))) (hM : M.IsConcentratedInDegreeZero) :
    (degreeZero R A).obj (forgetToRightModuleCat.obj M) ≅ M :=
  isoMk (LinearEquiv.refl Aᵐᵒᵖ M)
    (fun q x ↦ by
      rw [degreeZero_obj_grading, mem_trivialGrading_iff, hM.mem_grading_iff]
      rfl)
    (fun x ↦ by rw [hM.differential_eq_zero]; rfl)

/-- The comparison with the degree-zero model keeps the values of elements. -/
@[simp]
theorem degreeZeroIso_hom_apply (M : DGRightModuleCat.{uR, uA, uM}
    (isDGAlgebra_zero (trivialGrading R A))) (hM : M.IsConcentratedInDegreeZero)
    (x : (degreeZero R A).obj (forgetToRightModuleCat.obj M)) :
    (degreeZeroIso M hM).hom x = (x : M) := by
  unfold degreeZeroIso
  exact isoMk_hom_apply _ _ _ x

/-- The inverse comparison also keeps the values of elements. -/
@[simp]
theorem degreeZeroIso_inv_apply (M : DGRightModuleCat.{uR, uA, uM}
    (isDGAlgebra_zero (trivialGrading R A))) (hM : M.IsConcentratedInDegreeZero) (x : M) :
    (degreeZeroIso M hM).inv x = x := by
  unfold degreeZeroIso
  exact isoMk_inv_apply _ _ _ x

variable (R A)

/-- The essential image of ordinary right modules consists exactly of the DG modules
concentrated in degree zero. -/
@[simp]
theorem essImage_degreeZero_iff (M : DGRightModuleCat.{uR, uA, uM}
    (isDGAlgebra_zero (trivialGrading R A))) :
    (degreeZero R A).essImage M ↔ M.IsConcentratedInDegreeZero := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩
    exact (isConcentratedInDegreeZero_degreeZero_obj R A N).of_iso e
  · intro hM
    exact ⟨forgetToRightModuleCat.obj M, ⟨degreeZeroIso M hM⟩⟩

/-- The degree-zero inclusion with codomain restricted to concentrated DG modules. -/
abbrev degreeZeroToConcentrated : ModuleCat.{uM} Aᵐᵒᵖ ⥤
    ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R A))) :=
  ObjectProperty.lift _ (degreeZero R A) (isConcentratedInDegreeZero_degreeZero_obj R A)

instance : (degreeZeroToConcentrated.{uR, uA, uM} R A).EssSurj where
  mem_essImage M :=
    ⟨forgetToRightModuleCat.obj M.obj,
      ⟨ObjectProperty.isoMk _ (degreeZeroIso M.obj M.property)⟩⟩

instance : (degreeZeroToConcentrated.{uR, uA, uM} R A).IsEquivalence where

/-- Ordinary right modules are equivalent to DG right modules concentrated in degree zero. -/
def degreeZeroEquivalence : ModuleCat.{uM} Aᵐᵒᵖ ≌
    ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R A))) :=
  (degreeZeroToConcentrated R A).asEquivalence

/-- The forward functor of the equivalence is the degree-zero inclusion. -/
@[simp]
theorem degreeZeroEquivalence_functor :
    (degreeZeroEquivalence.{uR, uA, uM} R A).functor = degreeZeroToConcentrated R A := (rfl)

/-- An ordinary left module as a right DG module over the opposite algebra in degree zero. -/
-- The forward functor exposes its carrier and opposite action for the pointwise API.
@[expose]
def leftDegreeZero : ModuleCat.{uM} A ⥤
    ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R Aᵐᵒᵖ))) :=
  ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom ⋙ degreeZeroToConcentrated R Aᵐᵒᵖ

/-- Ordinary left modules are equivalent to right DG modules over the opposite algebra
concentrated in degree zero. -/
def leftDegreeZeroEquivalence : ModuleCat.{uM} A ≌
    ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R Aᵐᵒᵖ))) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm).trans
    (degreeZeroEquivalence R Aᵐᵒᵖ)

/-- The forward functor of the left-module equivalence is the explicit opposite-action bridge. -/
@[simp]
theorem leftDegreeZeroEquivalence_functor :
    (leftDegreeZeroEquivalence.{uR, uA, uM} R A).functor = leftDegreeZero R A := (rfl)

/-- In the left-to-right comparison, right multiplication by `op a` is the original left
action of `a`. -/
@[simp]
theorem leftDegreeZero_obj_op_smul (M : ModuleCat.{uM} A) (a : A)
    (x : ((leftDegreeZero R A).obj M).obj) :
    op (op a) • x = @SMul.smul A M inferInstance a x := (rfl)

/-- The left-to-right bridge keeps the values of an ordinary module homomorphism. -/
@[simp]
theorem leftDegreeZero_map_apply {M N : ModuleCat.{uM} A} (f : M ⟶ N)
    (x : ((leftDegreeZero R A).obj M).obj) :
    ((leftDegreeZero R A).map f).hom x = f.hom x := (rfl)

end TauCeti.DGRightModuleCat
