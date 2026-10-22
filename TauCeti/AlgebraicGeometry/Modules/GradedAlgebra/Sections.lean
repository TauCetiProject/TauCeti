/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GradedObject.MonObj
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.GradedRing
public import TauCeti.RingTheory.GradedAlgebra.DirectSum
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Graded rings of sections of graded algebras

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X` and let `U` be an open of `X`.
The sections `Γ(Aₙ, U)` of the homogeneous components carry a native graded multiplication
`Γ(Aᵢ, U) × Γ(Aⱼ, U) → Γ(Aᵢ₊ⱼ, U)`: the homogeneous multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` applied to
the image of `x ⊗ₜ y` in the sections of the tensor product. Together with the unit
`Γ(X, U) → Γ(A₀, U)` this makes the family `n ↦ Γ(Aₙ, U)` a graded commutative `Γ(X, U)`-algebra,
so that `⨁ n, Γ(Aₙ, U)` is a commutative `Γ(X, U)`-algebra graded by its summands. Over an affine
open this is the graded ring whose homogeneous pieces are the modules corresponding to the `Aₙ`
when they are quasicoherent; it is the input of affine-local constructions with graded algebras,
such as their relative spectra and relative `Proj`.

The graded laws are obtained by transporting the homogeneous laws of `A` along the lax braided
sections functor `Scheme.Modules.sectionsFunctor U`
(`CategoryTheory.GradedObject.mul_assoc_of_laxMonoidal` and its companions), and the graded ring
is then assembled by `TauCeti.ModuleCat.gCommRingOfHomogeneous`.

This is the graded analogue of the ungraded construction of
`TauCeti/AlgebraicGeometry/Modules/Algebra/Sections.lean`, whose
`CategoryTheory.CommMon.commRingSections`, `CategoryTheory.CommMon.restrictSections` and
`CategoryTheory.CommMon.toSectionsPresheaf` give the sections of a commutative `𝒪_X`-algebra
their ring structure, restriction maps and structure morphism; the restriction and naturality
arguments here follow the proofs there.

## Main declarations

* `CategoryTheory.CommMon.gCommRingSections` and
  `CategoryTheory.CommMon.gAlgebraSections`: the graded
  commutative `Γ(X, U)`-algebra structure on `n ↦ Γ(Aₙ, U)`, characterized by
  `sections_gMul_def`, `sections_gOne_def` and `gAlgebraSections_toFun`;
* `CategoryTheory.CommMon.gradedSectionsGrading`: the grading of `⨁ n, Γ(Aₙ, U)` by its
  summands, as an internally graded algebra in the sense of `GradedAlgebra`;
* `CategoryTheory.CommMon.restrictGradedSections`: restriction of
  sections along `V ≤ U`, a degree-preserving ring homomorphism, assembled into the presheaf of
  commutative rings `gradedSectionsPresheaf` under the structure presheaf of `X`
  (`toGradedSectionsPresheaf`); its graded form is
  `CategoryTheory.CommMon.restrictGradedSectionsGradedHom`;
* `CategoryTheory.CommMon.gradedSectionsMap`: the degree-preserving
  `Γ(X, U)`-algebra homomorphism induced by a morphism of graded algebras, natural in `U`
  (`gradedSectionsPresheafMap`).
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti

open CategoryTheory.CommMon
open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) (U : X.Opens)

/-- The unit of `A` on sections over `U`, as a morphism of `Γ(X, U)`-modules. -/
private abbrev sectionsOne :
    𝟙_ (ModuleCat.{u} Γ(X, U)) ⟶ (Scheme.Modules.sectionsFunctor U).obj (A.X 0) :=
  Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) ≫
    (Scheme.Modules.sectionsFunctor U).map A.toMon.one

/-- The homogeneous multiplication of `A` on sections over `U`, as a morphism of
`Γ(X, U)`-modules out of the tensor product of the modules of sections. -/
private abbrev sectionsMul (i j : ℕ) :
    (Scheme.Modules.sectionsFunctor U).obj (A.X i) ⊗
        (Scheme.Modules.sectionsFunctor U).obj (A.X j) ⟶
      (Scheme.Modules.sectionsFunctor U).obj (A.X (i + j)) :=
  Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ ≫
    (Scheme.Modules.sectionsFunctor U).map (A.toMon.mul i j)

private lemma sectionsMul_eq (i j : ℕ) :
    sectionsMul A U i j =
      ((Iso.refl _).hom ⊗ₘ (Iso.refl _).hom) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) (A.X i) (A.X j) ≫
          (Scheme.Modules.sectionsFunctor U).map (A.toMon.mul i j) ≫ (Iso.refl _).inv := by
  rw [Iso.refl_hom, Iso.refl_hom, Iso.refl_inv, id_tensorHom_id, Category.id_comp,
    Category.comp_id]
  rfl

private lemma sectionsOne_eq :
    sectionsOne A U =
      Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) ≫
        (Scheme.Modules.sectionsFunctor U).map A.toMon.one ≫ (Iso.refl _).inv := by
  rw [Iso.refl_inv, Category.comp_id]
  rfl

/-- The sections over `U` of the homogeneous components of a graded algebra form a
graded commutative ring. The product of `x : Γ(Aᵢ, U)` and `y : Γ(Aⱼ, U)` is the homogeneous
multiplication of `A` applied to the image of `x ⊗ₜ y` in the sections of `Aᵢ ⊗ Aⱼ`
(`sections_gMul_def`). -/
@[instance_reducible, instance]
def _root_.CategoryTheory.CommMon.gCommRingSections :
    DirectSum.GCommRing (fun n ↦ Γ(A.X n, U)) :=
  TauCeti.ModuleCat.gCommRingOfHomogeneous
    (fun n ↦ (Scheme.Modules.sectionsFunctor U).obj (A.X n)) (sectionsOne A U)
    (sectionsMul A U)
    (GradedObject.one_mul_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.toMon.one_mul)
    (GradedObject.mul_one_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.toMon.mul_one)
    (GradedObject.mul_assoc_of_laxMonoidal _ _ (sectionsMul_eq A U) A.toMon.mul_assoc)
    (GradedObject.mul_comm_of_laxBraided _ _ (sectionsMul_eq A U) A.mul_comm)

/-- The sections over `U` of the homogeneous components of a graded algebra form a
graded `Γ(X, U)`-algebra, whose structure map `Γ(X, U) → Γ(A₀, U)` is the unit of `A`
(`gAlgebraSections_toFun`). -/
@[instance_reducible, instance]
def _root_.CategoryTheory.CommMon.gAlgebraSections :
    DirectSum.GAlgebra Γ(X, U) (fun n ↦ Γ(A.X n, U)) :=
  TauCeti.ModuleCat.gAlgebraOfHomogeneous
    (fun n ↦ (Scheme.Modules.sectionsFunctor U).obj (A.X n)) (sectionsOne A U)
    (sectionsMul A U)
    (GradedObject.one_mul_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.toMon.one_mul)
    (GradedObject.mul_one_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.toMon.mul_one)
    (GradedObject.mul_assoc_of_laxMonoidal _ _ (sectionsMul_eq A U) A.toMon.mul_assoc)

/-- The product of homogeneous sections `x : Γ(Aᵢ, U)` and `y : Γ(Aⱼ, U)` is the homogeneous
multiplication of `A` applied to the image of `x ⊗ₜ y` under the tensor map of the sections
functor. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sections_gMul_def {i j : ℕ}
    (x : Γ(A.X i, U)) (y : Γ(A.X j, U)) :
    GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, U)) x y =
      (A.toMon.mul i j).app U
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)) :=
  (rfl)

/-- The unit of the graded ring of sections is the unit of `A` applied to `1 : Γ(X, U)`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sections_gOne_def :
    GradedMonoid.GOne.one (A := fun n ↦ Γ(A.X n, U)) =
      A.toMon.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1) :=
  (rfl)

/-- The structure map `Γ(X, U) → Γ(A₀, U)` of the graded algebra of sections is the unit of
`A` on sections over `U`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gAlgebraSections_toFun (r : Γ(X, U)) :
    GAlgebra.toFun (R := Γ(X, U)) (A := fun n ↦ Γ(A.X n, U)) r =
      A.toMon.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) :=
  (rfl)

section Restriction

variable {U} {V : X.Opens} (f : V ⟶ U)

/-- Restriction of sections along `V ≤ U` preserves the homogeneous multiplication. -/
private lemma map_gMul_sections {i j : ℕ} (x : Γ(A.X i, U)) (y : Γ(A.X j, U)) :
    (A.X (i + j)).presheaf.map f.op
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, V))
        ((A.X i).presheaf.map f.op x) ((A.X j).presheaf.map f.op y) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The product is the multiplication of `A` applied to the tensor map of `F`; both commute
  -- with restriction, and restriction of the sectionwise tensor product sends `x ⊗ₜ y` to the
  -- pure tensor of the restrictions.
  have h₁ := PresheafOfModules.naturality_apply (A.toMon.mul i j).val f.op
    ((Functor.LaxMonoidal.μ F (A.X i) (A.X j)).app' (op U) (x ⊗ₜ y))
  have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.μ F (A.X i) (A.X j))
    f.op (x ⊗ₜ y)
  exact h₁.symm.trans (congrArg _ h₂.symm)

/-- Restriction of sections along `V ≤ U` commutes with the structure maps
`Γ(X, U) → Γ(A₀, U)`. -/
private lemma map_gAlgebraSections_toFun (r : Γ(X, U)) :
    (A.X 0).presheaf.map f.op
        (GAlgebra.toFun (R := Γ(X, U)) (A := fun n ↦ Γ(A.X n, U)) r) =
      GAlgebra.toFun (R := Γ(X, V)) (A := fun n ↦ Γ(A.X n, V)) (X.presheaf.map f.op r) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The structure map is the unit of `A` after the unit map of `F`; both commute with
  -- restriction.
  have h₁ := PresheafOfModules.naturality_apply A.toMon.one.val f.op
    ((Functor.LaxMonoidal.ε F).app' (op U) r)
  have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) f.op r
  exact h₁.symm.trans (congrArg _ h₂.symm)

/-- Restriction of sections along `V ≤ U` preserves the unit. -/
private lemma map_gOne_sections :
    (A.X 0).presheaf.map f.op (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(A.X n, V)) :=
  (map_gAlgebraSections_toFun A f 1).trans (congrArg _ (map_one (X.presheaf.map f.op).hom))

/-- Restriction of sections along an inclusion of opens `V ≤ U`, as a ring homomorphism between
the graded rings of sections. It sends each homogeneous section to its restriction, in the same
degree (`restrictGradedSections_of`). -/
def _root_.CategoryTheory.CommMon.restrictGradedSections :
    (⨁ n, Γ(A.X n, U)) →+* ⨁ n, Γ(A.X n, V) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(A.X n, V)) n).comp ((A.X n).presheaf.map f.op).hom)
    ((congrArg _ (map_gOne_sections A f)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (map_gMul_sections A f x y)).trans (DirectSum.of_mul_of _ _).symm)

/-- Restriction of a homogeneous section is the restriction of the section, in the same
degree. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.restrictGradedSections_of (n : ℕ) (x : Γ(A.X n, U)) :
    A.restrictGradedSections f (DirectSum.of _ n x) =
      DirectSum.of _ n ((A.X n).presheaf.map f.op x) :=
  DirectSum.toSemiring_of _ _ _ _ _

variable (U) in
/-- Restriction of sections along the identity of an open is the identity. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.restrictGradedSections_id :
    A.restrictGradedSections (𝟙 U) = RingHom.id _ :=
  DirectSum.ringHom_ext fun n x ↦ by simp

/-- Restriction of sections along a composite of inclusions of opens is the composite of the
restrictions. -/
lemma _root_.CategoryTheory.CommMon.restrictGradedSections_comp {W : X.Opens} (g : W ⟶ V) :
    A.restrictGradedSections (g ≫ f) =
      (A.restrictGradedSections g).comp (A.restrictGradedSections f) :=
  DirectSum.ringHom_ext fun n x ↦ by simp

/-- Restriction of sections restricts each homogeneous component. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.restrictGradedSections_apply (x : ⨁ n, Γ(A.X n, U))
    (n : ℕ) :
    A.restrictGradedSections f x n = (A.X n).presheaf.map f.op (x n) := by
  have h : (A.restrictGradedSections f).toAddMonoidHom =
      DirectSum.map fun n ↦ ((A.X n).presheaf.map f.op).hom :=
    DirectSum.addHom_ext fun n y ↦ by simp
  exact congrArg (· n) (DFunLike.congr_fun h x)

/-- Restriction of sections commutes with the structure maps `Γ(X, U) → ⨁ n, Γ(Aₙ, U)`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.restrictGradedSections_algebraMap (r : Γ(X, U)) :
    A.restrictGradedSections f (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) =
      algebraMap Γ(X, V) (⨁ n, Γ(A.X n, V)) (X.presheaf.map f.op r) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, restrictGradedSections_of,
    map_gAlgebraSections_toFun]

end Restriction

/-- The grading of the ring `⨁ n, Γ(Aₙ, U)` of sections of a graded algebra by its summands
`Γ(Aₙ, U)`. -/
abbrev _root_.CategoryTheory.CommMon.gradedSectionsGrading :
    ℕ → Submodule Γ(X, U) (⨁ n, Γ(A.X n, U)) :=
  DirectSum.summand Γ(X, U) fun n ↦ Γ(A.X n, U)

section GradedRestriction

variable {A U} in
/-- A homogeneous section of degree `n` lies in the degree-`n` summand. -/
theorem _root_.CategoryTheory.CommMon.of_mem_gradedSectionsGrading (n : ℕ) (x : Γ(A.X n, U)) :
    DirectSum.of _ n x ∈ A.gradedSectionsGrading U n :=
  DirectSum.of_mem_summand (R := Γ(X, U)) (M := fun n ↦ Γ(A.X n, U)) n x

variable {U} {V : X.Opens}

/-- Restriction of sections along an inclusion of opens `V ≤ U`, as a graded ring homomorphism
between the graded rings of sections. Its underlying ring homomorphism is
`CategoryTheory.CommMon.restrictGradedSections`
(`CategoryTheory.CommMon.restrictGradedSectionsGradedHom_toRingHom`). -/
def _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom (i : V ⟶ U) :
    A.gradedSectionsGrading U →+*ᵍ A.gradedSectionsGrading V where
  __ := A.restrictGradedSections i
  map_mem {n x} hx := by
    obtain ⟨x, rfl⟩ := DirectSum.mem_summand.mp hx
    simpa using of_mem_gradedSectionsGrading n _

/-- The underlying ring homomorphism of the graded restriction of sections is the restriction of
sections. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_toRingHom (i : V ⟶ U) :
    (A.restrictGradedSectionsGradedHom i).toRingHom = A.restrictGradedSections i :=
  (rfl)

/-- The graded restriction of sections is the restriction of sections. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_apply (i : V ⟶ U)
    (x : ⨁ n, Γ(A.X n, U)) :
    A.restrictGradedSectionsGradedHom i x = A.restrictGradedSections i x :=
  (rfl)

variable (U) in
/-- Graded restriction of sections along the identity is the identity. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_id :
    A.restrictGradedSectionsGradedHom (𝟙 U) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x ↦ by simp

/-- Graded restriction of sections along a composite of inclusions is the composite of the graded
restrictions. -/
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_comp {W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) :
    A.restrictGradedSectionsGradedHom (j ≫ i) =
      (A.restrictGradedSectionsGradedHom j).comp (A.restrictGradedSectionsGradedHom i) :=
  GradedRingHom.ext fun x ↦ by simp [restrictGradedSections_comp]

end GradedRestriction

/-- The presheaf of graded rings of sections of a graded algebra: it sends an open
`U` to `⨁ n, Γ(Aₙ, U)` and an inclusion of opens to `restrictGradedSections`. -/
@[expose]
def _root_.CategoryTheory.CommMon.gradedSectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (⨁ n, Γ(A.X n, U.unop))
  map f := CommRingCat.ofHom (A.restrictGradedSections f.unop)
  map_id U := by
    rw [unop_id, restrictGradedSections_id]
    rfl
  map_comp f g := by
    rw [unop_comp, restrictGradedSections_comp]
    rfl

/-- The graded ring of sections over `U` is the value of `gradedSectionsPresheaf` at `U`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    A.gradedSectionsPresheaf.obj U = CommRingCat.of (⨁ n, Γ(A.X n, U.unop)) :=
  (rfl)

/-- The restriction maps of `gradedSectionsPresheaf` are `restrictGradedSections`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsPresheaf_map {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    A.gradedSectionsPresheaf.map f = CommRingCat.ofHom (A.restrictGradedSections f.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X` to the presheaf of graded rings of
sections, given on each open `U` by the algebra map `Γ(X, U) → ⨁ n, Γ(Aₙ, U)` into degree
zero. -/
def _root_.CategoryTheory.CommMon.toGradedSectionsPresheaf :
    X.presheaf ⟶ A.gradedSectionsPresheaf where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (⨁ n, Γ(A.X n, U.unop)))
  naturality _ _ f := by
    ext r
    exact (A.restrictGradedSections_algebraMap f.unop r).symm

/-- The structure morphism `toGradedSectionsPresheaf` is the algebra map on each open. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.toGradedSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    A.toGradedSectionsPresheaf.app U =
      CommRingCat.ofHom (algebraMap Γ(X, U.unop) (⨁ n, Γ(A.X n, U.unop))) :=
  (rfl)

section Map

variable {A} {B C : CommMon (GradedObject ℕ X.Modules)}

omit U in
/-- A morphism of graded algebras is multiplicative on sections. -/
private lemma app_gMul_sections (φ : A ⟶ B) (U : X.Opens) {i j : ℕ} (x : Γ(A.X i, U))
    (y : Γ(A.X j, U)) :
    (φ.hom.hom (i + j)).app U (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(B.X n, U))
        ((φ.hom.hom i).app U x) ((φ.hom.hom j).app U y) :=
  congr($(ModuleCat.hom_ext_iff.mp (GradedObject.map_mul_of_laxMonoidal _ _ (sectionsMul_eq A U)
    _ _ (sectionsMul_eq B U) _ (fun n ↦ (Scheme.Modules.sectionsFunctor U).map
      (φ.hom.hom n)) (fun n ↦ by rw [Iso.refl_hom, Iso.refl_inv, Category.id_comp,
        Category.comp_id]) (Mon.map_mul φ.hom) i j)) (x ⊗ₜ y)).symm

omit U in
/-- A morphism of graded algebras preserves the unit on sections. -/
private lemma app_gOne_sections (φ : A ⟶ B) (U : X.Opens) :
    (φ.hom.hom 0).app U (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(B.X n, U)) :=
  congr($(ModuleCat.hom_ext_iff.mp
    ((Scheme.Modules.sectionsFunctor U).congr_map (Mon.one_map φ.hom)))
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1))

omit U in
/-- The `Γ(X, U)`-algebra homomorphism between graded rings of sections induced by a morphism of
graded algebras. It applies the morphism degree by degree
(`gradedSectionsMap_of`). -/
def _root_.CategoryTheory.CommMon.gradedSectionsMap (φ : A ⟶ B) (U : X.Opens) :
    (⨁ n, Γ(A.X n, U)) →ₐ[Γ(X, U)] ⨁ n, Γ(B.X n, U) :=
  DirectSum.toAlgebra _ _
    (fun n ↦ (DirectSum.lof Γ(X, U) ℕ (fun n ↦ Γ(B.X n, U)) n).comp
      ((Scheme.Modules.sectionsFunctor U).map (φ.hom.hom n)).hom)
    ((congrArg _ (app_gOne_sections φ U)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (app_gMul_sections φ U x y)).trans (DirectSum.of_mul_of _ _).symm)

omit U in
/-- The map induced on graded rings of sections applies the morphism to each homogeneous
section. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsMap_of
    (φ : A ⟶ B) (U : X.Opens) (n : ℕ) (x : Γ(A.X n, U)) :
    gradedSectionsMap φ U (DirectSum.of _ n x) =
      DirectSum.of _ n ((φ.hom.hom n).app U x) :=
  (DirectSum.toAlgebra_apply _ _ _ _ _ _).trans (DirectSum.toSemiring_of _ _ _ _ _)

omit U in
/-- The identity morphism induces the identity on graded rings of sections. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsMap_id (U : X.Opens) :
    gradedSectionsMap (𝟙 A) U = AlgHom.id _ _ :=
  DirectSum.algHom_ext _ _ fun n x ↦ gradedSectionsMap_of (𝟙 A) U n x

omit U in
/-- The map induced on graded rings of sections by a composite is the composite of the induced
maps. -/
lemma _root_.CategoryTheory.CommMon.gradedSectionsMap_comp
    (φ : A ⟶ B) (ψ : B ⟶ C) (U : X.Opens) :
    gradedSectionsMap (φ ≫ ψ) U = (gradedSectionsMap ψ U).comp (gradedSectionsMap φ U) :=
  DirectSum.algHom_ext _ _ fun n x ↦ (gradedSectionsMap_of (φ ≫ ψ) U n x).trans
    ((congrArg (gradedSectionsMap ψ U) (gradedSectionsMap_of φ U n x)).trans
      (gradedSectionsMap_of ψ U n _)).symm

omit U in
/-- The maps induced on graded rings of sections commute with restriction. -/
lemma _root_.CategoryTheory.CommMon.gradedSectionsMap_restrictGradedSections
    (φ : A ⟶ B) {U V : X.Opens} (f : V ⟶ U)
    (x : ⨁ n, Γ(A.X n, U)) :
    gradedSectionsMap φ V (A.restrictGradedSections f x) =
      B.restrictGradedSections f (gradedSectionsMap φ U x) := by
  refine DFunLike.congr_fun (DirectSum.ringHom_ext (f := (gradedSectionsMap φ V).toRingHom.comp
    (A.restrictGradedSections f)) (g := (B.restrictGradedSections f).comp
      (gradedSectionsMap φ U).toRingHom) fun n y ↦ ?_) x
  calc gradedSectionsMap φ V (A.restrictGradedSections f (DirectSum.of _ n y))
      = DirectSum.of _ n ((φ.hom.hom n).app V ((A.X n).presheaf.map f.op y)) :=
        (congrArg _ (A.restrictGradedSections_of f n y)).trans (gradedSectionsMap_of φ V n _)
    _ = DirectSum.of _ n ((B.X n).presheaf.map f.op ((φ.hom.hom n).app U y)) :=
        congrArg _ (PresheafOfModules.naturality_apply (φ.hom.hom n).val f.op y)
    _ = B.restrictGradedSections f (gradedSectionsMap φ U (DirectSum.of _ n y)) :=
        ((congrArg _ (gradedSectionsMap_of φ U n y)).trans
          (B.restrictGradedSections_of f n _)).symm

omit U in
/-- The morphism of presheaves of graded rings of sections induced by a morphism of graded
algebras: on each open `U` it is `gradedSectionsMap`. -/
def _root_.CategoryTheory.CommMon.gradedSectionsPresheafMap (φ : A ⟶ B) :
    A.gradedSectionsPresheaf ⟶ B.gradedSectionsPresheaf where
  app U := CommRingCat.ofHom (gradedSectionsMap φ U.unop).toRingHom
  naturality _ _ f := by
    ext x
    exact gradedSectionsMap_restrictGradedSections φ f.unop x

omit U in
/-- The components of `gradedSectionsPresheafMap φ` are the maps `gradedSectionsMap φ`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsPresheafMap_app
    (φ : A ⟶ B) (U : X.Opensᵒᵖ) :
    (gradedSectionsPresheafMap φ).app U =
      CommRingCat.ofHom (gradedSectionsMap φ U.unop).toRingHom :=
  (rfl)

omit U in
/-- The identity morphism induces the identity of the presheaf of graded rings of sections. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.gradedSectionsPresheafMap_id :
    gradedSectionsPresheafMap (𝟙 A) = 𝟙 _ := by
  ext U x
  exact DFunLike.congr_fun (gradedSectionsMap_id U.unop) x

omit U in
/-- The morphism of presheaves induced by a composite is the composite of the induced
morphisms. -/
lemma _root_.CategoryTheory.CommMon.gradedSectionsPresheafMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) :
    gradedSectionsPresheafMap (φ ≫ ψ) =
      gradedSectionsPresheafMap φ ≫ gradedSectionsPresheafMap ψ := by
  ext U x
  exact DFunLike.congr_fun (gradedSectionsMap_comp φ ψ U.unop) x

omit U in
/-- The morphism of presheaves induced by a morphism of graded algebras is
compatible with the structure morphisms from the structure presheaf. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.toGradedSectionsPresheaf_gradedSectionsPresheafMap
    (φ : A ⟶ B) :
    A.toGradedSectionsPresheaf ≫ gradedSectionsPresheafMap φ = B.toGradedSectionsPresheaf := by
  ext U r
  exact (gradedSectionsMap φ U).commutes r

end Map

end

end TauCeti
