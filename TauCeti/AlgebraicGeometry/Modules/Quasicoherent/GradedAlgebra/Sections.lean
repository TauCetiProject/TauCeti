/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.GradedRing

/-!
# Graded rings of sections of graded quasicoherent algebras

Let `A = ⨁ₙ Aₙ` be a graded quasicoherent algebra on a scheme `X` and let `U` be an open of `X`.
The sections `Γ(Aₙ, U)` of the homogeneous components carry a native graded multiplication
`Γ(Aᵢ, U) × Γ(Aⱼ, U) → Γ(Aᵢ₊ⱼ, U)`: the homogeneous multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` applied to
the image of `x ⊗ₜ y` in the sections of the tensor product. Together with the unit
`Γ(X, U) → Γ(A₀, U)` this makes the family `n ↦ Γ(Aₙ, U)` a graded commutative `Γ(X, U)`-algebra,
so that `⨁ n, Γ(Aₙ, U)` is a commutative `Γ(X, U)`-algebra graded by its summands. Over an affine
open this is the graded ring whose homogeneous pieces are the modules corresponding to the `Aₙ`;
it is the input of affine-local constructions with graded quasicoherent algebras, such as their
relative spectra and relative `Proj`.

The graded laws are obtained by transporting the homogeneous laws of `A` along the lax braided
sections functor `Scheme.Modules.sectionsFunctor U`
(`CategoryTheory.GradedObject.mul_assoc_of_laxMonoidal` and its companions), and the graded ring
is then assembled by `TauCeti.ModuleCat.gCommRingOfHomogeneous`.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gCommRingSections` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gAlgebraSections`: the graded
  commutative `Γ(X, U)`-algebra structure on `n ↦ Γ(Aₙ, U)`, characterized by
  `gMul_sections_def`, `gOne_sections_def` and `gAlgebraSections_toFun`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.restrictGradedSections`: restriction of
  sections along `V ≤ U`, a degree-preserving ring homomorphism, assembled into the presheaf of
  commutative rings `gradedSectionsPresheaf`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gradedSectionsMap`: the degree-preserving
  `Γ(X, U)`-algebra homomorphism induced by a morphism of graded quasicoherent algebras.
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : GradedQuasicoherentAlgebra X) (U : X.Opens)

/-- The unit of `A` on sections over `U`, as a morphism of `Γ(X, U)`-modules. -/
private abbrev sectionsOne :
    𝟙_ (ModuleCat.{u} Γ(X, U)) ⟶ (Scheme.Modules.sectionsFunctor U).obj (A.obj.X 0) :=
  Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) ≫
    (Scheme.Modules.sectionsFunctor U).map A.one

/-- The homogeneous multiplication of `A` on sections over `U`, as a morphism of
`Γ(X, U)`-modules out of the tensor product of the modules of sections. -/
private abbrev sectionsMul (i j : ℕ) :
    (Scheme.Modules.sectionsFunctor U).obj (A.obj.X i) ⊗
        (Scheme.Modules.sectionsFunctor U).obj (A.obj.X j) ⟶
      (Scheme.Modules.sectionsFunctor U).obj (A.obj.X (i + j)) :=
  Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ ≫
    (Scheme.Modules.sectionsFunctor U).map (A.mul i j)

private lemma sectionsMul_eq (i j : ℕ) :
    sectionsMul A U i j =
      ((Iso.refl _).hom ⊗ₘ (Iso.refl _).hom) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) (A.obj.X i) (A.obj.X j) ≫
          (Scheme.Modules.sectionsFunctor U).map (A.mul i j) ≫ (Iso.refl _).inv := by
  rw [Iso.refl_hom, Iso.refl_hom, Iso.refl_inv, id_tensorHom_id, Category.id_comp,
    Category.comp_id]

private lemma sectionsOne_eq :
    sectionsOne A U =
      Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) ≫
        (Scheme.Modules.sectionsFunctor U).map A.one ≫ (Iso.refl _).inv := by
  rw [Iso.refl_inv, Category.comp_id]

/-- The sections over `U` of the homogeneous components of a graded quasicoherent algebra form a
graded commutative ring. The product of `x : Γ(Aᵢ, U)` and `y : Γ(Aⱼ, U)` is the homogeneous
multiplication of `A` applied to the image of `x ⊗ₜ y` in the sections of `Aᵢ ⊗ Aⱼ`
(`gMul_sections_def`). -/
@[instance_reducible, instance]
def gCommRingSections : DirectSum.GCommRing (fun n ↦ Γ(A.obj.X n, U)) :=
  TauCeti.ModuleCat.gCommRingOfHomogeneous
    (fun n ↦ (Scheme.Modules.sectionsFunctor U).obj (A.obj.X n)) (sectionsOne A U)
    (sectionsMul A U)
    (GradedObject.one_mul_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.one_mul)
    (GradedObject.mul_one_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.mul_one)
    (GradedObject.mul_assoc_of_laxMonoidal _ _ (sectionsMul_eq A U) A.mul_assoc)
    (GradedObject.mul_comm_of_laxBraided _ _ (sectionsMul_eq A U) A.mul_comm)

/-- The sections over `U` of the homogeneous components of a graded quasicoherent algebra form a
graded `Γ(X, U)`-algebra, whose structure map `Γ(X, U) → Γ(A₀, U)` is the unit of `A`
(`gAlgebraSections_toFun`). -/
@[instance_reducible, instance]
def gAlgebraSections : DirectSum.GAlgebra Γ(X, U) (fun n ↦ Γ(A.obj.X n, U)) :=
  TauCeti.ModuleCat.gAlgebraOfHomogeneous
    (fun n ↦ (Scheme.Modules.sectionsFunctor U).obj (A.obj.X n)) (sectionsOne A U)
    (sectionsMul A U)
    (GradedObject.one_mul_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.one_mul)
    (GradedObject.mul_one_of_laxMonoidal _ _ (sectionsMul_eq A U) _ _ (sectionsOne_eq A U)
      A.mul_one)
    (GradedObject.mul_assoc_of_laxMonoidal _ _ (sectionsMul_eq A U) A.mul_assoc)

/-- The product of homogeneous sections `x : Γ(Aᵢ, U)` and `y : Γ(Aⱼ, U)` is the homogeneous
multiplication of `A` applied to the image of `x ⊗ₜ y` under the tensor map of the sections
functor. -/
lemma gMul_sections_def {i j : ℕ} (x : Γ(A.obj.X i, U)) (y : Γ(A.obj.X j, U)) :
    GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y =
      (A.mul i j).app U
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)) :=
  (rfl)

/-- The unit of the graded ring of sections is the unit of `A` applied to `1 : Γ(X, U)`. -/
lemma gOne_sections_def :
    GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U)) =
      A.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1) :=
  (rfl)

/-- The structure map `Γ(X, U) → Γ(A₀, U)` of the graded algebra of sections is the unit of
`A` on sections over `U`. -/
lemma gAlgebraSections_toFun (r : Γ(X, U)) :
    GAlgebra.toFun (R := Γ(X, U)) (A := fun n ↦ Γ(A.obj.X n, U)) r =
      A.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) :=
  (rfl)

section Restriction

variable {U} {V : X.Opens} (f : V ⟶ U)

/-- Restriction of sections along `V ≤ U` preserves the homogeneous multiplication. -/
private lemma map_gMul_sections {i j : ℕ} (x : Γ(A.obj.X i, U)) (y : Γ(A.obj.X j, U)) :
    (A.obj.X (i + j)).presheaf.map f.op
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, V))
        ((A.obj.X i).presheaf.map f.op x) ((A.obj.X j).presheaf.map f.op y) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The product is the multiplication of `A` applied to the tensor map of `F`; both commute
  -- with restriction, and restriction of the sectionwise tensor product sends `x ⊗ₜ y` to the
  -- pure tensor of the restrictions.
  have h₁ := PresheafOfModules.naturality_apply (A.mul i j).val f.op
    ((Functor.LaxMonoidal.μ F (A.obj.X i) (A.obj.X j)).app' (op U) (x ⊗ₜ y))
  have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.μ F (A.obj.X i) (A.obj.X j))
    f.op (x ⊗ₜ y)
  exact h₁.symm.trans (congrArg _ h₂.symm)

/-- Restriction of sections along `V ≤ U` preserves the unit. -/
private lemma map_gOne_sections :
    (A.obj.X 0).presheaf.map f.op (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, V)) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The unit is the unit of `A` applied to the image of `1` under the unit map of `F`; both
  -- commute with restriction, and restriction of regular functions preserves `1`.
  have h₁ := PresheafOfModules.naturality_apply A.one.val f.op
    ((Functor.LaxMonoidal.ε F).app' (op U) (1 : Γ(X, U)))
  have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) f.op (1 : Γ(X, U))
  exact h₁.symm.trans (congrArg _ (h₂.symm.trans
    (congrArg _ (map_one (X.presheaf.map f.op).hom))))

/-- Restriction of sections along an inclusion of opens `V ≤ U`, as a ring homomorphism between
the graded rings of sections. It sends each homogeneous section to its restriction, in the same
degree (`restrictGradedSections_of`). -/
def restrictGradedSections : (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(A.obj.X n, V) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(A.obj.X n, V)) n).comp ((A.obj.X n).presheaf.map f.op).hom)
    ((congrArg _ (map_gOne_sections A f)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (map_gMul_sections A f x y)).trans (DirectSum.of_mul_of _ _).symm)

/-- Restriction of a homogeneous section is the restriction of the section, in the same
degree. -/
@[simp]
lemma restrictGradedSections_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    A.restrictGradedSections f (DirectSum.of _ n x) =
      DirectSum.of _ n ((A.obj.X n).presheaf.map f.op x) :=
  DirectSum.toSemiring_of _ _ _ _ _

variable (U) in
/-- Restriction of sections along the identity of an open is the identity. -/
@[simp]
lemma restrictGradedSections_id : A.restrictGradedSections (𝟙 U) = RingHom.id _ :=
  DirectSum.ringHom_ext fun n x ↦ by simp

/-- Restriction of sections along a composite of inclusions of opens is the composite of the
restrictions. -/
lemma restrictGradedSections_comp {W : X.Opens} (g : W ⟶ V) :
    A.restrictGradedSections (g ≫ f) =
      (A.restrictGradedSections g).comp (A.restrictGradedSections f) :=
  DirectSum.ringHom_ext fun n x ↦ by simp

end Restriction

/-- The presheaf of graded rings of sections of a graded quasicoherent algebra: it sends an open
`U` to `⨁ n, Γ(Aₙ, U)` and an inclusion of opens to `restrictGradedSections`. -/
@[expose]
def gradedSectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (⨁ n, Γ(A.obj.X n, U.unop))
  map f := CommRingCat.ofHom (A.restrictGradedSections f.unop)
  map_id U := by
    rw [unop_id, restrictGradedSections_id]
    rfl
  map_comp f g := by
    rw [unop_comp, restrictGradedSections_comp]
    rfl

/-- The graded ring of sections over `U` is the value of `gradedSectionsPresheaf` at `U`. -/
@[simp]
lemma gradedSectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    A.gradedSectionsPresheaf.obj U = CommRingCat.of (⨁ n, Γ(A.obj.X n, U.unop)) :=
  (rfl)

/-- The restriction maps of `gradedSectionsPresheaf` are `restrictGradedSections`. -/
@[simp]
lemma gradedSectionsPresheaf_map {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    A.gradedSectionsPresheaf.map f = CommRingCat.ofHom (A.restrictGradedSections f.unop) :=
  (rfl)

section Map

variable {A} {B C : GradedQuasicoherentAlgebra X}

omit U

/-- A morphism of graded quasicoherent algebras is multiplicative on sections. -/
private lemma app_gMul_sections (φ : A ⟶ B) (U : X.Opens) {i j : ℕ} (x : Γ(A.obj.X i, U))
    (y : Γ(A.obj.X j, U)) :
    (φ.hom.hom.hom (i + j)).app U (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(B.obj.X n, U))
        ((φ.hom.hom.hom i).app U x) ((φ.hom.hom.hom j).app U y) :=
  congr($(ModuleCat.hom_ext_iff.mp (GradedObject.map_mul_of_laxMonoidal _ _ (sectionsMul_eq A U)
    _ _ (sectionsMul_eq B U) _ (fun n ↦ (Scheme.Modules.sectionsFunctor U).map
      (φ.hom.hom.hom n)) (fun n ↦ by rw [Iso.refl_hom, Iso.refl_inv, Category.id_comp,
        Category.comp_id]) (map_mul φ) i j)) (x ⊗ₜ y)).symm

/-- A morphism of graded quasicoherent algebras preserves the unit on sections. -/
private lemma app_gOne_sections (φ : A ⟶ B) (U : X.Opens) :
    (φ.hom.hom.hom 0).app U (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(B.obj.X n, U)) :=
  congr($(ModuleCat.hom_ext_iff.mp ((Scheme.Modules.sectionsFunctor U).congr_map (one_map φ)))
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1))

/-- The `Γ(X, U)`-algebra homomorphism between graded rings of sections induced by a morphism of
graded quasicoherent algebras. It applies the morphism degree by degree
(`gradedSectionsMap_of`). -/
def gradedSectionsMap (φ : A ⟶ B) (U : X.Opens) :
    (⨁ n, Γ(A.obj.X n, U)) →ₐ[Γ(X, U)] ⨁ n, Γ(B.obj.X n, U) :=
  DirectSum.toAlgebra _ _
    (fun n ↦ (DirectSum.lof Γ(X, U) ℕ (fun n ↦ Γ(B.obj.X n, U)) n).comp
      ((Scheme.Modules.sectionsFunctor U).map (φ.hom.hom.hom n)).hom)
    ((congrArg _ (app_gOne_sections φ U)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (app_gMul_sections φ U x y)).trans (DirectSum.of_mul_of _ _).symm)

/-- The map induced on graded rings of sections applies the morphism to each homogeneous
section. -/
@[simp]
lemma gradedSectionsMap_of (φ : A ⟶ B) (U : X.Opens) (n : ℕ) (x : Γ(A.obj.X n, U)) :
    gradedSectionsMap φ U (DirectSum.of _ n x) =
      DirectSum.of _ n ((φ.hom.hom.hom n).app U x) :=
  (DirectSum.toAlgebra_apply _ _ _ _ _ _).trans (DirectSum.toSemiring_of _ _ _ _ _)

/-- The identity morphism induces the identity on graded rings of sections. -/
@[simp]
lemma gradedSectionsMap_id (U : X.Opens) : gradedSectionsMap (𝟙 A) U = AlgHom.id _ _ :=
  DirectSum.algHom_ext _ _ fun n x ↦ gradedSectionsMap_of (𝟙 A) U n x

/-- The map induced on graded rings of sections by a composite is the composite of the induced
maps. -/
lemma gradedSectionsMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) (U : X.Opens) :
    gradedSectionsMap (φ ≫ ψ) U = (gradedSectionsMap ψ U).comp (gradedSectionsMap φ U) :=
  DirectSum.algHom_ext _ _ fun n x ↦ (gradedSectionsMap_of (φ ≫ ψ) U n x).trans
    ((congrArg (gradedSectionsMap ψ U) (gradedSectionsMap_of φ U n x)).trans
      (gradedSectionsMap_of ψ U n _)).symm

/-- The maps induced on graded rings of sections commute with restriction. -/
lemma gradedSectionsMap_restrictGradedSections (φ : A ⟶ B) {U V : X.Opens} (f : V ⟶ U)
    (x : ⨁ n, Γ(A.obj.X n, U)) :
    gradedSectionsMap φ V (A.restrictGradedSections f x) =
      B.restrictGradedSections f (gradedSectionsMap φ U x) := by
  refine DFunLike.congr_fun (DirectSum.ringHom_ext (f := (gradedSectionsMap φ V).toRingHom.comp
    (A.restrictGradedSections f)) (g := (B.restrictGradedSections f).comp
      (gradedSectionsMap φ U).toRingHom) fun n y ↦ ?_) x
  calc gradedSectionsMap φ V (A.restrictGradedSections f (DirectSum.of _ n y))
      = DirectSum.of _ n ((φ.hom.hom.hom n).app V ((A.obj.X n).presheaf.map f.op y)) :=
        (congrArg _ (A.restrictGradedSections_of f n y)).trans (gradedSectionsMap_of φ V n _)
    _ = DirectSum.of _ n ((B.obj.X n).presheaf.map f.op ((φ.hom.hom.hom n).app U y)) :=
        congrArg _ (PresheafOfModules.naturality_apply (φ.hom.hom.hom n).val f.op y)
    _ = B.restrictGradedSections f (gradedSectionsMap φ U (DirectSum.of _ n y)) :=
        ((congrArg _ (gradedSectionsMap_of φ U n y)).trans
          (B.restrictGradedSections_of f n _)).symm

end Map

end

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
