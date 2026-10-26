/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor
public import TauCeti.CategoryTheory.GradedObject.Total
public import TauCeti.CategoryTheory.Monoidal.Mon
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# The direct-sum algebra of a graded quasicoherent algebra

A graded quasicoherent algebra `A = (Aₙ)ₙ` on a scheme `X` has an underlying quasicoherent
commutative `𝒪_X`-algebra `⨁ₙ Aₙ`: its underlying module is the direct sum (coproduct) of the
homogeneous components, the product of homogeneous sections of degrees `i` and `j` is their
homogeneous product in degree `i + j`, and the unit is the unit of `A₀`. A graded algebra
morphism induces the direct sum of its components. This forgets the grading, and it is the
algebra whose relative spectrum is the scheme affine over `X` attached to a graded quasicoherent
algebra, for instance the linear scheme of a quasicoherent sheaf.

The construction is the image of `A` under the lax braided monoidal functor
`CategoryTheory.GradedObject.total`, which sends a graded object to the coproduct of its
components, on commutative monoid objects (`CategoryTheory.Functor.mapCommMon`); the direct sum
is quasicoherent because coproducts of quasicoherent sheaves are.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toQuasicoherentAlgebra`: the functor
  `A ↦ ⨁ₙ Aₙ` from graded quasicoherent algebras to quasicoherent algebras;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ιTotal`: the inclusion
  of a homogeneous summand in the underlying direct sum;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isColimitιTotal` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toQuasicoherentAlgebra_hom_ext`: these
  inclusions exhibit the underlying module as the coproduct of the homogeneous components;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toQuasicoherentAlgebra_tensor_hom_ext`:
  morphisms out of the tensor square of the underlying module are determined on the summands
  `Aᵢ ⊗ Aⱼ`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ιTotal_tensorHom_ιTotal_mul` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.one_toQuasicoherentAlgebra`: its
  multiplication restricts to the homogeneous multiplication on `Aᵢ ⊗ Aⱼ`, and its unit is the
  unit of `A₀`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ιTotal_toQuasicoherentAlgebra_map`:
  the algebra morphism induced by a graded algebra morphism is its degree-`n` component on the
  summand `Aₙ`.
-/

public section

open CategoryTheory Limits MonoidalCategory MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X : Scheme.{u}}

/-- The direct-sum algebra `⨁ₙ Aₙ` underlying a graded quasicoherent algebra `A`, as a functor to
quasicoherent algebras: the image of `A` under the lax braided total-object functor
`GradedObject.total`, which is quasicoherent because each `Aₙ` is. -/
def toQuasicoherentAlgebra : GradedQuasicoherentAlgebra X ⥤ QuasicoherentAlgebra X :=
  ObjectProperty.lift _
    ((isGradedQuasicoherentAlgebra X).ι ⋙ (GradedObject.total ℕ X.Modules).mapCommMon)
    fun A ↦ inferInstanceAs (∐ fun n ↦ A.obj.X n).IsQuasicoherent

private theorem toQuasicoherentAlgebra_obj_obj (A : GradedQuasicoherentAlgebra X) :
    (toQuasicoherentAlgebra.obj A).obj =
      ((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj) := by
  rw [toQuasicoherentAlgebra, ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj]

/-- The underlying module of the direct-sum algebra is the direct sum of the homogeneous
components. -/
@[simp]
theorem toQuasicoherentAlgebra_obj_obj_X (A : GradedQuasicoherentAlgebra X) :
    (toQuasicoherentAlgebra.obj A).obj.X = (GradedObject.total ℕ X.Modules).obj A.obj.X := by
  rw [toQuasicoherentAlgebra_obj_obj, Functor.mapCommMon_obj_X]

private theorem toQuasicoherentAlgebra_map_hom {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (toQuasicoherentAlgebra.map f).hom =
      eqToHom (toQuasicoherentAlgebra_obj_obj A) ≫
        (GradedObject.total ℕ X.Modules).mapCommMon.map f.hom ≫
          eqToHom (toQuasicoherentAlgebra_obj_obj B).symm :=
  ObjectProperty.lift_map_hom_of_eq toQuasicoherentAlgebra.eq_1 f
    (toQuasicoherentAlgebra_obj_obj A) (toQuasicoherentAlgebra_obj_obj B)

private theorem toQuasicoherentAlgebra_map_hom_hom_hom
    {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (toQuasicoherentAlgebra.map f).hom.hom.hom =
      eqToHom (toQuasicoherentAlgebra_obj_obj_X A) ≫
        (GradedObject.total ℕ X.Modules).map f.hom.hom.hom ≫
          eqToHom (toQuasicoherentAlgebra_obj_obj_X B).symm := by
  rw [toQuasicoherentAlgebra_map_hom, CommMon.comp_hom, CommMon.comp_hom,
    Functor.mapCommMon_map_hom_hom,
    commMon_eqToHom_hom_hom _ (toQuasicoherentAlgebra_obj_obj_X A),
    commMon_eqToHom_hom_hom _ (toQuasicoherentAlgebra_obj_obj_X B).symm]
  -- The two sides now differ only in the implicit middle object of the composite,
  -- `(mapCommMon.obj A.obj).X` against `total.obj A.obj.X`. Mathlib identifies these
  -- definitionally (`Functor.mapCommMon_obj_X`), and `Functor.mapCommMon_map_hom_hom` is typed
  -- through that identification.
  rfl

private theorem total_mapCommMon_mul (A : GradedQuasicoherentAlgebra X) :
    μ[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] =
      Functor.LaxMonoidal.μ (GradedObject.total ℕ X.Modules) A.obj.X A.obj.X ≫
        (GradedObject.total ℕ X.Modules).map μ[A.obj.X] :=
  Functor.obj.μ_def A.obj.X

private theorem total_mapCommMon_one (A : GradedQuasicoherentAlgebra X) :
    η[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] =
      Functor.LaxMonoidal.ε (GradedObject.total ℕ X.Modules) ≫
        (GradedObject.total ℕ X.Modules).map η[A.obj.X] :=
  Functor.obj.η_def A.obj.X

/-- The inclusion of the degree-`n` homogeneous component into the direct-sum algebra. -/
def ιTotal (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    A.obj.X n ⟶ (toQuasicoherentAlgebra.obj A).obj.X :=
  GradedObject.ιTotal A.obj.X n ≫
    (eqToHom (toQuasicoherentAlgebra_obj_obj A).symm).hom.hom

/-- The inclusion of the degree-`n` summand is the coprojection `GradedObject.ιTotal` into the
total object, transported along the identification of the direct-sum algebra's underlying module
with the total object. -/
theorem ιTotal_def (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ιTotal A n =
      GradedObject.ιTotal A.obj.X n ≫ eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm :=
  (rfl)

/-- The underlying module of the direct-sum algebra is the coproduct of the homogeneous
components, with coprojections `ιTotal`. -/
def isColimitιTotal (A : GradedQuasicoherentAlgebra X) :
    IsColimit (Cofan.mk (toQuasicoherentAlgebra.obj A).obj.X (ιTotal A)) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct fun n ↦ A.obj.X n)
    (Cofan.ext (eqToIso (toQuasicoherentAlgebra_obj_obj_X A).symm)
      fun n ↦ (ιTotal_def A n).symm)

/-- Morphisms out of the direct-sum algebra agree as soon as they agree on every homogeneous
summand. -/
@[ext]
theorem toQuasicoherentAlgebra_hom_ext {A : GradedQuasicoherentAlgebra X} {M : X.Modules}
    {f g : (toQuasicoherentAlgebra.obj A).obj.X ⟶ M} (h : ∀ n, ιTotal A n ≫ f = ιTotal A n ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (isColimitιTotal A) f g h

/-- Morphisms out of the tensor square of the direct-sum algebra agree as soon as they agree on
every summand `Aᵢ ⊗ Aⱼ`. -/
theorem toQuasicoherentAlgebra_tensor_hom_ext {A : GradedQuasicoherentAlgebra X} {M : X.Modules}
    {f g : (toQuasicoherentAlgebra.obj A).obj.X ⊗ (toQuasicoherentAlgebra.obj A).obj.X ⟶ M}
    (h : ∀ i j, (ιTotal A i ⊗ₘ ιTotal A j) ≫ f = (ιTotal A i ⊗ₘ ιTotal A j) ≫ g) :
    f = g := by
  rw [← cancel_epi (eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm ⊗ₘ
    eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm)]
  refine GradedObject.total_tensor_hom_ext fun i j ↦ ?_
  simpa only [tensorHom_comp_tensorHom_assoc, ιTotal_def] using h i j

/-- On the summand `Aᵢ ⊗ Aⱼ`, the multiplication of the direct-sum algebra is the homogeneous
multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` followed by the inclusion of the summand of degree `i + j`. -/
@[simp, reassoc (attr := simp)]
theorem ιTotal_tensorHom_ιTotal_mul (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    (ιTotal A i ⊗ₘ ιTotal A j) ≫
        μ[(toQuasicoherentAlgebra.obj A).obj.X] =
      GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫
        μ[A.obj.X] (i + j) ≫ ιTotal A (i + j) := by
  let e : ((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj) ⟶
      (toQuasicoherentAlgebra.obj A).obj :=
    eqToHom (toQuasicoherentAlgebra_obj_obj A).symm
  let φ := e.hom.hom
  have hφ : IsMonHom φ := e.hom.isMonHom_hom
  let _ : IsMonHom φ := hφ
  have hmul : μ[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] ≫ φ =
      (φ ⊗ₘ φ) ≫ μ[(toQuasicoherentAlgebra.obj A).obj.X] :=
    IsMonHom.mul_hom φ
  have htotal :
      (GradedObject.ιTotal A.obj.X i ⊗ₘ GradedObject.ιTotal A.obj.X j) ≫
          μ[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] =
        GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫
          μ[A.obj.X] (i + j) ≫ GradedObject.ιTotal A.obj.X (i + j) := by
    have h : (GradedObject.ιTotal A.obj.X i ⊗ₘ GradedObject.ιTotal A.obj.X j) ≫
        Functor.LaxMonoidal.μ (GradedObject.total ℕ X.Modules) A.obj.X A.obj.X ≫
          (GradedObject.total ℕ X.Modules).map μ[A.obj.X] =
        GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫
          μ[A.obj.X] (i + j) ≫ GradedObject.ιTotal A.obj.X (i + j) := by
      rw [GradedObject.ιTotal_tensorHom_ιTotal_total_μ_assoc _ _ i j _ rfl,
        GradedObject.ιTotal_total_map]
    rw [total_mapCommMon_mul]
    -- `h` is this goal with the carrier of `mapCommMon.obj A.obj` written as the total object,
    -- as which Mathlib defines it (`Functor.mapCommMon_obj_X`).
    exact h
  have hφX : eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm = φ :=
    (commMon_eqToHom_hom_hom (toQuasicoherentAlgebra_obj_obj A).symm
      (toQuasicoherentAlgebra_obj_obj_X A).symm).symm
  rw [ιTotal_def, ιTotal_def, ιTotal_def, hφX]
  have hcomp := (tensorHom_comp_tensorHom_assoc (GradedObject.ιTotal A.obj.X i)
    (GradedObject.ιTotal A.obj.X j) φ φ
    μ[(toQuasicoherentAlgebra.obj A).obj.X]).symm
  have hmon := congrArg ((GradedObject.ιTotal A.obj.X i ⊗ₘ
    GradedObject.ιTotal A.obj.X j) ≫ ·) hmul.symm
  have htotal' := congrArg (· ≫ φ) htotal
  exact hcomp.trans (hmon.trans ((Category.assoc _ _ _).symm.trans
    (htotal'.trans (Category.assoc _ _ _))))

/-- The unit of the direct-sum algebra is the unit of `A₀` followed by the inclusion of the
summand of degree `0`. -/
@[simp, reassoc]
theorem one_toQuasicoherentAlgebra (A : GradedQuasicoherentAlgebra X) :
    η[(toQuasicoherentAlgebra.obj A).obj.X] =
      (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[A.obj.X] 0 ≫ ιTotal A 0 := by
  let e : ((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj) ⟶
      (toQuasicoherentAlgebra.obj A).obj :=
    eqToHom (toQuasicoherentAlgebra_obj_obj A).symm
  let φ := e.hom.hom
  have hφ : IsMonHom φ := e.hom.isMonHom_hom
  let _ : IsMonHom φ := hφ
  have hone : η[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] ≫ φ =
      η[(toQuasicoherentAlgebra.obj A).obj.X] :=
    IsMonHom.one_hom φ
  have htotal : η[((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj).X] =
      (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[A.obj.X] 0 ≫
        GradedObject.ιTotal A.obj.X 0 := by
    have h : Functor.LaxMonoidal.ε (GradedObject.total ℕ X.Modules) ≫
        (GradedObject.total ℕ X.Modules).map η[A.obj.X] =
          (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[A.obj.X] 0 ≫
            GradedObject.ιTotal A.obj.X 0 := by
      rw [GradedObject.total_ε, Category.assoc, GradedObject.ιTotal_total_map]
    rw [total_mapCommMon_one]
    -- As in `ιTotal_tensorHom_ιTotal_mul`, `h` is this goal up to `Functor.mapCommMon_obj_X`.
    exact h
  have hφX : eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm = φ :=
    (commMon_eqToHom_hom_hom (toQuasicoherentAlgebra_obj_obj A).symm
      (toQuasicoherentAlgebra_obj_obj_X A).symm).symm
  rw [ιTotal_def, hφX]
  exact hone.symm.trans ((congrArg (· ≫ φ) htotal).trans (Category.assoc _ _ _))

/-- On the summand `Aₙ`, the algebra morphism induced by a graded algebra morphism `f` is the
degree-`n` component of `f`. -/
@[simp, reassoc]
theorem ιTotal_toQuasicoherentAlgebra_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B)
    (n : ℕ) :
    ιTotal A n ≫ (toQuasicoherentAlgebra.map f).hom.hom.hom =
      f.hom.hom.hom n ≫ ιTotal B n := by
  have h : eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm ≫
      (toQuasicoherentAlgebra.map f).hom.hom.hom =
        (GradedObject.total ℕ X.Modules).map f.hom.hom.hom ≫
          eqToHom (toQuasicoherentAlgebra_obj_obj_X B).symm := by
    rw [toQuasicoherentAlgebra_map_hom_hom_hom]
    exact (eqToHom_trans_assoc _ _ _).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  rw [ιTotal_def, ιTotal_def]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (GradedObject.ιTotal_total_map f.hom.hom.hom n)).trans (Category.assoc _ _ _))))

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
