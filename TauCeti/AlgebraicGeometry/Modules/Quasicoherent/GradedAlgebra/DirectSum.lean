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
public import TauCeti.CategoryTheory.Limits.Shapes.Products
public import TauCeti.CategoryTheory.Monoidal.Mon
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

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
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.mul_ιTotal_comp` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.one_ιTotal_comp`: hence an algebra
  morphism out of `⨁ₙ Aₙ` is multiplicative and unital on the homogeneous summands
  (`mul_ιTotal` and `one_ιTotal` for the identity);
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_ιTotal_zero` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_one_toQuasicoherentAlgebra`: a
  graded algebra whose positive-degree components vanish is its degree-zero component, and its
  direct sum has invertible unit when `A₀` does;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ιTotal_toQuasicoherentAlgebra_map`:
  the algebra morphism induced by a graded algebra morphism is its degree-`n` component on the
  summand `Aₙ`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.epi_toQuasicoherentAlgebra_map`: a
  graded algebra morphism that is an epimorphism in positive degrees, into an algebra whose unit
  is an epimorphism onto the degree-zero component, induces an epimorphism of direct sums.
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.πTotal`: the projection of the direct
  sum onto a homogeneous summand, compatible with induced morphisms
  (`toQuasicoherentAlgebra_map_πTotal`);
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_of_isIso_toQuasicoherentAlgebra_map`:
  the direct-sum functor reflects isomorphisms.
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
          eqToHom (toQuasicoherentAlgebra_obj_obj B).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using ObjectProperty.map_hom_of_comp_ι_eq
    (F := (isGradedQuasicoherentAlgebra X).ι ⋙ (GradedObject.total ℕ X.Modules).mapCommMon)
    (by rw [toQuasicoherentAlgebra]; exact ObjectProperty.lift_comp_ι ..) f
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

/-- The homogeneous multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` followed by the inclusion of the summand
`Aᵢ₊ⱼ` is the multiplication of the direct-sum algebra on the summand `Aᵢ ⊗ Aⱼ`. -/
@[reassoc]
theorem mul_ιTotal (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    A.obj.toMon.mul i j ≫ ιTotal A (i + j) =
      (ιTotal A i ⊗ₘ ιTotal A j) ≫ μ[(toQuasicoherentAlgebra.obj A).obj.X] := by
  rw [ιTotal_tensorHom_ιTotal_mul, Mon.mul_eq]
  exact Category.assoc _ _ _

/-- The unit of `A₀` followed by the inclusion of the summand `A₀` is the unit of the direct-sum
algebra. -/
@[reassoc]
theorem one_ιTotal (A : GradedQuasicoherentAlgebra X) :
    A.obj.toMon.one ≫ ιTotal A 0 = η[(toQuasicoherentAlgebra.obj A).obj.X] := by
  rw [one_toQuasicoherentAlgebra, Mon.one_eq]
  exact Category.assoc _ _ _

/-- A morphism of commutative algebras `k` out of the direct-sum algebra `⨁ₙ Aₙ` sends the
homogeneous multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` to the product of its restrictions to `Aᵢ` and
`Aⱼ`. -/
@[reassoc]
theorem mul_ιTotal_comp {B : CommMon X.Modules} (A : GradedQuasicoherentAlgebra X)
    (k : (toQuasicoherentAlgebra.obj A).obj ⟶ B) (i j : ℕ) :
    A.obj.toMon.mul i j ≫ ιTotal A (i + j) ≫ k.hom.hom =
      ((ιTotal A i ≫ k.hom.hom) ⊗ₘ (ιTotal A j ≫ k.hom.hom)) ≫ μ[B.X] :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ k.hom.hom) (mul_ιTotal A i j)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (IsMonHom.mul_hom k.hom.hom)).trans
      (tensorHom_comp_tensorHom_assoc _ _ _ _ _))))

/-- A morphism of commutative algebras `k` out of the direct-sum algebra `⨁ₙ Aₙ` sends the unit
of `A₀` to the unit of its target. -/
@[reassoc]
theorem one_ιTotal_comp {B : CommMon X.Modules} (A : GradedQuasicoherentAlgebra X)
    (k : (toQuasicoherentAlgebra.obj A).obj ⟶ B) :
    A.obj.toMon.one ≫ ιTotal A 0 ≫ k.hom.hom = η[B.X] :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ k.hom.hom) (one_ιTotal A)).trans (IsMonHom.one_hom k.hom.hom))

/-- If every homogeneous component of positive degree vanishes, the inclusion of the degree-zero
component into the direct sum `⨁ₙ Aₙ` is an isomorphism. -/
theorem isIso_ιTotal_zero (A : GradedQuasicoherentAlgebra X)
    (h : ∀ n, n ≠ 0 → IsZero (A.obj.X n)) : IsIso (ιTotal A 0) :=
  Cofan.IsColimit.isIso_inj_of_isInitial (isColimitιTotal A) 0 fun n hn ↦ (h n hn).isInitial

/-- **A graded algebra concentrated in degree zero has trivial direct sum.** If the unit
`𝒪_X ⟶ A₀` is an isomorphism and every homogeneous component of positive degree vanishes, the
unit of the direct-sum algebra `⨁ₙ Aₙ` is an isomorphism. -/
theorem isIso_one_toQuasicoherentAlgebra (A : GradedQuasicoherentAlgebra X)
    [IsIso A.obj.toMon.one] (h : ∀ n, n ≠ 0 → IsZero (A.obj.X n)) :
    IsIso η[(toQuasicoherentAlgebra.obj A).obj.X] := by
  have := A.isIso_ιTotal_zero h
  rw [← one_ιTotal]
  exact IsIso.comp_isIso' inferInstance this

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

/-- A morphism `g : A ⟶ B` of graded quasicoherent algebras that is an epimorphism in every positive
degree induces an epimorphism `⨁ₙ Aₙ ⟶ ⨁ₙ Bₙ` of the direct sums when the unit `𝒪_X ⟶ B₀` is an
epimorphism: in degree zero, `B₀` is then the image of the unit, which `g` preserves. -/
theorem epi_toQuasicoherentAlgebra_map {A B : GradedQuasicoherentAlgebra X} (g : A ⟶ B)
    [Epi B.obj.toMon.one] (hg : ∀ n, 0 < n → Epi (g.hom.hom.hom n)) :
    Epi (toQuasicoherentAlgebra.map g).hom.hom.hom := by
  refine ⟨fun {Z} u v h ↦ toQuasicoherentAlgebra_hom_ext fun n ↦ ?_⟩
  -- The composites are typed partly in `SheafOfModules X.ringCatSheaf` and partly in
  -- `X.Modules`, which `rw` does not identify, so the equations are chained as terms.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e (w : (toQuasicoherentAlgebra.obj B).obj.X ⟶ Z) :
        B.obj.toMon.one ≫ ιTotal B 0 ≫ w = η[(toQuasicoherentAlgebra.obj A).obj.X] ≫
          (toQuasicoherentAlgebra.map g).hom.hom.hom ≫ w :=
      (one_ιTotal_assoc B w).trans
        (IsMonHom.one_hom_assoc (self := (toQuasicoherentAlgebra.map g).hom.hom.isMonHom_hom) _
          w).symm
    exact (cancel_epi B.obj.toMon.one).1 ((e u).trans ((congrArg (_ ≫ ·) h).trans (e v).symm))
  · have := hg n hn
    exact (cancel_epi (g.hom.hom.hom n)).1
      ((ιTotal_toQuasicoherentAlgebra_map_assoc g n u).symm.trans
        ((congrArg (ιTotal A n ≫ ·) h).trans (ιTotal_toQuasicoherentAlgebra_map_assoc g n v)))

/-- The projection of the direct sum `⨁ₙ Aₙ` onto its summand `Aₙ`: the projection `Sigma.π` of
the coproduct, transported along the identification of the direct-sum algebra's underlying module
with the total object, as for `ιTotal`. -/
def πTotal (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (toQuasicoherentAlgebra.obj A).obj.X ⟶ A.obj.X n :=
  eqToHom (toQuasicoherentAlgebra_obj_obj_X A) ≫ Sigma.π (fun m ↦ A.obj.X m) n

/-- The projection onto `Aₙ` is the identity on the summand `Aₙ` (up to `m = n`) and zero on the
other summands. -/
theorem ιTotal_πTotal (A : GradedQuasicoherentAlgebra X) (m n : ℕ) :
    ιTotal A m ≫ πTotal A n = if h : m = n then eqToHom (congrArg A.obj.X h) else 0 := by
  rw [ιTotal_def, πTotal, Category.assoc]
  -- The two transports are typed partly in `SheafOfModules X.ringCatSheaf` and partly in
  -- `X.Modules`, which `rw` does not identify, so they are cancelled as a term.
  exact (congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).trans ((congrArg (· ≫ _)
    (eqToHom_refl _ _)).trans (Category.id_comp _)))).trans (Sigma.ι_π (fun m ↦ A.obj.X m) m n)

/-- The projection onto `Aₙ` is a retraction of the inclusion of `Aₙ`. -/
@[simp]
theorem ιTotal_πTotal_self (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ιTotal A n ≫ πTotal A n = 𝟙 _ :=
  (ιTotal_πTotal A n n).trans (by simp)

/-- The algebra morphism induced by a graded algebra morphism `f` commutes with the projections
onto the summands, where it is the degree-`n` component of `f`. -/
theorem toQuasicoherentAlgebra_map_πTotal {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B)
    (n : ℕ) :
    (toQuasicoherentAlgebra.map f).hom.hom.hom ≫ πTotal B n = πTotal A n ≫ f.hom.hom.hom n := by
  refine toQuasicoherentAlgebra_hom_ext fun m ↦ ?_
  -- The composites are typed partly in `SheafOfModules X.ringCatSheaf` and partly in
  -- `X.Modules`, which `rw` and `simp` do not identify (for the same reason `@[reassoc]` would
  -- not reassociate `ιTotal_toQuasicoherentAlgebra_map`), so the reassociations are chained as
  -- terms: both sides become `f m ≫ (ιTotal B m ≫ πTotal B n)` and
  -- `(ιTotal A m ≫ πTotal A n) ≫ f n`.
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ πTotal B n)
    (ιTotal_toQuasicoherentAlgebra_map f m)).trans (Category.assoc _ _ _))).trans
      (Eq.trans ?_ (Category.assoc _ _ _))
  refine (congrArg (f.hom.hom.hom m ≫ ·) (ιTotal_πTotal B m n)).trans
    (Eq.trans ?_ (congrArg (· ≫ f.hom.hom.hom n) (ιTotal_πTotal A m n)).symm)
  split_ifs with h
  · subst h
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact comp_zero.trans zero_comp.symm

/-- **The direct-sum functor reflects isomorphisms.** A morphism of graded quasicoherent algebras
whose direct sum `⨁ₙ Aₙ ⟶ ⨁ₙ Bₙ` is an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_toQuasicoherentAlgebra_map {A B : GradedQuasicoherentAlgebra X}
    (f : A ⟶ B) [IsIso (toQuasicoherentAlgebra.map f)] : IsIso f := by
  let φ := (toQuasicoherentAlgebra.map f).hom.hom.hom
  let ψ := (inv (toQuasicoherentAlgebra.map f)).hom.hom.hom
  have h₁ : φ ≫ ψ = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.hom.hom) (IsIso.hom_inv_id (toQuasicoherentAlgebra.map f))
  have h₂ : ψ ≫ φ = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.hom.hom) (IsIso.inv_hom_id (toQuasicoherentAlgebra.map f))
  -- Each component `fₙ` is an isomorphism with inverse `ιTotal B n ≫ ψ ≫ πTotal A n`. As in
  -- `toQuasicoherentAlgebra_map_πTotal`, `φ` and `ψ` are typed in `SheafOfModules X.ringCatSheaf`
  -- and `ιTotal`, `πTotal` in `X.Modules`, so `rw`, `simp` and `calc` cannot be used and the
  -- reassociations are chained as terms.
  have (n : ℕ) : IsIso (f.hom.hom.hom n) := by
    refine ⟨ιTotal B n ≫ ψ ≫ πTotal A n, ?_, ?_⟩
    · -- `fₙ ≫ ιTotal B n ≫ ψ ≫ πTotal A n = ιTotal A n ≫ (φ ≫ ψ) ≫ πTotal A n = 𝟙`
      have e : ιTotal A n ≫ φ = f.hom.hom.hom n ≫ ιTotal B n :=
        ιTotal_toQuasicoherentAlgebra_map f n
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ ≫ πTotal A n) e.symm)).trans
        (((Category.assoc _ _ _).trans (congrArg (ιTotal A n ≫ ·) ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ πTotal A n) h₁).trans (Category.id_comp _))))).trans
            (ιTotal_πTotal_self A n))
    · -- `(ιTotal B n ≫ ψ ≫ πTotal A n) ≫ fₙ = ιTotal B n ≫ (ψ ≫ φ) ≫ πTotal B n = 𝟙`
      have e : φ ≫ πTotal B n = πTotal A n ≫ f.hom.hom.hom n :=
        toQuasicoherentAlgebra_map_πTotal f n
      exact ((Category.assoc _ _ _).trans (congrArg (ιTotal B n ≫ ·)
        ((Category.assoc _ _ _).trans (congrArg (ψ ≫ ·) e.symm)))).trans
          ((congrArg (ιTotal B n ≫ ·) ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ πTotal B n) h₂).trans (Category.id_comp _)))).trans
              (ιTotal_πTotal_self B n))
  have : IsIso f.hom.hom.hom := GradedObject.isIso_of_isIso_apply _
  -- The forgetful functor to graded modules sends `f` to its underlying morphism
  -- `f.hom.hom.hom` (`Functor.comp_map`, `ObjectProperty.ι_map`, `CommMon.forget₂Mon_map_hom`,
  -- `Mon.forget_map`), and it reflects isomorphisms.
  have : IsIso ((ObjectProperty.ι _ ⋙ CommMon.forget₂Mon _ ⋙ Mon.forget _).map f) := by
    simpa only [Functor.comp_map, ObjectProperty.ι_map, CommMon.forget₂Mon_map_hom,
      Mon.forget_map]
  exact isIso_of_reflects_iso f (ObjectProperty.ι _ ⋙ CommMon.forget₂Mon _ ⋙ Mon.forget _)

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
