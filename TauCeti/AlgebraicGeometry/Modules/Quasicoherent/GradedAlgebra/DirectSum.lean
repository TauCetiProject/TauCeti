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

/-!
# The direct-sum algebra of a graded quasicoherent algebra

A graded quasicoherent algebra `A = (Aₙ)ₙ` on a scheme `X` has an underlying quasicoherent
commutative `𝒪_X`-algebra `⨁ₙ Aₙ`: its underlying module is the direct sum (coproduct) of the
homogeneous components, the product of homogeneous sections of degrees `i` and `j` is their
homogeneous product in degree `i + j`, and the unit is the unit of `A₀`. A graded algebra
morphism induces the direct sum of its components. This forgets the grading, and it is the
algebra whose relative spectrum is the affine scheme attached to a graded quasicoherent algebra,
for instance the linear scheme of a quasicoherent sheaf.

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
      ((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj) :=
  (rfl)

/-- The underlying module of the direct-sum algebra is the direct sum of the homogeneous
components. -/
@[simp]
theorem toQuasicoherentAlgebra_obj_obj_X (A : GradedQuasicoherentAlgebra X) :
    (toQuasicoherentAlgebra.obj A).obj.X = (GradedObject.total ℕ X.Modules).obj A.obj.X :=
  congrArg (fun B : CommMon X.Modules ↦ B.X) (toQuasicoherentAlgebra_obj_obj A)

private theorem toQuasicoherentAlgebra_map_hom {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (toQuasicoherentAlgebra.map f).hom =
      eqToHom (toQuasicoherentAlgebra_obj_obj A) ≫
        (GradedObject.total ℕ X.Modules).mapCommMon.map f.hom ≫
          eqToHom (toQuasicoherentAlgebra_obj_obj B).symm := by
  convert ObjectProperty.ι_obj_lift_map
    (show ObjectProperty (CommMon X.Modules) from fun A ↦ A.X.IsQuasicoherent)
    ((isGradedQuasicoherentAlgebra X).ι ⋙
      (GradedObject.total ℕ X.Modules).mapCommMon)
    (fun A ↦ inferInstanceAs (∐ fun n ↦ A.obj.X n).IsQuasicoherent) f using 1 <;> rfl

private theorem toQuasicoherentAlgebra_map_naturality
    {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    eqToHom (toQuasicoherentAlgebra_obj_obj A).symm ≫
        (toQuasicoherentAlgebra.map f).hom =
      (GradedObject.total ℕ X.Modules).mapCommMon.map f.hom ≫
        eqToHom (toQuasicoherentAlgebra_obj_obj B).symm := by
  rw [toQuasicoherentAlgebra_map_hom]
  exact (eqToIso (toQuasicoherentAlgebra_obj_obj A)).inv_hom_id_assoc _

private theorem toQuasicoherentAlgebra_map_naturality_hom_hom
    {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (eqToHom (toQuasicoherentAlgebra_obj_obj A).symm).hom.hom ≫
        (toQuasicoherentAlgebra.map f).hom.hom.hom =
      (GradedObject.total ℕ X.Modules).map f.hom.hom.hom ≫
        (eqToHom (toQuasicoherentAlgebra_obj_obj B).symm).hom.hom := by
  have h := congrArg (fun g :
      ((GradedObject.total ℕ X.Modules).mapCommMon.obj A.obj) ⟶
        (toQuasicoherentAlgebra.obj B).obj ↦ g.hom.hom)
    (toQuasicoherentAlgebra_map_naturality f)
  simp only [CommMon.comp_hom, Functor.mapCommMon_map_hom_hom] at h
  convert h using 1; rfl

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

/-- On the summand `Aᵢ ⊗ Aⱼ`, the multiplication of the direct-sum algebra is the homogeneous
multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` followed by the inclusion of the summand of degree `i + j`. -/
@[simp, reassoc (attr := simp)]
theorem ιTotal_tensorHom_ιTotal_mul (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    (ιTotal A i ⊗ₘ ιTotal A j) ≫
        μ[(toQuasicoherentAlgebra.obj A).obj.X] =
      A.mul i j ≫ ιTotal A (i + j) := by
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
        A.mul i j ≫ GradedObject.ιTotal A.obj.X (i + j) := by
    rw [total_mapCommMon_mul]
    -- The preceding computation lemma exposes the multiplication; this goal normalization only
    -- identifies `mapCommMon`'s carrier with the total object (`mapCommMon_obj_X`).
    change (GradedObject.ιTotal A.obj.X i ⊗ₘ GradedObject.ιTotal A.obj.X j) ≫
      Functor.LaxMonoidal.μ (GradedObject.total ℕ X.Modules) A.obj.X A.obj.X ≫
        (GradedObject.total ℕ X.Modules).map μ[A.obj.X] = _
    rw [GradedObject.ιTotal_tensorHom_ιTotal_total_μ_assoc _ _ i j _ rfl,
      GradedObject.ιTotal_total_map, mul_def, Category.assoc]
  -- The morphism underlying the identification `e` of monoid objects is the identification of
  -- their underlying modules, which is the one occurring in `ιTotal_def`.
  have hφX : eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm = φ := rfl
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
@[simp]
theorem one_toQuasicoherentAlgebra (A : GradedQuasicoherentAlgebra X) :
    η[(toQuasicoherentAlgebra.obj A).obj.X] = A.one ≫ ιTotal A 0 := by
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
      A.one ≫ GradedObject.ιTotal A.obj.X 0 := by
    rw [total_mapCommMon_one]
    -- As above, normalize only the carrier after applying the explicit unit computation lemma.
    change Functor.LaxMonoidal.ε (GradedObject.total ℕ X.Modules) ≫
      (GradedObject.total ℕ X.Modules).map η[A.obj.X] = _
    rw [GradedObject.total_ε, Category.assoc,
      GradedObject.ιTotal_total_map,
      one_def, Category.assoc]
  -- As in `ιTotal_tensorHom_ιTotal_mul`, `φ` is the identification occurring in `ιTotal_def`.
  have hφX : eqToHom (toQuasicoherentAlgebra_obj_obj_X A).symm = φ := rfl
  rw [ιTotal_def, hφX]
  exact hone.symm.trans ((congrArg (· ≫ φ) htotal).trans (Category.assoc _ _ _))

/-- On the summand `Aₙ`, the algebra morphism induced by a graded algebra morphism `f` is the
degree-`n` component of `f`. -/
@[simp, reassoc]
theorem ιTotal_toQuasicoherentAlgebra_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B)
    (n : ℕ) :
    ιTotal A n ≫ (toQuasicoherentAlgebra.map f).hom.hom.hom =
      f.hom.hom.hom n ≫ ιTotal B n := by
  have h := congrArg (GradedObject.ιTotal A.obj.X n ≫ ·)
    (toQuasicoherentAlgebra_map_naturality_hom_hom f)
  unfold ιTotal
  exact (Category.assoc _ _ _).trans (h.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (eqToHom (toQuasicoherentAlgebra_obj_obj B).symm).hom.hom)
      (GradedObject.ιTotal_total_map f.hom.hom.hom n))))

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
