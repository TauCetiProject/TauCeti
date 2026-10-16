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
-- Exposed so that the carrier is definitionally the direct sum `∐ₙ Aₙ`, whose summand inclusions
-- `GradedObject.ιTotal` state the characteristic lemmas below.
@[expose]
def toQuasicoherentAlgebra : GradedQuasicoherentAlgebra X ⥤ QuasicoherentAlgebra X :=
  ObjectProperty.lift _
    ((isGradedQuasicoherentAlgebra X).ι ⋙ (GradedObject.total ℕ X.Modules).mapCommMon)
    fun A ↦ inferInstanceAs (∐ fun n ↦ A.obj.X n).IsQuasicoherent

/-- The underlying module of the direct-sum algebra is the direct sum of the homogeneous
components. -/
@[simp]
theorem toQuasicoherentAlgebra_obj_obj_X (A : GradedQuasicoherentAlgebra X) :
    (toQuasicoherentAlgebra.obj A).obj.X = (GradedObject.total ℕ X.Modules).obj A.obj.X :=
  (rfl)

/-- On the summand `Aᵢ ⊗ Aⱼ`, the multiplication of the direct-sum algebra is the homogeneous
multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` followed by the inclusion of the summand of degree `i + j`. -/
@[reassoc]
theorem ιTotal_tensorHom_ιTotal_mul (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    (GradedObject.ιTotal A.obj.X i ⊗ₘ GradedObject.ιTotal A.obj.X j) ≫
        μ[(toQuasicoherentAlgebra.obj A).obj.X] =
      A.mul i j ≫ GradedObject.ιTotal A.obj.X (i + j) := by
  -- The multiplication of the image of a monoid object under a lax monoidal functor is the
  -- tensor map of the functor followed by the image of the multiplication (`Functor.obj.μ_def`).
  -- It is restated through `change`: rewriting with `Functor.obj.μ_def` fails because the carrier
  -- is only definitionally the total object, through the full subcategory of algebras.
  change (GradedObject.ιTotal A.obj.X i ⊗ₘ GradedObject.ιTotal A.obj.X j) ≫
      Functor.LaxMonoidal.μ (GradedObject.total ℕ X.Modules) A.obj.X A.obj.X ≫
        (GradedObject.total ℕ X.Modules).map μ[A.obj.X] = _
  rw [GradedObject.ιTotal_tensorHom_ιTotal_total_μ_assoc _ _ i j _ rfl,
    GradedObject.ιTotal_total_map, mul_def, Category.assoc]

/-- The unit of the direct-sum algebra is the unit of `A₀` followed by the inclusion of the
summand of degree `0`. -/
@[simp]
theorem one_toQuasicoherentAlgebra (A : GradedQuasicoherentAlgebra X) :
    η[(toQuasicoherentAlgebra.obj A).obj.X] = A.one ≫ GradedObject.ιTotal A.obj.X 0 := by
  -- The unit of the image of a monoid object under a lax monoidal functor is the unit of the
  -- functor followed by the image of the unit (`Functor.obj.η_def`), restated through `change`
  -- as in `ιTotal_tensorHom_ιTotal_mul`.
  change Functor.LaxMonoidal.ε (GradedObject.total ℕ X.Modules) ≫
      (GradedObject.total ℕ X.Modules).map η[A.obj.X] = _
  rw [GradedObject.total_ε, Category.assoc, GradedObject.ιTotal_total_map,
    one_def, Category.assoc]

/-- On the summand `Aₙ`, the algebra morphism induced by a graded algebra morphism `f` is the
degree-`n` component of `f`. -/
@[simp, reassoc]
theorem ιTotal_toQuasicoherentAlgebra_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B)
    (n : ℕ) :
    GradedObject.ιTotal A.obj.X n ≫ (toQuasicoherentAlgebra.map f).hom.hom.hom =
      f.hom.hom.hom n ≫ GradedObject.ιTotal B.obj.X n :=
  GradedObject.ιTotal_total_map _ n

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
