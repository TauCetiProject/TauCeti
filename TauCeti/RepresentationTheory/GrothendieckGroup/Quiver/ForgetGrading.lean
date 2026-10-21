/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.Multiplicity
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple

/-!
# Forgetting the grading on the Grothendieck group of a path algebra

For a finite quiver with finite-dimensional path algebra, forgetting the path-length grading
induces an isomorphism from graded `G₀` specialized at `q = 1` to ordinary `G₀`. No grading of
every ungraded module is required: the graded vertex-simple classes form a Laurent basis, and
both groups have the same integral vertex coordinates after specialization.

The equivalence constructed here has the actual forgetful map as its forward map. Its inverse
sends each ordinary vertex-simple class to the specialized graded vertex-simple class; more
generally it expands a class using its integral vertex dimensions. The coordinate calculation
also supplies the dimension comparison used when specializing the quiver q-Euler form.

## Main results

* `TauCeti.PathAlgebra.pathAlgebraDimensionVectorK0_forgetGrading`: the coordinates of a
  specialized graded class are the dimension vector after forgetting grading.
* `TauCeti.PathAlgebra.gradedFiniteModulesForgetK0Equiv`: specialization at `q = 1` identifies
  graded and ordinary `G₀` through forgetting grading.

## References

* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for graded
  Grothendieck groups and specialization at `q = 1`.
* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the simple-class basis.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped ModuleCat Pointwise

universe u v w

section VertexDimension

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q]

/-- Two `k`-module structures on a `kQ`-module, each compatible with the `kQ`-action, coincide.
Hence the vertex components have the same dimension for both. This reconciles the `k`-structure
of a graded module with the one `ModuleCat.moduleOfAlgebraModule` puts on its underlying
module. -/
private theorem finrank_vertexComponent_congr [Finite Q] {M : Type*} [AddCommGroup M]
    [Module (pathAlgebra k Q) M] (m₁ m₂ : Module k M)
    (t₁ : letI := m₁; IsScalarTower k (pathAlgebra k Q) M)
    (t₂ : letI := m₂; IsScalarTower k (pathAlgebra k Q) M) (i : Q) :
    (letI := m₁; haveI := t₁; Module.finrank k (vertexComponent k M i)) =
      (letI := m₂; haveI := t₂; Module.finrank k (vertexComponent k M i)) := by
  obtain rfl : m₁ = m₂ := Module.ext' _ _ fun c x => by
    have e₁ := (letI := m₁; haveI := t₁; algebraMap_smul (pathAlgebra k Q) c x)
    have e₂ := (letI := m₂; haveI := t₂; algebraMap_smul (pathAlgebra k Q) c x)
    exact e₁.symm.trans e₂
  rfl

/-- **At `q = 1` the graded dimension at a vertex is the dimension vector** of the underlying
`kQ`-module: `gdim(eᵢ • X)` evaluated at `q = 1` is `dim_k(eᵢ X)`. -/
@[simp]
theorem laurentEval_one_smulGradedDimension_vertexIdempotent [Finite Q]
    (X : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k X] (i : Q) :
    laurentEval (1 : ℤˣ) (X.smulGradedDimension (vertexIdempotent k i)) =
      dimVector ((quiverRepFunctor k Q).obj (GradedModuleCat.toModuleCat.obj X)) i := by
  rw [GradedModuleCat.laurentEval_one_smulGradedDimension _
      (vertexIdempotent_mem_integerGrade_zero k Q i), quiverRepFunctor_obj,
    dimVector_quiverRepOfModule, ← vertexComponent_def]
  exact congrArg Nat.cast <| finrank_vertexComponent_congr k Q _ _ X.isScalarTower
    (ModuleCat.isScalarTower_of_algebra_moduleCat (GradedModuleCat.toModuleCat.obj X)) i

end VertexDimension

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- **Specialized graded simple coordinates are the ungraded vertex dimensions.** This compares
arbitrary classes, including differences of module classes, through the actual forgetful map. -/
theorem pathAlgebraDimensionVectorK0_forgetGrading
    (x : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0.{max u v} (gradedFiniteModulesExactStructure (integerGrade k Q)))) (i : Q) :
    pathAlgebraDimensionVectorK0 k Q (gradedFiniteModulesForgetK0 (integerGrade k Q) x) i =
      (LaurentSpecialization.basis (1 : ℤˣ) (gradedVertexSimpleClassBasis k Q)).repr x i := by
  obtain ⟨x, rfl⟩ := LaurentSpecialization.mk_surjective 1 x
  rw [LaurentSpecialization.basis_repr_mk_apply, gradedVertexSimpleClassBasis_repr_apply]
  obtain ⟨x, rfl⟩ := (LaurentK0.ofExactK0 _).surjective x
  induction x using ExactK0.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | neg x hx => simp only [map_neg, Pi.neg_apply, hx]
  | of M =>
    have : Module.Finite (pathAlgebra k Q) M.obj := gradedFiniteModules_iff.mp M.property
    have : Module.Finite k M.obj := Module.Finite.trans (pathAlgebra k Q) M.obj
    simp only [LaurentK0.ofExactK0_exactK0_of, gradedFiniteModulesForgetK0_mk_of,
      pathAlgebraDimensionVectorK0_of, gradedFiniteModulesForget_obj]
    -- The exported coordinate uses the idempotence equality as an IsIdempotentElem proof.
    erw [gradedIdempotentCoordinate_of]
    exact (laurentEval_one_smulGradedDimension_vertexIdempotent k Q M.obj i).symm

/-- **Forgetting grading is an isomorphism on `G₀` after specialization at `q = 1`**, for a
finite quiver whose path algebra is finite-dimensional. The inverse reconstructs a class from
its vertex dimensions using the specialized graded vertex simples. -/
def gradedFiniteModulesForgetK0Equiv :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{max u v} (gradedFiniteModulesExactStructure (integerGrade k Q))) ≃ₗ[ℤ]
      ExactK0.{max u v} (finiteModulesExactStructure (pathAlgebra k Q)) :=
  letI := Fintype.ofFinite Q
  (LaurentSpecialization.basis (1 : ℤˣ) (gradedVertexSimpleClassBasis k Q)).equivFun.trans
    (pathAlgebraDimensionVectorK0Equiv k Q).toIntLinearEquiv.symm

/-- The forward map of the comparison equivalence is the map induced by forgetting grading. -/
@[simp]
theorem gradedFiniteModulesForgetK0Equiv_toLinearMap :
    (gradedFiniteModulesForgetK0Equiv k Q).toLinearMap =
      gradedFiniteModulesForgetK0 (integerGrade k Q) := by
  classical
  let _ := Fintype.ofFinite Q
  apply LinearMap.ext
  intro x
  apply (pathAlgebraDimensionVectorK0Equiv k Q).injective
  funext i
  simp only [pathAlgebraDimensionVectorK0Equiv_apply]
  rw [pathAlgebraDimensionVectorK0_forgetGrading]
  rw [← pathAlgebraDimensionVectorK0Equiv_apply]
  simpa only [gradedFiniteModulesForgetK0Equiv, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, AddEquiv.coe_symm_toIntLinearEquiv,
    AddEquiv.apply_symm_apply] using
      congrFun ((LaurentSpecialization.basis (1 : ℤˣ)
        (gradedVertexSimpleClassBasis k Q)).equivFun_apply x) i

/-- On a specialized module class the equivalence returns its underlying ungraded class. -/
-- A simp rule here would normalize the inner application before generic inverse laws match.
theorem gradedFiniteModulesForgetK0Equiv_mk_of
    (M : (gradedFiniteModules (integerGrade k Q)).FullSubcategory) :
    gradedFiniteModulesForgetK0Equiv k Q
        (LaurentSpecialization.mk 1 (LaurentK0.of _ M)) =
      ExactK0.of ((gradedFiniteModulesForget (integerGrade k Q)).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedFiniteModulesForgetK0Equiv_toLinearMap]
  exact gradedFiniteModulesForgetK0_mk_of _ M

/-- The inverse comparison expands an ungraded class in the specialized graded vertex simples,
with its integral vertex dimensions as coefficients. -/
theorem gradedFiniteModulesForgetK0Equiv_symm_apply [Fintype Q]
    (x : ExactK0.{max u v} (finiteModulesExactStructure (pathAlgebra k Q))) :
    (gradedFiniteModulesForgetK0Equiv k Q).symm x =
      ∑ i, pathAlgebraDimensionVectorK0 k Q x i •
        LaurentSpecialization.mk (1 : ℤˣ)
          (LaurentK0.of _ ⟨gradedVertexSimple k Q i,
            gradedFiniteModules_gradedVertexSimple k Q i⟩) := by
  classical
  let b := LaurentSpecialization.basis (1 : ℤˣ) (gradedVertexSimpleClassBasis k Q)
  have hcoord (i : Q) :
      b.repr ((gradedFiniteModulesForgetK0Equiv k Q).symm x) i =
        pathAlgebraDimensionVectorK0 k Q x i := by
    rw [← pathAlgebraDimensionVectorK0_forgetGrading,
      ← gradedFiniteModulesForgetK0Equiv_toLinearMap, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  simpa only [b, hcoord, LaurentSpecialization.basis_apply,
    gradedVertexSimpleClassBasis_apply] using
    (b.sum_repr ((gradedFiniteModulesForgetK0Equiv k Q).symm x)).symm

/-- The inverse sends an ordinary vertex-simple class to its graded class at `q = 1`. -/
-- Keep this named: child normalization would prevent generic equivalence inverse laws matching.
theorem gradedFiniteModulesForgetK0Equiv_symm_vertexSimple (i : Q) :
    (gradedFiniteModulesForgetK0Equiv k Q).symm
        (ExactK0.of (vertexSimpleModuleFG k Q i)) =
      LaurentSpecialization.mk (1 : ℤˣ)
        (LaurentK0.of _ ⟨gradedVertexSimple k Q i,
          gradedFiniteModules_gradedVertexSimple k Q i⟩) := by
  classical
  let _ := Fintype.ofFinite Q
  rw [gradedFiniteModulesForgetK0Equiv_symm_apply,
    ← pathAlgebraDimensionVectorK0Equiv_apply,
    pathAlgebraDimensionVectorK0Equiv_vertexSimple]
  simp [Pi.single_apply]

end TauCeti.PathAlgebra
