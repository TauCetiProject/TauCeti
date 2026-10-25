/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RepresentationTheory.GrothendieckGroup.CartanMatrix
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ForgetGrading
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.Multiplicity
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.ModuleClassification
import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Specialization
import TauCeti.RepresentationTheory.Quiver.LastArrow
import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Dimension

/-!
# The Cartan maps of a path algebra, its Cartan matrix, and forgetting grading on projective `K₀`

Let `Q` be a finite quiver whose path algebra `kQ` is finite-dimensional, so that `Q` is acyclic
with finitely many arrows. Every finitely generated `kQ`-module has projective dimension at most
one, so the resolution theorem applies to `kQ` with and without its path-length grading: both
the Cartan map `K₀(proj kQ) → G₀(mod kQ)` and the graded Cartan map
`K₀^gr(proj kQ) → G₀^gr(mod kQ)` are isomorphisms. The finite-resolution hypotheses proved here
are the inputs of `TauCeti.cartanEquiv` and `TauCeti.gradedCartanEquiv`, whose inverses send a
module to the alternating class of a finite projective resolution.

Forgetting the grading identifies graded `G₀` specialized at `q = 1` with ordinary `G₀`
(`TauCeti.PathAlgebra.gradedFiniteModulesForgetK0Equiv`). The same holds for the Grothendieck
groups of finitely generated projectives: forgetting the grading identifies `K₀^gr(proj kQ)`
specialized at `q = 1` with `K₀(proj kQ)`. This is the instance of
`TauCeti.gradedIdempotentProjectiveForgetK0Equiv` for the vertex idempotents, which span the
degree-zero part of the path-length grading.

The vertex projectives `Pᵢ` are indecomposable, pairwise nonisomorphic, and exhaust the
indecomposable finitely generated projective `kQ`-modules, so their classes form a `ℤ`-basis of
`K₀(proj kQ)`, just as the vertex simples `Sᵢ` form a basis of `G₀(mod kQ)`. In these two bases the
Cartan map has the path-counting matrix: its `(i, j)` entry is the multiplicity `[Pⱼ : Sᵢ]`, the
number of paths from `j` to `i`. Rows are indexed by simples and columns by projectives, following
the left-module convention for Cartan matrices. Counting paths by their last arrow turns this into
a closed formula: if the `(i, j)` entry of `A` counts arrows `i ⟶ j`, then the Cartan matrix is
`(1 - Aᵀ)⁻¹`. This is the ungraded counterpart of
`TauCeti.PathAlgebra.gradedCartanMatrix_eq_inv_one_sub_T_smul_transpose`.

## Main definitions

* `TauCeti.PathAlgebra.vertexProjectiveFiniteProjective`: the vertex projective `Pᵢ` as a finitely
  generated projective `kQ`-module.
* `TauCeti.PathAlgebra.vertexProjectiveClassBasis`: the basis `[Pᵢ]` of `K₀(proj kQ)`.

## Main results

* `TauCeti.PathAlgebra.finiteModules_le_admitsFiniteResolution` and
  `TauCeti.PathAlgebra.gradedFiniteModules_le_admitsFiniteResolution`: every finite module, graded
  or not, has a finite resolution by finitely generated projectives.
* `TauCeti.PathAlgebra.cartanMap_bijective` and `TauCeti.PathAlgebra.gradedCartanMap_bijective`:
  both Cartan maps are bijective.
* `TauCeti.PathAlgebra.gradedFiniteProjectiveModulesForgetK0Equiv`: specialization at `q = 1`
  identifies graded and ordinary projective `K₀` through forgetting grading.
* `TauCeti.PathAlgebra.isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective`:
  every indecomposable finitely generated projective `kQ`-module is a vertex projective.
* `TauCeti.PathAlgebra.cartanMatrix_vertexProjectiveFiniteProjective_apply`: the `(i, j)` entry of
  the Cartan matrix is the number of paths from `j` to `i`.
* `TauCeti.PathAlgebra.cartanMap_vertexProjectiveFiniteProjective`: the Cartan map sends `[Pⱼ]` to
  `∑ᵢ #(j → i) • [Sᵢ]`.
* `TauCeti.PathAlgebra.cartanMatrix_vertexProjectiveFiniteProjective_eq_inv`: the Cartan matrix is
  `(1 - Aᵀ)⁻¹`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for hereditary path algebras and the Cartan matrix.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for graded
  Grothendieck groups and specialization at `q = 1`.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory
open scoped Matrix ModuleCat

universe u v

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- **Every finitely generated module over a finite-dimensional path algebra has a finite
resolution by finitely generated projectives**, the hypothesis of `TauCeti.cartanEquiv`. -/
theorem finiteModules_le_admitsFiniteResolution :
    ModuleCat.isFG (pathAlgebra k Q) ≤
      (ExactStructure.abelian (ModuleCat.{max u v} (pathAlgebra k Q))).admitsFiniteResolution
        (finiteProjectiveModules (pathAlgebra k Q)) :=
  have : IsNoetherianRing (pathAlgebra k Q) := IsNoetherianRing.of_finite k (pathAlgebra k Q)
  finiteModules_le_admitsFiniteResolution_of_finite_projectiveDimension fun M hM ↦
    ⟨1, hasProjectiveDimensionLT_two_pathAlgebra_of_moduleFinite k Q M hM⟩

/-- **Every finite graded module over a finite-dimensional path algebra has a finite resolution
by finite graded projectives**, for the path-length grading. This is the hypothesis of
`TauCeti.gradedCartanEquiv`. -/
theorem gradedFiniteModules_le_admitsFiniteResolution :
    gradedFiniteModules (integerGrade k Q) ≤
      (gradedModuleCanonicalExactStructure (integerGrade k Q)).admitsFiniteResolution
        (gradedFiniteProjectiveModules (integerGrade k Q)) :=
  let _ := integerGradedAlgebra k Q
  have : IsNoetherianRing (pathAlgebra k Q) := IsNoetherianRing.of_finite k (pathAlgebra k Q)
  gradedFiniteModules_le_admitsFiniteResolution_of_finite_projectiveDimension fun _ hM ↦
    ⟨1, hasProjectiveDimensionLT_two_pathAlgebra_of_moduleFinite k Q _ hM⟩

/-- **The Cartan map of a finite-dimensional path algebra is bijective**: `K₀(proj kQ)` and
`G₀(mod kQ)` are identified by the inclusion of projectives. -/
theorem cartanMap_bijective : Function.Bijective (cartanMap (pathAlgebra k Q)) :=
  TauCeti.cartanMap_bijective _ (finiteModules_le_admitsFiniteResolution k Q)

/-- **The graded Cartan map of a finite-dimensional path algebra is bijective**, for the
path-length grading. -/
theorem gradedCartanMap_bijective : Function.Bijective (gradedCartanMap (integerGrade k Q)) :=
  let _ := integerGradedAlgebra k Q
  TauCeti.gradedCartanMap_bijective _ (gradedFiniteModules_le_admitsFiniteResolution k Q)

/-- **Forgetting grading is an isomorphism on projective `K₀` after specialization at `q = 1`**,
for a finite quiver whose path algebra is finite-dimensional. The forward map sends the
specialized class of a finite graded projective to the class of its underlying module. -/
def gradedFiniteProjectiveModulesForgetK0Equiv :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{max u v} (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q)))
      ≃ₗ[ℤ] ExactK0.{max u v} (finiteProjectiveModulesExactStructure (pathAlgebra k Q)) :=
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  gradedIdempotentProjectiveForgetK0Equiv (completeOrthogonalIdempotents_vertexIdempotent k Q)
    (vertexIdempotent_mem_integerGrade_zero k Q) (fun _ => integerGrade_eq_bot_of_neg k Q)
    (integerGrade_zero_eq_span_range_vertexIdempotent k Q).le vertexIdempotent_ne_zero

/-- The forward map of the projective comparison equivalence is the map induced by forgetting
grading. -/
@[simp]
theorem gradedFiniteProjectiveModulesForgetK0Equiv_toLinearMap :
    (gradedFiniteProjectiveModulesForgetK0Equiv k Q).toLinearMap =
      gradedFiniteProjectiveModulesForgetK0 (integerGrade k Q) :=
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  gradedIdempotentProjectiveForgetK0Equiv_toLinearMap _ _ _ _ _

/-- Forgetting the path-length grading is bijective on projective `K₀` after specialization at
`q = 1`. -/
theorem gradedFiniteProjectiveModulesForgetK0_bijective :
    Function.Bijective (gradedFiniteProjectiveModulesForgetK0 (integerGrade k Q)) := by
  rw [← gradedFiniteProjectiveModulesForgetK0Equiv_toLinearMap, LinearEquiv.coe_coe]
  exact (gradedFiniteProjectiveModulesForgetK0Equiv k Q).bijective

/-- On a specialized graded projective class the equivalence returns its underlying ungraded
class. -/
-- A simp rule here would normalize the inner application before generic inverse laws match.
theorem gradedFiniteProjectiveModulesForgetK0Equiv_mk_of
    (P : (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory) :
    gradedFiniteProjectiveModulesForgetK0Equiv k Q
        (LaurentSpecialization.mk 1 (LaurentK0.of.{max u v} _ P)) =
      ExactK0.of.{max u v} ((gradedFiniteProjectiveModulesForget (integerGrade k Q)).obj P) := by
  rw [← LinearEquiv.coe_coe, gradedFiniteProjectiveModulesForgetK0Equiv_toLinearMap]
  exact gradedFiniteProjectiveModulesForgetK0_mk_of _ P

/-- The inverse comparison sends the class of the underlying module of a finite graded
projective to its specialized graded class. -/
theorem gradedFiniteProjectiveModulesForgetK0Equiv_symm_of
    (P : (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory) :
    (gradedFiniteProjectiveModulesForgetK0Equiv k Q).symm
        (ExactK0.of.{max u v} ((gradedFiniteProjectiveModulesForget (integerGrade k Q)).obj P)) =
      LaurentSpecialization.mk 1 (LaurentK0.of.{max u v} _ P) := by
  rw [LinearEquiv.symm_apply_eq, gradedFiniteProjectiveModulesForgetK0Equiv_mk_of]

/-! ### The Cartan matrix in the vertex bases -/

omit [FiniteDimensional k (pathAlgebra k Q)] in
/-- **The vertex projective `Pᵢ` as a finitely generated projective `kQ`-module.** Its underlying
module is `TauCeti.indecProjModule k Q i`, the module of `TauCeti.vertexProjectiveModuleFG`. -/
def vertexProjectiveFiniteProjective (i : Q) :
    (finiteProjectiveModules (pathAlgebra k Q)).FullSubcategory :=
  ⟨(vertexProjectiveModuleFG k Q i).obj,
    finiteProjectiveModules_iff.mpr ⟨(vertexProjectiveModuleFG k Q i).property, inferInstance⟩⟩

omit [FiniteDimensional k (pathAlgebra k Q)] in
/-- The underlying module of `TauCeti.PathAlgebra.vertexProjectiveFiniteProjective` is the vertex
projective module. -/
@[simp]
theorem vertexProjectiveFiniteProjective_obj (i : Q) :
    (vertexProjectiveFiniteProjective k Q i).obj = indecProjModule k Q i :=
  vertexProjectiveModuleFG_obj k Q i

/-- The vertex projectives of a finite-dimensional path algebra are indecomposable modules. -/
theorem isIndecomposableModule_vertexProjectiveFiniteProjective (i : Q) :
    IsIndecomposableModule (pathAlgebra k Q) (vertexProjectiveFiniteProjective k Q i).obj := by
  rw [vertexProjectiveFiniteProjective_obj]
  exact isIndecomposableModule_indecProjModule
    (isAcyclic_of_module_finite_pathAlgebra k Q inferInstance) i

/-- The vertex projectives of a finite-dimensional path algebra at distinct vertices are not
isomorphic. -/
theorem pairwise_isEmpty_linearEquiv_vertexProjectiveFiniteProjective :
    Pairwise fun i j ↦ IsEmpty ((vertexProjectiveFiniteProjective k Q i).obj ≃ₗ[pathAlgebra k Q]
      (vertexProjectiveFiniteProjective k Q j).obj) := by
  intro i j hij
  rw [vertexProjectiveFiniteProjective_obj, vertexProjectiveFiniteProjective_obj]
  exact isEmpty_linearEquiv_indecProjModule
    (isAcyclic_of_module_finite_pathAlgebra k Q inferInstance) hij

/-- **The vertex projectives exhaust the indecomposable finitely generated projective modules of
a finite-dimensional path algebra.** -/
theorem isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective :
    IsExhaustiveIndecomposableProjectiveFamily (vertexProjectiveFiniteProjective k Q) := by
  rw [isExhaustiveIndecomposableProjectiveFamily_iff]
  intro X hX
  obtain ⟨hfin, hproj⟩ := finiteProjectiveModules_iff.mp X.property
  have : FiniteDimensional k X.obj := Module.Finite.trans (pathAlgebra k Q) X.obj
  obtain ⟨i, ⟨e⟩⟩ := exists_linearEquiv_indecProjModule
    (isAcyclic_of_module_finite_pathAlgebra k Q inferInstance) X.obj hX
  exact ⟨i, ⟨e.trans (eqToIso (vertexProjectiveFiniteProjective_obj k Q i).symm).toLinearEquiv⟩⟩

/-- **The vertex-projective basis of `K₀(proj kQ)`**, for a finite acyclic quiver: its vector at
`i` is the class `[Pᵢ]` of the vertex projective. -/
def vertexProjectiveClassBasis :
    Module.Basis Q ℤ
      (ExactK0.{max u v} (finiteProjectiveModulesExactStructure (pathAlgebra k Q))) :=
  indecomposableProjectiveClassBasis (vertexProjectiveFiniteProjective k Q)
    (isIndecomposableModule_vertexProjectiveFiniteProjective k Q)
    (pairwise_isEmpty_linearEquiv_vertexProjectiveFiniteProjective k Q)
    (isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective k Q)

/-- The basis vector of `TauCeti.PathAlgebra.vertexProjectiveClassBasis` at `i` is the class
`[Pᵢ]`. -/
@[simp]
theorem vertexProjectiveClassBasis_apply (i : Q) :
    vertexProjectiveClassBasis k Q i = (ExactK0.of (vertexProjectiveFiniteProjective k Q i) :
      ExactK0.{max u v} (finiteProjectiveModulesExactStructure (pathAlgebra k Q))) :=
  indecomposableProjectiveClassBasis_apply _ _ _ _ i

/-- **The Cartan map of a path algebra on a vertex projective**: it sends `[Pⱼ]` to
`∑ᵢ #(j → i) • [Sᵢ]`, the `j`th column of the path-counting matrix. -/
theorem cartanMap_vertexProjectiveFiniteProjective [Fintype Q] (j : Q) :
    cartanMap (pathAlgebra k Q) (ExactK0.of (vertexProjectiveFiniteProjective k Q j)) =
      ∑ i, (Nat.card (Quiver.Path j i) : ℤ) • ExactK0.of (vertexSimpleModuleFG k Q i) := by
  rw [cartanMap_of_eq_sum (vertexProjectiveFiniteProjective k Q) (vertexSimpleModuleFG k Q)
    (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
    (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q) j]
  -- The finitely generated module is `vertexProjectiveModuleFG k Q j` up to structure eta.
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [← jordanHolderMultiplicity_vertexProjectiveModuleFG_eq_card_path k Q i j]; rfl

/-- **The Cartan matrix of a path algebra counts paths.** In the bases of vertex projectives and
vertex simples, the `(i, j)` entry `[Pⱼ : Sᵢ]` is the number of paths from `j` to `i`. -/
theorem cartanMatrix_vertexProjectiveFiniteProjective_apply [Fintype Q] (i j : Q) :
    cartanMatrix (vertexProjectiveFiniteProjective k Q) (vertexSimpleModuleFG k Q)
        (isIndecomposableModule_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexProjectiveFiniteProjective k Q)
        (isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
        (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q) i j =
      Nat.card (Quiver.Path j i) := by
  rw [cartanMatrix_apply]
  exact_mod_cast jordanHolderMultiplicity_vertexProjectiveModuleFG_eq_card_path k Q i j

/-- **The Cartan matrix of a path algebra inverts `1 - Aᵀ`**, where the `(i, j)` entry of `A`
counts arrows `i ⟶ j`, in the bases of vertex projectives and vertex simples. Entrywise this is
the last-arrow recursion for path counts: a nontrivial path from `j` to `i` is a path from `j` to
some `l` followed by an arrow `l ⟶ i`. -/
theorem one_sub_transpose_mul_cartanMatrix_vertexProjectiveFiniteProjective_eq_one [Fintype Q]
    [DecidableEq Q] :
    (1 - (Matrix.of fun i j : Q ↦ (Nat.card (i ⟶ j) : ℤ))ᵀ) *
      cartanMatrix (vertexProjectiveFiniteProjective k Q) (vertexSimpleModuleFG k Q)
        (isIndecomposableModule_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexProjectiveFiniteProjective k Q)
        (isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
        (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q) = 1 := by
  have : ∀ a b : Q, Finite (a ⟶ b) := finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  have : Finite (Σ a b : Q, Quiver.Path a b) := (module_finite_pathAlgebra_iff k Q).mp inferInstance
  have (a b : Q) : Finite (Quiver.Path a b) :=
    Finite.of_injective (fun p : Quiver.Path a b ↦ (⟨a, b, p⟩ : Σ x y : Q, Quiver.Path x y))
      fun p q hpq ↦ by simpa using hpq
  ext i j
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) (card_path_eq_ite_add_sum_lastArrow j i)
  push_cast at h
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.transpose_apply,
    Matrix.of_apply, cartanMatrix_vertexProjectiveFiniteProjective_apply, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, h,
    mul_comm]
  simp [eq_comm]

/-- **The Cartan matrix of a path algebra is `(1 - Aᵀ)⁻¹`**, where the `(i, j)` entry of `A`
counts arrows `i ⟶ j`, in the bases of vertex projectives and vertex simples. -/
theorem cartanMatrix_vertexProjectiveFiniteProjective_eq_inv [Fintype Q] [DecidableEq Q] :
    cartanMatrix (vertexProjectiveFiniteProjective k Q) (vertexSimpleModuleFG k Q)
        (isIndecomposableModule_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexProjectiveFiniteProjective k Q)
        (isExhaustiveIndecomposableProjectiveFamily_vertexProjectiveFiniteProjective k Q)
        (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
        (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q) =
      (1 - (Matrix.of fun i j : Q ↦ (Nat.card (i ⟶ j) : ℤ))ᵀ)⁻¹ :=
  (Matrix.inv_eq_right_inv
    (one_sub_transpose_mul_cartanMatrix_vertexProjectiveFiniteProjective_eq_one k Q)).symm

end TauCeti.PathAlgebra
