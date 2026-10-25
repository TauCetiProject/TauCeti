/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.ForgetGrading
import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Specialization
import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Dimension

/-!
# The Cartan maps of a path algebra and forgetting grading on projective `K₀`

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

## Main results

* `TauCeti.PathAlgebra.finiteModules_le_admitsFiniteResolution` and
  `TauCeti.PathAlgebra.gradedFiniteModules_le_admitsFiniteResolution`: every finite module, graded
  or not, has a finite resolution by finitely generated projectives.
* `TauCeti.PathAlgebra.cartanMap_bijective` and `TauCeti.PathAlgebra.gradedCartanMap_bijective`:
  both Cartan maps are bijective.
* `TauCeti.PathAlgebra.gradedFiniteProjectiveModulesForgetK0Equiv`: specialization at `q = 1`
  identifies graded and ordinary projective `K₀` through forgetting grading.

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
open scoped ModuleCat

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

end TauCeti.PathAlgebra
