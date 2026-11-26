/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.DirectSum
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix

/-!
# Linear projective resolutions of graded quiver vertex simples

Give the path algebra `kQ` of a quiver `Q` with finitely many vertices its path-length grading.
For every vertex `i`, the first-arrow short exact sequence

`0 ⟶ ⨁_{a : i ⟶ j} (kQ eⱼ){1} ⟶ kQ eᵢ ⟶ Sᵢ ⟶ 0`

from `TauCeti.PathAlgebra.gradedVertexSimpleResolution` assembles into a concrete
`TauCeti.GradedProjectiveResolution` of length one for the graded vertex simple `Sᵢ`.

Because `eᵢ` has path length zero, the projective cover `kQ eᵢ` is generated in internal degree
zero, and each shifted summand `(kQ eⱼ){1}` of the arrow kernel is generated in internal degree
one. Consequently, `Sᵢ` is concentrated in internal degree zero and admits a linear (and hence
minimal) graded projective resolution over any commutative coefficient ring `k`, with no
acyclicity, finite-dimensionality, or outgoing-arrow finiteness assumption on `Q`.

In `K₀^gr(proj kQ)`, `[P₀(Sᵢ)] = [kQ eᵢ]` and `[Pₙ(Sᵢ)] = 0` for `n ≥ 2` unconditionally, while
for a vertex `i` with finitely many outgoing arrows `[P₁(Sᵢ)] = ∑ⱼ #{a : i ⟶ j} q [kQ eⱼ]`. When
`k` is a field and `kQ` is finite-dimensional, these formulas give the coordinates of the
resolution terms in `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis`.

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution`: the length-one
  `TauCeti.GradedProjectiveResolution` of `Sᵢ` built from the first-arrow short exact sequence.

## Main results

* `TauCeti.PathAlgebra.isLinear_gradedVertexSimpleProjectiveResolution` and
  `TauCeti.PathAlgebra.isMinimal_gradedVertexSimpleProjectiveResolution`: the first-arrow
  resolution of `Sᵢ` is linear and minimal.
* `TauCeti.PathAlgebra.laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_zero`,
  `TauCeti.PathAlgebra.laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one`,
`TauCeti.PathAlgebra.laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_add_two`:
  Grothendieck classes of the resolution terms in `K₀^gr(proj kQ)`.
* `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_zero`,
  `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_one`, and
  `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_add_two`:
  coordinates of `[Pₙ(Sᵢ)]` in `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 2, for the first-arrow projective resolution.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for linear graded projective resolutions of path algebras.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

attribute [local instance] integerGradedAlgebra

universe u v w

section CommRing

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]

/-- **The first-arrow graded projective resolution of a vertex simple `Sᵢ`.** Its degree-`0` term
is `kQ eᵢ`, its degree-`1` term is `⨁_{a : i ⟶ j} (kQ eⱼ){1}`, and its terms vanish from
homological degree `2` on.

This is an abbreviation so that the carrier types and module instances of its terms reduce
directly to `gradedVertexProjective`, `gradedArrowSum`, and the empty direct sum. -/
abbrev gradedVertexSimpleProjectiveResolution (i : Q) :
    GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q i).grading :=
  GradedProjectiveResolution.ofShortExact
    (Eq.mp (congrArg ShortComplex.ShortExact (gradedVertexSimpleResolution_def k Q i))
      (shortExact_gradedVertexSimpleResolution k Q i))

/-- In homological degree `0`, the resolution of `Sᵢ` has term `kQ eᵢ`. -/
theorem gradedVertexSimpleProjectiveResolution_termObj_zero (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).termObj 0 =
      gradedVertexProjective k Q i := (rfl)

/-- In homological degree `1`, the resolution of `Sᵢ` has term `⨁_{a : i ⟶ j} (kQ eⱼ){1}`. -/
theorem gradedVertexSimpleProjectiveResolution_termObj_one (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).termObj 1 =
      gradedArrowSum k Q i := (rfl)

/-- The degree-`0` differential of the resolution of `Sᵢ` is `gradedArrowSumToVertexProjective`. -/
theorem gradedVertexSimpleProjectiveResolution_differential_zero (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).differential 0 =
      gradedArrowSumToVertexProjective k Q i := (rfl)

/-- Higher differentials of the resolution of `Sᵢ` vanish. -/
theorem gradedVertexSimpleProjectiveResolution_differential_succ (i : Q) (n : ℕ) :
    (gradedVertexSimpleProjectiveResolution k Q i).differential (n + 1) = 0 := (rfl)

/-- The augmentation of the resolution of `Sᵢ` is `gradedVertexProjectiveToSimple`. -/
theorem gradedVertexSimpleProjectiveResolution_augmentation (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).augmentation =
      gradedVertexProjectiveToSimple k Q i := (rfl)

/-- **The first-arrow resolution of `Sᵢ` is linear**: `kQ eᵢ` is generated in degree `0`,
`⨁_{a : i ⟶ j} (kQ eⱼ){1}` is generated in degree `1`, and higher terms vanish. -/
theorem isLinear_gradedVertexSimpleProjectiveResolution (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).IsLinear :=
  (GradedProjectiveResolution.isLinear_ofShortExact_iff _).2
    ⟨isGeneratedInDegree_gradedVertexProjective k Q i,
      isGeneratedInDegree_gradedArrowSum k Q i⟩

/-- **The first-arrow resolution of `Sᵢ` is minimal**: over the nonnegatively graded path algebra,
linearity implies minimality. -/
theorem isMinimal_gradedVertexSimpleProjectiveResolution (i : Q) :
    (gradedVertexSimpleProjectiveResolution k Q i).IsMinimal :=
  (isLinear_gradedVertexSimpleProjectiveResolution k Q i).isMinimal
    (fun _ => integerGrade_eq_bot_of_neg k Q)

/-- Every graded vertex simple of a finite-vertex quiver admits a linear graded projective
resolution. -/
theorem exists_isLinear_gradedVertexSimple (i : Q) :
    ∃ r : GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q i).grading, r.IsLinear :=
  ⟨gradedVertexSimpleProjectiveResolution k Q i,
    isLinear_gradedVertexSimpleProjectiveResolution k Q i⟩

/-! ### Grothendieck classes of the resolution terms -/

/-- In `K₀^gr(proj kQ)`, the degree-`0` term of the resolution of `Sᵢ` has class `[kQ eᵢ]`. -/
@[simp]
theorem laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_zero (i : Q) :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm 0) =
      gradedVertexProjectiveClass k Q i := by
  rw [gradedVertexProjectiveClass_eq]
  exact congrArg (LaurentK0.of _)
    (ObjectProperty.FullSubcategory.ext
      (GradedProjectiveResolution.finiteProjectiveTerm_obj _ 0))

/-- From homological degree `2` on, the terms of the resolution of `Sᵢ` have class `0` in
`K₀^gr(proj kQ)`. -/
@[simp]
theorem laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_add_two
    (i : Q) (n : ℕ) :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm (n + 2)) = 0 := by
  have : Subsingleton
      ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm (n + 2)).obj := by
    rw [GradedProjectiveResolution.finiteProjectiveTerm_obj]
    infer_instance
  exact laurentK0_projective_of_eq_zero_of_subsingleton _

/-- The class of `gradedArrowSum k Q i` in `K₀^gr(proj kQ)` is `q` times the sum of `[kQ eⱼ]`
over all outgoing arrows `a : i ⟶ j`. -/
theorem laurentK0_projective_gradedArrowSum (i : Q) [Fintype ((j : Q) × (i ⟶ j))] :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ⟨gradedArrowSum k Q i, gradedFiniteProjectiveModules_gradedArrowSum k Q i⟩ =
      (T 1 : LaurentPolynomial ℤ) •
        ∑ a : (j : Q) × (i ⟶ j), gradedVertexProjectiveClass k Q a.1 := by
  let summand (a : (j : Q) × (i ⟶ j)) :
      (gradedFiniteProjectiveModules (integerGrade k Q)).FullSubcategory :=
    ⟨(gradedVertexProjective k Q a.1).shiftObj 1,
      gradedFiniteProjectiveModules_shiftObj
        (gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1) 1⟩
  rw [laurentK0_projective_of_isColimit_cofan summand _
      (GradedModuleCat.coproductCofanIsColimit fun a => (summand a).obj) rfl,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simpa only [summand, gradedVertexProjectiveClass_eq] using
    laurentK0_projective_of_shiftObj
      ⟨gradedVertexProjective k Q a.1,
        gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1⟩ 1

/-- In `K₀^gr(proj kQ)`, the degree-`1` term of the resolution of `Sᵢ` has class
`q • ∑_{a : i ⟶ j} [kQ eⱼ]`. -/
theorem laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one
    (i : Q) [Fintype ((j : Q) × (i ⟶ j))] :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm 1) =
      (T 1 : LaurentPolynomial ℤ) •
        ∑ a : (j : Q) × (i ⟶ j), gradedVertexProjectiveClass k Q a.1 := by
  rw [← laurentK0_projective_gradedArrowSum k Q i]
  exact congrArg (LaurentK0.of _)
    (ObjectProperty.FullSubcategory.ext
      (GradedProjectiveResolution.finiteProjectiveTerm_obj _ 1))

end CommRing

section Fintype

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Fintype Q]

/-- Grouping outgoing arrows by target vertex expresses `[P₁(Sᵢ)]` as
`∑ⱼ (#{a : i ⟶ j} · q) • [kQ eⱼ]`. -/
theorem laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one_eq_sum
    (i : Q) [Finite ((j : Q) × (i ⟶ j))] :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm 1) =
      ∑ j : Q,
        ((Nat.card (i ⟶ j) : LaurentPolynomial ℤ) * T 1) •
          gradedVertexProjectiveClass k Q j := by
  have (j : Q) : Finite (i ⟶ j) :=
    Finite.of_injective (fun a : i ⟶ j => (⟨j, a⟩ : (j' : Q) × (i ⟶ j')))
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  let _ (j : Q) := Fintype.ofFinite (i ⟶ j)
  rw [laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one,
    Fintype.sum_sigma, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul (LaurentPolynomial ℤ), smul_smul, mul_comm]

end Fintype

/-! ### Basis coordinates of the resolution terms -/

section Field

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- In `gradedVertexProjectiveClassBasis`, the `j`th coordinate of `[P₀(Sᵢ)]` is `δᵢⱼ`. -/
theorem gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_zero
    [DecidableEq Q] (i j : Q) :
    (gradedVertexProjectiveClassBasis k Q).repr
        (LaurentK0.of.{max u v w} _
          ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm 0)) j =
      if i = j then 1 else 0 := by
  rw [laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_zero,
    gradedVertexProjectiveClassBasis_repr_gradedVertexProjectiveClass, Finsupp.single_apply]

/-- In `gradedVertexProjectiveClassBasis`, the `j`th coordinate of `[P₁(Sᵢ)]` is
`#{a : i ⟶ j} · q`: rows are projectives and columns are resolved simples, so the shift exponent
is `+1`. -/
@[simp]
theorem gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_one (i j : Q) :
    letI : ∀ a b : Q, Finite (a ⟶ b) :=
      finite_hom_of_module_finite_pathAlgebra k Q inferInstance
    (gradedVertexProjectiveClassBasis k Q).repr
        (LaurentK0.of.{max u v w} _
          ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm 1)) j =
      (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) * T 1 := by
  classical
  let _ := Fintype.ofFinite Q
  let _ : ∀ a b : Q, Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  rw [laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one_eq_sum,
    map_sum, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- From homological degree `2` on, all coordinates of `[P_{n+2}(Sᵢ)]` vanish. -/
theorem gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_add_two (i j : Q) (n : ℕ) :
    (gradedVertexProjectiveClassBasis k Q).repr
        (LaurentK0.of.{max u v w} _
          ((gradedVertexSimpleProjectiveResolution k Q i).finiteProjectiveTerm (n + 2))) j = 0 := by
  rw [laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_add_two,
    map_zero, Finsupp.zero_apply]

end Field

end TauCeti.PathAlgebra
