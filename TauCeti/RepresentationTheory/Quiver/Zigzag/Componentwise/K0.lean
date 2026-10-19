/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.CartanMap
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Idempotents
-- Idempotent.Projective imports this privately; the brick criterion is needed below.
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# Class bases and the graded Cartan map of the componentwise zigzag algebra

The graded vertex projectives of the public zigzag algebra form a basis of its actual
Laurent Grothendieck group of finite graded projectives. This includes isolated vertices,
whose projectives retain the degree-two generator of the dual-number factor. These are
the projectives on which the zigzag braid complexes act, rather than projectives of the
relation quotient with its different isolated-vertex convention.

The graded Cartan map sends a vertex-projective class to a class with coordinate `1 + q²`
at that vertex, `q` at adjacent vertices, and zero elsewhere. The heads of the vertex projectives
form the simple-class basis of the graded module Grothendieck group, with the idempotent
coordinates as its coordinates. Thus the matrix of the categorical graded Cartan map in these
two bases is `(1 + q²) I + q A_G`, including its dual-number diagonal entries at isolated vertices.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Sections 3 and 4.6.
* Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
* The graded Krull–Schmidt and simple-head basis constructions are
  `TauCeti.gradedIndecomposableProjectiveClassBasis` and `TauCeti.gradedIdempotentHeadBasis`.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Pointwise

universe u w
variable (k : Type w) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "A" => zigzagAlgebraIntegerGrade k G
local notation "P" => zigzagAlgebraGradedProjective k G

open scoped Classical in
/-- Degree-preserving maps between vertex projectives are scalar endomorphisms at the same
vertex and vanish between distinct vertices. -/
theorem finrank_zigzagAlgebraGradedProjective_hom (i j : V) :
    Module.finrank k (P i ⟶ P j) = if i = j then 1 else 0 := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  rw [(GradedModuleCat.ofIdealSpanSingletonHomEquiv
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G i) (P j)).finrank_eq]
  have h := coeff_smulGradedDimension_zigzagAlgebraGradedProjective k G i j 0
  rw [GradedModuleCat.coeff_smulGradedDimension] at h
  exact_mod_cast (by simpa using h :
    (Module.finrank k ↥(e i • (P j).grading.piece 0) : ℤ) = if i = j then 1 else 0)

/-- Every vertex projective of the public algebra is indecomposable as a finite graded
projective, including the dual-number projective at an isolated vertex. -/
theorem indecomposable_zigzagAlgebraGradedProjective (i : V) :
    Indecomposable (⟨P i, gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩ :
      (gradedFiniteProjectiveModules A).FullSubcategory) := by
  apply indecomposable_of_finrank_end_eq_one (k := k)
  let Q : (gradedFiniteProjectiveModules A).FullSubcategory :=
    ⟨P i, gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩
  calc
    Module.finrank k (Q ⟶ Q) = Module.finrank k (P i ⟶ P i) :=
      (InducedCategory.homLinearEquiv (R := k) (X := Q) (Y := Q)).finrank_eq
    _ = 1 := by simp [finrank_zigzagAlgebraGradedProjective_hom]

/-- Distinct vertex projectives of the public algebra cannot become isomorphic after an
internal shift. -/
theorem isEmpty_iso_zigzagAlgebraGradedProjective_shiftObj {i j : V} (hij : i ≠ j) (d : ℤ) :
    IsEmpty (P i ≅ (P j).shiftObj d) := by
  classical
  refine ⟨fun f ↦ ?_⟩
  have h := GradedModuleCat.smulGradedDimension_congr (e i) f
  rw [GradedModuleCat.smulGradedDimension_shiftObj,
    smulGradedDimension_zigzagAlgebraGradedProjective,
    smulGradedDimension_zigzagAlgebraGradedProjective] at h
  simp only [ite_true, hij, ite_false] at h
  have heval := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)) h
  by_cases hadj : G.Adj i j <;>
    simp only [hadj, ite_true, ite_false, map_add, map_one, map_mul, map_zero,
      LaurentPolynomial.eval₂_T, one_zpow, Units.val_one] at heval <;>
    norm_num at heval

/-- Every finite graded indecomposable projective of the public zigzag algebra is an internal
shift of a vertex projective. -/
theorem isExhaustiveGradedIndecomposableProjectiveFamily_zigzagAlgebraGradedProjective :
    IsExhaustiveGradedIndecomposableProjectiveFamily (fun i : V ↦
      ⟨P i, gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  exact isExhaustiveGradedIndecomposableProjectiveFamily_of_completeOrthogonalIdempotents
    (completeOrthogonalIdempotents_zigzagAlgebraBasis_inl k G)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G)
    (indecomposable_zigzagAlgebraGradedProjective k G)

/-- The vertex-projective class basis of `K₀^gr(proj Z)` for the public componentwise algebra.
Its Laurent scalar action represents internal grading shifts. -/
def zigzagAlgebraGradedProjectiveClassBasis :
    Module.Basis V (LaurentPolynomial ℤ)
      (LaurentK0.{max u w} (gradedFiniteProjectiveModulesExactStructure A)) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  exact gradedIndecomposableProjectiveClassBasis
    (fun i ↦ ⟨P i, gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩)
    (indecomposable_zigzagAlgebraGradedProjective k G)
    (fun i j hij d ↦ ⟨fun f ↦
      (isEmpty_iso_zigzagAlgebraGradedProjective_shiftObj k G hij d).false
        ((gradedFiniteProjectiveModules A).ι.mapIso f)⟩)
    (isExhaustiveGradedIndecomposableProjectiveFamily_zigzagAlgebraGradedProjective k G)

/-- The basis vector at a vertex is the class of its actual graded vertex projective. -/
@[simp]
theorem zigzagAlgebraGradedProjectiveClassBasis_apply (i : V) :
    zigzagAlgebraGradedProjectiveClassBasis k G i =
      zigzagAlgebraGradedProjectiveClass k G i := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  rw [zigzagAlgebraGradedProjectiveClass_def]
  unfold zigzagAlgebraGradedProjectiveClassBasis
  exact gradedIndecomposableProjectiveClassBasis_apply _ _ _ _ i

/-- The coordinate of a vertex-projective class is the corresponding coordinate vector. -/
@[simp]
theorem zigzagAlgebraGradedProjectiveClassBasis_repr_class (i : V) :
    (zigzagAlgebraGradedProjectiveClassBasis k G).repr
      (zigzagAlgebraGradedProjectiveClass k G i) = Finsupp.single i 1 := by
  rw [← zigzagAlgebraGradedProjectiveClassBasis_apply]
  exact Module.Basis.repr_self _ i

/-! ### The simple-class basis and the categorical Cartan matrix -/

/-- The graded head of the public vertex projective, obtained by killing its positive-degree
part. At an isolated vertex this kills the degree-two dual-number generator. -/
def zigzagAlgebraGradedSimple (i : V) : GradedModuleCat.{max u w} A :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedPositiveMulQuotient A (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)

/-- A graded vertex simple is the generic graded head of its vertex idempotent. -/
theorem zigzagAlgebraGradedSimple_def (i : V) :
    zigzagAlgebraGradedSimple k G i =
      let _ := zigzagAlgebraIntegerGradedAlgebra k G
      gradedPositiveMulQuotient A (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i) := by
  rw [zigzagAlgebraGradedSimple]

/-- The class of a vertex-projective element in its graded simple head. -/
def zigzagAlgebraGradedSimpleMk (i : V) :
    (Ideal.span {e i} : Ideal (zigzagAlgebra k G)) →ₗ[zigzagAlgebra k G]
      zigzagAlgebraGradedSimple k G i :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedPositiveMulQuotientMk (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)

/-- Every element of the graded simple head has a vertex-projective representative. -/
theorem zigzagAlgebraGradedSimpleMk_surjective (i : V) :
    Function.Surjective (zigzagAlgebraGradedSimpleMk k G i) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedPositiveMulQuotientMk_surjective _

/-- A representative vanishes in the graded head exactly when it lies in the
positive-degree ideal of its vertex projective. -/
@[simp]
theorem zigzagAlgebraGradedSimpleMk_eq_zero_iff (i : V)
    (x : (Ideal.span {e i} : Ideal (zigzagAlgebra k G))) :
    zigzagAlgebraGradedSimpleMk k G i x = 0 ↔
      (x : zigzagAlgebra k G) ∈ gradedPositiveMulIdeal A (e i) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedPositiveMulQuotientMk_eq_zero_iff _ x

/-- The head projection sends a homogeneous representative of degree `p` to the
degree-`p` piece of the graded vertex simple. -/
theorem zigzagAlgebraGradedSimpleMk_mem_piece (i : V) {p : ℤ}
    (x : (Ideal.span {e i} : Ideal (zigzagAlgebra k G)))
    (hx : (x : zigzagAlgebra k G) ∈ A p) :
    zigzagAlgebraGradedSimpleMk k G i x ∈
      (zigzagAlgebraGradedSimple k G i).grading.piece p := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  exact (mem_gradedPositiveMulQuotient_piece_iff _).2 ⟨x, hx, rfl⟩

/-- The head of a public vertex projective is a finite graded module. -/
theorem gradedFiniteModules_zigzagAlgebraGradedSimple (i : V) :
    gradedFiniteModules A (zigzagAlgebraGradedSimple k G i) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedFiniteModules_gradedPositiveMulQuotient A
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)

/-- Each graded vertex head of the public algebra is simple. -/
theorem simple_zigzagAlgebraGradedSimple (i : V) :
    Simple (zigzagAlgebraGradedSimple k G i) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  exact simple_gradedIdempotentHead
    (fun _ ↦ zigzagAlgebraIntegerGrade_eq_bot_of_neg k G)
    (completeOrthogonalIdempotents_zigzagAlgebraBasis_inl k G).toOrthogonalIdempotents
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G)
    (zigzagAlgebraIntegerGrade_zero_eq_span_range k G).le i
    ((zigzagAlgebraBasis k G).ne_zero (.inl i))

/-- A graded vertex simple is finite-dimensional. -/
instance (i : V) : Module.Finite k (zigzagAlgebraGradedSimple k G i) :=
  have : Module.Finite (zigzagAlgebra k G) (zigzagAlgebraGradedSimple k G i) :=
    gradedFiniteModules_iff.1 (gradedFiniteModules_zigzagAlgebraGradedSimple k G i)
  Module.Finite.trans (zigzagAlgebra k G) _

/-- The graded vertex simple is concentrated in degree zero, with dimension one at its own
vertex and zero at every other vertex. -/
@[simp]
theorem smulGradedDimension_zigzagAlgebraGradedSimple [DecidableEq V] (j i : V) :
    (zigzagAlgebraGradedSimple k G i).smulGradedDimension (e j) =
      if j = i then 1 else 0 := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  exact smulGradedDimension_gradedIdempotentHead
    (fun _ ↦ zigzagAlgebraIntegerGrade_eq_bot_of_neg k G)
    (completeOrthogonalIdempotents_zigzagAlgebraBasis_inl k G).toOrthogonalIdempotents
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G)
    (zigzagAlgebraIntegerGrade_zero_eq_span_range k G).le j i
    ((zigzagAlgebraBasis k G).ne_zero (.inl i))

/-- The vertex-head class basis of `G₀^gr(mod Z)` for the public componentwise zigzag algebra. -/
def zigzagAlgebraGradedSimpleClassBasis :
    Module.Basis V (LaurentPolynomial ℤ)
      (LaurentK0.{max u w} (gradedFiniteModulesExactStructure A)) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  exact gradedIdempotentHeadBasis
    (fun _ ↦ zigzagAlgebraIntegerGrade_eq_bot_of_neg k G)
    (completeOrthogonalIdempotents_zigzagAlgebraBasis_inl k G)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G)
    (zigzagAlgebraIntegerGrade_zero_eq_span_range k G).le
    (fun i ↦ (zigzagAlgebraBasis k G).ne_zero (.inl i))

/-- The simple-class basis vector is the class of the graded head at that vertex. -/
@[simp]
theorem zigzagAlgebraGradedSimpleClassBasis_apply (i : V) :
    zigzagAlgebraGradedSimpleClassBasis k G i =
      LaurentK0.of _ ⟨zigzagAlgebraGradedSimple k G i,
        gradedFiniteModules_zigzagAlgebraGradedSimple k G i⟩ := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  unfold zigzagAlgebraGradedSimpleClassBasis
  exact gradedIdempotentHeadBasis_apply _ _ _ _ _ i

/-- The simple-class coordinates are the graded dimensions of the vertex-idempotent pieces. -/
@[simp]
theorem zigzagAlgebraGradedSimpleClassBasis_repr_apply
    (x : LaurentK0.{max u w} (gradedFiniteModulesExactStructure A)) (i : V) :
    (zigzagAlgebraGradedSimpleClassBasis k G).repr x i =
      gradedIdempotentCoordinate (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i) x := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  unfold zigzagAlgebraGradedSimpleClassBasis
  exact gradedIdempotentHeadBasis_repr_apply _ _ _ _ _ x i

open scoped Classical in
/-- Entrywise, the categorical Cartan map records `1 + q²` at the projective's vertex,
`q` at an adjacent vertex, and zero otherwise. -/
theorem zigzagAlgebraGradedSimpleClassBasis_repr_gradedCartanMap (i j : V) :
    (zigzagAlgebraGradedSimpleClassBasis k G).repr
        (gradedCartanMap A (zigzagAlgebraGradedProjectiveClass k G j)) i =
      if i = j then 1 + T 2 else if G.Adj i j then T 1 else 0 := by
  rw [zigzagAlgebraGradedSimpleClassBasis_repr_apply,
    gradedIdempotentCoordinate_gradedCartanMap_zigzagAlgebraGradedProjectiveClass]

/-- The categorical graded Cartan map of the public algebra has matrix `(1 + q²) I + q A_G`
in the vertex-projective and vertex-head class bases, including isolated vertices. -/
theorem gradedCartanMatrix_zigzagAlgebra [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    gradedCartanMatrix A (zigzagAlgebraGradedProjectiveClassBasis k G)
        (zigzagAlgebraGradedSimpleClassBasis k G) =
      (1 + T 2 : LaurentPolynomial ℤ) • (1 : Matrix V V (LaurentPolynomial ℤ)) +
        (T 1 : LaurentPolynomial ℤ) • G.adjMatrix (LaurentPolynomial ℤ) := by
  ext i j
  rw [gradedCartanMatrix_apply, zigzagAlgebraGradedProjectiveClassBasis_apply,
    zigzagAlgebraGradedSimpleClassBasis_repr_gradedCartanMap]
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.adjMatrix_apply]
  · by_cases hadj : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, hij, hadj]

end TauCeti
