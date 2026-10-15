/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Quadratic.Dual
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Quadratic.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading

/-!
# The graded quadratic dual of a zigzag presentation

The existing identification of the quadratic dual of the quadratic zigzag presentation with
the signless preprojective algebra preserves the induced path-length grading in both directions.
It therefore identifies their degree submodules, not only their underlying algebras. The
degreewise linear equivalences support graded dimension and Koszul comparisons.

The relation space presents the strict zigzag algebra for connected graphs with at least three
vertices. The grading comparison itself needs neither connectedness nor a vertex bound: it
concerns the quadratic presentation even when that presentation differs from the exceptional
one-vertex or one-edge zigzag algebra. In particular it does not assert Koszulity in those cases.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Section 6.1, for the
  zigzag quadratic-dual calculation. The underlying algebra comparison is
  `TauCeti.quadraticDualQuadraticZigzagEquivSignless`.
* Polishchuk--Positselski, *Quadratic algebras*, Chapter 1, Section 2, for graded quadratic
  duality over a semisimple vertex algebra.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) [CommRing k] [Finite V]
  [∀ v : V, Fintype (G.neighborSet v)]

local notation "D" => quadraticDual k (DoubledQuiver G) (quadraticZigzagRelations k G)
local notation "DGrade" => quadraticDualGrade k (DoubledQuiver G) (quadraticZigzagRelations k G)
local notation "SGrade" => signlessPreprojectiveGrade k (DoubledQuiver G)
local notation "E" => quadraticDualQuadraticZigzagEquivSignless k G

/-- The quadratic-dual identification carries a homogeneous class to the same path degree
in the signless preprojective algebra. -/
theorem quadraticDualQuadraticZigzagEquivSignless_mem_grade {n : ℕ} {x : D}
    (hx : x ∈ DGrade n) : E x ∈ SGrade n := by
  obtain ⟨y, hy, rfl⟩ := (mem_quadraticDualGrade_iff _ _ _).1 hx
  rw [quadraticDualQuadraticZigzagEquivSignless_quadraticDualMk]
  exact signlessPreprojectiveMk_mem_grade _ _ (reverseOpAlgEquiv_symm_mem_grade _ _ hy)

/-- The inverse quadratic-dual identification also preserves path degree. -/
theorem quadraticDualQuadraticZigzagEquivSignless_symm_mem_grade {n : ℕ}
    {x : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hx : x ∈ SGrade n) : (E).symm x ∈ DGrade n := by
  obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff _ _).1 hx
  rw [quadraticDualQuadraticZigzagEquivSignless_symm_signlessPreprojectiveMk]
  exact quadraticDualMk_mem_grade _ _ _ (reverseOpAlgEquiv_mem_opGrade _ _ hy)

/-- The quadratic-dual comparison preserves and reflects each induced path-length piece.
This is a named rewrite: `mem_signlessPreprojectiveGrade_iff` already simplifies its left side. -/
theorem quadraticDualQuadraticZigzagEquivSignless_mem_grade_iff {n : ℕ} {x : D} :
    E x ∈ SGrade n ↔ x ∈ DGrade n := by
  constructor
  · intro hx
    simpa only [AlgEquiv.symm_apply_apply] using
      quadraticDualQuadraticZigzagEquivSignless_symm_mem_grade k G hx
  · exact quadraticDualQuadraticZigzagEquivSignless_mem_grade k G

/-- The inverse comparison preserves and reflects each path-length piece.
This is a named rewrite: `mem_quadraticDualGrade_iff` already simplifies its left side. -/
theorem quadraticDualQuadraticZigzagEquivSignless_symm_mem_grade_iff {n : ℕ}
    {x : signlessPreprojectiveAlgebra k (DoubledQuiver G)} :
    (E).symm x ∈ DGrade n ↔ x ∈ SGrade n := by
  rw [← quadraticDualQuadraticZigzagEquivSignless_mem_grade_iff k G,
    AlgEquiv.apply_symm_apply]

/-- The image of the degree-`n` quadratic-dual submodule is exactly the degree-`n` signless
preprojective submodule. -/
@[simp]
theorem map_quadraticDualGrade_quadraticZigzagEquivSignless (n : ℕ) :
    (DGrade n).map (E).toLinearMap = SGrade n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact quadraticDualQuadraticZigzagEquivSignless_mem_grade k G hy
  · intro hx
    exact ⟨(E).symm x, quadraticDualQuadraticZigzagEquivSignless_symm_mem_grade k G hx,
      (E).apply_symm_apply x⟩

/-- The quadratic-dual comparison restricts to a linear equivalence in every path degree. -/
noncomputable def quadraticDualQuadraticZigzagGradeEquivSignless (n : ℕ) :
    DGrade n ≃ₗ[k] SGrade n :=
  (Submodule.equivMapOfInjective (E).toLinearMap (E).injective (DGrade n)).trans
    (LinearEquiv.ofEq _ _ (map_quadraticDualGrade_quadraticZigzagEquivSignless k G n))

/-- The degreewise equivalence is the restriction of the existing algebra equivalence. -/
@[simp]
theorem coe_quadraticDualQuadraticZigzagGradeEquivSignless_apply (n : ℕ) (x : DGrade n) :
    (quadraticDualQuadraticZigzagGradeEquivSignless k G n x :
      signlessPreprojectiveAlgebra k (DoubledQuiver G)) = E x := by
  exact Submodule.coe_equivMapOfInjective_apply (E).toLinearMap (E).injective (DGrade n) x

/-- The inverse degreewise equivalence restricts the inverse algebra comparison. -/
@[simp]
theorem coe_quadraticDualQuadraticZigzagGradeEquivSignless_symm_apply (n : ℕ)
    (x : SGrade n) :
    ((quadraticDualQuadraticZigzagGradeEquivSignless k G n).symm x : D) = (E).symm x := by
  apply (E).injective
  rw [← coe_quadraticDualQuadraticZigzagGradeEquivSignless_apply,
    LinearEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end TauCeti
