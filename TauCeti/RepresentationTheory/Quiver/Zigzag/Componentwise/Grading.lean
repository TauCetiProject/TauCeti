/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Decomposition

/-!
# The grading of the componentwise zigzag algebra

The public zigzag algebra carries the product grading of its connected-component factors.
On a component with an edge this is the grading descended from path length; on a singleton
it is the dual-number grading with the infinitesimal generator in degree two. The global
vertex–arrow–volume basis is homogeneous in degrees zero, one and two, respectively.

The graded pieces are submodules of the public algebra itself. Their internal direct-sum
property and multiplicativity supply a `GradedAlgebra`, including for disconnected graphs
and graphs with isolated vertices.

See Huerfano–Khovanov, *A category for the adjoint representation*, Section 3, for the
path grading and singleton convention.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The degree-`n` submodule of a component algebra, transported from its quotient or
its dual-number presentation. -/
noncomputable def zigzagComponentGrade (C : G.ConnectedComponent) (n : ℕ) :
    Submodule k (zigzagComponentAlgebra k G C) := by
  classical
  by_cases hC : Nontrivial C
  · letI := hC
    exact (zigzagGrade k C.toSimpleGraph n).comap
      (zigzagComponentAlgebraEquivNonisolated k G C).toLinearMap
  · letI : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    exact (dualNumberGrade k n).comap
      ((zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
        (ULift.algEquiv (R := k) (A := DualNumber k))).toLinearMap

/-- On a nontrivial component, homogeneous membership is detected in the relation quotient. -/
@[simp]
theorem mem_zigzagComponentGrade_of_nontrivial (C : G.ConnectedComponent) [Nontrivial C]
    {n : ℕ} {x : zigzagComponentAlgebra k G C} :
    x ∈ zigzagComponentGrade k G C n ↔
      zigzagComponentAlgebraEquivNonisolated k G C x ∈ zigzagGrade k C.toSimpleGraph n := by
  classical
  simp [zigzagComponentGrade, (inferInstance : Nontrivial C)]

/-- On a singleton component, homogeneous membership is detected in the dual numbers. -/
@[simp]
theorem mem_zigzagComponentGrade_of_subsingleton (C : G.ConnectedComponent) [Subsingleton C]
    {n : ℕ} {x : zigzagComponentAlgebra k G C} :
    x ∈ zigzagComponentGrade k G C n ↔
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down ∈ dualNumberGrade k n := by
  classical
  simp [zigzagComponentGrade,
    not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton C)]

/-- Multiplication in a component adds degrees, and its unit has degree zero. -/
instance (C : G.ConnectedComponent) : SetLike.GradedMonoid (zigzagComponentGrade k G C) where
  one_mem := by
    rcases subsingleton_or_nontrivial C with hC | hC
    · simp
    · let := zigzagGradedAlgebra k C.toSimpleGraph
      simpa using (SetLike.GradedOne.one_mem (A := zigzagGrade k C.toSimpleGraph))
  mul_mem m n x y hx hy := by
    rcases subsingleton_or_nontrivial C with hC | hC
    · simp only [mem_zigzagComponentGrade_of_subsingleton] at hx hy ⊢
      simpa using mul_mem_dualNumberGrade k hx hy
    · simp only [mem_zigzagComponentGrade_of_nontrivial] at hx hy ⊢
      simpa using mul_mem_zigzagGrade k C.toSimpleGraph hx hy

/-- Every component grade above degree two vanishes. -/
theorem zigzagComponentGrade_eq_bot_of_three_le (C : G.ConnectedComponent)
    {n : ℕ} (hn : 3 ≤ n) : zigzagComponentGrade k G C n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  rcases subsingleton_or_nontrivial C with hC | hC
  · rw [mem_zigzagComponentGrade_of_subsingleton,
      dualNumberGrade_eq_bot k (by omega) (by omega), Submodule.mem_bot] at hx
    apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
    rw [map_zero]
    exact ULift.ext _ _ hx
  · rw [mem_zigzagComponentGrade_of_nontrivial,
      zigzagGrade_eq_bot_of_three_le k C.toSimpleGraph hn, Submodule.mem_bot] at hx
    exact (zigzagComponentAlgebraEquivNonisolated k G C).map_eq_zero_iff.mp hx

/-- The componentwise degree-`n` submodule of the public zigzag algebra. -/
noncomputable def zigzagAlgebraGrade (n : ℕ) : Submodule k (zigzagAlgebra k G) :=
  ⨅ C, (zigzagComponentGrade k G C n).comap (zigzagComponentProjection k G C).toLinearMap

/-- An element is homogeneous exactly when every component has the same degree. -/
theorem mem_zigzagAlgebraGrade {n : ℕ} {x : zigzagAlgebra k G} :
    x ∈ zigzagAlgebraGrade k G n ↔
      ∀ C, zigzagComponentProjection k G C x ∈ zigzagComponentGrade k G C n := by
  simp [zigzagAlgebraGrade]

/-- The public algebra has no homogeneous pieces in degrees three and above. -/
theorem zigzagAlgebraGrade_eq_bot_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    zigzagAlgebraGrade k G n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply zigzagAlgebra.ext
  intro C
  have hC := (mem_zigzagAlgebraGrade k G).mp hx C
  simpa [zigzagComponentGrade_eq_bot_of_three_le k G C hn] using hC

/-- The componentwise grading respects the unit and multiplication of the public algebra. -/
instance : SetLike.GradedMonoid (zigzagAlgebraGrade k G) where
  one_mem := by simp [mem_zigzagAlgebraGrade, SetLike.GradedOne.one_mem]
  mul_mem m n x y hx hy := by
    rw [mem_zigzagAlgebraGrade] at hx hy ⊢
    intro C
    rw [map_mul]
    exact SetLike.mul_mem_graded (hx C) (hy C)

private theorem zigzagComponentBasis_mem (C : G.ConnectedComponent)
    (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b ∈ zigzagComponentGrade k G C
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2)) b) := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · rcases b with i | d | i
    · simp
    · exact (C.toSimpleGraph.ne_of_adj d.adj (Subsingleton.elim _ _)).elim
    · simp
  · have hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
      SimpleGraph.exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    rw [mem_zigzagComponentGrade_of_nontrivial,
      zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns, zigzagBasis_apply]
    rcases b with i | d | i
    · simp only [zigzagBasisFun_inl, Sum.elim_inl]
      exact zigzagMk_mem_zigzagGrade k C.toSimpleGraph
        (PathAlgebra.vertexIdempotent_mem_grade_zero _)
    · simp only [zigzagBasisFun_inr_inl, Sum.elim_inr, Sum.elim_inl]
      exact zigzagMk_mem_zigzagGrade k C.toSimpleGraph (PathAlgebra.ofArrow_mem_grade_one _)
    · simp only [zigzagBasisFun_inr_inr, Sum.elim_inr]
      exact (zigzagGrade_two_eq_span_range_zigzagVolume k C.toSimpleGraph).symm ▸
        Submodule.subset_span ⟨i, rfl⟩

private theorem zigzagAlgebraBasis_mem (b : ZigzagBasisIndex G) :
    zigzagAlgebraBasis k G b ∈ zigzagAlgebraGrade k G
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2)) b) := by
  obtain ⟨⟨C, b⟩, rfl⟩ := (zigzagComponentBasisIndexEquiv G).surjective b
  rw [mem_zigzagAlgebraGrade]
  intro D
  by_cases h : D = C
  · subst D
    rw [zigzagComponentProjection_zigzagAlgebraBasis]
    have hb := zigzagComponentBasis_mem k G C b
    rcases b with i | d | i <;>
      simpa only [zigzagComponentBasisIndexEquiv_inl, zigzagComponentBasisIndexEquiv_inr_inl,
        zigzagComponentBasisIndexEquiv_inr_inr, Sum.elim_inl, Sum.elim_inr] using hb
  · rw [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C D h]
    exact Submodule.zero_mem _

/-- The global vertex basis vectors have degree zero. -/
@[simp]
theorem zigzagAlgebraBasis_inl_mem_grade_zero (i : V) :
    zigzagAlgebraBasis k G (.inl i) ∈ zigzagAlgebraGrade k G 0 :=
  zigzagAlgebraBasis_mem k G (.inl i)

/-- The global arrow basis vectors have degree one. -/
@[simp]
theorem zigzagAlgebraBasis_inr_inl_mem_grade_one (d : G.Dart) :
    zigzagAlgebraBasis k G (.inr (.inl d)) ∈ zigzagAlgebraGrade k G 1 :=
  zigzagAlgebraBasis_mem k G (.inr (.inl d))

/-- The global volume basis vectors have degree two, including at isolated vertices. -/
@[simp]
theorem zigzagAlgebraBasis_inr_inr_mem_grade_two (i : V) :
    zigzagAlgebraBasis k G (.inr (.inr i)) ∈ zigzagAlgebraGrade k G 2 :=
  zigzagAlgebraBasis_mem k G (.inr (.inr i))

private theorem iSupIndep_zigzagComponentGrade (C : G.ConnectedComponent) :
    iSupIndep (zigzagComponentGrade k G C) := by
  classical
  unfold zigzagComponentGrade
  rcases subsingleton_or_nontrivial C with hC | hC
  · let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    simpa only [Function.comp_def, Submodule.orderIsoMapComap_symm_apply,
      dite_eq_right (not_nontrivial_iff_subsingleton.mpr hC)] using
      (isInternal_dualNumberGrade k).submodule_iSupIndep.map_orderIso
        (Submodule.orderIsoMapComap e.toLinearEquiv).symm
  · simpa only [Function.comp_def, Submodule.orderIsoMapComap_symm_apply,
      dite_eq_left hC] using
      (isInternal_zigzagGrade k C.toSimpleGraph).submodule_iSupIndep.map_orderIso
        (Submodule.orderIsoMapComap
          (zigzagComponentAlgebraEquivNonisolated k G C).toLinearEquiv).symm

/-- The public zigzag algebra is the internal direct sum of its componentwise graded pieces. -/
theorem isInternal_zigzagAlgebraGrade : DirectSum.IsInternal (zigzagAlgebraGrade k G) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s x hx hsum n hn
    apply zigzagAlgebra.ext
    intro C
    rw [map_zero]
    exact ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      (iSupIndep_zigzagComponentGrade k G C)) s
      (fun j => zigzagComponentProjection k G C (x j))
      (fun j hj => (mem_zigzagAlgebraGrade k G).mp (hx j hj) C)
      (by rw [← map_sum, hsum, map_zero]) n hn
  · rw [eq_top_iff, ← (zigzagAlgebraBasis k G).span_eq, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact (le_iSup (zigzagAlgebraGrade k G) _) (zigzagAlgebraBasis_mem k G b)

/-- The product grading on the public algebra, including the degree-two singleton generators.
Install this structure locally to use Mathlib's graded-algebra projections and direct-sum
algebra equivalence. -/
@[instance_reducible]
noncomputable def zigzagAlgebraGradedAlgebra : GradedAlgebra (zigzagAlgebraGrade k G) :=
  DirectSum.IsInternal.gradedAlgebra (isInternal_zigzagAlgebraGrade k G)

end TauCeti
