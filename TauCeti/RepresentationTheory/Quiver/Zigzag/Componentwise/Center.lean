/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Center
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading

/-!
# A homogeneous basis of the center of the public zigzag algebra

The center of the zigzag algebra of a finite simple graph has one degree-zero basis vector
for each connected component and one degree-two basis vector for each vertex. The former is
the unit supported on that component; the latter is its vertex volume. At an isolated vertex
the volume is the infinitesimal generator of the dual numbers, rather than a zero backtrack.

We transport the connected quotient's center basis on components with an edge, use the
whole dual-number algebra on singleton components, and assemble these bases with `Pi.basis`
and `centerPiAlgEquiv`. Projection and coordinate formulas identify the resulting basis
without unfolding its construction.

See Huerfano–Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig–Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

omit [Finite V] in
private noncomputable def singletonCenterIndexEquiv (C : G.ConnectedComponent)
    [Subsingleton C] : Option C ≃ Fin 2 := by
  letI : Unique C := ⟨⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩,
    fun _ => Subsingleton.elim _ _⟩
  exact (Equiv.optionCongr (Equiv.ofUnique C (Fin 1))).trans (finSuccEquiv 1).symm

/-- The unit and vertex volumes form a basis of the center of a connected-component factor,
including a singleton dual-number factor. -/
noncomputable def zigzagComponentCenterBasis (C : G.ConnectedComponent) :
    Module.Basis (Option C) k (Subalgebra.center k (zigzagComponentAlgebra k G C)) := by
  classical
  by_cases hC : Nontrivial C
  · letI := hC
    letI : Fintype C := Fintype.ofFinite C
    exact (zigzagCenterBasis k C.toSimpleGraph C.connected_toSimpleGraph.preconnected).map
      (centerCongr (zigzagComponentAlgebraEquivNonisolated k G C)).symm.toLinearEquiv
  · letI : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    exact (((Module.Basis.finTwoProd k).reindex (singletonCenterIndexEquiv G C).symm).map
      ULift.moduleEquiv.symm).map (centerZigzagComponentAlgebraSubsingletonLinearEquiv k G C).symm

/-- The distinguished degree-zero vector is the component's unit. -/
@[simp]
theorem zigzagComponentCenterBasis_none (C : G.ConnectedComponent) :
    (zigzagComponentCenterBasis k G C none : zigzagComponentAlgebra k G C) = 1 := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · simp only [zigzagComponentCenterBasis, dite_eq_right
      (not_nontrivial_iff_subsingleton.mpr hC), Module.Basis.map_apply,
      Module.Basis.reindex_apply, Equiv.symm_symm]
    apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
    rw [← centerZigzagComponentAlgebraSubsingletonLinearEquiv_apply,
      LinearEquiv.apply_symm_apply]
    simp only [singletonCenterIndexEquiv, Equiv.trans_apply, Equiv.optionCongr_apply,
      Option.map_none, finSuccEquiv_symm_none,
      Module.Basis.finTwoProd_zero, ULift.moduleEquiv_symm_apply, map_one]
    rfl
  · simp [zigzagComponentCenterBasis, hC, zigzagCenterFun_none]

/-- The other center vectors are exactly the volume vectors in the component algebra basis. -/
@[simp]
theorem zigzagComponentCenterBasis_some (C : G.ConnectedComponent) (i : C) :
    (zigzagComponentCenterBasis k G C (some i) : zigzagComponentAlgebra k G C) =
      zigzagComponentBasis k G C (.inr (.inr i)) := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · simp only [zigzagComponentCenterBasis, dite_eq_right
      (not_nontrivial_iff_subsingleton.mpr hC), Module.Basis.map_apply,
      Module.Basis.reindex_apply, Equiv.symm_symm]
    apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
    rw [zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]
    rw [← centerZigzagComponentAlgebraSubsingletonLinearEquiv_apply,
      LinearEquiv.apply_symm_apply]
    simp only [singletonCenterIndexEquiv, Equiv.trans_apply, Equiv.optionCongr_apply,
      Option.map_some, Equiv.ofUnique_apply, Pi.default_apply,
      finSuccEquiv_symm_some,
      ULift.moduleEquiv_symm_apply]
    have hz : (default : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact congrArg ULift.up (Module.Basis.finTwoProd_one k)
  · let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
      SimpleGraph.exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    apply (zigzagComponentAlgebraEquivNonisolated k G C).injective
    simp [zigzagComponentCenterBasis, hC,
      zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns,
      zigzagCenterFun_some, zigzagBasisFun_inr_inr]

omit [Finite V] in
private def componentCenterIndexEquiv :
    (Σ C : G.ConnectedComponent, Option C) ≃ G.ConnectedComponent ⊕ V where
  toFun b := b.2.elim (.inl b.1) (fun i => .inr i.val)
  invFun := Sum.elim (fun C => ⟨C, none⟩)
    (fun i => ⟨G.connectedComponentMk i, some ⟨i, rfl⟩⟩)
  left_inv := by
    rintro ⟨C, _ | ⟨i, hi⟩⟩
    · rfl
    · subst C; rfl
  right_inv := by rintro (C | i) <;> rfl

/-- The center of the public algebra, decomposed as the product of the component centers. -/
noncomputable def zigzagAlgebraCenterPiAlgEquiv :
    Subalgebra.center k (zigzagAlgebra k G) ≃ₐ[k]
      ∀ C : G.ConnectedComponent, Subalgebra.center k (zigzagComponentAlgebra k G C) :=
  (centerCongr (zigzagAlgebraPiAlgEquiv k G)).trans centerPiAlgEquiv

/-- The center decomposition reads the ordinary component projections. -/
@[simp]
theorem zigzagAlgebraCenterPiAlgEquiv_apply_coe
    (x : Subalgebra.center k (zigzagAlgebra k G)) (C : G.ConnectedComponent) :
    (zigzagAlgebraCenterPiAlgEquiv k G x C : zigzagComponentAlgebra k G C) =
      zigzagComponentProjection k G C x := by
  simp [zigzagAlgebraCenterPiAlgEquiv]

/-- The inverse center decomposition assembles the prescribed central components. -/
@[simp]
theorem zigzagComponentProjection_zigzagAlgebraCenterPiAlgEquiv_symm
    (x : ∀ C : G.ConnectedComponent, Subalgebra.center k (zigzagComponentAlgebra k G C))
    (C : G.ConnectedComponent) :
    zigzagComponentProjection k G C ((zigzagAlgebraCenterPiAlgEquiv k G).symm x) = x C := by
  rw [← zigzagAlgebraCenterPiAlgEquiv_apply_coe, AlgEquiv.apply_symm_apply]

/-- The homogeneous center basis of the public zigzag algebra: one component unit and one
volume for every vertex. No connectedness or absence of isolated vertices is required. -/
noncomputable def zigzagAlgebraCenterBasis :
    Module.Basis (G.ConnectedComponent ⊕ V) k (Subalgebra.center k (zigzagAlgebra k G)) := by
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  exact ((Pi.basis (zigzagComponentCenterBasis k G)).map
    (zigzagAlgebraCenterPiAlgEquiv k G).symm.toLinearEquiv).reindex (componentCenterIndexEquiv G)

/-- The component-unit coefficient is read in the center basis of that component. -/
@[simp]
theorem zigzagAlgebraCenterBasis_repr_inl (x : Subalgebra.center k (zigzagAlgebra k G))
    (C : G.ConnectedComponent) :
    (zigzagAlgebraCenterBasis k G).repr x (.inl C) =
      (zigzagComponentCenterBasis k G C).repr (zigzagAlgebraCenterPiAlgEquiv k G x C) none := by
  simp [zigzagAlgebraCenterBasis, Module.Basis.map_repr, componentCenterIndexEquiv]

/-- The vertex-volume coefficient is read in the center basis of its component. -/
@[simp]
theorem zigzagAlgebraCenterBasis_repr_inr (x : Subalgebra.center k (zigzagAlgebra k G)) (i : V) :
    (zigzagAlgebraCenterBasis k G).repr x (.inr i) =
      (zigzagComponentCenterBasis k G (G.connectedComponentMk i)).repr
        (zigzagAlgebraCenterPiAlgEquiv k G x (G.connectedComponentMk i)) (some ⟨i, rfl⟩) := by
  simp [zigzagAlgebraCenterBasis, Module.Basis.map_repr, componentCenterIndexEquiv]

open scoped Classical in
/-- A component unit projects to one on its component and to zero on every other component. -/
@[simp]
theorem zigzagComponentProjection_zigzagAlgebraCenterBasis_inl (C D : G.ConnectedComponent) :
    zigzagComponentProjection k G D (zigzagAlgebraCenterBasis k G (.inl C)) =
      if D = C then 1 else 0 := by
  classical
  rw [← zigzagAlgebraCenterPiAlgEquiv_apply_coe]
  suffices hsingle :
      ((Pi.single (M := fun C => Subalgebra.center k (zigzagComponentAlgebra k G C))
        C (zigzagComponentCenterBasis k G C none) D :
        Subalgebra.center k (zigzagComponentAlgebra k G D)) : zigzagComponentAlgebra k G D) =
        if D = C then 1 else 0 by
    simpa [zigzagAlgebraCenterBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
      componentCenterIndexEquiv] using hsingle
  by_cases h : D = C
  · subst D; simp
  · rw [Pi.single_eq_of_ne h]; simp [h]

/-- A global center-volume vector is the vertex-volume vector of the public algebra basis. -/
@[simp]
theorem coe_zigzagAlgebraCenterBasis_inr (i : V) :
    (zigzagAlgebraCenterBasis k G (.inr i) : zigzagAlgebra k G) =
      zigzagAlgebraBasis k G (.inr (.inr i)) := by
  classical
  apply zigzagAlgebra.ext
  intro C
  rw [zigzagAlgebraBasis_apply, zigzagComponentBasisIndexEquiv_symm_inr_inr,
    zigzagComponentProjection_zigzagAlgebraMk, ← zigzagAlgebraCenterPiAlgEquiv_apply_coe]
  suffices hsingle :
      ((Pi.single (M := fun C => Subalgebra.center k (zigzagComponentAlgebra k G C))
        (G.connectedComponentMk i)
        (zigzagComponentCenterBasis k G (G.connectedComponentMk i) (some ⟨i, rfl⟩)) C :
          Subalgebra.center k (zigzagComponentAlgebra k G C)) : zigzagComponentAlgebra k G C) =
      Pi.single (M := fun C => zigzagComponentAlgebra k G C) (G.connectedComponentMk i)
        (zigzagComponentBasis k G (G.connectedComponentMk i) (.inr (.inr ⟨i, rfl⟩))) C by
    simpa [zigzagAlgebraCenterBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
      componentCenterIndexEquiv] using hsingle
  by_cases h : C = G.connectedComponentMk i
  · subst C; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl

/-- Every component unit has degree zero in the public algebra. -/
theorem zigzagAlgebraCenterBasis_inl_mem_grade_zero (C : G.ConnectedComponent) :
    (zigzagAlgebraCenterBasis k G (.inl C) : zigzagAlgebra k G) ∈ zigzagAlgebraGrade k G 0 := by
  classical
  rw [mem_zigzagAlgebraGrade]
  intro D
  rw [zigzagComponentProjection_zigzagAlgebraCenterBasis_inl]
  split_ifs
  · exact SetLike.one_mem_graded _
  · exact Submodule.zero_mem _

/-- Every vertex volume has degree two, including the infinitesimal at an isolated vertex. -/
theorem zigzagAlgebraCenterBasis_inr_mem_grade_two (i : V) :
    (zigzagAlgebraCenterBasis k G (.inr i) : zigzagAlgebra k G) ∈ zigzagAlgebraGrade k G 2 := by
  rw [coe_zigzagAlgebraCenterBasis_inr]
  exact zigzagAlgebraBasis_inr_inr_mem_grade_two k G i

end TauCeti
