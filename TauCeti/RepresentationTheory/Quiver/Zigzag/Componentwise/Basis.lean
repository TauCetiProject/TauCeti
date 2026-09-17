/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Fin
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Basic

/-!
# Bases of zigzag component algebras

Each connected-component factor has a vertex--arrow--volume basis. On a component with an edge
this is the basis of the relation quotient. On a singleton component the vertex and volume
vectors are the unit and infinitesimal generator of the dual numbers. In particular the index
type is uniform across both cases, and the volume vector at an isolated vertex is not zero.

The construction uses Mathlib's two-coordinate basis and transport of bases along linear
equivalences. See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3,
for the singleton convention.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The two indices on a singleton component, ordered as vertex then volume. -/
private noncomputable def singletonComponentBasisIndexEquiv (C : G.ConnectedComponent)
    [Subsingleton C] : ZigzagBasisIndex C.toSimpleGraph ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))
  invFun := fun n => if n = 0 then .inl ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩
    else .inr (.inr ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩)
  left_inv := by
    rintro (i | d | i)
    · simp only [Sum.elim_inl, ↓reduceIte]
      congr 1
      exact Subsingleton.elim _ _
    · exact (C.toSimpleGraph.ne_of_adj d.adj (Subsingleton.elim _ _)).elim
    · simp only [Sum.elim_inr, Fin.isValue]
      exact congrArg (fun j : C => Sum.inr (Sum.inr j)) (Subsingleton.elim _ _)
  right_inv := by intro n; fin_cases n <;> rfl

/-- The vertex--arrow--volume basis of one connected-component factor. Singleton factors use
`1` and `DualNumber.eps` for the vertex and volume, respectively. -/
noncomputable def zigzagComponentBasis (C : G.ConnectedComponent) :
    Module.Basis (ZigzagBasisIndex C.toSimpleGraph) k (zigzagComponentAlgebra k G C) := by
  classical
  by_cases hC : Nontrivial C
  · letI := hC
    exact (zigzagBasis k C.toSimpleGraph fun i =>
      SimpleGraph.exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)).map
      (zigzagComponentAlgebraEquivNonisolated k G C).symm.toLinearEquiv
  · letI : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    -- DualNumber exposes the coordinatewise module of its underlying pair.
    let b : Module.Basis (Fin 2) k (DualNumber k) := Module.Basis.finTwoProd k
    exact ((b.reindex (singletonComponentBasisIndexEquiv G C).symm).map
      (ULift.moduleEquiv.symm)).map
      (zigzagComponentAlgebraEquivULiftDualNumber k G C).symm.toLinearEquiv

/-- On a component with an edge the component basis maps to the relation-quotient basis. -/
@[simp]
theorem zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis
    (C : G.ConnectedComponent) [Nontrivial C]
    (hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j)
    (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentAlgebraEquivNonisolated k G C (zigzagComponentBasis k G C b) =
      zigzagBasis k C.toSimpleGraph hns b := by
  classical
  simp [zigzagComponentBasis, (inferInstance : Nontrivial C)]

/-- Coordinates on a component with an edge are the relation-quotient coordinates. -/
@[simp]
theorem zigzagComponentBasis_repr_nonisolated (C : G.ConnectedComponent) [Nontrivial C]
    (hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j) (x : zigzagComponentAlgebra k G C)
    (b : ZigzagBasisIndex C.toSimpleGraph) :
    (zigzagComponentBasis k G C).repr x b =
      (zigzagBasis k C.toSimpleGraph hns).repr
        (zigzagComponentAlgebraEquivNonisolated k G C x) b := by
  classical
  simp [zigzagComponentBasis, (inferInstance : Nontrivial C)]

/-- On a singleton component the vertex basis vector maps to the dual-number unit. -/
@[simp]
theorem zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inl
    (C : G.ConnectedComponent) [Subsingleton C] (i : C) :
    zigzagComponentAlgebraEquivULiftDualNumber k G C
      (zigzagComponentBasis k G C (.inl i)) = 1 := by
  classical
  simp only [zigzagComponentBasis, dite_eq_right
    (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton C)),
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_symm, ← AlgEquiv.toLinearEquiv_apply,
    LinearEquiv.apply_symm_apply, ULift.moduleEquiv_symm_apply]
  -- The transported basis uses DualNumber's exposed coordinatewise pair module.
  change ULift.up (((Module.Basis.finTwoProd k).reindex
    (singletonComponentBasisIndexEquiv G C).symm) (.inl i)) = (1 : ULift (DualNumber k))
  have h := (Module.Basis.finTwoProd k).reindex_apply
    (singletonComponentBasisIndexEquiv G C).symm (.inl i)
  simp only [Equiv.symm_symm, singletonComponentBasisIndexEquiv, Equiv.coe_fn_mk,
    Sum.elim_inl, Module.Basis.finTwoProd_zero] at h
  exact congrArg ULift.up h

/-- On a singleton component the volume basis vector maps to the infinitesimal generator. -/
@[simp]
theorem zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr
    (C : G.ConnectedComponent) [Subsingleton C] (i : C) :
    zigzagComponentAlgebraEquivULiftDualNumber k G C
      (zigzagComponentBasis k G C (.inr (.inr i))) = ULift.up DualNumber.eps := by
  classical
  simp only [zigzagComponentBasis, dite_eq_right
    (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton C)),
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_symm, ← AlgEquiv.toLinearEquiv_apply,
    LinearEquiv.apply_symm_apply, ULift.moduleEquiv_symm_apply]
  -- The transported basis uses DualNumber's exposed coordinatewise pair module.
  change ULift.up (((Module.Basis.finTwoProd k).reindex
    (singletonComponentBasisIndexEquiv G C).symm) (.inr (.inr i))) =
      (ULift.up DualNumber.eps : ULift (DualNumber k))
  have h := (Module.Basis.finTwoProd k).reindex_apply
    (singletonComponentBasisIndexEquiv G C).symm (.inr (.inr i))
  simp only [Equiv.symm_symm, singletonComponentBasisIndexEquiv, Equiv.coe_fn_mk,
    Sum.elim_inr, Module.Basis.finTwoProd_one] at h
  exact congrArg ULift.up h

/-- The vertex coordinate on a singleton factor is its scalar coefficient. -/
@[simp]
theorem zigzagComponentBasis_repr_inl_of_subsingleton
    (C : G.ConnectedComponent) [Subsingleton C] (x : zigzagComponentAlgebra k G C) (i : C) :
    (zigzagComponentBasis k G C).repr x (.inl i) =
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down.fst := by
  classical
  simp only [zigzagComponentBasis, dite_eq_right
    (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton C)),
    Module.Basis.map_repr, AlgEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm]
  -- DualNumber exposes the coordinatewise module of its underlying pair.
  change (((Module.Basis.finTwoProd k).reindex
    (singletonComponentBasisIndexEquiv G C).symm).repr
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down) (.inl i) = _
  exact (Module.Basis.finTwoProd k).repr_reindex_apply
    (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down
    (singletonComponentBasisIndexEquiv G C).symm _

/-- The volume coordinate on a singleton factor is its infinitesimal coefficient. -/
@[simp]
theorem zigzagComponentBasis_repr_inr_inr_of_subsingleton
    (C : G.ConnectedComponent) [Subsingleton C] (x : zigzagComponentAlgebra k G C) (i : C) :
    (zigzagComponentBasis k G C).repr x (.inr (.inr i)) =
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down.snd := by
  classical
  simp only [zigzagComponentBasis, dite_eq_right
    (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton C)),
    Module.Basis.map_repr, AlgEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm]
  -- DualNumber exposes the coordinatewise module of its underlying pair.
  change (((Module.Basis.finTwoProd k).reindex
    (singletonComponentBasisIndexEquiv G C).symm).repr
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down) (.inr (.inr i)) = _
  exact (Module.Basis.finTwoProd k).repr_reindex_apply
    (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down
    (singletonComponentBasisIndexEquiv G C).symm _

end TauCeti
