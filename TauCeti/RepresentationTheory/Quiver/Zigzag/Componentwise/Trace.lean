/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Decomposition
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Trace

/-!
# The trace of the componentwise zigzag algebra

The public zigzag algebra is a product over the connected components of a finite simple graph.
This file equips each factor with its canonical trace and sums those traces over the product. On a
component containing an edge this is `TauCeti.zigzagTrace`, transported from the relation-quotient
presentation. On a singleton component it is the infinitesimal coordinate of the dual numbers.

The resulting functional is one on every volume basis vector and zero on vertex and arrow basis
vectors, including at isolated vertices. It is a trace: `tr (x * y) = tr (y * x)`. Its restriction
to a single embedded factor recovers that factor's trace, giving the trace part of the connected-
component decomposition.

## Main definitions

* `TauCeti.zigzagComponentTrace`: the trace on one connected-component factor.
* `TauCeti.zigzagAlgebraTrace`: the sum of the component traces on the public zigzag algebra.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open SimpleGraph

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The finite indexing type used internally for the componentwise trace. -/
noncomputable local instance zigzagTraceConnectedComponentFintype :
    Fintype G.ConnectedComponent := Fintype.ofFinite _

/-! ### The trace of one component -/

/-- The canonical trace on one connected-component factor of the public zigzag algebra. It is
zero on the vertex and arrow blocks of `TauCeti.zigzagComponentBasis` and one on its volume block.
For a nontrivial component this is the transported relation-quotient trace; for a singleton it is
the infinitesimal coordinate of the dual numbers. -/
noncomputable def zigzagComponentTrace (C : G.ConnectedComponent) :
    zigzagComponentAlgebra k G C →ₗ[k] k :=
  (zigzagComponentBasis k G C).constr k
    (Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 0) fun _ ↦ 1))

/-- The component trace is zero on vertex and arrow basis vectors and one on volume basis
vectors. -/
@[simp]
theorem zigzagComponentTrace_zigzagComponentBasis (C : G.ConnectedComponent)
    (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentTrace k G C (zigzagComponentBasis k G C b) =
      Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 0) fun _ ↦ 1) b := by
  exact (zigzagComponentBasis k G C).constr_basis k
    (Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 0) fun _ ↦ 1)) b

/-- On a component containing an edge, the component trace is the relation-quotient zigzag trace
under the canonical presentation equivalence. -/
theorem zigzagComponentTrace_apply_nontrivial (C : G.ConnectedComponent) [Nontrivial C]
    (x : zigzagComponentAlgebra k G C) :
    zigzagComponentTrace k G C x =
      zigzagTrace k C.toSimpleGraph (fun i ↦
        exists_adj_iff_not_isIsolated.mpr
          (C.connected_toSimpleGraph.preconnected.not_isIsolated i))
        (zigzagComponentAlgebraEquivNonisolated k G C x) := by
  let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i ↦
    exists_adj_iff_not_isIsolated.mpr
      (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
  have htrace : zigzagComponentTrace k G C =
      (zigzagTrace k C.toSimpleGraph hns).comp
        (zigzagComponentAlgebraEquivNonisolated k G C).toLinearMap := by
    apply (zigzagComponentBasis k G C).ext
    intro b
    rw [zigzagComponentTrace_zigzagComponentBasis, LinearMap.comp_apply]
    -- The transported basis lemma is stated for the `AlgEquiv` coercion, while composition above
    -- leaves its definitionally equal `toLinearMap` coercion in the goal.
    change Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 0) fun _ ↦ 1) b =
      zigzagTrace k C.toSimpleGraph hns
        (zigzagComponentAlgebraEquivNonisolated k G C (zigzagComponentBasis k G C b))
    rw [zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns,
      zigzagBasis_apply, zigzagTrace_zigzagBasisFun]
  exact LinearMap.congr_fun htrace x

/-- On a singleton component, the component trace is the infinitesimal coordinate under the
canonical dual-number presentation. -/
theorem zigzagComponentTrace_apply_subsingleton (C : G.ConnectedComponent) [Subsingleton C]
    (x : zigzagComponentAlgebra k G C) :
    zigzagComponentTrace k G C x =
      (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down.snd := by
  have htrace : zigzagComponentTrace k G C =
      (TrivSqZeroExt.sndHom k k).comp
        (ULift.moduleEquiv.toLinearMap.comp
          (zigzagComponentAlgebraEquivULiftDualNumber k G C).toLinearMap) := by
    apply (zigzagComponentBasis k G C).ext
    rintro (i | d | i)
    · rw [zigzagComponentTrace_zigzagComponentBasis, LinearMap.comp_apply,
        LinearMap.comp_apply]
      -- Composition leaves linear-map coercions; the basis lemma uses the equivalent algebra-map
      -- coercion and exposes the `ULift` coordinate directly.
      change 0 = (zigzagComponentAlgebraEquivULiftDualNumber k G C
        (zigzagComponentBasis k G C (.inl i))).down.snd
      rw [zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inl]
      rfl
    · exact (C.toSimpleGraph.ne_of_adj d.adj (Subsingleton.elim _ _)).elim
    · rw [zigzagComponentTrace_zigzagComponentBasis, LinearMap.comp_apply,
        LinearMap.comp_apply]
      -- This is the same coercion bridge for the volume basis vector.
      change 1 = (zigzagComponentAlgebraEquivULiftDualNumber k G C
        (zigzagComponentBasis k G C (.inr (.inr i)))).down.snd
      rw [zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]
      rfl
  exact LinearMap.congr_fun htrace x

/-- The trace on one component is cyclic. -/
theorem zigzagComponentTrace_mul_comm (C : G.ConnectedComponent)
    (x y : zigzagComponentAlgebra k G C) :
    zigzagComponentTrace k G C (x * y) = zigzagComponentTrace k G C (y * x) := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i ↦
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    rw [zigzagComponentTrace_apply_nontrivial k G C,
      zigzagComponentTrace_apply_nontrivial k G C]
    let e := zigzagComponentAlgebraEquivNonisolated k G C
    -- `AlgEquiv.map_mul` is phrased through `toMulEquiv`; the typed equalities bridge that
    -- coercion with the algebra-map applications in the trace.
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * x) = e y * e x from e.map_mul y x]
    exact zigzagTrace_mul_comm k C.toSimpleGraph hns _ _
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    rw [zigzagComponentTrace_apply_subsingleton k G C,
      zigzagComponentTrace_apply_subsingleton k G C]
    -- Passing through `ULift.algEquiv` makes the dual-number coordinate explicit.
    change (e (x * y)).snd = (e (y * x)).snd
    -- As in the nontrivial branch, use typed equalities to bridge the multiplication coercion.
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * x) = e y * e x from e.map_mul y x]
    simp only [DualNumber.snd_mul]
    ring

/-! ### The trace of the public algebra -/

/-- The trace of the public zigzag algebra, obtained by summing the canonical traces of all its
connected-component factors. -/
noncomputable def zigzagAlgebraTrace : zigzagAlgebra k G →ₗ[k] k := by
  classical
  exact (LinearMap.lsum k (fun C : G.ConnectedComponent ↦ zigzagComponentAlgebra k G C) k
    (zigzagComponentTrace k G)).comp (zigzagAlgebraPiAlgEquiv k G).toLinearMap

/-- The public trace is the sum of the traces of the component projections. -/
theorem zigzagAlgebraTrace_apply (x : zigzagAlgebra k G) :
    zigzagAlgebraTrace k G x =
      ∑ C, zigzagComponentTrace k G C (zigzagComponentProjection k G C x) := by
  classical
  rw [zigzagAlgebraTrace, LinearMap.comp_apply, LinearMap.lsum_apply]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro C _
  -- `toLinearMap` and `AlgEquiv` function coercions do not simplify to the same syntax.
  change zigzagComponentTrace k G C (zigzagAlgebraPiAlgEquiv k G x C) = _
  rw [zigzagAlgebraPiAlgEquiv_apply]

open Classical in
/-- Restricting the public trace to an embedded component factor recovers that component's
canonical trace. -/
@[simp]
theorem zigzagAlgebraTrace_zigzagAlgebraMk_single (C : G.ConnectedComponent)
    (x : zigzagComponentAlgebra k G C) :
    zigzagAlgebraTrace k G (zigzagAlgebraMk k G (Pi.single C x)) =
      zigzagComponentTrace k G C x := by
  rw [zigzagAlgebraTrace_apply]
  simp_rw [zigzagComponentProjection_zigzagAlgebraMk]
  simpa only [LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply] using LinearMap.lsum_piSingle k
      (fun C : G.ConnectedComponent ↦ zigzagComponentAlgebra k G C) k
      (zigzagComponentTrace k G) C x

/-- The public trace is zero on vertex and arrow basis vectors and one on volume basis vectors. -/
@[simp]
theorem zigzagAlgebraTrace_zigzagAlgebraBasis
    (C : G.ConnectedComponent) (b : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagAlgebraTrace k G
        (zigzagAlgebraBasis k G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)) =
      Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 0) fun _ ↦ 1) b := by
  rw [zigzagAlgebraBasis_apply, Equiv.symm_apply_apply,
    zigzagAlgebraTrace_zigzagAlgebraMk_single,
    zigzagComponentTrace_zigzagComponentBasis]

/-- The trace of the public zigzag algebra is cyclic. -/
theorem zigzagAlgebraTrace_mul_comm (x y : zigzagAlgebra k G) :
    zigzagAlgebraTrace k G (x * y) = zigzagAlgebraTrace k G (y * x) := by
  classical
  simp only [zigzagAlgebraTrace_apply, map_mul]
  exact Finset.sum_congr rfl fun C _ ↦ zigzagComponentTrace_mul_comm k G C _ _

end TauCeti
