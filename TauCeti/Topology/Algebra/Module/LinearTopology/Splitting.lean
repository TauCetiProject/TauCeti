/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.DiscreteSubset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic.Abel

/-!
# Splitting strict surjections with discrete kernel

A discrete subspace of a linearly topologized vector space has an open algebraic
complement, hence a continuous linear retraction. Consequently every continuous linear
quotient map with discrete kernel admits a continuous linear section. Neither the
kernel nor the quotient needs to be finite-dimensional, and completeness is not required.

For topological central extensions of formal current Lie algebras, this supplies the
continuous *linear* section used to represent the extension by a continuous cocycle;
it does not assert the existence of a Lie algebra section.

The proof first separates the discrete subspace from an open subspace, extends the
latter to an algebraic complement, and uses the quotient-map property to descend the
complementary projection to a section.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for continuously
  linearly split central extensions of formal loop algebras.
-/

public section

open Filter Topology

namespace Submodule

section Ring

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [IsLinearTopology R E]

/-- A discrete submodule of a linearly topologized module meets some open
submodule only at zero. -/
theorem exists_isOpen_disjoint_of_discreteTopology (p : Submodule R E)
    [DiscreteTopology p] :
    ∃ U : Submodule R E, IsOpen (U : Set E) ∧ Disjoint p U := by
  obtain ⟨V, hV, hVp⟩ := discreteTopology_subtype_iff'.mp
    (inferInstance : DiscreteTopology (p : Set E)) 0 p.zero_mem
  have hV0 : (0 : E) ∈ V := by
    have : (0 : E) ∈ V ∩ (p : Set E) := hVp.symm ▸ Set.mem_singleton 0
    exact this.1
  obtain ⟨U, hU, hUV⟩ := (IsLinearTopology.hasBasis_open_submodule R).mem_iff.mp
    (hV.mem_nhds hV0)
  refine ⟨U, hU, Submodule.disjoint_def.mpr ?_⟩
  intro x hxp hxU
  exact Set.mem_singleton_iff.mp (hVp ▸ ⟨hUV hxU, hxp⟩)

end Ring

section DivisionRing

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [IsLinearTopology K E]

/-- A discrete subspace of a linearly topologized vector space has an open
algebraic complement. -/
theorem exists_isOpen_isCompl_of_discreteTopology (p : Submodule K E)
    [DiscreteTopology p] :
    ∃ q : Submodule K E, IsOpen (q : Set E) ∧ IsCompl p q := by
  obtain ⟨U, hU, hpU⟩ := p.exists_isOpen_disjoint_of_discreteTopology
  obtain ⟨q, hUq, hpq⟩ := hpU.symm.exists_isCompl
  exact ⟨q, q.toAddSubgroup.isOpen_of_mem_nhds
    (mem_of_superset (hU.mem_nhds U.zero_mem) hUq), hpq.symm⟩

/-- Discrete subspaces of linearly topologized vector spaces are continuously
complemented, even in infinite dimension. -/
theorem closedComplemented_of_discreteTopology (p : Submodule K E)
    [DiscreteTopology p] : p.ClosedComplemented := by
  obtain ⟨q, hq, hpq⟩ := p.exists_isOpen_isCompl_of_discreteTopology
  have hcont : Continuous (p.projection q hpq) := by
    apply continuous_of_continuousAt_zero (p.projection q hpq).toAddMonoidHom
    apply tendsto_const_nhds.congr'
    filter_upwards [hq.mem_nhds q.zero_mem] with x hx
    simpa using (p.projection_apply_of_mem_right hpq hx).symm
  exact (⟨hpq, hcont⟩ : p.IsTopCompl q).closedComplemented

end DivisionRing

end Submodule

namespace ContinuousLinearMap

variable {K E F : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [IsLinearTopology K E]
  [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- A continuous linear quotient map from a linearly topologized vector space
with discrete kernel admits a continuous linear right inverse. Thus a strict exact
sequence with discrete kernel is continuously linearly split. -/
theorem exists_rightInverse_of_isQuotientMap_of_discreteTopology_ker
    (f : E →L[K] F) (hf : IsQuotientMap f)
    [DiscreteTopology f.ker] :
    ∃ s : F →L[K] E, Function.RightInverse s f := by
  obtain ⟨r, hr⟩ := f.ker.closedComplemented_of_discreteTopology
  obtain ⟨g, hg'⟩ := f.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf.surjective)
  have hg (y : F) : f (g y) = y := LinearMap.congr_fun hg' y
  let P : E →L[K] E := f.ker.subtypeL.comp r
  have hP (x : E) (hx : f x = 0) : P x = x :=
    congrArg Subtype.val (hr ⟨x, hx⟩)
  have hfP (x : E) : f (P x) = 0 := (r x).property
  let s : F →ₗ[K] E := (LinearMap.id - P.toLinearMap).comp g
  have hs (x : E) : s (f x) = x - P x := by
    have hx : f (g (f x) - x) = 0 := by simp [hg]
    have h := hP _ hx
    simp only [map_sub] at h
    simp only [s, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      coe_coe]
    calc
      g (f x) - P (g (f x)) =
          (g (f x) - x) - (P (g (f x)) - P x) + (x - P x) := by abel
      _ = x - P x := by rw [h, sub_self, zero_add]
  have hscont : Continuous s := by
    apply hf.continuous_iff.mpr
    exact (continuous_id.sub P.continuous).congr (fun x ↦ (hs x).symm)
  refine ⟨⟨s, hscont⟩, fun y ↦ ?_⟩
  simp [s, hfP, hg]

end ContinuousLinearMap
