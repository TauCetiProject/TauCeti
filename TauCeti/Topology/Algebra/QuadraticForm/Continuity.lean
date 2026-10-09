/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
-- Supplies the real topology used by the public `IsModuleTopology ℝ V` hypothesis.
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Real.Sqrt

/-!
# Continuity of quadratic maps

A quadratic map on a finite module with the module topology is continuous into any
topological module. No invertibility assumption on two is needed: in finitely many generators,
the quadratic-map axioms express its values using continuous scalar multiplication and addition.
For any continuous quadratic map, its preserving endomorphisms form a closed set when the
codomain is Hausdorff.

Over the reals, near a vector with nonzero quadratic value, the ratio to that value is a
nonzero square. This is the neighborhood condition that allows weak approximation of vectors
to preserve the square classes of their quadratic values.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §66.
-/

public section

namespace TauCeti

open scoped Topology

/-- A quadratic map on a finite module with the module topology is continuous into any
topological module, including in characteristic two. -/
@[continuity, fun_prop]
theorem _root_.QuadraticMap.continuous
    {R M N : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [IsModuleTopology R M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (Q : QuadraticMap R M N) : Continuous Q := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨B, hB⟩ := Q.exists_companion
  have : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let v (i : Fin n) := f (fun j => if i = j then 1 else 0)
  -- The quadratic-map axioms give continuity on every finite sum of generators.
  have hs (s : Finset (Fin n)) :
      Continuous (fun x : Fin n → R => Q (∑ i ∈ s, x i • v i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : Fin n → R => (0 : N)))
    | @insert i s hi ih =>
      have hlin := IsModuleTopology.continuous_of_linearMap (B (v i))
      have hsum : Continuous (fun x : Fin n → R => ∑ j ∈ s, x j • v j) := by fun_prop
      simp_rw [Finset.sum_insert hi, hB, Q.map_smul, map_smul, LinearMap.smul_apply]
      exact (((continuous_apply i).fun_mul (continuous_apply i)).fun_smul
        continuous_const).fun_add ih |>.fun_add
          ((continuous_apply i).fun_smul (hlin.comp hsum))
  -- The coordinate surjection is a quotient map for the module topology.
  rw [Topology.IsQuotientMap.continuous_iff (IsModuleTopology.isQuotientMap_of_surjective hf)]
  exact (hs Finset.univ).congr (fun x => congrArg Q (f.pi_apply_eq_sum_univ x).symm)

/-- Endomorphisms preserving a continuous quadratic map form a closed subset of the
endomorphism space when the codomain is Hausdorff. -/
theorem _root_.QuadraticMap.isClosed_setOfPred_forall_map_app
    {R M N : Type*} [CommSemiring R] [TopologicalSpace R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M]
    [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] [T2Space N]
    (Q : QuadraticMap R M N) (hQ : Continuous Q) :
    IsClosed {f : Module.End R M | ∀ x : M, Q (f x) = Q x} := by
  have h (x : M) : IsClosed {f : Module.End R M | Q (f x) = Q x} := by
    have hev : Continuous (fun f : Module.End R M => f x) :=
      IsModuleTopology.continuous_of_linearMap ((LinearMap.applyₗ :
        M →ₗ[R] Module.End R M →ₗ[R] M) x)
    exact isClosed_eq (hQ.comp hev) continuous_const
  simpa only [Set.ofPred_forall] using isClosed_iInter h

/-- Near a vector where a real quadratic form is nonzero, its value remains nonzero and in
the same square class. No nondegeneracy assumption on the form is needed. -/
theorem _root_.QuadraticForm.eventually_isSquare_div
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    [TopologicalSpace V] [IsModuleTopology ℝ V]
    (Q : QuadraticForm ℝ V) {x : V} (hx : Q x ≠ 0) :
    ∀ᶠ z in 𝓝 x, Q z ≠ 0 ∧ IsSquare (Q z / Q x) := by
  have hpos : ∀ᶠ z in 𝓝 x, 0 < Q z / Q x :=
    (Q.continuous.div_const (Q x)).continuousAt.eventually
      (isOpen_Ioi.mem_nhds (by simp [hx]))
  filter_upwards [hpos] with z hz
  exact ⟨fun hzero ↦ by simp [hzero] at hz, Real.isSquare_iff.mpr hz.le⟩

end TauCeti
