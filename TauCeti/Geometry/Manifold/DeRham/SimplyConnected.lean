/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.Topology
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Closed `1`-forms on simply connected manifolds are exact

On a simply connected manifold every closed `1`-form is the differential of a function
(`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`), so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

The proof is the monodromy argument. By the Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`)
a closed `1`-form `φ` has a primitive near every point, and two primitives on a common open set
differ by a locally constant function. Pairs `(x, a)` of a point and a value are topologized so
that the graphs `{(y, g y) | y ∈ U}` of the primitives `g` of `φ` on open sets `U` form a basis.
Projecting to the point is a covering map: over an open set carrying a primitive `g`, the sheets
are the graphs of the translates `g + c`. A simply connected, locally path-connected base lifts
the identity through every covering map, and the second coordinate of such a lift is a global
primitive of `φ`, since near each point it agrees with a translate of a local primitive.

The Poincaré lemma is where finite dimensionality, the Hausdorff property and completeness of the
coefficient space are used. Manifolds with boundary or corners are included.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`: a closed `C^r` `1`-form (`1 ≤ r`) with
  values in a complete space on a simply connected manifold has a `C^r` primitive.
* `TauCeti.exactForms_one_eq_closedForms_of_simplyConnectedSpace`: on a simply connected manifold
  every closed smooth real `1`-form is exact.
* `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`: `H¹_dR(M) = 0` for simply
  connected `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields* (closed covector fields on simply connected manifolds are exact), and
  Chapter 17.
* Allen Hatcher, *Algebraic Topology*, Proposition 1.33 (the lifting criterion).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]

/-! ### Exactness on simply connected manifolds -/

/-- **Closed `1`-forms on simply connected manifolds are exact.** A closed `C^r` `1`-form
(`1 ≤ r`) with values in a complete space on a simply connected manifold is the exterior
derivative of a `C^r` function. -/
theorem exists_mextDeriv_eq_of_simplyConnectedSpace [SimplyConnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- lift the identity of `M` through the covering space of local primitives
  have hp := PrimitiveSpace.isCoveringMap_proj hr hφ hclosed
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id M) x₀ (PrimitiveSpace.graph φ 0 x₀)
      (PrimitiveSpace.proj_graph x₀)
  have hps (y : M) : PrimitiveSpace.proj φ (s y) = y := congrFun hs y
  -- Near each point `x`, the value of `s` differs by a constant from a local primitive of `φ`.
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const
    (by simpa using (zero_lt_one.trans_le hr).ne') (f := fun y ↦ PrimitiveSpace.value φ (s y))
    fun x ↦ ?_
  obtain ⟨g, hg, U, hxU, hgU, c, hc⟩ :=
    PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq hr hφ hclosed
      (s.continuous.continuousAt (x := x))
  rw [hps] at hxU
  exact ⟨g, c, hg x, hc.mono fun y hy ↦ by rw [hy.2, hps], hgU.mextDeriv_eq x hxU⟩

variable (I M) in
/-- On a simply connected manifold every closed smooth real `1`-form is exact. -/
theorem exactForms_one_eq_closedForms_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    exactForms I M 1 = closedForms I M 1 := by
  refine le_antisymm (exactForms_le_closedForms I 1) fun φ hφ ↦ ?_
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_simplyConnectedSpace (r := ⊤) le_top
    φ.isSmoothForm ((mem_closedForms I φ).mp hφ)
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

variable (I M) in
/-- **The first de Rham cohomology of a simply connected manifold vanishes.** -/
theorem subsingleton_deRhamCohomology_one_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    Subsingleton (deRhamCohomology I M 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective _ _ c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_one_eq_closedForms_of_simplyConnectedSpace]
  exact φ.2

end TauCeti
