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
# `1`-forms on simply connected manifolds are exact

On a simply connected manifold every `1`-form with local primitives, that is, every `1`-form `φ`
such that each point lies in an open set carrying a function with differential `φ` there, has a
global primitive (`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`). In particular every
closed `1`-form is the differential of a function
(`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`), so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

The proof is the monodromy argument. Two primitives of `φ` on a common open set differ by a locally
constant function. Pairs `(x, a)` of a point and a value are topologized so that the graphs
`{(y, g y) | y ∈ U}` of the primitives `g` of `φ` on open sets `U` form a basis. Projecting to the
point is a covering map: over an open set carrying a primitive `g`, the sheets are the graphs of the
translates `g + c`. A simply connected, locally path-connected base lifts the identity through
every covering map, and the second coordinate of such a lift is a global primitive of `φ`, since
near each point it agrees with a translate of a local primitive.

For forms with local primitives this needs only a `C¹` manifold over a real model with corners:
nothing else is assumed of the form, and the manifold need be neither finite-dimensional nor
Hausdorff, nor the coefficient space complete. For closed forms, the local primitives come from the
Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`), which is where finite dimensionality, the
Hausdorff property and completeness of the coefficient space are used. Manifolds with boundary or
corners are included.

## Main declarations

* `TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`: a `1`-form with local primitives on
  a simply connected `C¹` manifold has a global primitive.
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

/-! ### `1`-forms with local primitives -/

/-- **`1`-forms with local primitives on simply connected manifolds have global primitives.** On a
simply connected `C¹` manifold over any real model with corners, a `1`-form `φ` such that every
point lies in an open set carrying a primitive of `φ` is the differential of a function
differentiable on the whole manifold. Nothing else is assumed of `φ`, and neither finite
dimensionality, the Hausdorff property nor completeness of the coefficients is needed. -/
theorem exists_isPrimitiveOn_univ_of_simplyConnectedSpace [IsManifold I 1 M]
    [SimplyConnectedSpace M] {φ : RoughForm I M F 1}
    (hφ : ∀ x, ∃ g : M → F, ∃ U, x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g univ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- lift the identity of `M` through the covering space of local primitives
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
      hφ).existsUnique_continuousMap_lifts (ContinuousMap.id M) x₀ (PrimitiveSpace.graph φ 0 x₀)
      (PrimitiveSpace.proj_graph x₀)
  have hps (y : M) : PrimitiveSpace.proj φ (s y) = y := congrFun hs y
  -- Near each point `x`, the value of `s` differs by a constant from a local primitive of `φ`.
  refine ⟨fun y ↦ PrimitiveSpace.value φ (s y),
    isPrimitiveOn_of_forall_eventuallyEq_add_const isOpen_univ fun x _ ↦ ?_⟩
  obtain ⟨g, U, hxU, hgU⟩ := hφ x
  refine ⟨g, U, hxU, hgU, PrimitiveSpace.value φ (s x) - g x, ?_⟩
  filter_upwards [PrimitiveSpace.eventually_value_eq_add_const (s.continuous.continuousAt (x := x))
    hgU ((hps x).symm ▸ hxU)] with y hy
  rw [hy.2, hps, hps]

/-! ### Closed `1`-forms -/

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]

/-- **Closed `1`-forms on simply connected manifolds are exact.** A closed `C^r` `1`-form
(`1 ≤ r`) with values in a complete space on a simply connected manifold is the exterior
derivative of a `C^r` function. -/
theorem exists_mextDeriv_eq_of_simplyConnectedSpace [SimplyConnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  obtain ⟨f, hf⟩ := exists_isPrimitiveOn_univ_of_simplyConnectedSpace fun x ↦
    let ⟨g, _, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
    ⟨g, U, hxU, hgU⟩
  -- Near each point, the global primitive differs by a constant from a local `C^r` primitive.
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const (f := f) fun x ↦ ?_
  obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
  exact ⟨g, _, hg x, hf.eventuallyEq_add_const hgU (mem_univ x) hxU, hgU.mextDeriv_eq x hxU⟩

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
  exact φ.property

end TauCeti
