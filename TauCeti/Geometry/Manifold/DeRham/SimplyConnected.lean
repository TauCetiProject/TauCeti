/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Geometry.Manifold.DeRham.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.SimplyConnected

/-!
# Closed `1`-forms on simply connected manifolds are exact

On a simply connected manifold every closed `C^r` `1`-form (`1 ≤ r`) with complete coefficients is
the exterior derivative of a `C^r` function (`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`),
so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

The proof combines the Poincaré lemma (`TauCeti.exists_contMDiff_isPrimitiveOn`), which gives
local `C^r` primitives near every point, with the monodromy argument for `1`-forms with local
primitives on simply connected manifolds
(`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`, in
`TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.SimplyConnected`): near each point, the
global primitive differs by a constant from a local `C^r` primitive, hence is itself `C^r`.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`: a closed `C^r` `1`-form (`1 ≤ r`) with
  values in a complete space on a simply connected manifold has a `C^r` primitive.
* `TauCeti.exactForms_one_eq_closedForms_of_simplyConnectedSpace`: on a simply connected manifold
  every closed smooth real `1`-form is exact.
* `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`: `H¹_dR(M) = 0` for simply
  connected `M`.
* `TauCeti.SmoothForm.wedge_mem_exactForms_of_simplyConnectedSpace`: on a simply connected
  manifold the wedge of a closed `1`-form with a closed form is exact.

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

/-- On a simply connected manifold, the wedge `α ∧ β` of a closed `1`-form `α` with a closed form
`β` is exact: `α = dg` for a function `g`, and then `α ∧ β = d (g β)`. -/
theorem SmoothForm.wedge_mem_exactForms_of_simplyConnectedSpace [SimplyConnectedSpace M] {l : ℕ}
    {α : SmoothForm I M ℝ 1} {β : SmoothForm I M ℝ l} (hα : α ∈ closedForms I M 1)
    (hβ : β ∈ closedForms I M l) : SmoothForm.wedge α β ∈ exactForms I M (1 + l) :=
  SmoothForm.wedge_mem_exactForms_of_left_mem
    ((exactForms_one_eq_closedForms_of_simplyConnectedSpace (I := I) (M := M)).ge hα) hβ

end TauCeti
