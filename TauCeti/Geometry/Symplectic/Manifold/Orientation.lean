/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Orientation

import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Normed.Module.Alternating.Tame
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The symplectic orientation of a symplectic manifold

A fiberwise nondegenerate smooth two-form `σ` on a manifold `M` makes each tangent space a
symplectic vector space, which carries its symplectic orientation
(`TauCeti.SymplecticForm.orientation`, the orientation of its Darboux bases). These tangent
orientations form an orientation of `M`, the **symplectic orientation**
`TauCeti.SmoothTwoForm.IsNondegenerate.orientation`. Classically it is the orientation in which the
volume form `σⁿ` is positive. Closedness of `σ` plays no role, so the construction applies to any
almost symplectic manifold, and in particular to every symplectic manifold.

The tangent orientations are locally constant because the linear symplectic orientation is locally
constant in the form. Read in a trivialization of the tangent bundle near `b`, the forms `σ_x` are
symplectic forms on the model space depending continuously on `x`. An almost complex structure `J`
tamed by `σ_b` is still tamed by `σ_x` for `x` near `b`, because taming a fixed `J` is an open
condition on alternating two-forms (`ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos`).
Symplectic forms taming a common almost complex structure have the same orientation
(`TauCeti.SymplecticForm.Tames.orientation_eq`).

A diffeomorphism pulling one nondegenerate form back to another preserves their symplectic
orientations (`TauCeti.SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation`). In
particular symplectomorphisms preserve the symplectic orientation.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.orientation`: the symplectic orientation of a manifold
  with a fiberwise nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_orientation`: its tangent orientation at
  `x` is the symplectic orientation of the tangent space at `x`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation`: diffeomorphisms
  pulling one nondegenerate form back to another preserve the symplectic orientations.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1 and 3.1 (the symplectic volume form and the orientation of a symplectic manifold).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1 and Homework 1.
-/

public section

noncomputable section

open Bundle Filter Module
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {k : ℕ}

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate) (hk : finrank ℝ E = k)

omit [FiniteDimensional ℝ E] in
/-- Read in the preferred trivialization of the tangent bundle at `b`, the tangent symplectic form
at `x` is the coordinate expression of `σ` in the chart at `b`. -/
private theorem transport_symplecticFormAt_apply {b x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet) (u v : E) :
    (hσ.symplecticFormAt x).transport
        ((trivializationAt E (TangentSpace I) b).linearEquivAt ℝ x hx) u v =
      RoughForm.inChartAt (I := I) σ.1 b (extChartAt I b x) ![u, v] := by
  have hx' : x ∈ (chartAt H b).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [SymplecticForm.transport_apply, symplecticFormAt_apply, SmoothBundleForm.eval₂_apply,
    RoughForm.inChartAt_apply,
    (extChartAt I b).left_inv (by simpa only [extChartAt_source] using hx'),
    ← TangentBundle.symmL_trivializationAt hx']
  congr 1
  ext i
  fin_cases i <;> simp only [Trivialization.linearEquivAt_symm_apply] <;>
    exact (Trivialization.symmL_apply (R := ℝ) _ hx _).symm

/-- The tangent symplectic orientations are locally constant in the preferred trivializations of
the tangent bundle. -/
private theorem eventually_mapOrientation_orientation_eq (b : M) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet,
      (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k) hx
          ((hσ.symplecticFormAt x).orientation hk) =
        (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k)
          (FiberBundle.mem_baseSet_trivializationAt' b)
          ((hσ.symplecticFormAt b).orientation hk) := by
  set e := trivializationAt E (TangentSpace I) b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  -- The tangent symplectic forms, transported to the model space `E`.
  set ωE : ∀ x, x ∈ e.baseSet → SymplecticForm E := fun x hx ↦
    (hσ.symplecticFormAt x).transport (e.linearEquivAt ℝ x hx)
  have hmap (x : M) (hx : x ∈ e.baseSet) :
      e.mapOrientation (Fin k) hx ((hσ.symplecticFormAt x).orientation hk) =
        (ωE x hx).orientation hk := by
    rw [Trivialization.mapOrientation_apply]
    exact (SymplecticForm.isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk
  -- An almost complex structure on `E` tamed by the form at `b` is tamed nearby.
  obtain ⟨J, hJ⟩ := (ωE b hb).exists_tames
  set g : M → E [⋀^Fin 2]→L[ℝ] ℝ := fun x ↦ RoughForm.inChartAt (I := I) σ.1 b (extChartAt I b x)
  have hgc : ContinuousAt g b :=
    (((SmoothForm.isSmoothForm σ).continuousOn_inChartAt b).comp (continuousOn_extChartAt b)
      (extChartAt I b).mapsTo).continuousAt (extChartAt_source_mem_nhds b)
  have hpos := hgc.eventually_mem <| (ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos
    (LinearMap.toContinuousLinearMap J.toLinearMap)).mem_nhds fun u hu ↦ by
      rw [LinearMap.coe_toContinuousLinearMap', ← transport_symplecticFormAt_apply hσ hb]
      exact hJ u hu
  filter_upwards [hpos, e.open_baseSet.mem_nhds hb] with x hx hxe hxe'
  rw [hmap, hmap]
  refine SymplecticForm.Tames.orientation_eq (fun u hu ↦ ?_) hJ hk
  have := hx u hu
  rwa [LinearMap.coe_toContinuousLinearMap', ← transport_symplecticFormAt_apply hσ hxe'] at this

/-- The **symplectic orientation** of a manifold `M` carrying a fiberwise nondegenerate smooth
two-form `σ`, for instance a symplectic form: at each point it is the symplectic orientation of the
tangent space, in which the Darboux bases `(q₁, p₁, …, qₙ, pₙ)` of `σ_x` are positive. -/
def orientation : Manifold.Orientation I M (Fin k) :=
  Manifold.Orientation.ofVectorBundleOrientation (Module.finBasisOfFinrankEq ℝ E hk).orientation
    ((Fintype.card_fin k).trans hk.symm)
    ⟨fun x ↦ (hσ.symplecticFormAt x).orientation hk,
      hσ.eventually_mapOrientation_orientation_eq hk⟩

/-- The tangent orientation of the symplectic orientation at `x` is the symplectic orientation of
the tangent space at `x`. -/
@[simp]
theorem orientationAt_orientation (x : M) :
    (hσ.orientation hk).orientationAt x = (hσ.symplecticFormAt x).orientation hk := by
  rw [orientation, Manifold.Orientation.orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk]

section Transport

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- **Symplectomorphisms preserve the symplectic orientation.** A diffeomorphism pulling a
nondegenerate two-form `σ₂` back to `σ` preserves the symplectic orientations at every point. -/
theorem isOrientationPreservingAt_orientation (hσ₂ : σ₂.IsNondegenerate)
    (hk₂ : finrank ℝ E₂ = k) (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (hσ.orientation hk) (hσ₂.orientation hk₂) ψ
      x := by
  rw [Manifold.Orientation.isOrientationPreservingAt_iff]
  refine ⟨ψ.mfderivToContinuousLinearEquiv (by simp) x,
    Diffeomorph.mfderivToContinuousLinearEquiv_coe _ _, ?_⟩
  rw [orientationAt_orientation, orientationAt_orientation,
    ← hσ.symplecticFormAt_transport ψ hψ x]
  exact (SymplecticForm.isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk

end Transport

end IsNondegenerate

end SmoothTwoForm

end TauCeti
