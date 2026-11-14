/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Invariant neighbourhoods of a fixed point of a bounded representation

Let a group `G` act on a real normed space `V` through a continuous representation `ρ` whose
operators form a bounded set, as they do for a finite group, or for a compact group acting
continuously. If `x₀` is fixed by every `ρ g`, then `x₀` has arbitrarily small open convex
neighbourhoods which are invariant under every `ρ g`
(`ContRepresentation.nhds_basis_isOpen_convex_mapsTo`).

Invariant neighbourhoods are the domains of equivariant local constructions around a fixed point,
such as equivariant charts, invariant primitives of invariant forms and equivariant Moser flows;
convexity makes them star-convex with respect to `x₀`, as the Poincaré lemma requires.

Without boundedness the conclusion fails: the hyperbolic one-parameter group
`diag(eᵗ, e⁻ᵗ)` of `ℝ²` fixes `0`, but every invariant neighbourhood of `0` contains the
coordinate axes.

## Main results

* `ContRepresentation.nhds_basis_isOpen_convex_mapsTo`: the open convex invariant neighbourhoods
  of a fixed point of a bounded representation form a basis of its neighbourhoods.
-/

public section

open Set Filter Topology Metric

namespace ContRepresentation

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The open convex neighbourhoods of a point `x₀` which are invariant under a bounded continuous
representation `ρ` fixing `x₀` form a basis of the neighbourhoods of `x₀`. -/
theorem nhds_basis_isOpen_convex_mapsTo (ρ : ContRepresentation ℝ G V)
    (hρ : Bornology.IsBounded (range ρ)) {x₀ : V} (hx₀ : ∀ g, ρ g x₀ = x₀) :
    (𝓝 x₀).HasBasis (fun U : Set V ↦ IsOpen U ∧ Convex ℝ U ∧ x₀ ∈ U ∧ ∀ g, MapsTo (ρ g) U U)
      id := by
  refine ⟨fun N ↦ ⟨fun hN ↦ ?_, fun ⟨U, hU, hUN⟩ ↦ mem_of_superset (hU.1.mem_nhds hU.2.2.1) hUN⟩⟩
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hρ
  -- The points whose whole orbit lies in the ball of radius `δ`; we take its interior.
  set S : Set V := ⋂ g, ρ g ⁻¹' ball x₀ δ with hS
  have hSρ (h : G) : MapsTo (ρ h) S S := fun x hx ↦ by
    simp only [hS, mem_iInter, mem_preimage] at hx ⊢
    intro g
    simpa only [← mul_apply_eq_comp, ← map_mul] using hx (g * h)
  -- Since `‖ρ g‖ ≤ C`, the ball of radius `δ / C` lies in `S`.
  have hC' : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hball : ball x₀ (δ / max C 1) ⊆ S := fun x hx ↦ by
    simp only [hS, mem_iInter, mem_preimage, mem_ball, dist_eq_norm]
    intro g
    rw [← hx₀ g, ← map_sub]
    calc ‖ρ g (x - x₀)‖ ≤ ‖ρ g‖ * ‖x - x₀‖ := (ρ g).le_opNorm _
      _ ≤ max C 1 * ‖x - x₀‖ :=
          mul_le_mul_of_nonneg_right ((hC _ (mem_range_self g)).trans (le_max_left _ _))
            (norm_nonneg _)
      _ < max C 1 * (δ / max C 1) := by
          rw [mem_ball, dist_eq_norm] at hx
          exact mul_lt_mul_of_pos_left hx hC'
      _ = δ := mul_div_cancel₀ _ hC'.ne'
  refine ⟨interior S, ⟨isOpen_interior, ?_, ?_, fun h x hx ↦ ?_⟩, ?_⟩
  · exact (convex_iInter fun g ↦ (convex_ball x₀ δ).linear_preimage (ρ g).toLinearMap).interior
  · exact interior_maximal hball isOpen_ball (mem_ball_self (div_pos hδ hC'))
  · -- `ρ h` maps `interior S` onto the open subset `(ρ h⁻¹)⁻¹' (interior S)` of `S`.
    have hinv (y : V) : ρ h⁻¹ (ρ h y) = y := by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one,
        one_apply_eq_self]
    refine interior_maximal (fun y hy ↦ ?_) (isOpen_interior.preimage (ρ h⁻¹).continuous)
      (by rwa [mem_preimage, hinv])
    have := hSρ h (interior_subset hy)
    rwa [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self] at this
  · refine interior_subset.trans (fun x hx ↦ hδN ?_)
    simpa using mem_iInter.1 hx 1

end ContRepresentation
