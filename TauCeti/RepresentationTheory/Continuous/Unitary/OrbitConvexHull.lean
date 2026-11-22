/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Invariant vectors in the closed convex hull of an orbit

For a unitary representation `ρ` of a monoid on a complex Hilbert space, the closed convex hull
`C` of the orbit `{ρ g ξ}` of a vector `ξ` contains a `ρ`-invariant vector: its element of
minimal norm. Each `ρ g` maps `C` into itself and preserves norms, and a closed convex set in a
Hilbert space has a unique element of minimal norm, so `ρ g` fixes it.

Consequently, if the coefficients `g ↦ re ⟪ξ, ρ g ξ⟫` are bounded below by a positive constant,
then `ρ` has a nonzero invariant vector: the real-part bound passes from the orbit to its closed
convex hull, so the minimal element is not `0`. This is how a positive-definite function which is
uniformly close to `1` on a subgroup produces vectors fixed by that subgroup.

## Main statements

* `ContRepresentation.IsUnitary.exists_mem_closedConvexHull_mem_invariants`: the closed convex
  hull of an orbit contains an invariant vector.
* `ContRepresentation.IsUnitary.exists_ne_zero_mem_invariants_of_le_re_inner`: a vector whose
  coefficients have real part bounded below by a positive constant yields a nonzero invariant
  vector.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation.IsUnitary

variable {G H : Type*} [Monoid G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : ContRepresentation ℂ G H}

/-- The closed convex hull of the orbit of a vector under a unitary representation contains an
invariant vector, namely its element of minimal norm. -/
theorem exists_mem_closedConvexHull_mem_invariants (hρ : ρ.IsUnitary) (ξ : H) :
    ∃ η ∈ closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ), η ∈ ρ.invariants := by
  set C := closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ)
  have hξC : ξ ∈ C := subset_closedConvexHull ⟨1, by simp⟩
  -- `C` is a nonempty complete convex set, so it has an element `η` of minimal norm.
  obtain ⟨η, hηC, hη⟩ : ∃ η ∈ C, ∀ w ∈ C, ‖η‖ ≤ ‖w‖ := by
    let := InnerProductSpace.rclikeToReal ℂ H
    obtain ⟨η, hηC, hη⟩ := exists_norm_eq_iInf_of_complete_convex ⟨ξ, hξC⟩
      isClosed_closedConvexHull.isComplete convex_closedConvexHull 0
    refine ⟨η, hηC, fun w hw ↦ ?_⟩
    have := ciInf_le (f := fun w : C ↦ ‖(0 : H) - w‖)
      ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ ⟨w, hw⟩
    rwa [← hη, zero_sub, norm_neg, zero_sub, norm_neg] at this
  -- Each `ρ g` maps `C` into itself.
  have hmaps (g : G) : ∀ w ∈ C, ρ g w ∈ C := by
    refine closedConvexHull_min (t := ρ g ⁻¹' C) ?_
      (convex_closedConvexHull.linear_preimage ((ρ g).toLinearMap.restrictScalars ℝ))
      (isClosed_closedConvexHull.preimage (ρ g).continuous)
    rintro _ ⟨k, rfl⟩
    exact subset_closedConvexHull ⟨g * k, by simp [map_mul]⟩
  -- `ρ g η` and `η` both have minimal norm, so their midpoint forces them to coincide.
  refine ⟨η, hηC, fun g ↦ ?_⟩
  set w := ρ g η
  have hw : ‖w‖ = ‖η‖ := hρ.norm_map g η
  have hmid : ‖η‖ ≤ ‖(1 / 2 : ℝ) • w + (1 / 2 : ℝ) • η‖ :=
    hη _ (convex_closedConvexHull (hmaps g η hηC) hηC (by norm_num) (by norm_num) (by norm_num))
  have hmid' : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • η = (1 / 2 : ℝ) • (w + η) := by
    rw [smul_add]
  rw [hmid', norm_smul, Real.norm_of_nonneg (by norm_num)] at hmid
  have hpar := parallelogram_law_with_norm ℂ w η
  have hsub : ‖w - η‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg η, norm_nonneg (w + η)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm hsub (sq_nonneg _))))

/-- If the coefficients `g ↦ re ⟪ξ, ρ g ξ⟫` of a vector `ξ` are bounded below by a positive
constant, then a unitary representation `ρ` has a nonzero invariant vector, found in the closed
convex hull of the orbit of `ξ`. -/
theorem exists_ne_zero_mem_invariants_of_le_re_inner (hρ : ρ.IsUnitary) {ξ : H} {c : ℝ}
    (hc : 0 < c) (hξ : ∀ g, c ≤ RCLike.re ⟪ξ, ρ g ξ⟫_ℂ) :
    ∃ η ≠ 0, η ∈ ρ.invariants := by
  obtain ⟨η, hηC, hη⟩ := hρ.exists_mem_closedConvexHull_mem_invariants ξ
  -- The closed half-space `{x | c ≤ re ⟪ξ, x⟫}` contains the orbit, hence its closed convex hull.
  let f : H →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ ξ).restrictScalars ℝ)
  have hf (x : H) : f x = RCLike.re ⟪ξ, x⟫_ℂ := rfl
  have hsub : closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ) ⊆ f ⁻¹' Set.Ici c :=
    closedConvexHull_min (by rintro _ ⟨g, rfl⟩; exact hξ g)
      ((convex_Ici c).linear_preimage f.toLinearMap) (isClosed_Ici.preimage f.continuous)
  refine ⟨η, fun h0 ↦ ?_, hη⟩
  have := hsub hηC
  simp only [Set.mem_preimage, Set.mem_Ici, hf, h0, inner_zero_right, map_zero] at this
  linarith

end ContRepresentation.IsUnitary
