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

For a unitary representation `ρ` of a monoid on a Hilbert space over an `RCLike` field such as
`ℝ` or `ℂ`, the closed convex hull `C` of the orbit `{ρ g ξ}` of a vector `ξ` contains a
`ρ`-invariant vector: its element of minimal norm. Each `ρ g` maps `C` into itself and preserves
norms, and a closed convex set in a Hilbert space has a unique element of minimal norm, so `ρ g`
fixes it. The convex hull is taken over `ℝ`, so `H` also carries a real scalar action compatible
with that of the field.

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

variable {𝕜 G H : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] [CompleteSpace H] {ρ : ContRepresentation 𝕜 G H}

/-- The closed convex hull of the orbit of a vector under a unitary representation contains an
invariant vector, namely its element of minimal norm. -/
theorem exists_mem_closedConvexHull_mem_invariants (hρ : ρ.IsUnitary) (ξ : H) :
    ∃ η ∈ closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ), η ∈ ρ.invariants := by
  set C := closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ)
  have hξC : ξ ∈ C := subset_closedConvexHull ⟨1, by simp⟩
  -- `C` is a nonempty complete convex set, so it has an element `η` of minimal norm.
  obtain ⟨η, hηC, hη⟩ : ∃ η ∈ C, ∀ w ∈ C, ‖η‖ ≤ ‖w‖ := by
    -- The real inner product `re ⟪x, y⟫` is compatible with the given real scalar action.
    let : InnerProductSpace ℝ H :=
      { ‹NormedSpace ℝ H› with
        inner x y := RCLike.re ⟪x, y⟫_𝕜
        norm_sq_eq_re_inner := norm_sq_eq_re_inner
        conj_inner_symm x y := inner_re_symm (𝕜 := 𝕜) y x
        add_left x y z := by rw [inner_add_left, map_add]
        smul_left x y r := by
          rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left, RCLike.conj_ofReal,
            RCLike.re_ofReal_mul, conj_trivial] }
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
  have hpar := parallelogram_law_with_norm 𝕜 w η
  have hsub : ‖w - η‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg η, norm_nonneg (w + η)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm hsub (sq_nonneg _))))

/-- If the coefficients `g ↦ re ⟪ξ, ρ g ξ⟫` of a vector `ξ` are bounded below by a positive
constant, then a unitary representation `ρ` has a nonzero invariant vector, found in the closed
convex hull of the orbit of `ξ`. -/
theorem exists_ne_zero_mem_invariants_of_le_re_inner (hρ : ρ.IsUnitary) {ξ : H} {c : ℝ}
    (hc : 0 < c) (hξ : ∀ g, c ≤ RCLike.re ⟪ξ, ρ g ξ⟫_𝕜) :
    ∃ η ≠ 0, η ∈ ρ.invariants := by
  obtain ⟨η, hηC, hη⟩ := hρ.exists_mem_closedConvexHull_mem_invariants ξ
  -- The closed half-space `{x | c ≤ re ⟪ξ, x⟫}` contains the orbit, hence its closed convex hull.
  let f : H →L[ℝ] ℝ := RCLike.reCLM.comp ((innerSL 𝕜 ξ).restrictScalars ℝ)
  have hf (x : H) : f x = RCLike.re ⟪ξ, x⟫_𝕜 := rfl
  have hsub : closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ) ⊆ f ⁻¹' Set.Ici c :=
    closedConvexHull_min (by rintro _ ⟨g, rfl⟩; exact hξ g)
      ((convex_Ici c).linear_preimage f.toLinearMap) (isClosed_Ici.preimage f.continuous)
  refine ⟨η, fun h0 ↦ ?_, hη⟩
  have := hsub hηC
  simp only [Set.mem_preimage, Set.mem_Ici, hf, h0, inner_zero_right, map_zero] at this
  linarith

end ContRepresentation.IsUnitary
