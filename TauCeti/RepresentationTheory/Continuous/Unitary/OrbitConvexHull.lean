/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Minimal

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

Moreover, for any invariant vector `u` and any `m : G`, unitarity gives `⟪u, v - ρ m v⟫ = 0`, so
`v - z` is orthogonal to `ρ.invariants` for every `z` in the closed convex hull of the orbit.
The invariant element in the closed convex hull is therefore `ρ.invariants.starProjection v`
(the Alaoglu–Birkhoff projection). In particular, if every element of `G` moves `v` by at most
`ε`, then `‖ρ.invariants.starProjection v - v‖ ≤ ε`.

## Main statements

* `ContRepresentation.IsUnitary.exists_mem_closedConvexHull_mem_invariants`: the closed convex
  hull of an orbit contains an invariant vector.
* `ContRepresentation.IsUnitary.exists_ne_zero_mem_invariants_of_le_re_inner`: a vector whose
  coefficients have real part bounded below by a positive constant yields a nonzero invariant
  vector.
* `ContRepresentation.IsUnitary.starProjection_invariants_mem_closure_convexHull`: the orthogonal
  projection of `v` onto `ρ.invariants` belongs to the closed convex hull of the orbit of `v`.
* `ContRepresentation.IsUnitary.norm_starProjection_invariants_sub_le`: if `‖ρ m v - v‖ ≤ ε` for
  every `m`, then `‖ρ.invariants.starProjection v - v‖ ≤ ε`.
* `ContRepresentation.IsUnitary.exists_invariant_norm_sub_le`: if `‖ρ m v - v‖ ≤ ε` for every `m`,
  there is an invariant vector within `ε` of `v`.

## References

* L. Alaoglu and G. Birkhoff, *General ergodic theorems*, Ann. of Math. (2) 41 (1940), 293–309.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Proposition 1.1.5.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §14.1.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation.IsUnitary

section

variable {𝕜 G H : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] [CompleteSpace H] {ρ : ContRepresentation 𝕜 G H}

/-- The closed convex hull of the orbit of a vector under a unitary representation contains an
invariant vector, namely its element of minimal norm. -/
theorem exists_mem_closedConvexHull_mem_invariants (hρ : ρ.IsUnitary) (ξ : H) :
    ∃ η ∈ closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ), η ∈ ρ.invariants := by
  set C := closedConvexHull ℝ (Set.range fun g ↦ ρ g ξ)
  have hξC : ξ ∈ C := subset_closedConvexHull ⟨1, by simp⟩
  -- `C` is a nonempty complete convex set, so it has an element `η` of minimal norm.
  obtain ⟨η, hηC, hη⟩ := TauCeti.exists_mem_forall_norm_le_of_isComplete_convex 𝕜 ⟨ξ, hξC⟩
    isClosed_closedConvexHull.isComplete convex_closedConvexHull
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

end

section Projection

variable {𝕜 M V : Type*} [RCLike 𝕜] [Monoid M] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {ρ : ContRepresentation 𝕜 M V}

section ConvexHull

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- Every vector in the closed convex hull of the orbit of `v` under a unitary representation
differs from `v` by a vector orthogonal to `ρ.invariants`. -/
private theorem sub_mem_invariants_orthogonal_of_mem_closedConvexHull (hρ : ρ.IsUnitary) (v : V) :
    ∀ z ∈ closedConvexHull ℝ (Set.range fun m : M ↦ ρ m v), v - z ∈ ρ.invariantsᗮ := by
  let S : Set V := {z | v - z ∈ ρ.invariantsᗮ}
  have hclosed : IsClosed S :=
    (Submodule.isClosed_orthogonal _).preimage (continuous_const.sub continuous_id)
  have hconv : Convex ℝ S :=
    (ρ.invariantsᗮ.restrictScalars ℝ).convex.affine_preimage
      (AffineEquiv.constVSub ℝ v).toAffineMap
  refine closedConvexHull_min ?_ hconv hclosed
  rintro _ ⟨m, rfl⟩
  rw [Set.mem_ofPred_eq, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_sub_right]
  nth_rw 2 [← hu m]
  rw [hρ.inner_map_map, sub_self]

/-- **Alaoglu–Birkhoff projection.** For a unitary representation `ρ` of a monoid `M` on a Hilbert
space, the orthogonal projection of any vector `v` onto `ρ.invariants` lies in the closed real
convex hull of the orbit `{ρ m v | m : M}`. -/
theorem starProjection_invariants_mem_closure_convexHull [CompleteSpace V] (hρ : ρ.IsUnitary)
    (v : V) :
    ρ.invariants.starProjection v ∈ closure (convexHull ℝ (Set.range fun m : M ↦ ρ m v)) := by
  obtain ⟨w, hwC, hwinv⟩ := hρ.exists_mem_closedConvexHull_mem_invariants v
  rw [← closedConvexHull_eq_closure_convexHull]
  exact Submodule.eq_starProjection_of_mem_orthogonal hwinv
    (hρ.sub_mem_invariants_orthogonal_of_mem_closedConvexHull v w hwC) ▸ hwC

end ConvexHull

variable [CompleteSpace V]

/-- If every element of `M` moves `v` by at most `ε`, the orthogonal projection of `v` onto
`ρ.invariants` is within `ε` of `v`. -/
theorem norm_starProjection_invariants_sub_le (hρ : ρ.IsUnitary) {v : V} {ε : ℝ}
    (hv : ∀ m, ‖ρ m v - v‖ ≤ ε) :
    ‖ρ.invariants.starProjection v - v‖ ≤ ε := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  let : IsScalarTower ℝ 𝕜 V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hmem : ρ.invariants.starProjection v ∈ Metric.closedBall v ε := by
    have hmem' := hρ.starProjection_invariants_mem_closure_convexHull v
    rw [← closedConvexHull_eq_closure_convexHull] at hmem'
    refine closedConvexHull_min ?_ (convex_closedBall v ε) Metric.isClosed_closedBall hmem'
    rintro _ ⟨m, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hv m
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hmem

/-- If every element of `M` moves `v` by at most `ε`, there is an invariant vector within `ε` of
`v`. -/
theorem exists_invariant_norm_sub_le (hρ : ρ.IsUnitary) {v : V} {ε : ℝ}
    (hv : ∀ m, ‖ρ m v - v‖ ≤ ε) :
    ∃ w ∈ ρ.invariants, ‖w - v‖ ≤ ε :=
  ⟨ρ.invariants.starProjection v, Submodule.starProjection_apply_mem _ v,
    hρ.norm_starProjection_invariants_sub_le hv⟩

end Projection

end ContRepresentation.IsUnitary
