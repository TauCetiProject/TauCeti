/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.Analysis.Convex.Topology

/-!
# The Alaoglu–Birkhoff orbit projection for unitary representations

For a unitary representation `ρ` of a monoid `M` on a Hilbert space `V` and a vector `v : V`, the
closed convex hull of the orbit `{ρ m v | m : M}` contains a unique element of minimal norm, and
that element is the orthogonal projection of `v` onto the subspace `ρ.invariants` of fixed vectors.

Minimality in norm forces invariance under every `ρ m` by the parallelogram law, since `ρ m`
preserves norms and maps the closed convex hull of the orbit into itself. On the other hand, for
every invariant vector `u` and every `m : M` one has `⟪u, v - ρ m v⟫ = 0`, so `v - z` is orthogonal
to `ρ.invariants` for every `z` in the closed convex hull; the unique invariant element in the
closed convex hull is therefore `ρ.invariants.starProjection v`.

In particular, if every element of `M` moves `v` by at most `ε`, the closed ball around `v` of
radius `ε` contains the orbit and hence its closed convex hull, so
`‖ρ.invariants.starProjection v - v‖ ≤ ε`.

## Main statements

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

variable {𝕜 M V : Type*} [RCLike 𝕜] [Monoid M] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {ρ : ContRepresentation 𝕜 M V}

section ConvexHull

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- Each operator of a representation maps the closed convex hull of an orbit into itself. -/
private theorem mapsTo_closedConvexHull_orbit (ρ : ContRepresentation 𝕜 M V) (v : V) (m : M) :
    Set.MapsTo (ρ m) (closedConvexHull ℝ (Set.range fun n : M ↦ ρ n v))
      (closedConvexHull ℝ (Set.range fun n : M ↦ ρ n v)) := by
  let C := closedConvexHull ℝ (Set.range fun n : M ↦ ρ n v)
  have hconv : Convex ℝ (ρ m ⁻¹' C) := by
    intro x hx y hy a b ha hb hab
    rw [Set.mem_preimage, map_add, ← algebraMap_smul 𝕜 a, ← algebraMap_smul 𝕜 b, map_smul, map_smul,
      algebraMap_smul, algebraMap_smul]
    exact convex_closedConvexHull hx hy ha hb hab
  have hclosed : IsClosed (ρ m ⁻¹' C) := isClosed_closedConvexHull.preimage (ρ m).continuous
  refine closedConvexHull_min ?_ hconv hclosed
  rintro _ ⟨n, rfl⟩
  exact subset_closedConvexHull ⟨m * n, by simp [mul_apply_eq_comp]⟩

/-- Every vector in the closed convex hull of the orbit of `v` under a unitary representation
differs from `v` by a vector orthogonal to `ρ.invariants`. -/
private theorem sub_mem_invariants_orthogonal_of_mem_closedConvexHull (hρ : ρ.IsUnitary) (v : V) :
    ∀ z ∈ closedConvexHull ℝ (Set.range fun m : M ↦ ρ m v), v - z ∈ ρ.invariantsᗮ := by
  let S : Set V := {z | v - z ∈ ρ.invariantsᗮ}
  have hclosed : IsClosed S :=
    (Submodule.isClosed_orthogonal _).preimage (continuous_const.sub continuous_id)
  have hconv : Convex ℝ S := by
    intro x hx y hy a b _ _ hab
    have hlin : v - (a • x + b • y) = a • (v - x) + b • (v - y) := by
      calc v - (a • x + b • y)
          = (a + b) • v - (a • x + b • y) := by rw [hab, one_smul]
        _ = a • (v - x) + b • (v - y) := by rw [add_smul, smul_sub, smul_sub]; abel
    rw [Set.mem_ofPred_eq, hlin, ← algebraMap_smul 𝕜 a, ← algebraMap_smul 𝕜 b]
    exact ρ.invariantsᗮ.add_mem (ρ.invariantsᗮ.smul_mem _ hx) (ρ.invariantsᗮ.smul_mem _ hy)
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
  rw [← closedConvexHull_eq_closure_convexHull]
  let C := closedConvexHull ℝ (Set.range fun m : M ↦ ρ m v)
  have hCne : C.Nonempty := ⟨v, subset_closedConvexHull ⟨1, by simp⟩⟩
  have hCconv : Convex ℝ C := convex_closedConvexHull
  -- Pass `InnerProductSpace.rclikeToReal 𝕜 V` explicitly rather than as a local instance so its
  -- restricted `NormedSpace ℝ V` does not clash with the caller's `[NormedSpace ℝ V]`.
  have hCconv_r : @Convex ℝ V _ _ _ (InnerProductSpace.rclikeToReal 𝕜 V).toSMul C := by
    intro x hx y hy a b ha hb hab
    have hsmul (r : ℝ) (z : V) :
        @HSMul.hSMul ℝ V V (@instHSMul ℝ V (InnerProductSpace.rclikeToReal 𝕜 V).toSMul) r z =
          r • z := algebraMap_smul 𝕜 r z
    simpa only [hsmul] using hCconv hx hy ha hb hab
  obtain ⟨w, hwC, hwmin⟩ :=
    @exists_norm_eq_iInf_of_complete_convex V _ (InnerProductSpace.rclikeToReal 𝕜 V)
      C hCne isClosed_closedConvexHull.isComplete hCconv_r 0
  have hle (z : V) (hz : z ∈ C) : ‖w‖ ≤ ‖z‖ := by
    have h0 : ‖(0 : V) - w‖ ≤ ‖(0 : V) - z‖ := by
      rw [hwmin]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (⟨z, hz⟩ : C)
    simpa using h0
  -- Minimal norm in `C` forces `ρ m w = w` by the parallelogram law.
  have hwinv : w ∈ ρ.invariants := by
    intro m
    have hmw : ρ m w ∈ C := mapsTo_closedConvexHull_orbit ρ v m hwC
    have hmid : (2 : ℝ)⁻¹ • w + (2 : ℝ)⁻¹ • ρ m w ∈ C :=
      hCconv hwC hmw (by positivity) (by positivity) (by ring)
    have hmid_norm : 2 * ‖w‖ ≤ ‖w + ρ m w‖ := by
      calc 2 * ‖w‖
          ≤ 2 * ‖(2 : ℝ)⁻¹ • w + (2 : ℝ)⁻¹ • ρ m w‖ :=
            mul_le_mul_of_nonneg_left (hle _ hmid) zero_le_two
        _ = ‖(2 : ℝ) • ((2 : ℝ)⁻¹ • (w + ρ m w))‖ := by
            rw [← smul_add, norm_smul (2 : ℝ), Real.norm_of_nonneg zero_le_two]
        _ = ‖w + ρ m w‖ := by rw [smul_smul]; norm_num
    have hpar := parallelogram_law_with_norm 𝕜 (ρ m w) w
    rw [hρ.norm_map, add_comm (ρ m w) w] at hpar
    have hsq : ‖ρ m w - w‖ ^ 2 ≤ 0 := by
      nlinarith [pow_le_pow_left₀ (by positivity) hmid_norm 2]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))))
  have heq : ρ.invariants.starProjection v = w :=
    Submodule.eq_starProjection_of_mem_orthogonal hwinv
      (hρ.sub_mem_invariants_orthogonal_of_mem_closedConvexHull v w hwC)
  exact heq ▸ hwC

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

end ContRepresentation.IsUnitary
