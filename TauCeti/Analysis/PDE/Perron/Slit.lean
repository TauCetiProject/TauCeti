/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Regular
public import TauCeti.Analysis.SpecialFunctions.Complex.Log.Reciprocal
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.LinearIsometry.ApplyEq

/-!
# Regularity at the end of a slit in the plane

In the plane a single boundary point is too small to be seen by harmonic functions: an isolated
boundary point is irregular (`TauCeti.not_isBarrier_of_mem_nhdsNE`). A segment is not. This file
proves that in a two-dimensional real inner product space `E`, a point `ξ` that is an endpoint of
a nondegenerate segment `[ξ, η]` lying outside the open set `Ω` is a regular boundary point of
`Ω` (`TauCeti.exists_isBarrier_of_disjoint_segment`). No exterior cone need touch `ξ`: on the
disc slit along a radius, the slit has empty interior, and the exterior cone condition
(`TauCeti.exists_isBarrier_of_exterior_cone`) fails at every point of the slit inside the disc.

## The barrier

Identify `E` with `ℂ` by a linear isometry `L` taking `η - ξ` to the negative real axis
(`TauCeti.exists_linearIsometryEquiv_apply_eq`), and put `z = L (x - ξ)`. Near `ξ` the set `Ω`
misses the slit `[ξ, η]`, so `z` stays in the slit plane, where the principal logarithm is
holomorphic. The local barrier is

`w x = -Re (1 / log z) = -log ‖z‖ / ((log ‖z‖)² + (arg z)²)`.

It is a barrier relative to any set inside a ball of radius less than `1` about `ξ` whose image
under `x ↦ L (x - ξ)` lies in the slit plane (`TauCeti.isBarrier_neg_inv_log_re`); in
`TauCeti.exists_isBarrier_of_disjoint_segment` this set is `Ω ∩ ball ξ ρ` with
`ρ = min ‖η - ξ‖ (1 / 2)`. It is harmonic there, being the real part of the
holomorphic function `-1 / log z`. It is positive on the punctured disc `0 < ‖z‖ < 1`, and it is
continuous on all of `closure Ω` near `ξ`, including the points of the slit, because it depends on
the argument only through `(arg z)²`, which does not jump across the negative real axis, and it
tends to `0` at `ξ`, where `log ‖z‖ → -∞`. Regularity is local
(`TauCeti.IsBarrier.exists_isBarrier_of_inter`), so the local barrier yields a barrier relative to
`Ω`.

Consequently the Dirichlet problem for harmonic functions is solvable for continuous data on every
bounded open subset of the plane each of whose boundary points is the end of a segment outside it
(`TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_disjoint_segment`), for
instance on a disc with a nondegenerate segment removed, such as a slit disc
(`TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_ball_sdiff_segment`).

## Main declarations

* `TauCeti.isBarrier_neg_inv_log_re`: the logarithmic barrier relative to a set inside a ball of
  radius less than `1` about `ξ` that misses the slit.
* `TauCeti.exists_isBarrier_of_disjoint_segment`: an endpoint of a nondegenerate segment outside
  `Ω` is a regular boundary point.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_disjoint_segment`: the
  Dirichlet problem when every boundary point is such an endpoint.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_ball_sdiff_segment`: the
  Dirichlet problem on a disc with a nondegenerate segment removed.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 (barriers and regular boundary points).
* T. Ransford, *Potential Theory in the Complex Plane*, London Mathematical Society Student
  Texts 28, Cambridge University Press, 1995, Section 4.2 (barriers built from `1 / log`, and
  regularity at points of nondegenerate components of the complement).
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} {ξ : E}

/-- **The logarithmic barrier at the end of a slit.** Let `L` be a linear isometry of `E` onto
`ℂ`, and let `Ω` lie in a ball of radius `r < 1` about `ξ`, with `L (x - ξ)` in the slit plane for
every `x ∈ Ω`. Then `x ↦ -Re (1 / log (L (x - ξ)))` is a barrier at `ξ` relative to `Ω`. Points of
`closure Ω` on the slit are allowed. -/
theorem isBarrier_neg_inv_log_re (L : E ≃ₗᵢ[ℝ] ℂ) {r : ℝ} (hr : r < 1) (hΩ : Ω ⊆ ball ξ r)
    (hslit : ∀ x ∈ Ω, L (x - ξ) ∈ Complex.slitPlane) :
    IsBarrier Ω ξ fun x ↦ -(Complex.log (L (x - ξ)))⁻¹.re := by
  -- On `closure Ω`, `‖L (x - ξ)‖ = dist x ξ ≤ r < 1`.
  have hcl : ∀ x ∈ closure Ω, ‖L (x - ξ)‖ < 1 := fun x hx ↦ by
    rw [L.norm_map, ← dist_eq_norm]
    exact (mem_closedBall.1 (closure_ball_subset_closedBall (closure_mono hΩ hx))).trans_lt hr
  have hne : ∀ x ∈ closure Ω, L (x - ξ) ≠ 1 := fun x hx h ↦ by simpa [h] using hcl x hx
  refine ⟨?_, fun x hx ↦ ?_, by simp, fun x hx hxξ ↦ ?_⟩
  · have hneg : (-fun x ↦ -(Complex.log (L (x - ξ)))⁻¹.re) =
        fun x ↦ (Complex.log (L (x - ξ)))⁻¹.re := by
      ext x
      simp
    rw [hneg]
    refine HarmonicOnNhd.subharmonicOn fun x hx ↦ ?_
    exact harmonicAt_comp_sub_right_iff.2 <| (harmonicAt_comp_linearIsometryEquiv_right_iff L).2 <|
      Complex.harmonicAt_inv_log_re (hslit x hx) (hne x (subset_closure hx))
  · exact ((Complex.continuousAt_inv_log_re (hne x hx)).comp (f := fun y ↦ L (y - ξ))
      (by fun_prop)).neg.continuousWithinAt
  · have hz : L (x - ξ) ≠ 0 := L.map_ne_zero_iff.2 (sub_ne_zero.2 hxξ)
    exact neg_pos.2 (Complex.inv_log_re_neg hz (hcl x hx))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let `L` be a linear isometry of `E` onto `ℂ` taking `η - ξ` to the negative real axis. A point
`x` no farther from `ξ` than `η` whose image `L (x - ξ)` is off the slit plane, that is, on the
nonpositive real axis, lies on the segment `[ξ, η]`. -/
private theorem mem_segment_of_not_mem_slitPlane (L : E ≃ₗᵢ[ℝ] ℂ) {x η : E} (hη : η ≠ ξ)
    (hL : L (η - ξ) = -(‖η - ξ‖ : ℂ)) (hx : L (x - ξ) ∉ Complex.slitPlane)
    (hle : ‖x - ξ‖ ≤ ‖η - ξ‖) : x ∈ segment ℝ ξ η := by
  rw [Complex.mem_slitPlane_iff_not_le_zero, not_not] at hx
  -- `L (x - ξ)` is the nonpositive real `-‖x - ξ‖`.
  have hre := Complex.re_eq_neg_norm.2 hx
  rw [L.norm_map] at hre
  have hz : L (x - ξ) = -(‖x - ξ‖ : ℂ) :=
    Complex.ext (by simpa using hre) (by simpa using (Complex.le_def.1 hx).2)
  have hpos : 0 < ‖η - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hη)
  have hpos' : (‖η - ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hxt : x - ξ = (‖x - ξ‖ / ‖η - ξ‖) • (η - ξ) := L.injective <| by
    rw [L.map_smul, hL, hz, Complex.real_smul]
    push_cast
    field_simp
  rw [segment_eq_image']
  exact ⟨‖x - ξ‖ / ‖η - ξ‖, ⟨by positivity, (div_le_one hpos).2 hle⟩, by simp [← hxt]⟩

/-- **The end of a segment outside the domain is a regular boundary point.** In a
two-dimensional real inner product space, let `Ω` be open and let `[ξ, η]`, `η ≠ ξ`, be a
segment missing `Ω`. Then `ξ` admits a barrier relative to `Ω`. -/
theorem exists_isBarrier_of_disjoint_segment (hE : Module.finrank ℝ E = 2) (hΩ : IsOpen Ω)
    {η : E} (hη : η ≠ ξ) (hseg : Disjoint (segment ℝ ξ η) Ω) : ∃ w, IsBarrier Ω ξ w := by
  -- A linear isometry onto `ℂ` taking `η - ξ` to the negative real axis.
  obtain ⟨L, hL⟩ : ∃ L : E ≃ₗᵢ[ℝ] ℂ, L (η - ξ) = -(‖η - ξ‖ : ℂ) :=
    exists_linearIsometryEquiv_apply_eq (hE.trans Complex.finrank_real_complex.symm)
      (by rw [norm_neg, Complex.norm_real, norm_norm])
  set ρ := min ‖η - ξ‖ (1 / 2)
  have hρ : 0 < ρ := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hη)) one_half_pos
  refine (isBarrier_neg_inv_log_re (Ω := Ω ∩ ball ξ ρ) L
    ((min_le_right _ _).trans_lt one_half_lt_one) inter_subset_right ?_).exists_isBarrier_of_inter
    hΩ (ball_mem_nhds ξ hρ)
  -- A point of `Ω` near `ξ` whose image is off the slit plane would lie on `[ξ, η]`.
  rintro x ⟨hxΩ, hxρ⟩
  by_contra hx
  exact disjoint_left.1 hseg (mem_segment_of_not_mem_slitPlane L hη hL hx
    ((mem_ball_iff_norm.1 hxρ).le.trans (min_le_left _ _))) hxΩ

/-- **The Dirichlet problem when every boundary point ends a segment outside the domain.** In a
two-dimensional real inner product space, let `Ω` be a bounded open set such that every
`ξ ∈ frontier Ω` is an endpoint of a nondegenerate segment `[ξ, η]` missing `Ω`. For boundary data
`g` continuous on `frontier Ω`, there is a function harmonic in `Ω`, continuous on `closure Ω` and
equal to `g` on `frontier Ω`. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_disjoint_segment
    (hE : Module.finrank ℝ E = 2) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hseg : ∀ ξ ∈ frontier Ω, ∃ η ≠ ξ, Disjoint (segment ℝ ξ η) Ω)
    {g : E → ℝ} (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  refine exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb (fun ξ hξ ↦ ?_) hg
  obtain ⟨η, hη, hd⟩ := hseg ξ hξ
  exact exists_isBarrier_of_disjoint_segment hE hΩ hη hd

/-- **The Dirichlet problem on a disc with a segment removed.** In a two-dimensional real inner
product space, let `[a, b]`, `a ≠ b`, be a nondegenerate segment, for instance a radius of the
disc, which gives the slit disc. For boundary data `g` continuous on the frontier of
`ball c R \ [a, b]`, there is a function harmonic there, continuous on the closure and equal to
`g` on the frontier. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_ball_sdiff_segment
    (hE : Module.finrank ℝ E = 2) {c a b : E} {R : ℝ} (hab : a ≠ b) {g : E → ℝ}
    (hg : ContinuousOn g (frontier (ball c R \ segment ℝ a b))) :
    ∃ u, HarmonicOnNhd u (ball c R \ segment ℝ a b) ∧
      ContinuousOn u (closure (ball c R \ segment ℝ a b)) ∧
      EqOn u g (frontier (ball c R \ segment ℝ a b)) := by
  have hΩ : IsOpen (ball c R \ segment ℝ a b) :=
    isOpen_ball.sdiff (isCompact_segment ℝ a b).isClosed
  refine exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_disjoint_segment hE hΩ
    (isBounded_ball.subset sdiff_subset) (fun ξ hξ ↦ ?_) hg
  rw [hΩ.frontier_eq] at hξ
  obtain ⟨hξcl, hξΩ⟩ := hξ
  by_cases hξR : ξ ∈ ball c R
  · -- On the segment: continue along `[a, b]` towards an endpoint other than `ξ`.
    have hξab : ξ ∈ segment ℝ a b := by_contra fun h ↦ hξΩ ⟨hξR, h⟩
    have hdisj : Disjoint (segment ℝ a b) (ball c R \ segment ℝ a b) := disjoint_sdiff_self_right
    by_cases hξa : ξ = a
    · exact ⟨b, hξa ▸ hab.symm, hξa ▸ hdisj⟩
    · exact ⟨a, Ne.symm hξa, hdisj.mono_left
        ((convex_segment a b).segment_subset hξab (left_mem_segment ℝ a b))⟩
  -- On the circle: continue radially outwards, away from the disc.
  have hR : dist ξ c = R := le_antisymm
    (mem_closedBall.1 (closure_mono sdiff_subset |>.trans closure_ball_subset_closedBall <| hξcl))
    (not_lt.1 hξR)
  have hξc : ξ ≠ c := by
    rintro rfl
    obtain ⟨x, hx⟩ := (closure_nonempty_iff.1 ⟨ξ, hξcl⟩)
    exact (dist_nonneg.trans_lt (mem_ball.1 hx.1)).ne' (by simpa using hR.symm)
  refine ⟨ξ + (ξ - c), by simpa [sub_eq_zero] using hξc, disjoint_left.2 fun y hy hyΩ ↦ ?_⟩
  rw [segment_eq_image'] at hy
  obtain ⟨θ, ⟨hθ0, -⟩, rfl⟩ := hy
  refine (not_lt.2 ?_) (mem_ball.1 hyΩ.1)
  have : ξ + θ • (ξ + (ξ - c) - ξ) - c = (1 + θ) • (ξ - c) := by module
  rw [dist_eq_norm, this, norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm, hR]
  nlinarith [dist_nonneg.trans_eq hR]

end TauCeti
