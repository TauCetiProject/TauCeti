/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.CompleteLattice.Finset

/-!
# Symplectic area on a disc with holes

Let `(V, ω)` be a symplectic vector space. A *disc with holes* is a closed disc
`‖z - z₀‖ ≤ ρ` with finitely many open discs `‖z - cᵢ‖ < rᵢ` removed, where the closed holes lie in
the closed disc and do not overlap: `‖cᵢ - z₀‖ + rᵢ ≤ ρ` and `rᵢ + rⱼ ≤ ‖cᵢ - cⱼ‖` for `i ≠ j`.
The holes may touch each other and the outer circle. This file proves Stokes' formula for the
symplectic area of a map `u` which is `C²` at every point of the disc with holes:

`∫ u^*ω = a(u ∘ γ_{z₀, ρ}) - ∑ i, a(u ∘ γ_{cᵢ, rᵢ})`

(`SymplecticForm.integral_fderiv_apply_closedBall_sdiff_biUnion_ball`). Here
`γ_{c, r}(t) = c + r e^{2πit}` runs once counterclockwise around the circle of radius `r` about
`c`, and `a` is the loop area `TauCeti.SymplecticForm.loopArea`, the integral of the primitive
`λₓ(v) = ½ ω(x, v)` of `ω`. Nothing is assumed about `u` inside the holes, so the formula applies
to maps on punctured spheres, whose punctures lie in the holes.

The truncations of the domains of Floer theory are discs with holes: the truncation of the
thrice-punctured sphere, bounded by the circles of its three cylindrical ends
(`SymplecticForm.integral_fderiv_apply_truncation`), and the truncations of spheres with finitely
many moving input ends, which make up the associativity family of the pair-of-pants product
(`SymplecticForm.integral_fderiv_apply_closedBall_sdiff_iUnion_ball_eq_sum_loopArea_sub`). On
these domains the formula turns the symplectic area term of the energy identity into the loop
areas of the end loops, and hence the energy into the signed sum of the Hamiltonian actions of
the end loops minus the integrated curvature.

The proof removes one hole at a time. A bump function cuts `u` off inside the hole, away from its
boundary circle (`TauCeti.exists_contDiffAt_closedBall_eventuallyEq`); the cut-off map is `C²` on
the closed hole, where Stokes' formula on a closed disc
(`SymplecticForm.integral_fderiv_apply_closedBall_eq_loopArea`) applies, and it agrees with `u`
outside the hole.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.5 and 8.1.
-/

public section

open Set Metric MeasureTheory Complex Filter Topology
open scoped Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ V]

/-- **Removing one hole.** Let the open disc `‖z - c‖ < r` lie in a compact set `D`, and let `u` be
`C²` at every point of `D` outside it. Then a map `v` which is `C²` on all of `D` and agrees with
`u` outside the hole computes the symplectic area of `u` over `D` minus the hole: it is the area of
`v` over `D` minus the loop area of the boundary circle of the hole. -/
private theorem exists_integral_fderiv_apply_sdiff_ball (ω : SymplecticForm V) {D : Set ℂ}
    (hD : IsCompact D) {c : ℂ} {r : ℝ} (hr : 0 < r) (hBD : ball c r ⊆ D) {u : ℂ → V}
    (hu : ∀ z ∈ D \ ball c r, ContDiffAt ℝ 2 u z) :
    ∃ v : ℂ → V, (∀ z ∈ D, ContDiffAt ℝ 2 v z) ∧ (∀ z, r ≤ ‖z - c‖ → v z = u z) ∧
      ∫ z in D \ ball c r, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
        (∫ z in D, ω (fderiv ℝ v z 1) (fderiv ℝ v z I)) -
          ω.loopArea (fun t ↦ u (circleMap c r (2 * π * t))) := by
  -- The boundary circle of the hole lies in `D`, outside the hole.
  have hsphere : sphere c r ⊆ D \ ball c r := fun z hz ↦
    ⟨hD.isClosed.closure_subset_iff.2 hBD
      (closure_ball c hr.ne' ▸ sphere_subset_closedBall hz),
      fun h ↦ (mem_sphere.1 hz ▸ mem_ball.1 h).false⟩
  obtain ⟨v, hv, hvu'⟩ :=
    exists_contDiffAt_closedBall_eventuallyEq (n := 2) fun z hz ↦ hu z (hsphere hz)
  have hvu (z : ℂ) (hz : r ≤ ‖z - c‖) : v =ᶠ[𝓝 z] u :=
    hvu' z (by rwa [mem_ball, dist_eq_norm, not_lt])
  have hvD : ∀ z ∈ D, ContDiffAt ℝ 2 v z := by
    intro z hz
    rcases le_or_gt ‖z - c‖ r with h | h
    · exact hv z (by rw [mem_closedBall, dist_eq_norm]; exact h)
    · exact (hu z ⟨hz, by rw [mem_ball, dist_eq_norm]; exact h.not_gt⟩).congr_of_eventuallyEq
        (hvu z h.le)
  have hv_eq {z : ℂ} (hz : r ≤ ‖z - c‖) : v z = u z := (hvu z hz).eq_of_nhds
  refine ⟨v, hvD, fun z hz ↦ hv_eq hz, ?_⟩
  -- Over the hole, Stokes' formula on the closed disc applies to `v`.
  have hball : ∫ z in ball c r, ω (fderiv ℝ v z 1) (fderiv ℝ v z I) =
      ω.loopArea (fun t ↦ u (circleMap c r (2 * π * t))) := by
    rw [setIntegral_congr_set (volume.addHaar_closedBall_ae_eq_ball c r).symm,
      ω.integral_fderiv_apply_closedBall_eq_loopArea c hr hv]
    congr 1
    exact funext fun t ↦ hv_eq (by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr])
  -- Outside the hole, `v` is `u` near every point.
  have hout : ∫ z in D \ ball c r, ω (fderiv ℝ v z 1) (fderiv ℝ v z I) =
      ∫ z in D \ ball c r, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) := by
    refine setIntegral_congr_fun (hD.measurableSet.diff measurableSet_ball) fun z hz ↦ ?_
    have h : r ≤ ‖z - c‖ := by
      have := hz.2
      rwa [mem_ball, dist_eq_norm, not_lt] at this
    simp only [(hvu z h).fderiv_eq]
  have hint : IntegrableOn (fun z ↦ ω (fderiv ℝ v z 1) (fderiv ℝ v z I)) D :=
    ω.integrableOn_fderiv_apply_of_contDiffAt hD fun z hz ↦ (hvD z hz).of_le (by norm_num)
  rw [← hout, setIntegral_sdiff measurableSet_ball hint hBD, hball]

/-- **Stokes' formula for symplectic area on a disc with holes.** Let the closed discs
`‖z - cᵢ‖ ≤ rᵢ`, `i ∈ s`, lie in the closed disc `‖z - z₀‖ ≤ ρ` and have pairwise disjoint
interiors. If `u` is `C²` at every point of the disc with these holes removed, then its symplectic
area over it is the loop area of the outer boundary circle minus the loop areas of the boundary
circles of the holes, all traversed once counterclockwise:

`∫ u^*ω = a(t ↦ u(z₀ + ρ e^{2πit})) - ∑ i ∈ s, a(t ↦ u(cᵢ + rᵢ e^{2πit}))`. -/
theorem integral_fderiv_apply_closedBall_sdiff_biUnion_ball (ω : SymplecticForm V) {ι : Type*}
    (s : Finset ι) {u : ℂ → V} (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (c : ι → ℂ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) (hout : ∀ i ∈ s, ‖c i - z₀‖ + r i ≤ ρ)
    (hsep : (s : Set ι).Pairwise fun i j ↦ r i + r j ≤ ‖c i - c j‖)
    (hu : ∀ z ∈ closedBall z₀ ρ \ ⋃ i ∈ s, ball (c i) (r i), ContDiffAt ℝ 2 u z) :
    ∫ z in closedBall z₀ ρ \ ⋃ i ∈ s, ball (c i) (r i), ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      ω.loopArea (fun t ↦ u (circleMap z₀ ρ (2 * π * t))) -
        ∑ i ∈ s, ω.loopArea (fun t ↦ u (circleMap (c i) (r i) (2 * π * t))) := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty,
      Finset.sum_empty, sub_zero] at hu ⊢
    exact ω.integral_fderiv_apply_closedBall_eq_loopArea z₀ hρ hu
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hr hout
    rw [Finset.coe_insert, Set.pairwise_insert] at hsep
    -- Remove the hole about `c a` from the disc `D` with the holes of `s`.
    set D := closedBall z₀ ρ \ ⋃ i ∈ s, ball (c i) (r i) with hD
    rw [Finset.set_biUnion_insert, union_comm, ← sdiff_sdiff, ← hD] at hu ⊢
    have hsepa {i : ι} (hi : i ∈ s) : r a + r i ≤ ‖c a - c i‖ :=
      (hsep.2 i hi (by rintro rfl; exact ha hi)).1
    -- The outer circle and the closed holes of `s` lie outside the hole about `c a`, which lies
    -- in `D`.
    have hfar_out (z : ℂ) (hz : ρ ≤ ‖z - z₀‖) : r a ≤ ‖z - c a‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z (c a) z₀
      linarith [hout.1]
    have hfar_hole {i : ι} (hi : i ∈ s) (z : ℂ) (hz : ‖z - c i‖ ≤ r i) : r a ≤ ‖z - c a‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (c a) z (c i)
      rw [norm_sub_rev (c a) z] at this
      linarith [hsepa hi, norm_sub_rev z (c i)]
    have hBD : ball (c a) (r a) ⊆ D := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm]
        have := norm_sub_le_norm_sub_add_norm_sub z (c a) z₀
        linarith [hout.1]
      · simp only [mem_iUnion, mem_ball, dist_eq_norm, not_exists, not_lt]
        intro i hi
        by_contra h
        linarith [hfar_hole hi z (not_le.1 h).le]
    have hDcpt : IsCompact D :=
      (isCompact_closedBall z₀ ρ).diff (isOpen_biUnion fun i _ ↦ isOpen_ball)
    obtain ⟨v, hvD, hv_eq, hDB⟩ := ω.exists_integral_fderiv_apply_sdiff_ball hDcpt hr.1 hBD hu
    -- The induction hypothesis for `v`, whose boundary loops on `D` are those of `u`.
    have hD' := ih (u := v) hr.2 hout.2 hsep.1 hvD
    have hloop_out : (fun t ↦ v (circleMap z₀ ρ (2 * π * t))) =
        fun t ↦ u (circleMap z₀ ρ (2 * π * t)) :=
      funext fun t ↦ hv_eq _ (hfar_out _ (by rw [circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hρ]))
    have hloop_hole : ∀ i ∈ s, (fun t ↦ v (circleMap (c i) (r i) (2 * π * t))) =
        fun t ↦ u (circleMap (c i) (r i) (2 * π * t)) := fun i hi ↦
      funext fun t ↦ hv_eq _ (hfar_hole hi _ (by rw [circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos (hr.2 i hi)]))
    rw [hloop_out, Finset.sum_congr rfl fun i hi ↦ by rw [hloop_hole i hi]] at hD'
    rw [hDB, hD', Finset.sum_insert ha]
    ring

end TauCeti.SymplecticForm
