/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Winding
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Boundary degrees of maps of round discs

Let `h` be a complex-valued function continuous on the closed disc of radius `r > 0` about `z₀`,
with no zero on the boundary circle. Its boundary direction map
`u : S¹ → S¹`, `u ζ = h(z₀ + rζ) / ‖h(z₀ + rζ)‖`, has a degree `Circle.degree u.toBasedLoop`: the
number of times `h` winds around `0` along the circle. When `h = α ∘ σ` for a disc `σ` and a
section `α`, this is the framed charge of `σ`
(`TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree`).

This file identifies the boundary degree with a homological local degree
(`TauCeti.HomologicalOrientation.localDegree`): the zeros of `h` in the open disc form a compact
set, and the local degree at `0` of `h` on the open disc, oriented by restricting an orientation
`o` of `ℂ`, is the boundary degree
(`TauCeti.HomologicalOrientation.localDegree_comap_ball_eq_degree_toBasedLoop`). The same holds
for a map defined on any open set containing the closed disc, all of whose zeros lie in the open
disc (`TauCeti.HomologicalOrientation.localDegree_comap_eq_degree_toBasedLoop`). The local degree
needs no boundary circle, so this transfers its laws to boundary degrees:

* **proper degree**: if `θ : U' → D` is a proper map into the open disc, then the boundary degree
  of `h ∘ θ` along any circle in `U'` enclosing its zeros is `deg θ` times the boundary degree of
  `h`
  (`TauCeti.HomologicalOrientation.degree_toBasedLoop_comp_eq_degree_mul`), where `deg θ` is the
  homological degree of a proper map (`TauCeti.HomologicalOrientation.degree`);
* **additivity**: if finitely many pairwise disjoint open subdiscs of the closed disc contain all
  its zeros, the boundary degree of `h` is the sum of its boundary degrees along those circles
  (`Circle.degree_toBasedLoop_eq_sum`). For the empty family this is the vanishing of the degree
  of a map without zeros, and for a single subdisc it is the invariance of the boundary degree
  under passing to a subdisc containing all the zeros.

The proof extends `h` from the closed disc to the plane by the radial retraction onto the disc
(`TauCeti.centeredRadialRetraction`). The extension has no zero outside the open disc, so its local
degree at `0` is the boundary degree
(`TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`), and that local degree is
read on the open disc by naturality under open embeddings
(`TauCeti.HomologicalOrientation.localDegree_comap`) and on subdiscs by additivity
(`TauCeti.HomologicalOrientation.localDegree_eq_sum`).

## Main results

* `TauCeti.HomologicalOrientation.localDegree_comap_ball_eq_degree_toBasedLoop`: the local degree of
  `h` on the open disc is its boundary degree.
* `TauCeti.HomologicalOrientation.localDegree_comap_eq_degree_toBasedLoop`: the same for a map on
  an open set containing the closed disc, with all its zeros in the open disc.
* `TauCeti.HomologicalOrientation.degree_toBasedLoop_comp_eq_degree_mul`: boundary degrees multiply
  by the degree of a proper map into the open disc.
* `Circle.degree_toBasedLoop_eq_sum`: boundary degrees are additive over disjoint subdiscs
  containing all the zeros.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
-/

public section

noncomputable section

open Complex Filter Metric Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable (o : HomologicalOrientation ℂ ℂ 2) {z₀ : ℂ} {r : ℝ}

/-! ### The radial extension of a disc map -/

/-- The extension of `h` from the closed disc of radius `r` about `z₀` to the plane, constant along
the rays leaving the disc. -/
private def radialExtension {h : ℂ → ℂ} (hr : 0 < r) (hh : ContinuousOn h (closedBall z₀ r)) :
    C(ℂ, ℂ) :=
  ⟨h ∘ centeredRadialRetraction z₀ r,
    hh.comp_continuous (lipschitzWith_centeredRadialRetraction hr.le).continuous
      (centeredRadialRetraction_mem_closedBall hr.le)⟩

private theorem radialExtension_apply {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) {w : ℂ} (hw : w ∈ closedBall z₀ r) :
    radialExtension hr hh w = h w :=
  congrArg h (centeredRadialRetraction_of_mem_closedBall hw)

/-- Without zeros of `h` on the boundary circle, the zeros of the radial extension lie in the open
disc. -/
private theorem radialExtension_preimage_zero_subset {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0) :
    radialExtension hr hh ⁻¹' {0} ⊆ ball z₀ r := fun w hw ↦ by
  by_contra hwb
  rw [mem_ball, not_lt] at hwb
  refine hne _ ?_ hw
  rw [mem_sphere, dist_centeredRadialRetraction hr.le, min_eq_right hwb]

private theorem isCompact_radialExtension_preimage_zero {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0) :
    IsCompact (radialExtension hr hh ⁻¹' {0}) :=
  (isCompact_closedBall z₀ r).of_isClosed_subset
    (isClosed_singleton.preimage (radialExtension hr hh).continuous)
    ((radialExtension_preimage_zero_subset hr hh hne).trans ball_subset_closedBall)

/-- On an open set `B` equal to the open disc, the radial extension restricts to the restriction
`g` of `h`. -/
private theorem radialExtension_comp_val {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) {B : TopologicalSpace.Opens ℂ}
    (hB : (B : Set ℂ) = ball z₀ r) {g : C(B, ℂ)} (hg : ∀ z : B, g z = h z) :
    (radialExtension hr hh).comp ⟨Subtype.val, continuous_subtypeVal⟩ = g :=
  ContinuousMap.ext fun z ↦ (radialExtension_apply hr hh
    (ball_subset_closedBall (hB ▸ z.property : (z : ℂ) ∈ ball z₀ r))).trans (hg z).symm

/-- Without zeros of `h` on the boundary circle, the zeros of the radial extension lie in an open
set `B` equal to the open disc. -/
private theorem radialExtension_preimage_zero_subset_range {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0)
    {B : TopologicalSpace.Opens ℂ} (hB : (B : Set ℂ) = ball z₀ r) :
    radialExtension hr hh ⁻¹' {0} ⊆ range (Subtype.val : B → ℂ) := fun w hw ↦
  ⟨⟨w, (hB ▸ radialExtension_preimage_zero_subset hr hh hne hw : w ∈ (B : Set ℂ))⟩, rfl⟩

/-- The local degree at `0` of the radial extension is the boundary degree of `h`. -/
private theorem localDegree_radialExtension {h : ℂ → ℂ} (hr : 0 < r)
    (hh : ContinuousOn h (closedBall z₀ r)) (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0)
    {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = h (z₀ + r * ζ) / ‖h (z₀ + r * ζ)‖) :
    o.localDegree o finrank_real_complex (radialExtension hr hh) 0 =
      Circle.degree u.toBasedLoop := by
  set G := radialExtension hr hh
  -- Centred at `0`, the extension has no zero outside the disc of radius `r`.
  have hG : ∀ w : ℂ, r ≤ ‖w‖ → G.comp (ContinuousMap.addRight z₀) w ≠ 0 := fun w hw hGw ↦ by
    have h := radialExtension_preimage_zero_subset hr hh hne hGw
    rw [mem_ball, dist_eq_norm, ContinuousMap.coe_addRight, add_sub_cancel_right] at h
    exact h.not_ge hw
  have hcirc (ζ : Circle) : G.comp (ContinuousMap.addRight z₀) (r * ζ) = h (z₀ + r * ζ) := by
    rw [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, add_comm]
    exact radialExtension_apply hr hh (by simp [abs_of_pos hr])
  rw [← o.localDegree_eq_degree_toBasedLoop hr hG fun ζ ↦ by rw [hcirc, hu],
    o.localDegree_comp o o finrank_real_complex finrank_real_complex finrank_real_complex
      (isCompact_radialExtension_preimage_zero hr hh hne) (Homeomorph.addRight z₀).isProperMap,
    o.degree_addRight finrank_real_complex, one_mul]

/-! ### Boundary degrees as local degrees -/

/-- **The local degree of a disc map is its boundary degree.** Let `h` be continuous on the closed
disc of radius `r > 0` about `z₀`, with no zero on the boundary circle, and let `g` be its
restriction to the open disc `B`, oriented by restricting the orientation `o` of `ℂ`. Then the local
degree of `g` at `0` is the degree of the boundary direction map
`ζ ↦ h(z₀ + rζ) / ‖h(z₀ + rζ)‖`. -/
theorem localDegree_comap_ball_eq_degree_toBasedLoop (hr : 0 < r)
    {B : TopologicalSpace.Opens ℂ} (hB : (B : Set ℂ) = ball z₀ r) {h : ℂ → ℂ}
    (hh : ContinuousOn h (closedBall z₀ r)) (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0) {g : C(B, ℂ)}
    (hg : ∀ z : B, g z = h z) {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = h (z₀ + r * ζ) / ‖h (z₀ + r * ζ)‖) :
    (o.comap B.isOpenEmbedding').localDegree o finrank_real_complex g 0 =
      Circle.degree u.toBasedLoop := by
  rw [← radialExtension_comp_val hr hh hB hg, o.localDegree_comap o finrank_real_complex
      finrank_real_complex (j := ⟨Subtype.val, continuous_subtypeVal⟩) B.isOpenEmbedding' _
      (radialExtension_preimage_zero_subset_range hr hh hne hB),
    o.localDegree_radialExtension hr hh hne hu]

/-- **The local degree of a map on an open set is the boundary degree of an enclosing disc.** Let
`g` be continuous on an open set `U ⊆ ℂ`, oriented by restricting the orientation `o` of `ℂ`, and
let `U` contain the closed disc of radius `r > 0` about `z₀`. If every zero of `g` lies in the open
disc, the local degree of `g` at `0` is the degree of the boundary direction map
`ζ ↦ g(z₀ + rζ) / ‖g(z₀ + rζ)‖`. -/
theorem localDegree_comap_eq_degree_toBasedLoop (hr : 0 < r) {U : TopologicalSpace.Opens ℂ}
    (hU : closedBall z₀ r ⊆ U) {g : C(U, ℂ)} (hg : ∀ z : U, g z = 0 → (z : ℂ) ∈ ball z₀ r)
    {u : C(Circle, Circle)}
    (hu : ∀ (ζ : Circle) (hζ : z₀ + r * ζ ∈ U), (u ζ : ℂ) = g ⟨_, hζ⟩ / ‖g ⟨_, hζ⟩‖) :
    (o.comap U.isOpenEmbedding').localDegree o finrank_real_complex g 0 =
      Circle.degree u.toBasedLoop := by
  classical
  -- `g`, extended by zero off `U`, is continuous on the closed disc.
  set h : ℂ → ℂ := fun z ↦ if hz : z ∈ U then g ⟨z, hz⟩ else 0
  have hgh (z : U) : h z = g z := by simp [h]
  have hh : ContinuousOn h (closedBall z₀ r) :=
    (continuousOn_iff_continuous_domRestrict.2
      (by convert g.continuous using 1; ext z; exact hgh z) : ContinuousOn h U).mono hU
  have hne (z : ℂ) (hz : z ∈ sphere z₀ r) : h z ≠ 0 := fun hz0 ↦ by
    have h' := hg ⟨z, hU (sphere_subset_closedBall hz)⟩ ((hgh _).symm.trans hz0)
    exact (mem_sphere.1 hz).not_lt (mem_ball.1 h')
  set G := radialExtension hr hh
  let j : C(U, ℂ) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hGsub := radialExtension_preimage_zero_subset hr hh hne
  -- On the open disc, `G ∘ j` agrees with `g`, and both have their zeros there.
  have hcongr : (o.comap U.isOpenEmbedding').localDegree o finrank_real_complex g 0 =
      (o.comap U.isOpenEmbedding').localDegree o finrank_real_complex (G.comp j) 0 := by
    refine (o.comap U.isOpenEmbedding').localDegree_congr o finrank_real_complex
      finrank_real_complex ?_ fun z hz ↦ ?_
    · refine eventually_nhdsSet_iff_exists.2 ⟨j ⁻¹' ball z₀ r, isOpen_ball.preimage j.continuous,
        fun z hz ↦ hg z hz, fun z hz ↦ ?_⟩
      exact (hgh z).symm.trans (radialExtension_apply hr hh (ball_subset_closedBall hz)).symm
    · have hz' := hGsub hz
      exact ((hgh z).symm.trans (radialExtension_apply hr hh (ball_subset_closedBall hz')).symm
        |>.trans hz :)
  rw [hcongr, o.localDegree_comap o finrank_real_complex finrank_real_complex
      (j := j) U.isOpenEmbedding' _ fun w hw ↦ ⟨⟨w, hU (ball_subset_closedBall (hGsub hw))⟩, rfl⟩,
    o.localDegree_radialExtension hr hh hne fun ζ ↦ ?_]
  have hζ : z₀ + r * ζ ∈ U := hU (by simp [abs_of_pos hr])
  rw [hu ζ hζ, ← hgh ⟨_, hζ⟩]

/-! ### The laws of boundary degrees -/

/-- **Boundary degrees multiply by the degree of a proper map.** Let `h` be continuous on the
closed disc of radius `r > 0` about `z₀`, with no zero on the boundary circle, let `g` be its
restriction to the open disc `B`, and let `θ : U' → B` be a proper map from an open set `U'`. If
the closed disc of radius `r' > 0` about `z₁` lies in `U'` and contains every zero of `g ∘ θ` in
its interior, the boundary degree of `g ∘ θ` along its boundary circle is the degree of `θ` times
the boundary degree of `h`. The open sets are oriented by restricting the orientation `o` of
`ℂ`. -/
theorem degree_toBasedLoop_comp_eq_degree_mul (hr : 0 < r) {B U' : TopologicalSpace.Opens ℂ}
    (hB : (B : Set ℂ) = ball z₀ r) {h : ℂ → ℂ} (hh : ContinuousOn h (closedBall z₀ r))
    (hne : ∀ z ∈ sphere z₀ r, h z ≠ 0) {g : C(B, ℂ)} (hg : ∀ z : B, g z = h z) {θ : C(U', B)}
    (hθ : IsProperMap θ) {z₁ : ℂ} {r' : ℝ} (hr' : 0 < r') (hU' : closedBall z₁ r' ⊆ U')
    (hgθ : ∀ z : U', g (θ z) = 0 → (z : ℂ) ∈ ball z₁ r') {u u' : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = h (z₀ + r * ζ) / ‖h (z₀ + r * ζ)‖)
    (hu' : ∀ (ζ : Circle) (hζ : z₁ + r' * ζ ∈ U'),
      (u' ζ : ℂ) = g (θ ⟨_, hζ⟩) / ‖g (θ ⟨_, hζ⟩)‖) :
    Circle.degree u'.toBasedLoop =
      (o.comap U'.isOpenEmbedding').degree (o.comap B.isOpenEmbedding') finrank_real_complex θ *
        Circle.degree u.toBasedLoop := by
  have : PreconnectedSpace B :=
    isPreconnected_iff_preconnectedSpace.1 (hB ▸ isPreconnected_ball)
  -- The zeros of `g` are those of the radial extension, a compact subset of the open disc.
  have hgc : IsCompact (g ⁻¹' {0}) := by
    rw [← radialExtension_comp_val hr hh hB hg]
    exact B.isOpenEmbedding'.isInducing.isCompact_preimage'
      (isCompact_radialExtension_preimage_zero hr hh hne)
      (radialExtension_preimage_zero_subset_range hr hh hne hB)
  rw [← o.localDegree_comap_eq_degree_toBasedLoop hr' hU' hgθ (g := g.comp θ) hu',
    (o.comap U'.isOpenEmbedding').localDegree_comp (o.comap B.isOpenEmbedding') o
      finrank_real_complex finrank_real_complex finrank_real_complex hgc hθ,
    o.localDegree_comap_ball_eq_degree_toBasedLoop hr hB hh hne hg hu]

end HomologicalOrientation

end TauCeti

namespace Circle

open TauCeti

/-- **Boundary degrees are additive over disjoint subdiscs.** Let `h` be continuous on the closed
disc of radius `r > 0` about `z₀`. Let finitely many closed subdiscs, of radii `ρ i > 0` about
`c i`, have pairwise disjoint interiors, and suppose that every zero of `h` in the closed disc lies
in one of their interiors. Then the boundary degree of `h` along the circle of radius `r` is the
sum of its boundary degrees along the circles of radii `ρ i`. -/
theorem degree_toBasedLoop_eq_sum {ι : Type*} [Fintype ι] {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {h : ℂ → ℂ} (hh : ContinuousOn h (closedBall z₀ r)) {c : ι → ℂ} {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, closedBall (c i) (ρ i) ⊆ closedBall z₀ r)
    (hdisj : Pairwise fun i k ↦ Disjoint (ball (c i) (ρ i)) (ball (c k) (ρ k)))
    (hzero : ∀ z ∈ closedBall z₀ r, h z = 0 → ∃ i, z ∈ ball (c i) (ρ i))
    {u : C(Circle, Circle)} (hu : ∀ ζ : Circle, (u ζ : ℂ) = h (z₀ + r * ζ) / ‖h (z₀ + r * ζ)‖)
    {v : ι → C(Circle, Circle)}
    (hv : ∀ i (ζ : Circle), (v i ζ : ℂ) = h (c i + ρ i * ζ) / ‖h (c i + ρ i * ζ)‖) :
    degree u.toBasedLoop = ∑ i, degree (v i).toBasedLoop := by
  -- The zeros of `h` lie in the open subdiscs, so off the outer circle and the subdisc circles.
  have hne (z) (hz : z ∈ sphere z₀ r) : h z ≠ 0 := fun hz0 ↦ by
    obtain ⟨i, hi⟩ := hzero z (sphere_subset_closedBall hz) hz0
    have hball : ball (c i) (ρ i) ⊆ ball z₀ r := interior_closedBall z₀ hr.ne' ▸
      interior_maximal (ball_subset_closedBall.trans (hsub i)) isOpen_ball
    exact (mem_sphere.1 hz).not_lt (mem_ball.1 (hball hi))
  have hne' (i) (z) (hz : z ∈ sphere (c i) (ρ i)) : h z ≠ 0 := fun hz0 ↦ by
    obtain ⟨k, hk⟩ := hzero z (hsub i (sphere_subset_closedBall hz)) hz0
    obtain rfl | hik := eq_or_ne i k
    · exact (mem_sphere.1 hz).not_lt (mem_ball.1 hk)
    · refine disjoint_left.1 ((hdisj hik).closure_left isOpen_ball) ?_ hk
      rw [closure_ball _ (hρ i).ne']
      exact sphere_subset_closedBall hz
  have o : HomologicalOrientation ℂ ℂ 2 :=
    (HomologicalOrientation.nonempty_of_simplyConnectedSpace finrank_real_complex).some
  set G := HomologicalOrientation.radialExtension hr hh
  let D (i : ι) : TopologicalSpace.Opens ℂ := ⟨ball (c i) (ρ i), isOpen_ball⟩
  have hGsub := HomologicalOrientation.radialExtension_preimage_zero_subset hr hh hne
  rw [← o.localDegree_radialExtension hr hh hne hu,
    o.localDegree_eq_sum o finrank_real_complex finrank_real_complex G
      (HomologicalOrientation.isCompact_radialExtension_preimage_zero hr hh hne) (U := D)
      (fun i k hik ↦ (hdisj hik).mono inter_subset_right inter_subset_right)
      fun w hw ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦
      o.localDegree_comap_ball_eq_degree_toBasedLoop (hρ i) rfl (hh.mono (hsub i)) (hne' i)
        (fun z ↦ HomologicalOrientation.radialExtension_apply hr hh
          (hsub i (ball_subset_closedBall z.property))) (hv i)
  · have hw' := ball_subset_closedBall (hGsub hw)
    have hw0 : h w = 0 := (HomologicalOrientation.radialExtension_apply hr hh hw').symm.trans hw
    exact mem_iUnion.2 (hzero w hw' hw0)

end Circle
