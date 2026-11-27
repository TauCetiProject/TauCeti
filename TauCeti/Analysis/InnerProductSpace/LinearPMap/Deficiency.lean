/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.DualNorm
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute.Isometry
public import TauCeti.Analysis.RCLike.Convex

/-!
# Deficiency subspaces of a symmetric operator on half-planes

For a partial linear map `S` on an inner product space over `RCLike 𝕜` and a scalar `z`, the
*deficiency subspace* `N_z(S)` (`LinearPMap.deficiencySubspace`) is the orthogonal complement of
the range of the shift `x ↦ conj z • x - S x`. When `S` is densely defined on a Hilbert space it
is the eigenspace `ker (S† - z)` of the adjoint (`LinearPMap.mem_deficiencySubspace_iff_adjoint`),
so the classical deficiency spaces of a symmetric operator are `N₊ = N_i = ker (S† - i)` and
`N₋ = N_{-i} = ker (S† + i)`.

The main result is von Neumann's theorem that, for a symmetric `S` on a Hilbert space, the
deficiency subspace is constant up to unitary equivalence on each open half-plane: if `z` and `w`
both have positive or both have negative imaginary part, then `N_z(S)` and `N_w(S)` are linearly
isometrically equivalent. Consequently every unitary invariant of `N_z(S)`, such as its Hilbert
dimension (the cardinality of a Hilbert basis) or its `finrank`, is constant on each open
half-plane. No closedness, density or dimension hypothesis on `S` is needed.

The proof is quantitative. For `u ∈ N_w(S)` and `v` in the closure of the range of
`conj z - S`, symmetry gives `|im z| ‖⟪u, v⟫‖ ≤ ‖w - z‖ ‖u‖ ‖v‖`, so the directed gap from
`N_w(S)` to `N_z(S)` satisfies `|im z| ‖P_{N_z(S)ᗮ} P_{N_w(S)}‖ ≤ ‖w - z‖`
(`LinearPMap.IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le`); for
`im z ≠ 0` it is therefore at most `‖w - z‖ / |im z|`. Applying this estimate in both directions,
if `‖w - z‖ < min |im z| |im w|` then both directed gaps are less than one, so neither subspace
contains a nonzero vector orthogonal to the other. The pair is then acute and the two are
unitarily equivalent (`Submodule.IsAcute.nonempty_linearIsometryEquiv`); connectedness spreads
this over each half-plane.

The definition of `N_z(S)` and its basic API (membership, the adjoint eigenspace description and
the vanishing criteria `LinearPMap.deficiencySubspace_eq_bot_iff_denseRange` and
`LinearPMap.IsFormalAdjoint.deficiencySubspace_eq_bot_iff_smul_sub_surjective`) live with the
other shift API in `TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`. Von Neumann's
self-adjointness criterion in terms of deficiency subspaces (in the namespace
`LinearPMap.IsFormalAdjoint`,
`isSelfAdjoint_iff_deficiencySubspace_eq_bot_and_deficiencySubspace_eq_bot`) lives with the
resolvent criteria in `TauCeti.Analysis.InnerProductSpace.LinearPMap.SymmetricSpectrum`.

## Main results

* `LinearPMap.IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le`: for
  symmetric `S`, `|im z| ‖P_{N_z(S)ᗮ} P_{N_w(S)}‖ ≤ ‖w - z‖`.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace`: for symmetric
  `S`, the deficiency subspaces at two points of a preconnected set of nonreal scalars are
  linearly isometrically equivalent.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_pos` and
  `..._of_im_neg`: the same on the open upper and lower half-planes.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), §X.1.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS (2009), §2.6.
-/

public section

noncomputable section

namespace LinearPMap

open RCLike
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S : E →ₗ.[𝕜] E} {z w : 𝕜}

/-- **Deficiency vectors almost annihilate nearby shifted ranges.** For symmetric `S`, a vector
`u` of the deficiency subspace `N_w(S)` and a vector `v` in the closure of the range of
`conj z - S` satisfy `|im z| ‖⟪u, v⟫‖ ≤ ‖w - z‖ ‖u‖ ‖v‖`. -/
theorem IsFormalAdjoint.abs_im_mul_norm_inner_le_of_mem_deficiencySubspace
    (hS : S.IsFormalAdjoint S) {u v : E} (hu : u ∈ S.deficiencySubspace w)
    (hv : v ∈ (LinearMap.range (S.smulSub (starRingEnd 𝕜 z))).topologicalClosure) :
    |im z| * ‖⟪u, v⟫_𝕜‖ ≤ ‖w - z‖ * ‖u‖ * ‖v‖ := by
  refine closure_minimal (s := (LinearMap.range (S.smulSub (starRingEnd 𝕜 z)) : Set E))
    (t := {v | |im z| * ‖⟪u, v⟫_𝕜‖ ≤ ‖w - z‖ * ‖u‖ * ‖v‖}) ?_
    (isClosed_le (by fun_prop) (by fun_prop)) hv
  rintro _ ⟨x, rfl⟩
  -- `u ⊥ conj w • x - S x`, so `⟪u, conj z • x - S x⟫ = (conj z - conj w) ⟪u, x⟫`.
  have hux : ⟪u, S.smulSub (starRingEnd 𝕜 z) x⟫_𝕜 =
      (starRingEnd 𝕜 z - starRingEnd 𝕜 w) * ⟪u, (x : E)⟫_𝕜 := by
    have h := mem_deficiencySubspace_iff.1 hu x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at h
    rw [smulSub_apply, inner_sub_right, inner_smul_right, ← h, sub_mul]
  have hx := hS.abs_im_mul_norm_le_norm_smul_sub (starRingEnd 𝕜 z) x
  rw [conj_im, abs_neg] at hx
  have hn : ‖starRingEnd 𝕜 z - starRingEnd 𝕜 w‖ = ‖w - z‖ := by
    simpa [norm_sub_rev] using norm_conj (z - w)
  rw [Set.mem_ofPred_eq, hux, norm_mul, hn]
  calc |im z| * (‖w - z‖ * ‖⟪u, (x : E)⟫_𝕜‖)
      ≤ |im z| * (‖w - z‖ * (‖u‖ * ‖(x : E)‖)) := by
        gcongr
        exact norm_inner_le_norm u _
    _ = ‖w - z‖ * ‖u‖ * (|im z| * ‖(x : E)‖) := by ring
    _ ≤ ‖w - z‖ * ‖u‖ * ‖S.smulSub (starRingEnd 𝕜 z) x‖ := by
        rw [smulSub_apply]
        gcongr

/-- **Directed gap between deficiency subspaces.** For symmetric `S` on a Hilbert space, the
directed gap `‖P_{N_z(S)ᗮ} P_{N_w(S)}‖` from `N_w(S)` to `N_z(S)` satisfies
`|im z| ‖P_{N_z(S)ᗮ} P_{N_w(S)}‖ ≤ ‖w - z‖`; for nonreal `z` it is at most `‖w - z‖ / |im z|`. -/
theorem IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le [CompleteSpace E]
    (hS : S.IsFormalAdjoint S) (z w : 𝕜) :
    |im z| * Submodule.directedProjectionGap (S.deficiencySubspace w) (S.deficiencySubspace z) ≤
      ‖w - z‖ := by
  rcases eq_or_ne (im z) 0 with hz | hz
  · simp [hz]
  have hz' : 0 < |im z| := abs_pos.2 hz
  rw [← le_div_iff₀' hz', Submodule.directedProjectionGap_le_iff _ _ (by positivity)]
  refine fun u hu ↦ (Submodule.norm_starProjection_le_iff_forall_norm_inner_le _ u
    (by positivity)).2 fun v hv ↦ ?_
  rw [orthogonal_deficiencySubspace] at hv
  have h := hS.abs_im_mul_norm_inner_le_of_mem_deficiencySubspace hu hv
  calc ‖⟪v, u⟫_𝕜‖ = (|im z| * ‖⟪u, v⟫_𝕜‖) / |im z| := by
        rw [norm_inner_symm, mul_div_cancel_left₀ _ hz'.ne']
    _ ≤ (‖w - z‖ * ‖u‖ * ‖v‖) / |im z| := by gcongr
    _ = ‖w - z‖ / |im z| * ‖u‖ * ‖v‖ := by ring

/-- For symmetric `S` on a Hilbert space and `‖w - z‖ < |im z|`, no nonzero vector of `N_w(S)`
is orthogonal to `N_z(S)`. -/
theorem IsFormalAdjoint.disjoint_deficiencySubspace_orthogonal [CompleteSpace E]
    (hS : S.IsFormalAdjoint S) (h : ‖w - z‖ < |im z|) :
    Disjoint (S.deficiencySubspace w) (S.deficiencySubspace z)ᗮ := by
  refine Submodule.disjoint_orthogonal_of_directedProjectionGap_lt_one _ _ ?_
  have hz : 0 < |im z| := (norm_nonneg _).trans_lt h
  have := hS.abs_im_mul_directedProjectionGap_deficiencySubspace_le z w
  nlinarith

/-- **Deficiency subspaces at nearby points are unitarily equivalent.** For symmetric `S` on a
Hilbert space, if `‖w - z‖ < |im z|` and `‖w - z‖ < |im w|`, then `N_z(S)` and `N_w(S)` are
linearly isometrically equivalent. -/
theorem IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_norm_sub_lt
    [CompleteSpace E] (hS : S.IsFormalAdjoint S) (hz : ‖w - z‖ < |im z|)
    (hw : ‖w - z‖ < |im w|) :
    Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w) :=
  (Submodule.isAcute_iff_disjoint.2
    ⟨hS.disjoint_deficiencySubspace_orthogonal (norm_sub_rev z w ▸ hw),
      hS.disjoint_deficiencySubspace_orthogonal hz⟩).nonempty_linearIsometryEquiv

/-- **Constancy of the deficiency subspaces.** For symmetric `S` on a Hilbert space, the
deficiency subspaces `N_z(S)` and `N_w(S)` at two points of a preconnected set of nonreal scalars
are linearly isometrically equivalent. -/
theorem IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace [CompleteSpace E]
    (hS : S.IsFormalAdjoint S) {s : Set 𝕜} (hs : IsPreconnected s) (hs₀ : ∀ z ∈ s, im z ≠ 0)
    (hz : z ∈ s) (hw : w ∈ s) :
    Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w) := by
  refine hs.induction₂ (fun z w ↦ Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w))
    (fun z hz ↦ ?_) (fun _ _ _ _ _ _ ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩) (fun _ _ _ _ ⟨e⟩ ↦ ⟨e.symm⟩) hz hw
  -- On the ball of radius `|im z| / 2` about `z`, both nearness conditions hold.
  have hz' : 0 < |im z| := abs_pos.2 (hs₀ z hz)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z (half_pos hz'))] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  refine hS.nonempty_linearIsometryEquiv_deficiencySubspace_of_norm_sub_lt (by linarith) ?_
  have him : |im z| - |im w| ≤ ‖w - z‖ := by
    have := abs_im_le_norm (w - z)
    rw [AddMonoidHom.map_sub] at this
    linarith [abs_sub_abs_le_abs_sub (im z) (im w), abs_sub_comm (im w) (im z)]
  linarith

/-- **Von Neumann's theorem on the upper half-plane.** For symmetric `S` on a Hilbert space, the
deficiency subspaces at any two points of the open upper half-plane are linearly isometrically
equivalent; in particular all are equivalent to `N₊ = N_i(S)` when `𝕜 = ℂ`. -/
theorem IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_pos
    [CompleteSpace E] (hS : S.IsFormalAdjoint S) (hz : 0 < im z) (hw : 0 < im w) :
    Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w) :=
  hS.nonempty_linearIsometryEquiv_deficiencySubspace
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun _ h ↦ ne_of_gt h) hz hw

/-- **Von Neumann's theorem on the lower half-plane.** For symmetric `S` on a Hilbert space, the
deficiency subspaces at any two points of the open lower half-plane are linearly isometrically
equivalent; in particular all are equivalent to `N₋ = N_{-i}(S)` when `𝕜 = ℂ`. -/
theorem IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_neg
    [CompleteSpace E] (hS : S.IsFormalAdjoint S) (hz : im z < 0) (hw : im w < 0) :
    Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w) :=
  hS.nonempty_linearIsometryEquiv_deficiencySubspace
    (convex_halfSpace_im_lt 0).isPreconnected
    (fun _ h ↦ ne_of_lt h) hz hw

end LinearPMap
