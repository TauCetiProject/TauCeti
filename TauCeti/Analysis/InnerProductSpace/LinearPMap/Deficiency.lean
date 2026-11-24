/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SymmetricSpectrum
public import TauCeti.Analysis.InnerProductSpace.Projection.DualNorm
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute.Isometry

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
`im z ≠ 0` it is therefore at most `‖w - z‖ / |im z|`. For `w` close to `z` neither subspace then
contains a nonzero vector orthogonal to the other, so the pair is acute and the two are unitarily
equivalent (`Submodule.IsAcute.nonempty_linearIsometryEquiv`); connectedness spreads this over
each half-plane.

Over `ℂ`, a closed symmetric `S` is self-adjoint exactly when its deficiency subspaces at one point
of each open half-plane vanish, equivalently at `±i`: this is von Neumann's criterion in terms of
the deficiency subspaces.

The definition of `N_z(S)` and its basic API (membership, the adjoint eigenspace description and
the vanishing criterion `LinearPMap.IsFormalAdjoint.deficiencySubspace_eq_bot_iff_surjective`)
live with the other shift API in `TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`.

## Main results

* `LinearPMap.IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le`: for
  symmetric `S`, `|im z| ‖P_{N_z(S)ᗮ} P_{N_w(S)}‖ ≤ ‖w - z‖`.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace`: for symmetric
  `S`, the deficiency subspaces at two points of a preconnected set of nonreal scalars are
  linearly isometrically equivalent.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_pos` and
  `..._of_im_neg`: the same on the open upper and lower half-planes.
* `LinearPMap.IsFormalAdjoint.conj_mem_resolventSet_of_deficiencySubspace_eq_bot`: for closed
  symmetric `S` and nonreal `z` with `N_z(S) = 0`, `conj z` is a resolvent point of `S`.
* `IsFormalAdjoint.isSelfAdjoint_iff_deficiencySubspace_eq_bot_and_deficiencySubspace_eq_bot`:
  over `ℂ`, a closed symmetric `S` is self-adjoint exactly when `N_z(S) = 0` and `N_w(S) = 0` for
  some (equivalently any) `z` in the upper and `w` in the lower half-plane.

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
theorem IsFormalAdjoint.abs_im_mul_norm_inner_le (hS : S.IsFormalAdjoint S) {u v : E}
    (hu : u ∈ S.deficiencySubspace w)
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
  have h := hS.abs_im_mul_norm_inner_le hu hv
  rw [norm_inner_symm, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀' hz']
  linarith

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
    (convex_halfSpace_gt (imLm_coe (K := 𝕜) ▸ imLm.isLinear) 0).isPreconnected
    (fun _ h ↦ ne_of_gt h) hz hw

/-- **Von Neumann's theorem on the lower half-plane.** For symmetric `S` on a Hilbert space, the
deficiency subspaces at any two points of the open lower half-plane are linearly isometrically
equivalent; in particular all are equivalent to `N₋ = N_{-i}(S)` when `𝕜 = ℂ`. -/
theorem IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_neg
    [CompleteSpace E] (hS : S.IsFormalAdjoint S) (hz : im z < 0) (hw : im w < 0) :
    Nonempty (S.deficiencySubspace z ≃ₗᵢ[𝕜] S.deficiencySubspace w) :=
  hS.nonempty_linearIsometryEquiv_deficiencySubspace
    (convex_halfSpace_lt (imLm_coe (K := 𝕜) ▸ imLm.isLinear) 0).isPreconnected
    (fun _ h ↦ ne_of_lt h) hz hw

/-- For closed symmetric `S` on a Hilbert space and nonreal `z`, if the deficiency subspace `N_z(S)`
vanishes then `conj z` is a resolvent point of `S`. -/
theorem IsFormalAdjoint.conj_mem_resolventSet_of_deficiencySubspace_eq_bot [CompleteSpace E]
    (hS : S.IsFormalAdjoint S) (hcl : S.IsClosed) (hz : im z ≠ 0)
    (h : S.deficiencySubspace z = ⊥) : starRingEnd 𝕜 z ∈ S.resolventSet :=
  hcl.mem_resolventSet_iff_bijective.2 ⟨hS.smul_sub_injective (by rwa [conj_im, neg_ne_zero]),
    (hS.deficiencySubspace_eq_bot_iff_surjective hcl hz).1 h⟩

section Complex

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : H →ₗ.[ℂ] H} {z w : ℂ}

/-- **Von Neumann's criterion via deficiency subspaces.** A closed symmetric operator `S` on a
complex Hilbert space is self-adjoint exactly when both its deficiency subspaces `N_z(S)` and
`N_w(S)` vanish, for any `z` in the open upper half-plane and `w` in the open lower half-plane; for
`z = i`, `w = -i` these are `N₊` and `N₋`. -/
theorem IsFormalAdjoint.isSelfAdjoint_iff_deficiencySubspace_eq_bot_and_deficiencySubspace_eq_bot
    (hS : S.IsFormalAdjoint S) (hcl : S.IsClosed) (hz : 0 < z.im) (hw : w.im < 0) :
    IsSelfAdjoint S ↔ S.deficiencySubspace z = ⊥ ∧ S.deficiencySubspace w = ⊥ := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hz₀, hw₀⟩ ↦ ?_⟩
  · exact (hS.deficiencySubspace_eq_bot_iff_surjective hcl hz.ne').2
      (h.smul_sub_surjective (by simpa using hz.ne'))
  · exact (hS.deficiencySubspace_eq_bot_iff_surjective hcl hw.ne).2
      (h.smul_sub_surjective (by simpa using hw.ne))
  -- `conj w` and `conj z` are resolvent points in the upper and lower half-planes.
  exact hS.isSelfAdjoint_of_mem_resolventSet (by simpa using hw)
    (hS.conj_mem_resolventSet_of_deficiencySubspace_eq_bot hcl hw.ne hw₀) (by simpa using hz)
    (hS.conj_mem_resolventSet_of_deficiencySubspace_eq_bot hcl hz.ne' hz₀)

end Complex

end LinearPMap
