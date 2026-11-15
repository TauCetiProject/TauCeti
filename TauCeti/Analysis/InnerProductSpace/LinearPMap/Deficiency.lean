/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute

/-!
# Deficiency subspaces of a symmetric operator on half-planes

For a partial linear map `S` on an inner product space over `RCLike 𝕜` and a scalar `z`, the
*deficiency subspace* `N_z(S)` is the orthogonal complement of the range of the shift
`x ↦ conj z • x - S x`. When `S` is densely defined on a Hilbert space it is the eigenspace
`ker (S† - z)` of the adjoint (`LinearPMap.mem_deficiencySubspace_iff_adjoint`), so the classical
deficiency spaces of a symmetric operator are `N₊ = N_i = ker (S† - i)` and
`N₋ = N_{-i} = ker (S† + i)`.

The main result is von Neumann's theorem that, for a symmetric `S`, the deficiency subspace is
constant up to unitary equivalence on each open half-plane: if `z` and `w` both have positive or
both have negative imaginary part, then `N_z(S)` and `N_w(S)` are linearly isometrically
equivalent. Consequently every unitary invariant of `N_z(S)`, such as its Hilbert dimension (the
cardinality of a Hilbert basis) or its `finrank`, is constant on each open half-plane. No
closedness, density or dimension hypothesis is needed.

The proof is quantitative. For `u ∈ N_w(S)` and `v` in the closure of the range of
`conj z - S`, symmetry gives `|im z| ‖⟪u, v⟫‖ ≤ ‖w - z‖ ‖u‖ ‖v‖`, so the directed gap from
`N_w(S)` to `N_z(S)` is at most `‖w - z‖ / |im z|`
(`LinearPMap.IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le`). For `w`
close to `z` neither subspace then contains a nonzero vector orthogonal to the other, so the pair
is acute and the two are unitarily equivalent (`Submodule.IsAcute.nonempty_linearIsometryEquiv`);
connectedness spreads this over each half-plane.

Over `ℂ`, a closed symmetric `S` is self-adjoint exactly when its deficiency subspaces at one point
of each open half-plane vanish, equivalently at `±i`: this is von Neumann's criterion in terms of
the deficiency subspaces.

## Main definitions

* `LinearPMap.deficiencySubspace S z`: the deficiency subspace `N_z(S)`, the orthogonal complement
  of the range of `conj z - S`.

## Main results

* `LinearPMap.mem_deficiencySubspace_iff_adjoint`: for densely defined `S`, `N_z(S)` is the
  eigenspace of `S†` for the eigenvalue `z`.
* `LinearPMap.IsFormalAdjoint.abs_im_mul_directedProjectionGap_deficiencySubspace_le`: for
  symmetric `S`, `|im z| ‖P_{N_z(S)ᗮ} P_{N_w(S)}‖ ≤ ‖w - z‖`.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace`: for symmetric
  `S`, the deficiency subspaces at two points of a preconnected set of nonreal scalars are
  linearly isometrically equivalent.
* `LinearPMap.IsFormalAdjoint.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_pos` and
  `..._of_im_neg`: the same on the open upper and lower half-planes.
* `LinearPMap.IsFormalAdjoint.deficiencySubspace_eq_bot_iff_surjective`: for closed symmetric `S`
  and nonreal `z`, `N_z(S) = 0` exactly when `conj z - S` is surjective.
* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_deficiencySubspace_eq_bot`: over `ℂ`, a closed
  symmetric `S` is self-adjoint exactly when `N_z(S) = 0` and `N_w(S) = 0` for some (equivalently
  any) `z` in the upper and `w` in the lower half-plane.

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

/-- The **deficiency subspace** `N_z(S)` of a partial linear map `S` at a scalar `z`: the
orthogonal complement of the range of the shift `x ↦ conj z • x - S x`. For densely defined `S`
on a Hilbert space it is the eigenspace `ker (S† - z)` of the adjoint
(`LinearPMap.mem_deficiencySubspace_iff_adjoint`). -/
def deficiencySubspace (S : E →ₗ.[𝕜] E) (z : 𝕜) : Submodule 𝕜 E :=
  (LinearMap.range (S.smulSub (starRingEnd 𝕜 z)))ᗮ

variable {S : E →ₗ.[𝕜] E} {z w : 𝕜}

/-- A vector lies in the deficiency subspace `N_z(S)` exactly when it is orthogonal to every
`conj z • x - S x` with `x` in the domain of `S`. -/
theorem mem_deficiencySubspace_iff {y : E} :
    y ∈ S.deficiencySubspace z ↔ ∀ x : S.domain, ⟪y, starRingEnd 𝕜 z • (x : E) - S x⟫_𝕜 = 0 := by
  simp only [deficiencySubspace, Submodule.mem_orthogonal', LinearMap.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff, smulSub_apply]

/-- The deficiency subspace is closed. -/
theorem isClosed_deficiencySubspace : _root_.IsClosed (S.deficiencySubspace z : Set E) :=
  Submodule.isClosed_orthogonal _

instance [CompleteSpace E] : CompleteSpace (S.deficiencySubspace z) :=
  inferInstanceAs (CompleteSpace (LinearMap.range (S.smulSub (starRingEnd 𝕜 z)))ᗮ)

/-- For closed symmetric `S` on a Hilbert space and nonreal `z`, the deficiency subspace `N_z(S)`
vanishes exactly when the shift `x ↦ conj z • x - S x` is surjective. -/
theorem IsFormalAdjoint.deficiencySubspace_eq_bot_iff_surjective [CompleteSpace E]
    (hS : S.IsFormalAdjoint S) (hcl : S.IsClosed) (hz : im z ≠ 0) :
    S.deficiencySubspace z = ⊥ ↔
      Function.Surjective fun x : S.domain ↦ starRingEnd 𝕜 z • (x : E) - S x := by
  have hcl' := hS.isClosed_range_smul_sub hcl (c := starRingEnd 𝕜 z) (by rwa [conj_im, neg_ne_zero])
  rw [← coe_range_smulSub] at hcl'
  have hfun : ⇑(S.smulSub (starRingEnd 𝕜 z)) =
      fun x : S.domain ↦ starRingEnd 𝕜 z • (x : E) - S x :=
    funext (smulSub_apply _ S)
  rw [deficiencySubspace, ← Submodule.topologicalClosure_eq_top_iff,
    IsClosed.submodule_topologicalClosure_eq hcl', LinearMap.range_eq_top, hfun]

/-- For densely defined `S` on a Hilbert space, the deficiency subspace `N_z(S)` is the eigenspace
`ker (S† - z)` of the adjoint. -/
theorem mem_deficiencySubspace_iff_adjoint [CompleteSpace E] (hdense : Dense (S.domain : Set E))
    {y : E} : y ∈ S.deficiencySubspace z ↔ ∃ hy : y ∈ S†.domain, S† ⟨y, hy⟩ = z • y := by
  refine ⟨fun h ↦ ?_, fun ⟨hy, hSy⟩ ↦ mem_deficiencySubspace_iff.2 fun x ↦ ?_⟩
  · simpa using exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero hdense
      (mem_deficiencySubspace_iff.1 h)
  · rw [inner_sub_right, inner_smul_right, ← adjoint_isFormalAdjoint hdense ⟨y, hy⟩ x, hSy,
      inner_smul_left, sub_self]

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
  intro u hu
  -- `p = P_{N_z(S)ᗮ} u` lies in the closure of the range of `conj z - S`, and `‖p‖² = ⟪u, p⟫`.
  set p := (S.deficiencySubspace z)ᗮ.starProjection u
  have hp : p ∈ (LinearMap.range (S.smulSub (starRingEnd 𝕜 z))).topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.starProjection_apply_mem _ u
  have hpp : ‖p‖ ^ 2 = re ⟪u, p⟫_𝕜 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ u)]
  have h := hS.abs_im_mul_norm_inner_le hu hp
  have hre : re ⟪u, p⟫_𝕜 ≤ ‖⟪u, p⟫_𝕜‖ := re_le_norm _
  rw [div_mul_eq_mul_div, le_div_iff₀ hz']
  -- From `|im z| ‖p‖² ≤ ‖w - z‖ ‖u‖ ‖p‖`, cancel one factor `‖p‖`.
  rcases (norm_nonneg p).eq_or_lt with hp0 | hp0
  · rw [← hp0, zero_mul]
    positivity
  refine le_of_mul_le_mul_right ?_ hp0
  nlinarith [norm_nonneg u, norm_nonneg (w - z)]

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

section Complex

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : H →ₗ.[ℂ] H} {z w : ℂ}

/-- **Von Neumann's criterion via deficiency subspaces.** A closed symmetric operator `S` on a
complex Hilbert space is self-adjoint exactly when its deficiency subspaces `N_z(S)` and `N_w(S)`
vanish, for any `z` in the open upper half-plane and `w` in the open lower half-plane; for
`z = i`, `w = -i` these are `N₊` and `N₋`. -/
theorem IsFormalAdjoint.isSelfAdjoint_iff_deficiencySubspace_eq_bot (hS : S.IsFormalAdjoint S)
    (hcl : S.IsClosed) (hz : 0 < z.im) (hw : w.im < 0) :
    IsSelfAdjoint S ↔ S.deficiencySubspace z = ⊥ ∧ S.deficiencySubspace w = ⊥ := by
  -- Vanishing of a deficiency subspace transfers across a half-plane.
  have htrans {a b : ℂ} (e : S.deficiencySubspace a ≃ₗᵢ[ℂ] S.deficiencySubspace b)
      (hb : S.deficiencySubspace b = ⊥) : S.deficiencySubspace a = ⊥ := by
    rw [← Submodule.subsingleton_iff_eq_bot] at hb ⊢
    exact e.toEquiv.subsingleton
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hz₀, hw₀⟩ ↦ ?_⟩
  · exact (hS.deficiencySubspace_eq_bot_iff_surjective hcl hz.ne').2
      (h.smul_sub_surjective (by simpa using hz.ne'))
  · exact (hS.deficiencySubspace_eq_bot_iff_surjective hcl hw.ne).2
      (h.smul_sub_surjective (by simpa using hw.ne))
  obtain ⟨ePlus⟩ := hS.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_pos
    (z := I) (w := z) (by simp) hz
  obtain ⟨eMinus⟩ := hS.nonempty_linearIsometryEquiv_deficiencySubspace_of_im_neg
    (z := -I) (w := w) (by simp) hw
  have hplus := (hS.deficiencySubspace_eq_bot_iff_surjective hcl (by simp)).1 (htrans ePlus hz₀)
  have hminus := (hS.deficiencySubspace_eq_bot_iff_surjective hcl (by simp)).1 (htrans eMinus hw₀)
  refine isSelfAdjoint_of_surjective_addSub S hS (fun φ ↦ ?_) (fun φ ↦ ?_)
  · obtain ⟨ψ, hψ⟩ := hplus (-φ)
    exact ⟨ψ, by simpa [neg_sub', sub_neg_eq_add, add_comm] using congrArg Neg.neg hψ⟩
  · obtain ⟨ψ, hψ⟩ := hminus (-φ)
    exact ⟨ψ, by simpa [neg_sub', sub_neg_eq_add, add_comm] using congrArg Neg.neg hψ⟩

end Complex

end LinearPMap
