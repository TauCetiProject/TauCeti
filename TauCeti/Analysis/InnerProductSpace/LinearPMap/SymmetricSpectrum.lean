/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.Resolvent.Characterization
public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# The resolvent set of a symmetric operator

Let `S` be a symmetric (formally self-adjoint) partial linear map on a Hilbert space over an
`RCLike` field. At a nonreal scalar `z` the shift `z • I - S` is bounded below by `|im z|`, so a
resolvent of `S` at `z` has norm at most `|im z|⁻¹`, and a Neumann series shows that the whole
disc of radius `|im z|` about a nonreal resolvent point consists of resolvent points. Hence the
resolvent set is relatively closed in the nonreal scalars, and, being open, it either contains or
misses each connected set of nonreal scalars, in particular each open half-plane.

Over `ℂ` this gives the classical four-way alternative for a symmetric operator `S` on a complex
Hilbert space: the resolvent set of `S` is empty, exactly the open lower half-plane, exactly the
open upper half-plane, or contains every nonreal point; and `S` is self-adjoint exactly when its
spectrum is real. In the second and third cases `S` is closed but not self-adjoint; when `S` is
not closed, its resolvent set is empty.

For a closed densely defined symmetric `S` and nonreal `z`, the scalar `z` is a resolvent point
exactly when `conj z` is not an eigenvalue of the adjoint `S†`: the range of `z • I - S` is
closed, and its orthogonal complement is the eigenspace `ker (S† - conj z)`, the deficiency
space at `z`. This is the link between the four alternatives and the deficiency indices of `S`.

## Main results

In the namespace `LinearPMap.IsFormalAdjoint`:

* `ball_subset_resolventSet`: the disc of radius `|im z|` about a resolvent point `z` consists
  of resolvent points.
* `closure_resolventSet_inter_subset`: every nonreal point of the closure of the resolvent set
  is a resolvent point.
* `subset_resolventSet_or_disjoint`: a preconnected set of nonreal scalars lies in the resolvent
  set or is disjoint from it.
* `mem_resolventSet_iff_of_im_pos`, `mem_resolventSet_iff_of_im_neg`: membership in the
  resolvent set is constant on each open half-plane.
* `mem_resolventSet_iff_forall_adjoint_apply_eq_smul`: for a closed densely defined symmetric
  operator, a nonreal `z` is a resolvent point exactly when `S†` has no eigenvector for
  `conj z`.
* `isSelfAdjoint_of_mem_resolventSet`: one resolvent point in each open half-plane makes a
  symmetric operator on a complex Hilbert space self-adjoint.
* `resolventSet_alternatives`, `spectrum_alternatives`: the four possible resolvent sets and
  spectra of a symmetric operator on a complex Hilbert space.
* `isSelfAdjoint_iff_spectrum_subset`: a symmetric operator on a complex Hilbert space is
  self-adjoint exactly when its spectrum is real.

## Implementation notes

The alternative is proved by connectedness of the half-planes, using only the resolvent bound
`‖R(z)‖ ≤ |im z|⁻¹` and the Neumann series, rather than from the half-plane constancy of the
deficiency dimensions. The partial-operator spectrum is `LinearPMap.spectrum`, the complement of
`LinearPMap.resolventSet`, so a resolvent point requires a bounded inverse of `z • I - S` with
values in the domain.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), Theorem X.1.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  American Mathematical Society (2009), Theorem 2.18.
-/

public section

open Metric Set

namespace LinearPMap.IsFormalAdjoint

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {S : E →ₗ.[𝕜] E}

/-- **Resolvent discs of a symmetric operator.** The open disc of radius `|im z|` about a
resolvent point `z` of a symmetric operator consists of resolvent points. When `z` is real the
disc is empty. -/
theorem ball_subset_resolventSet (hS : S.IsFormalAdjoint S) {z : 𝕜}
    (hz : z ∈ S.resolventSet) : ball z |RCLike.im z| ⊆ S.resolventSet := by
  intro w hw
  have him : RCLike.im z ≠ 0 := by
    rintro h
    simp [h] at hw
  refine TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one hz ?_
  calc ‖w - z‖ * ‖S.resolvent z‖ ≤ ‖w - z‖ * |RCLike.im z|⁻¹ := by
        gcongr
        exact hS.norm_resolvent_le hz him
    _ < 1 := by
        rwa [← dist_eq_norm, mul_inv_lt_iff₀ (abs_pos.mpr him), one_mul, ← mem_ball]

/-- **The resolvent set of a symmetric operator is relatively closed off the real axis.** Every
nonreal point of the closure of the resolvent set is a resolvent point. -/
theorem closure_resolventSet_inter_subset (hS : S.IsFormalAdjoint S) :
    _root_.closure S.resolventSet ∩ {z | RCLike.im z ≠ 0} ⊆ S.resolventSet := by
  rintro w ⟨hw, him⟩
  have him' : 0 < |RCLike.im w| := abs_pos.mpr him
  obtain ⟨z, hz, hwz⟩ := Metric.mem_closure_iff.mp hw (|RCLike.im w| / 2) (by positivity)
  refine hS.ball_subset_resolventSet hz (mem_ball.mpr ?_)
  -- `|im w| ≤ |im z| + |im (w - z)| ≤ |im z| + dist w z`, and `dist w z < |im w| / 2`.
  have him_sub : |RCLike.im w - RCLike.im z| ≤ dist w z := by
    rw [dist_eq_norm, ← _root_.map_sub RCLike.im w z]
    exact RCLike.abs_im_le_norm _
  have := abs_sub_abs_le_abs_sub (RCLike.im w) (RCLike.im z)
  linarith

/-- **Resolvent alternative on connected sets.** A preconnected set of nonreal scalars is either
contained in the resolvent set of a symmetric operator or disjoint from it. -/
theorem subset_resolventSet_or_disjoint (hS : S.IsFormalAdjoint S) {s : Set 𝕜}
    (hs : IsPreconnected s) (him : ∀ z ∈ s, RCLike.im z ≠ 0) :
    s ⊆ S.resolventSet ∨ Disjoint s S.resolventSet := by
  rcases (s ∩ S.resolventSet).eq_empty_or_nonempty with h | h
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr h)
  · exact Or.inl (hs.subset_of_closure_inter_subset S.isOpen_resolventSet h
      fun z hz ↦ hS.closure_resolventSet_inter_subset ⟨hz.1, him z hz.2⟩)

/-- A resolvent point in a preconnected set of nonreal scalars puts the whole set in the
resolvent set of a symmetric operator. -/
private theorem subset_resolventSet_of_mem (hS : S.IsFormalAdjoint S) {s : Set 𝕜}
    (hs : IsPreconnected s) (him : ∀ z ∈ s, RCLike.im z ≠ 0) {z : 𝕜} (hz : z ∈ s)
    (hzρ : z ∈ S.resolventSet) : s ⊆ S.resolventSet :=
  (hS.subset_resolventSet_or_disjoint hs him).resolve_right
    fun h ↦ h.notMem_of_mem_left hz hzρ

/-- Membership in the resolvent set of a symmetric operator is constant on the open upper
half-plane. -/
theorem mem_resolventSet_iff_of_im_pos (hS : S.IsFormalAdjoint S) {z w : 𝕜}
    (hz : 0 < RCLike.im z) (hw : 0 < RCLike.im w) :
    z ∈ S.resolventSet ↔ w ∈ S.resolventSet := by
  have hs : IsPreconnected {u : 𝕜 | 0 < RCLike.im u} :=
    (convex_halfSpace_gt RCLike.imLm.isLinear 0).isPreconnected
  have him : ∀ u ∈ {u : 𝕜 | 0 < RCLike.im u}, RCLike.im u ≠ 0 := fun _ h ↦ ne_of_gt h
  exact ⟨fun h ↦ hS.subset_resolventSet_of_mem hs him hz h hw,
    fun h ↦ hS.subset_resolventSet_of_mem hs him hw h hz⟩

/-- Membership in the resolvent set of a symmetric operator is constant on the open lower
half-plane. -/
theorem mem_resolventSet_iff_of_im_neg (hS : S.IsFormalAdjoint S) {z w : 𝕜}
    (hz : RCLike.im z < 0) (hw : RCLike.im w < 0) :
    z ∈ S.resolventSet ↔ w ∈ S.resolventSet := by
  have hs : IsPreconnected {u : 𝕜 | RCLike.im u < 0} :=
    (convex_halfSpace_lt RCLike.imLm.isLinear 0).isPreconnected
  have him : ∀ u ∈ {u : 𝕜 | RCLike.im u < 0}, RCLike.im u ≠ 0 := fun _ h ↦ ne_of_lt h
  exact ⟨fun h ↦ hS.subset_resolventSet_of_mem hs him hz h hw,
    fun h ↦ hS.subset_resolventSet_of_mem hs him hw h hz⟩

/-- **Nonreal resolvent points and deficiency vectors.** For a closed densely defined symmetric
operator `S` and a nonreal scalar `z`, `z` is a resolvent point of `S` exactly when the adjoint
`S†` has no nonzero eigenvector for the eigenvalue `conj z`, that is, when the deficiency space
`ker (S† - conj z)` is trivial. -/
theorem mem_resolventSet_iff_forall_adjoint_apply_eq_smul (hS : S.IsFormalAdjoint S)
    (hdense : Dense (S.domain : Set E)) (hcl : S.IsClosed) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    z ∈ S.resolventSet ↔
      ∀ y : S†.domain, S† y = (starRingEnd 𝕜) z • (y : E) → (y : E) = 0 :=
  ⟨fun hρ ↦ (denseRange_smul_sub_iff hdense).mp
    (mem_resolventSet_iff_isClosed_denseRange_norm_le.mp hρ).2.1, fun hker ↦
    mem_resolventSet_iff_isClosed_denseRange_norm_le.mpr ⟨hS.isClosed_range_smul_sub hcl hz,
      (denseRange_smul_sub_iff hdense).mpr hker, _, abs_pos.mpr hz,
      hS.abs_im_mul_norm_le_norm_smul_sub z⟩⟩

end RCLike

section Complex

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : H →ₗ.[ℂ] H}

/-- **One resolvent point in each half-plane makes a symmetric operator self-adjoint.** A
symmetric operator on a complex Hilbert space with a resolvent point in the open upper half-plane
and one in the open lower half-plane is self-adjoint. -/
theorem isSelfAdjoint_of_mem_resolventSet (hS : S.IsFormalAdjoint S) {z w : ℂ}
    (hz : 0 < z.im) (hzρ : z ∈ S.resolventSet) (hw : w.im < 0) (hwρ : w ∈ S.resolventSet) :
    IsSelfAdjoint S := by
  have hI : I ∈ S.resolventSet := (hS.mem_resolventSet_iff_of_im_pos hz (by simp)).mp hzρ
  have hnegI : -I ∈ S.resolventSet := (hS.mem_resolventSet_iff_of_im_neg hw (by simp)).mp hwρ
  refine isSelfAdjoint_of_surjective_addSub S hS (fun φ ↦ ?_) fun φ ↦ ?_
  · obtain ⟨ψ, hψ⟩ := (smul_sub_bijective hnegI).surjective (-φ)
    beta_reduce at hψ
    exact ⟨ψ, by rw [← neg_neg φ, ← hψ, neg_smul, neg_sub, sub_neg_eq_add, add_comm]⟩
  · obtain ⟨ψ, hψ⟩ := (smul_sub_bijective hI).surjective (-φ)
    beta_reduce at hψ
    exact ⟨ψ, by rw [← neg_neg φ, ← hψ, neg_sub]⟩

/-- **The four possible resolvent sets of a symmetric operator.** The resolvent set of a
symmetric operator on a complex Hilbert space is empty, exactly the open lower half-plane,
exactly the open upper half-plane, or contains every nonreal point. -/
theorem resolventSet_alternatives (hS : S.IsFormalAdjoint S) :
    S.resolventSet = ∅ ∨ S.resolventSet = {z : ℂ | z.im < 0} ∨
      S.resolventSet = {z : ℂ | 0 < z.im} ∨ {z : ℂ | z.im ≠ 0} ⊆ S.resolventSet := by
  have hU := hS.subset_resolventSet_or_disjoint
    (convex_halfSpace_gt (f := fun z : ℂ ↦ z.im) Complex.imLm.isLinear 0).isPreconnected
    fun _ hz ↦ by rw [mem_ofPred_eq] at hz; exact hz.ne'
  have hL := hS.subset_resolventSet_or_disjoint
    (convex_halfSpace_lt (f := fun z : ℂ ↦ z.im) Complex.imLm.isLinear 0).isPreconnected
    fun _ hz ↦ by rw [mem_ofPred_eq] at hz; exact hz.ne
  -- An open set missing an open half-plane misses its closure, so it lies in the opposite one.
  have hpos (h : Disjoint {z : ℂ | z.im < 0} S.resolventSet) :
      S.resolventSet ⊆ {z : ℂ | 0 < z.im} := fun z hz ↦ by
    have := (h.symm.closure_right S.isOpen_resolventSet).notMem_of_mem_left hz
    rwa [closure_setOfPred_im_lt, mem_ofPred_eq, not_le] at this
  have hneg (h : Disjoint {z : ℂ | 0 < z.im} S.resolventSet) :
      S.resolventSet ⊆ {z : ℂ | z.im < 0} := fun z hz ↦ by
    have := (h.symm.closure_right S.isOpen_resolventSet).notMem_of_mem_left hz
    rwa [closure_setOfPred_lt_im, mem_ofPred_eq, not_le] at this
  rcases hU with hU | hU <;> rcases hL with hL | hL
  · exact Or.inr (Or.inr (Or.inr fun z hz ↦ (ne_iff_lt_or_gt.mp hz).elim (hL ·) (hU ·)))
  · exact Or.inr (Or.inr (Or.inl (Subset.antisymm (hpos hL) hU)))
  · exact Or.inr (Or.inl (Subset.antisymm (hneg hU) hL))
  · refine Or.inl (eq_empty_of_forall_notMem fun z hz ↦ ?_)
    have hz₁ := hpos hL hz
    have hz₂ := hneg hU hz
    rw [mem_ofPred_eq] at hz₁ hz₂
    exact lt_asymm hz₁ hz₂

/-- **The spectrum of a symmetric operator.** The spectrum of a symmetric operator on a complex
Hilbert space is all of `ℂ`, the closed upper half-plane, the closed lower half-plane, or a subset
of the real axis. -/
theorem spectrum_alternatives (hS : S.IsFormalAdjoint S) :
    S.spectrum = univ ∨ S.spectrum = {z : ℂ | 0 ≤ z.im} ∨ S.spectrum = {z : ℂ | z.im ≤ 0} ∨
      S.spectrum ⊆ {z : ℂ | z.im = 0} := by
  have hspec : S.spectrum = S.resolventSetᶜ := Set.ext fun z ↦ S.mem_spectrum_iff z
  rcases hS.resolventSet_alternatives with h | h | h | h
  · exact Or.inl (by rw [hspec, h, compl_empty])
  · exact Or.inr (Or.inl (by rw [hspec, h]; exact Set.ext fun z ↦ by simp))
  · exact Or.inr (Or.inr (Or.inl (by rw [hspec, h]; exact Set.ext fun z ↦ by simp)))
  · refine Or.inr (Or.inr (Or.inr fun z hz ↦ not_not.mp fun hne ↦ ?_))
    exact (S.mem_spectrum_iff z).mp hz (h hne)

/-- **Self-adjointness through the spectrum.** A symmetric operator on a complex Hilbert space is
self-adjoint exactly when its spectrum is contained in the real axis. -/
theorem isSelfAdjoint_iff_spectrum_subset (hS : S.IsFormalAdjoint S) :
    IsSelfAdjoint S ↔ S.spectrum ⊆ {z : ℂ | z.im = 0} := by
  refine ⟨fun h ↦ by simpa using h.spectrum_subset_im_eq_zero, fun h ↦ ?_⟩
  have hres (z : ℂ) (hz : z.im ≠ 0) : z ∈ S.resolventSet := by
    by_contra hz'
    exact hz (h ((S.mem_spectrum_iff z).mpr hz'))
  exact hS.isSelfAdjoint_of_mem_resolventSet (z := I) (w := -I) (by simp) (hres _ (by simp))
    (by simp) (hres _ (by simp))

end Complex

end LinearPMap.IsFormalAdjoint
