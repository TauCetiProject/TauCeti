/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift
import TauCeti.Analysis.Normed.Operator.Resolvent.Characterization
import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# The resolvent set of a symmetric operator

Let `A` be a symmetric (formally self-adjoint) partial linear map on a Hilbert space over an
`RCLike` field. At a nonreal resolvent point `z` the resolvent obeys `‖R(z)‖ ≤ |im z|⁻¹`, so the
Neumann series shows that the whole disc `‖w - z‖ < |im z|` lies in the resolvent set. A disc of
this radius around a point near `z` contains `z` again, so the resolvent set is relatively open
and relatively closed in the nonreal points. On a connected set of nonreal points, in particular
on each open half-plane, the resolvent set is therefore either everything or nothing.

Over `ℂ` this gives the classical alternative for the resolvent set of a symmetric operator: it
is empty, exactly the open lower half-plane, exactly the open upper half-plane, or it contains
every nonreal point. Since the resolvent set is open, a real resolvent point forces both
half-planes into the resolvent set. Equivalently, the spectrum is all of `ℂ`, the closed upper
half-plane, the closed lower half-plane, or a subset of the real axis. The last case is exactly
the self-adjoint one: a symmetric operator with a resolvent point in each open half-plane is
self-adjoint by von Neumann's criterion `LinearPMap.isSelfAdjoint_of_surjective_addSub`.
No closedness or density hypothesis is needed, since an operator with a resolvent point is
automatically closed, and the alternative `ρ(A) = ∅` covers every other operator.

For a closed, densely defined symmetric operator, a nonreal `z` is a resolvent point exactly when
the deficiency space `ker (A† - conj z)` is zero: the shift `z - A` is injective with closed range,
and a vector orthogonal to that range is an eigenvector of the adjoint `A†` for `conj z`.

## Main results

* `LinearPMap.IsFormalAdjoint.mem_resolventSet_of_norm_sub_lt`: the disc of radius `|im z|`
  around a nonreal resolvent point lies in the resolvent set.
* `LinearPMap.IsFormalAdjoint.subset_resolventSet_of_isPreconnected`: a preconnected set of
  nonreal points meeting the resolvent set lies in it.
* `LinearPMap.IsFormalAdjoint.mem_resolventSet_iff_of_im_pos` and
  `LinearPMap.IsFormalAdjoint.mem_resolventSet_iff_of_im_neg`: membership in the resolvent set is
  constant on each open half-plane.
* `LinearPMap.IsFormalAdjoint.mem_resolventSet_iff_forall_adjoint_apply_eq_smul`: for a closed,
  densely defined symmetric operator and nonreal `z`, `z ∈ ρ(A)` if and only if `A†` has no
  nonzero eigenvector for `conj z`.
* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_mem_resolventSet`: over `ℂ`, a symmetric operator
  with a resolvent point in each open half-plane is self-adjoint.
* `LinearPMap.IsFormalAdjoint.resolventSet_alternatives` and
  `LinearPMap.IsFormalAdjoint.spectrum_alternatives`: the four alternatives for the resolvent set
  and the spectrum of a symmetric operator over `ℂ`.
* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_spectrum_subset_im_eq_zero`: a symmetric
  operator over `ℂ` is self-adjoint if and only if its spectrum is real.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  American Mathematical Society (2009), Lemma 2.7 and Theorem 2.18.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem VIII.3.
-/

public section

open Complex Set

namespace LinearPMap

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →ₗ.[𝕜] E}

/-- **Resolvent discs of a symmetric operator.** If `z` is a resolvent point of a symmetric
operator, then so is every `w` with `‖w - z‖ < |im z|`. -/
theorem IsFormalAdjoint.mem_resolventSet_of_norm_sub_lt (hA : A.IsFormalAdjoint A) {z w : 𝕜}
    (hz : z ∈ A.resolventSet) (hw : ‖w - z‖ < |RCLike.im z|) : w ∈ A.resolventSet := by
  have him : 0 < |RCLike.im z| := (norm_nonneg _).trans_lt hw
  refine TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one hz ?_
  calc ‖w - z‖ * ‖A.resolvent z‖ ≤ ‖w - z‖ * |RCLike.im z|⁻¹ := by
        gcongr
        exact hA.norm_resolvent_le hz (abs_pos.mp him)
    _ < |RCLike.im z| * |RCLike.im z|⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ him.ne'

/-- A nonreal point in the closure of the resolvent set of a symmetric operator lies in the
resolvent set. -/
theorem IsFormalAdjoint.mem_resolventSet_of_mem_closure (hA : A.IsFormalAdjoint A) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) (hcl : z ∈ _root_.closure A.resolventSet) : z ∈ A.resolventSet := by
  have hpos : 0 < |RCLike.im z| / 2 := by positivity
  obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.mp hcl _ hpos
  rw [dist_eq_norm] at hwz
  refine hA.mem_resolventSet_of_norm_sub_lt hw ?_
  have him : |RCLike.im z| - |RCLike.im w| ≤ ‖z - w‖ :=
    (abs_sub_abs_le_abs_sub _ _).trans (by simpa using RCLike.abs_im_le_norm (z - w))
  linarith

/-- **A connected family of nonreal points meets the resolvent set entirely or not at all.** If a
preconnected set of nonreal points contains a resolvent point of a symmetric operator, it lies in
the resolvent set. -/
theorem IsFormalAdjoint.subset_resolventSet_of_isPreconnected (hA : A.IsFormalAdjoint A)
    {s : Set 𝕜} (hs : IsPreconnected s) (him : ∀ z ∈ s, RCLike.im z ≠ 0)
    (hne : (s ∩ A.resolventSet).Nonempty) : s ⊆ A.resolventSet := by
  refine hs.subset_left_of_subset_union A.isOpen_resolventSet isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr subset_closure) (fun z hz ↦ ?_) hne
  by_cases hcl : z ∈ _root_.closure A.resolventSet
  · exact Or.inl (hA.mem_resolventSet_of_mem_closure (him z hz) hcl)
  · exact Or.inr hcl

/-- Membership in the resolvent set of a symmetric operator is constant on the open upper
half-plane. -/
theorem IsFormalAdjoint.mem_resolventSet_iff_of_im_pos (hA : A.IsFormalAdjoint A) {z w : 𝕜}
    (hz : 0 < RCLike.im z) (hw : 0 < RCLike.im w) :
    z ∈ A.resolventSet ↔ w ∈ A.resolventSet := by
  have hs : IsPreconnected {u : 𝕜 | 0 < RCLike.im u} :=
    (convex_halfSpace_gt RCLike.imLm.isLinear 0).isPreconnected
  have key : ∀ u v : 𝕜, 0 < RCLike.im u → 0 < RCLike.im v → u ∈ A.resolventSet →
      v ∈ A.resolventSet := fun u v hu hv hρ ↦
    hA.subset_resolventSet_of_isPreconnected hs (fun u (h : 0 < RCLike.im u) ↦ h.ne')
      ⟨u, hu, hρ⟩ hv
  exact ⟨key z w hz hw, key w z hw hz⟩

/-- Membership in the resolvent set of a symmetric operator is constant on the open lower
half-plane. -/
theorem IsFormalAdjoint.mem_resolventSet_iff_of_im_neg (hA : A.IsFormalAdjoint A) {z w : 𝕜}
    (hz : RCLike.im z < 0) (hw : RCLike.im w < 0) :
    z ∈ A.resolventSet ↔ w ∈ A.resolventSet := by
  have hs : IsPreconnected {u : 𝕜 | RCLike.im u < 0} :=
    (convex_halfSpace_lt RCLike.imLm.isLinear 0).isPreconnected
  have key : ∀ u v : 𝕜, RCLike.im u < 0 → RCLike.im v < 0 → u ∈ A.resolventSet →
      v ∈ A.resolventSet := fun u v hu hv hρ ↦
    hA.subset_resolventSet_of_isPreconnected hs (fun u (h : RCLike.im u < 0) ↦ h.ne)
      ⟨u, hu, hρ⟩ hv
  exact ⟨key z w hz hw, key w z hw hz⟩

/-- **Nonreal resolvent points and deficiency spaces.** For a closed, densely defined symmetric
operator `A` and nonreal `z`, the point `z` lies in the resolvent set exactly when the adjoint
`A†` has no nonzero eigenvector for the eigenvalue `conj z`, that is, when the deficiency space
`ker (A† - conj z)` is zero. -/
theorem IsFormalAdjoint.mem_resolventSet_iff_forall_adjoint_apply_eq_smul
    (hA : A.IsFormalAdjoint A) (hcl : A.IsClosed) (hdense : Dense (A.domain : Set E)) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    z ∈ A.resolventSet ↔
      ∀ y : A†.domain, A† y = (starRingEnd 𝕜) z • (y : E) → (y : E) = 0 := by
  refine ⟨fun hρ ↦ (denseRange_smul_sub_iff hdense).mp
    (mem_resolventSet_iff_isClosed_denseRange_norm_le.mp hρ).2.1, fun hker ↦ ?_⟩
  exact mem_resolventSet_iff_isClosed_denseRange_norm_le.mpr ⟨hA.isClosed_range_smul_sub hcl hz,
    (denseRange_smul_sub_iff hdense).mpr hker, _, abs_pos.mpr hz,
    hA.abs_im_mul_norm_le_norm_smul_sub z⟩

end RCLike

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **One resolvent point in each half-plane makes a symmetric operator self-adjoint.** A
symmetric partial linear map on a complex Hilbert space with a resolvent point in the open upper
half-plane and one in the open lower half-plane is self-adjoint. -/
theorem IsFormalAdjoint.isSelfAdjoint_of_mem_resolventSet (hA : A.IsFormalAdjoint A) {z w : ℂ}
    (hz : 0 < z.im) (hzρ : z ∈ A.resolventSet) (hw : w.im < 0) (hwρ : w ∈ A.resolventSet) :
    IsSelfAdjoint A := by
  have hI : I ∈ A.resolventSet := (hA.mem_resolventSet_iff_of_im_pos hz (by simp)).mp hzρ
  have hnegI : -I ∈ A.resolventSet := (hA.mem_resolventSet_iff_of_im_neg hw (by simp)).mp hwρ
  refine isSelfAdjoint_of_surjective_addSub A hA (fun φ ↦ ?_) (fun φ ↦ ?_)
  · obtain ⟨ψ, hψ⟩ := (smul_sub_bijective hnegI).2 (-φ)
    have hψ' : (-I) • (ψ : H) - A ψ = -φ := hψ
    refine ⟨ψ, ?_⟩
    rw [← neg_neg φ, ← hψ', neg_smul]
    abel
  · obtain ⟨ψ, hψ⟩ := (smul_sub_bijective hI).2 (-φ)
    have hψ' : I • (ψ : H) - A ψ = -φ := hψ
    exact ⟨ψ, by rw [← neg_sub, hψ', neg_neg]⟩

/-- **The resolvent set of a symmetric operator.** For a symmetric partial linear map `A` on a
complex Hilbert space, the resolvent set is empty, exactly the open lower half-plane, exactly the
open upper half-plane, or contains every nonreal point. In the last case `A` is self-adjoint
(`IsFormalAdjoint.isSelfAdjoint_of_mem_resolventSet`). -/
theorem IsFormalAdjoint.resolventSet_alternatives (hA : A.IsFormalAdjoint A) :
    A.resolventSet = ∅ ∨ A.resolventSet = {z | z.im < 0} ∨ A.resolventSet = {z | 0 < z.im} ∨
      {z | z.im ≠ 0} ⊆ A.resolventSet := by
  -- The resolvent set is open, so if it misses one open half-plane it lies in the interior of
  -- the other closed half-plane, which is the other open half-plane.
  have hpos (hL : -I ∉ A.resolventSet) : A.resolventSet ⊆ {z | 0 < z.im} := by
    rw [← Complex.interior_setOfPred_le_im]
    refine interior_maximal (fun z hz ↦ mem_ofPred.mpr (not_lt.mp fun h ↦ hL ?_))
      A.isOpen_resolventSet
    exact (hA.mem_resolventSet_iff_of_im_neg h (by simp)).mp hz
  have hneg (hU : I ∉ A.resolventSet) : A.resolventSet ⊆ {z | z.im < 0} := by
    rw [← Complex.interior_setOfPred_im_le]
    refine interior_maximal (fun z hz ↦ mem_ofPred.mpr (not_lt.mp fun h ↦ hU ?_))
      A.isOpen_resolventSet
    exact (hA.mem_resolventSet_iff_of_im_pos h (by simp)).mp hz
  by_cases hU : I ∈ A.resolventSet <;> by_cases hL : -I ∈ A.resolventSet
  · refine Or.inr (Or.inr (Or.inr fun z hz ↦ ?_))
    rcases (show z.im ≠ 0 from hz).lt_or_gt with h | h
    · exact (hA.mem_resolventSet_iff_of_im_neg (by simp) h).mp hL
    · exact (hA.mem_resolventSet_iff_of_im_pos (by simp) h).mp hU
  · refine Or.inr (Or.inr (Or.inl (subset_antisymm (hpos hL) fun z hz ↦ ?_)))
    exact (hA.mem_resolventSet_iff_of_im_pos (by simp) hz).mp hU
  · refine Or.inr (Or.inl (subset_antisymm (hneg hU) fun z hz ↦ ?_))
    exact (hA.mem_resolventSet_iff_of_im_neg (by simp) hz).mp hL
  · exact Or.inl (eq_empty_of_forall_notMem fun z hz ↦
      (mem_ofPred.mp (hpos hL hz)).not_ge (mem_ofPred.mp (hneg hU hz)).le)

/-- **The spectrum of a symmetric operator.** For a symmetric partial linear map on a complex
Hilbert space, the spectrum is all of `ℂ`, the closed upper half-plane, the closed lower
half-plane, or a subset of the real axis. -/
theorem IsFormalAdjoint.spectrum_alternatives (hA : A.IsFormalAdjoint A) :
    A.spectrum = univ ∨ A.spectrum = {z | 0 ≤ z.im} ∨ A.spectrum = {z | z.im ≤ 0} ∨
      A.spectrum ⊆ {z | z.im = 0} := by
  have hspec : A.spectrum = A.resolventSetᶜ := Set.ext fun z ↦ A.mem_spectrum_iff z
  rcases hA.resolventSet_alternatives with h | h | h | h
  · exact Or.inl (by rw [hspec, h, compl_empty])
  · exact Or.inr (Or.inl (by rw [hspec, h]; exact Set.ext fun z ↦ by simp))
  · exact Or.inr (Or.inr (Or.inl (by rw [hspec, h]; exact Set.ext fun z ↦ by simp)))
  · refine Or.inr (Or.inr (Or.inr fun z hz ↦ not_not.mp fun hne ↦ ?_))
    exact (A.mem_spectrum_iff z).mp hz (h hne)

/-- **Self-adjointness criterion.** A symmetric partial linear map on a complex Hilbert space is
self-adjoint if and only if its spectrum is contained in the real axis. -/
theorem IsFormalAdjoint.isSelfAdjoint_iff_spectrum_subset_im_eq_zero
    (hA : A.IsFormalAdjoint A) :
    IsSelfAdjoint A ↔ A.spectrum ⊆ {z | z.im = 0} := by
  refine ⟨fun h ↦ by simpa using h.spectrum_subset_im_eq_zero, fun h ↦ ?_⟩
  have hρ : ∀ z : ℂ, z.im ≠ 0 → z ∈ A.resolventSet := fun z hz ↦
    not_not.mp fun hzρ ↦ hz (h ((A.mem_spectrum_iff z).mpr hzρ))
  exact hA.isSelfAdjoint_of_mem_resolventSet (z := I) (w := -I) (by simp) (hρ _ (by simp))
    (by simp) (hρ _ (by simp))

end Complex

end LinearPMap
