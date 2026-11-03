/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Configuration
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Disjoint
public import TauCeti.Geometry.Manifold.SmoothEmbedding.RadialContraction
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Orientation

/-!
# Moving finite ordered configurations of discs

Let `M` be a Hausdorff boundaryless manifold modelled on a finite-dimensional real normed space
`E` of dimension greater than one, oriented by `oM`, and let `U` be a preconnected open subset.
Consider two finite families `f i` and `g i` of smooth embeddings `E → M`, indexed by the same
labels, each family having pairwise disjoint images contained in `U`, and all preserving the
orientations at the origin. Each embedding is a disc together with an embedded collar: its image
of a closed ball is a closed disc, and the rest of its image is a collar around that disc. Then
one diffeotopy of `M`, fixing every point outside a compact subset of `U`, carries every `f i` to
`g i` with its label, on any prescribed compact subset of `E`
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_pairwise_disjoint`). Points outside `U`, for
instance protected discs and an outer boundary collar, are never moved.

The proof first matches the centres `f i 0` and `g i 0` by the motion of finite ordered point
configurations (`TauCeti.exists_diffeotopy_final_comp_eq_of_isPreconnected`). It then shrinks
every embedding by a radial contraction about the origin, inside its own image, by the relative
ambient disc theorem
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt_of_range_subset`);
the images of a family are pairwise disjoint, so the motions of the different labels have
disjoint supports and combine
(`TauCeti.exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint`). After the centres have been
matched, a sufficiently small shrink of the moved `f i` lies in the image of `g i`, where the
relative disc theorem matches it with the same shrink of `g i`. Undoing the shrink of the `g i`
finishes.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_pairwise_disjoint`: in dimension greater
  than one, two finite ordered configurations of orientation-preserving discs with collars in a
  preconnected open set agree on any compact subset of `E` after a diffeotopy supported in a
  compact subset of that open set.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.3 (the disc
  theorem and its ambient form).
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma.
-/

public noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι ι' : Type*} [Fintype ι']

/-- The relative disc theorem inside the image of an embedding `h` of `E`, which is open and
preconnected. -/
private theorem exists_diffeotopy_eqOn_of_range_subset_range [T2Space M]
    (h a b : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (ha : range a ⊆ range h)
    (hb : range b ⊆ range h) (o : Manifold.Orientation 𝓘(ℝ, E) E ι')
    (oM : Manifold.Orientation 𝓘(ℝ, E) M ι') (hao : o.IsOrientationPreservingAt oM a 0)
    (hbo : o.IsOrientationPreservingAt oM b 0) {A : Set E} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ K ⊆ range h ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧ EqOn (Φ.final ∘ a) b A :=
  exists_diffeotopy_eqOn_of_isOrientationPreservingAt_of_range_subset
    (h.isLocalDiffeomorph rfl (by simp)).isOpen_range
    (isPreconnected_range h.contMDiff.continuous) a b ha hb o oM hao hbo hA

/-- Finitely many orientation-preserving embeddings with pairwise disjoint images are shrunk
simultaneously by radial contractions about the origin, by one diffeotopy supported in a compact
subset of the union of their images. -/
private theorem exists_diffeotopy_eqOn_compRadialContraction [T2Space M] [Finite ι]
    (f : ι → SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i))) {κ : ι → ℝ} (hκ : ∀ i, 0 ≤ κ i)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι') (oM : Manifold.Orientation 𝓘(ℝ, E) M ι')
    (hfo : ∀ i, o.IsOrientationPreservingAt oM (f i) 0) {A : Set E} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ K ⊆ ⋃ i, range (f i) ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
        ∀ i, EqOn (Φ.final ∘ f i) ((f i).compRadialContraction le_rfl (hκ i)) A := by
  cases nonempty_fintype ι
  have hshrink (i : ι) : range ((f i).compRadialContraction le_rfl (hκ i)) ⊆ range (f i) :=
    (f i).range_compRadialContraction_subset le_rfl (hκ i)
  obtain ⟨Φ, K, hK, hKf, hΦK, hΦ⟩ :=
    exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint Finset.univ (hfd.set_pairwise _)
      (a := fun i ↦ f i) (b := fun i ↦ (f i).compRadialContraction le_rfl (hκ i))
      (fun i _ x _ ↦ mem_range_self x) (fun i _ x _ ↦ hshrink i (mem_range_self x)) fun i _ ↦
        exists_diffeotopy_eqOn_of_range_subset_range (f i) (f i) _ subset_rfl (hshrink i) o oM
          (hfo i) (isOrientationPreservingAt_compRadialContraction _ le_rfl _ (hfo i)) hA
  exact ⟨Φ, K, hK, by simpa using hKf, hΦK, fun i ↦ hΦ i (Finset.mem_univ i)⟩

/-- **Moving ordered configurations of discs.** Let `U` be a preconnected open subset of a
Hausdorff boundaryless manifold `M` modelled on a finite-dimensional real normed space `E` of
dimension greater than one. Let `f` and `g` be two families of smooth embeddings `E → M`, indexed
by the same finite set of labels, which preserve the orientations `o` of `E` and `oM` of `M` at
the origin, and such that each family has pairwise disjoint images contained in `U`. On every
compact subset `A` of `E`, every `g i` is `f i` followed by the final diffeomorphism of one smooth
diffeotopy of `M` fixing every point outside a compact subset of `U`. -/
theorem exists_diffeotopy_eqOn_of_pairwise_disjoint [T2Space M] [Finite ι]
    (hdim : 1 < Module.rank ℝ E) {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U)
    (f g : ι → SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (hgd : Pairwise (Disjoint on fun i ↦ range (g i)))
    (hfU : ∀ i, range (f i) ⊆ U) (hgU : ∀ i, range (g i) ⊆ U)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι') (oM : Manifold.Orientation 𝓘(ℝ, E) M ι')
    (hfo : ∀ i, o.IsOrientationPreservingAt oM (f i) 0)
    (hgo : ∀ i, o.IsOrientationPreservingAt oM (g i) 0) {A : Set E} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧ ∀ i, EqOn (Φ.final ∘ f i) (g i) A := by
  classical
  cases nonempty_fintype ι
  -- Step 1: match the centres, which are distinct because the images are disjoint.
  have hcentre {h : ι → SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M}
      (hd : Pairwise (Disjoint on fun i ↦ range (h i))) : Injective fun i ↦ h i 0 :=
    fun i j hij ↦ by_contra fun hne ↦ (hd hne).ne_of_mem (mem_range_self 0) (mem_range_self 0) hij
  obtain ⟨Φ₀, K₀, hK₀, hK₀U, hΦ₀K₀, hΦ₀⟩ := exists_diffeotopy_final_comp_eq_of_isPreconnected
    (n := ∞) (m := ⊤) hdim le_top le_rfl hU hUc (hcentre hfd) (hcentre hgd)
    (fun i ↦ hfU i (mem_range_self 0)) (fun i ↦ hgU i (mem_range_self 0))
  let f' (i : ι) := (f i).transDiffeomorph Φ₀.final
  have hf'0 (i : ι) : f' i 0 = g i 0 := by
    rw [transDiffeomorph_apply]
    exact congrFun hΦ₀ i
  have hf'o (i : ι) : o.IsOrientationPreservingAt oM (f' i) 0 := by
    rw [coe_transDiffeomorph]
    exact (Φ₀.isOrientationPreservingAt_final (by simp) oM (f i 0)).comp (hfo i)
  -- Step 2: choose radial contractions so small that the moved `f i`, shrunk, lands in the
  -- image of `g i`.
  have hr (i : ι) : ∃ r > 0, ∀ y, f' i (radialContraction 0 (r⁻¹ ^ 2) y) ∈ range (g i) := by
    have hmem : f' i ⁻¹' range (g i) ∈ 𝓝 0 :=
      (f' i).contMDiff.continuous.continuousAt.preimage_mem_nhds
        (((g i).isLocalDiffeomorph rfl (by simp)).isOpen_range.mem_nhds
        (hf'0 i ▸ mem_range_self 0))
    obtain ⟨r, hr, hrsub⟩ := Euclidean.nhds_basis_ball.mem_iff.mp hmem
    exact ⟨r, hr, fun y ↦ hrsub (radialContraction_mem_ball 0 y hr)⟩
  choose r hr0 hr using hr
  have hκ (i : ι) : 0 ≤ (r i)⁻¹ ^ 2 := sq_nonneg _
  let shrink (h : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (i : ι) :=
    h.compRadialContraction le_rfl (hκ i)
  -- Step 3: shrink every `f i`, and every `g i`, inside its own image.
  obtain ⟨Sf, Kf, hKf, hKfU, hSfK, hSf⟩ :=
    exists_diffeotopy_eqOn_compRadialContraction f hfd hκ o oM hfo hA
  obtain ⟨Sg, Kg, hKg, hKgU, hSgK, hSg⟩ :=
    exists_diffeotopy_eqOn_compRadialContraction g hgd hκ o oM hgo hA
  -- Step 4: match the shrunk moved `f i` with the shrunk `g i`, inside the image of `g i`.
  have hf'g (i : ι) : range (shrink (f' i) i) ⊆ range (g i) := by
    rintro _ ⟨y, rfl⟩
    simpa [shrink] using hr i y
  have hgg (i : ι) : range (shrink (g i) i) ⊆ range (g i) :=
    (g i).range_compRadialContraction_subset le_rfl (hκ i)
  obtain ⟨L, KL, hKL, hKLU, hLK, hL⟩ :=
    exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint Finset.univ (hgd.set_pairwise _)
      (a := fun i ↦ shrink (f' i) i) (b := fun i ↦ shrink (g i) i)
      (fun i _ x _ ↦ hf'g i (mem_range_self x)) (fun i _ x _ ↦ hgg i (mem_range_self x)) fun i _ ↦
        exists_diffeotopy_eqOn_of_range_subset_range (g i) _ _ (hf'g i) (hgg i) o oM
          (isOrientationPreservingAt_compRadialContraction _ le_rfl _ (hf'o i))
          (isOrientationPreservingAt_compRadialContraction _ le_rfl _ (hgo i)) hA
  -- Compose: shrink the `f i`, move the centres, match the shrinks, and undo the shrink of `g i`.
  have hKLU' : KL ⊆ U := hKLU.trans (iUnion₂_subset fun i _ ↦ hgU i)
  refine ⟨Sf.trans (Φ₀.trans (L.trans Sg.symm)), Kf ∪ K₀ ∪ KL ∪ Kg,
    ((hKf.union hK₀).union hKL).union hKg,
    union_subset (union_subset (union_subset (hKfU.trans (iUnion_subset hfU)) hK₀U) hKLU')
      (hKgU.trans (iUnion_subset hgU)), fun t y hy ↦ ?_, fun i x hx ↦ ?_⟩
  · simp only [mem_union, not_or] at hy
    rw [Diffeotopy.trans_apply, hSfK t y hy.1.1.1, Diffeotopy.trans_apply,
      hΦ₀K₀ t hy.1.1.2, id_eq, Diffeotopy.trans_apply, hLK t y hy.1.2,
      Diffeotopy.symm_apply_eq_self_iff, hSgK t y hy.2]
  · have hSfi := hSf i hx
    have hLi := hL i (Finset.mem_univ i) hx
    have hSgi := hSg i hx
    simp only [comp_apply, shrink, compRadialContraction_apply, f',
      transDiffeomorph_apply] at hSfi hLi hSgi
    simp only [comp_apply, Diffeotopy.final_trans, Diffeotopy.final_symm, Diffeomorph.coe_trans,
      hSfi, hLi, ← hSgi, Diffeomorph.symm_apply_apply]

end TauCeti.SmoothEmbedding
