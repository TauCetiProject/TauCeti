/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Data.Set.Lattice
import TauCeti.Topology.Homeomorph.CompactQuotient
import TauCeti.Topology.Homeomorph.Extend
import TauCeti.Topology.Homeomorph.Shrink
import TauCeti.Topology.MetricSpace.NestedCollapse

/-!
# Cellular sets and their collapse

A subset `X` of a space `M` is **cellular** (`TauCeti.IsCellularSet`) if it is the intersection of a
sequence of closed cells `Q₀ ⊇ Q₁ ⊇ ⋯`, each lying in the open cell of the previous one. Here a
closed cell is the image of the closed unit ball of a real normed space `E` under a map which is
continuous and injective on it, and the corresponding open cell is the image of the open unit ball
under the same map. When `M` is a topological manifold modelled on a finite-dimensional `E`,
invariance of domain shows that the open cell is the interior of the closed cell in `M`. A closed
ball of `E` is cellular in `E` (`TauCeti.isCellularSet_closedBall`).

The main theorem is that a cellular set can be collapsed to a point without changing the space:
if `M` is a metric space which is a topological manifold modelled on a finite-dimensional `E`, and
`X ⊆ M` is cellular, then for every open `U ⊇ X` there is a continuous surjection `g : M → M` which
collapses `X` to a single point, whose other fibres are all singletons, and which is the identity
outside `U` (`TauCeti.IsCellularSet.exists_collapse`). For compact `M` such a map is a quotient
map onto `M`, so any continuous surjection onto a Hausdorff space which collapses exactly `X` has
a target homeomorphic to `M` (`TauCeti.IsCellularSet.nonempty_homeomorph`). More generally, if
`K` is compact and `X ⊆ U ⊆ K` with `U` open, a map collapsing exactly `X` on `K` identifies `K`
with its image by a homeomorphism agreeing with the map outside `U`
(`TauCeti.IsCellularSet.exists_homeomorph_image`). This is how M. Brown's proof of the generalized
Schoenflies theorem recognizes the closures of the complementary regions of a bicollared sphere as
cells: each is mapped onto a closed hemisphere by a map whose only fibre with more than one point
is a cellular set inside the region.

The proof shrinks the cells one after another. If `K` is a compact subset of an open set `V` of `M`
homeomorphic to `E`, a radial squeeze of `E` (`TauCeti.exists_homeomorph_mapsTo_closedBall`), read
through `V` and extended by the identity, is a homeomorphism of `M` fixing every point outside `V`
which makes `K` as small as we like
(`Topology.IsOpenEmbedding.exists_homeomorph_diam_image_lt`). Applying this to the cells in turn,
each step supported inside the image of the previous cell, gives homeomorphisms `G₀, G₁, …` of `M`
which eventually stabilize at every point outside `X` and squeeze the image of `X` into a sequence
of compact sets with diameters tending to `0`. The collapse is their pointwise limit
(`TauCeti.exists_collapse_iInter`); invariance of domain makes the open cells open in `M`.

## Main definitions

* `TauCeti.IsCellularSet`: a cellular subset of a space.

## Main results

* `TauCeti.isCellularSet_iff`: the witnesses of cellularity.
* `TauCeti.IsCellularSet.isCompact`, `TauCeti.IsCellularSet.nonempty`: in a Hausdorff space, a
  cellular set is a nonempty compact set.
* `TauCeti.IsCellularSet.image`: the image of a cellular set under a map continuous and injective
  on an open neighbourhood of it is cellular.
* `TauCeti.exists_collapse_iInter`: the intersection of a nested sequence of compact sets with
  Euclidean interiors is collapsed to one point by a continuous surjection whose other fibres are
  singletons.
* `TauCeti.IsCellularSet.exists_collapse`: a cellular subset of a manifold is collapsed to one point
  by a continuous surjection, supported in any of its neighbourhoods, whose other fibres are
  singletons.
* `TauCeti.IsCellularSet.exists_homeomorph_image`: a map into a Hausdorff space, continuous on a
  compact set `K`, which collapses a cellular set inside `K` and is otherwise injective on `K`
  identifies `K` homeomorphically with its image.
* `TauCeti.IsCellularSet.nonempty_homeomorph`: collapsing a cellular set in a compact manifold to a
  point gives a space homeomorphic to the manifold.
* `TauCeti.IsCellularSet.nonempty_homeomorph_of_isOpenEmbedding`: the same for a cellular set
  inside an open copy of `E` in any compact Hausdorff space.
* `TauCeti.isCellularSet_closedBall`: closed balls are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* N. Sahoo, *The Generalized Schoenflies Theorem*, expository notes on Brown's paper, Lemma 3.2
  (the recognition of a compact set from a map collapsing exactly a cellular set).
-/

public section

open Set Metric Filter Topology Function Pointwise

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M]

namespace TauCeti

/-- The shrinking homeomorphisms behind `TauCeti.exists_collapse_iInter`: homeomorphisms `G k` of
`M`, each obtained from the previous one by a homeomorphism supported in the image of the next
open piece, which stabilize outside `K (k + 1)` from `k` on and squeeze `K (k + 1)` to diameter less
than `1 / (k + 1)`. -/
private theorem exists_homeomorph_seq {θ : ℕ → E → M} (hθ : ∀ i, IsOpenEmbedding (θ i))
    {K : ℕ → Set M} (hK : ∀ i, IsCompact (K i)) (hKθ : ∀ i, K (i + 1) ⊆ range (θ i))
    (hθK : ∀ i, range (θ i) ⊆ K i) :
    ∃ G : ℕ → M ≃ₜ M, (∀ x ∉ range (θ 0), G 0 x = x) ∧
      (∀ k m, k ≤ m → ∀ x ∉ K (k + 1), G m x = G k x) ∧
      (∀ k m, k ≤ m → G m '' K (k + 1) = G k '' K (k + 1)) ∧
      ∀ k, diam (G k '' K (k + 1)) < 1 / ((k : ℝ) + 1) := by
  have hKanti : Antitone K := antitone_nat_of_succ_le fun i ↦ (hKθ i).trans (hθK i)
  /- The shrinking step: after a homeomorphism `G`, the image of `K (k + 1)` can be squeezed to
  diameter less than `1 / (k + 1)` by a homeomorphism supported in the image of `θ k`. -/
  have hstep (G : M ≃ₜ M) (k : ℕ) : ∃ ψ : M ≃ₜ M, (∀ y ∉ range (G ∘ θ k), ψ y = y) ∧
      diam (ψ '' (G '' K (k + 1))) < 1 / ((k : ℝ) + 1) :=
    (G.isOpenEmbedding.comp (hθ k)).exists_homeomorph_diam_image_lt
      ((hK (k + 1)).image G.continuous) (by rw [range_comp]; exact image_mono (hKθ k))
      Nat.one_div_pos_of_nat
  choose ψ hψfix hψdiam using hstep
  obtain ⟨G, hG0, hGsucc⟩ : ∃ G : ℕ → M ≃ₜ M, G 0 = ψ (Homeomorph.refl M) 0 ∧
      ∀ k, G (k + 1) = (G k).trans (ψ (G k) (k + 1)) :=
    ⟨fun n ↦ Nat.rec (motive := fun _ ↦ M ≃ₜ M) (ψ (Homeomorph.refl M) 0)
      (fun k Gk ↦ Gk.trans (ψ Gk (k + 1))) n, rfl, fun _ ↦ rfl⟩
  have hGstep (k : ℕ) (x : M) (hx : x ∉ range (θ (k + 1))) : G (k + 1) x = G k x := by
    rw [hGsucc, Homeomorph.trans_apply]
    refine hψfix _ _ _ ?_
    rintro ⟨y, hxy⟩
    exact hx ⟨y, (G k).injective hxy⟩
  -- Outside `K (k + 1)` the sequence `G` is constant from `k` on.
  have hGstab (k m : ℕ) (hkm : k ≤ m) (x : M) (hx : x ∉ K (k + 1)) : G m x = G k x := by
    induction m, hkm using Nat.le_induction with
    | base => rfl
    | succ m hkm ih =>
      rw [hGstep m x fun h ↦ hx (hKanti (by omega) (hθK (m + 1) h)), ih]
  refine ⟨G, fun x hx ↦ ?_, hGstab, fun k m hkm ↦ ?_, fun k ↦ ?_⟩
  · rw [hG0]
    exact hψfix _ _ x (by simpa using hx)
  · -- All `G m` with `m ≥ k` agree outside `K (k + 1)`, so they map it onto the same set.
    refine compl_injective ?_
    rw [← (G m).image_compl, ← (G k).image_compl]
    exact image_congr fun x hx ↦ hGstab k m hkm x hx
  · cases k with
    | zero => simpa [hG0] using hψdiam (Homeomorph.refl M) 0
    | succ k =>
      have himg : G (k + 1) '' K (k + 1 + 1) = ψ (G k) (k + 1) '' (G k '' K (k + 1 + 1)) := by
        rw [hGsucc, image_image]
        exact image_congr fun x _ ↦ Homeomorph.trans_apply _ _ x
      rw [himg]
      exact hψdiam (G k) (k + 1)

/-- **Collapsing a nested intersection.** Let `K₀ ⊇ K₁ ⊇ ⋯` be compact subsets of a metric space
`M`, and `θᵢ : E → M` open embeddings of a finite-dimensional real normed space with
`K (i + 1) ⊆ range θᵢ ⊆ Kᵢ`. Then there is a continuous surjection `g : M → M` which collapses
`X = ⋂ i, K i` to a single point, whose other fibres are all singletons, and which fixes every point
outside the range of `θ₀`.
-/
theorem exists_collapse_iInter {θ : ℕ → E → M} (hθ : ∀ i, IsOpenEmbedding (θ i))
    {K : ℕ → Set M} (hK : ∀ i, IsCompact (K i)) (hKθ : ∀ i, K (i + 1) ⊆ range (θ i))
    (hθK : ∀ i, range (θ i) ⊆ K i) :
    ∃ g : M → M, Continuous g ∧ Surjective g ∧
      (∀ x y, g x = g y ↔ x = y ∨ x ∈ ⋂ i, K i ∧ y ∈ ⋂ i, K i) ∧ ∀ x ∉ range (θ 0), g x = x := by
  classical
  have hKsucc (i : ℕ) : K (i + 1) ⊆ K i := (hKθ i).trans (hθK i)
  have hKanti : Antitone K := antitone_nat_of_succ_le hKsucc
  have hKne (i : ℕ) : (K i).Nonempty := (range_nonempty (θ i)).mono (hθK i)
  obtain ⟨G, hG0, hGstab, hGimg, hGdiam⟩ := exists_homeomorph_seq hθ hK hKθ hθK
  obtain ⟨q, hqS, hdist⟩ := exists_mem_image_and_dist_lt hK hKsucc hKne
    (fun k ↦ (G k).continuous) hGimg hGdiam
  obtain ⟨g, hgX, hgG⟩ := exists_map_eq_of_notMem (G := fun k ↦ ⇑(G k)) hKsucc hGstab q
  have hgq (x : M) (hx : x ∉ ⋂ i, K i) : g x ≠ q := by
    obtain ⟨k, hk⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hx
    obtain ⟨y, hy, hyq⟩ := hqS k
    rw [hgG k x hk]
    intro h
    exact hk ((G k).injective (hyq.trans h.symm) ▸ hy)
  refine ⟨g, continuous_of_eq_of_notMem (fun i ↦ (hθ i).isOpen_range) (fun i ↦ (hK i).isClosed)
    hKθ hθK (fun k ↦ (G k).continuous) hdist hgX hgG, fun z ↦ ?_, fun x y ↦ ?_,
    fun x hx ↦ ?_⟩
  · rcases eq_or_ne z q with rfl | hzq
    · obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
        hKsucc hKne (hK 0) fun i ↦ (hK i).isClosed
      exact ⟨x, hgX x hx⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hzq)
    have hzK : (G k).symm z ∉ K (k + 1) := fun h ↦ by
      have := hdist k k le_rfl _ h
      rw [Homeomorph.apply_symm_apply] at this
      linarith
    exact ⟨(G k).symm z, by rw [hgG k _ hzK, Homeomorph.apply_symm_apply]⟩
  · refine ⟨fun h ↦ ?_, ?_⟩
    · by_cases hx : x ∈ ⋂ i, K i <;> by_cases hy : y ∈ ⋂ i, K i
      · exact .inr ⟨hx, hy⟩
      · exact (hgq y hy (h.symm.trans (hgX x hx))).elim
      · exact (hgq x hx (h.trans (hgX y hy))).elim
      · obtain ⟨j, hj⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hx
        obtain ⟨k, hk⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hy
        have hxm : x ∉ K (max j k + 1) := fun h ↦ hj (hKanti (by omega) h)
        have hym : y ∉ K (max j k + 1) := fun h ↦ hk (hKanti (by omega) h)
        exact .inl ((G _).injective (by rwa [← hgG _ x hxm, ← hgG _ y hym]))
    · rintro (rfl | ⟨hx, hy⟩)
      · rfl
      · rw [hgX x hx, hgX y hy]
  · rw [hgG 0 x fun h ↦ hx (hKθ 0 h), hG0 x hx]

/-- A subset `X` of a space `M` is **cellular** (modelled on the real normed space `E`) if it is the
intersection of a sequence of closed cells, each contained in the open cell of the previous one.
Here the `i`-th closed cell is the image of the closed unit ball of `E` under a map `e i` which is
continuous and injective on it, and the `i`-th open cell is the image of the open unit ball under
`e i`. When `M` is a topological manifold modelled on a finite-dimensional `E`, invariance of domain
shows that the open cell is the interior of the closed cell. -/
def IsCellularSet (E : Type*) [NormedAddCommGroup E] {M : Type*}
    [TopologicalSpace M] (X : Set M) : Prop :=
  ∃ e : ℕ → E → M, (∀ i, ContinuousOn (e i) (closedBall 0 1)) ∧
    (∀ i, InjOn (e i) (closedBall 0 1)) ∧
    (∀ i, e (i + 1) '' closedBall 0 1 ⊆ e i '' ball 0 1) ∧ ⋂ i, e i '' closedBall 0 1 = X

/-- The witnesses of cellularity: maps `e i : E → M`, continuous and injective on the closed unit
ball, whose closed cells are each contained in the open cell of the previous one and intersect in
`X`. -/
theorem isCellularSet_iff (E : Type*) [NormedAddCommGroup E] {M : Type*} [TopologicalSpace M]
    {X : Set M} :
    IsCellularSet E X ↔ ∃ e : ℕ → E → M, (∀ i, ContinuousOn (e i) (closedBall 0 1)) ∧
      (∀ i, InjOn (e i) (closedBall 0 1)) ∧
      (∀ i, e (i + 1) '' closedBall 0 1 ⊆ e i '' ball 0 1) ∧ ⋂ i, e i '' closedBall 0 1 = X :=
  Iff.rfl

/-- A cellular set in a Hausdorff space, modelled on a proper space, is closed. -/
theorem IsCellularSet.isClosed {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {M : Type*}
    [TopologicalSpace M] [T2Space M] {X : Set M} (hX : IsCellularSet E X) : IsClosed X := by
  obtain ⟨e, hec, -, -, rfl⟩ := (isCellularSet_iff E).1 hX
  exact isClosed_iInter fun i ↦ ((isCompact_closedBall 0 1).image_of_continuousOn (hec i)).isClosed

/-- A cellular set in a Hausdorff space, modelled on a proper space, is compact. -/
theorem IsCellularSet.isCompact {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {M : Type*}
    [TopologicalSpace M] [T2Space M] {X : Set M} (hX : IsCellularSet E X) : IsCompact X := by
  obtain ⟨e, hec, -, -, hX'⟩ := (isCellularSet_iff E).1 hX
  exact ((isCompact_closedBall 0 1).image_of_continuousOn (hec 0)).of_isClosed_subset hX.isClosed
    (hX' ▸ iInter_subset _ 0)

/-- A cellular set in a Hausdorff space, modelled on a proper space, is nonempty. -/
theorem IsCellularSet.nonempty {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {M : Type*}
    [TopologicalSpace M] [T2Space M] {X : Set M} (hX : IsCellularSet E X) : X.Nonempty := by
  obtain ⟨e, hec, -, hsub, rfl⟩ := (isCellularSet_iff E).1 hX
  have hQc (i : ℕ) : IsCompact (e i '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (hec i)
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun i ↦ (hsub i).trans (image_mono ball_subset_closedBall))
    (fun i ↦ ⟨e i 0, mem_image_of_mem _ (mem_closedBall_self zero_le_one)⟩) (hQc 0)
    fun i ↦ (hQc i).isClosed

/-- The image of a cellular set under a map which is continuous and injective on an open
neighbourhood of it is cellular: the cells from some index on lie in the neighbourhood, and their
images are cells of the image. -/
theorem IsCellularSet.image {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {M N : Type*}
    [TopologicalSpace M] [T2Space M] [TopologicalSpace N] {X U : Set M} (hX : IsCellularSet E X)
    (hU : IsOpen U) (hXU : X ⊆ U) {h : M → N} (hc : ContinuousOn h U) (hi : InjOn h U) :
    IsCellularSet E (h '' X) := by
  obtain ⟨e, hec, hei, hsub, rfl⟩ := (isCellularSet_iff E).1 hX
  set Q : ℕ → Set M := fun i ↦ e i '' closedBall 0 1
  have hQc (i : ℕ) : IsCompact (Q i) := (isCompact_closedBall 0 1).image_of_continuousOn (hec i)
  have hQanti : Antitone Q :=
    antitone_nat_of_succ_le fun i ↦ (hsub i).trans (image_mono ball_subset_closedBall)
  -- Some cell `Q n` already lies in `U`, and so do all the later ones.
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hQanti.directed_ge hQc
    (fun i ↦ (hQc i).isClosed) (hU.mem_nhdsSet.2 hXU)
  have hQU (i : ℕ) : MapsTo (e (i + n)) (closedBall 0 1) U :=
    mapsTo_iff_image_subset.2 ((hQanti (Nat.le_add_left n i)).trans hn)
  refine (isCellularSet_iff E).2 ⟨fun i ↦ h ∘ e (i + n), fun i ↦ hc.comp (hec _) (hQU i),
    fun i ↦ hi.comp (hei _) (hQU i), fun i ↦ ?_, ?_⟩
  · rw [image_comp, image_comp, add_right_comm]
    exact image_mono (hsub _)
  · simp_rw [image_comp]
    rw [← (hi.mono (iUnion_subset fun i ↦ (hQU i).image_subset)).image_iInter_eq,
      hQanti.iInter_nat_add n]

/-- **Collapsing a cellular set.** Let `M` be a metric space which is a topological manifold
modelled on a finite-dimensional real normed space `E`, and `X ⊆ M` a cellular set. For every open
`U ⊇ X` there is a continuous surjection `g : M → M` which collapses `X` to a single point, whose
other fibres are all singletons, and which fixes every point outside `U`. -/
theorem IsCellularSet.exists_collapse [ChartedSpace E M] {X : Set M} (hX : IsCellularSet E X)
    {U : Set M} (hU : IsOpen U) (hXU : X ⊆ U) :
    ∃ g : M → M, Continuous g ∧ Surjective g ∧ (∀ x y, g x = g y ↔ x = y ∨ x ∈ X ∧ y ∈ X) ∧
      ∀ x ∉ U, g x = x := by
  obtain ⟨e, hec, hei, hsub, rfl⟩ := (isCellularSet_iff E).1 hX
  set Q : ℕ → Set M := fun i ↦ e i '' closedBall 0 1
  have hQc (i : ℕ) : IsCompact (Q i) := (isCompact_closedBall 0 1).image_of_continuousOn (hec i)
  have hQanti : Antitone Q :=
    antitone_nat_of_succ_le fun i ↦ (hsub i).trans (image_mono ball_subset_closedBall)
  -- Some cell `Q n` already lies in `U`.
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hQanti.directed_ge hQc
    (fun i ↦ (hQc i).isClosed) (hU.mem_nhdsSet.2 hXU)
  -- The interiors of the cells from `n` on, parametrized by `E`; they are open by invariance of
  -- domain.
  let θ : ℕ → E → M := fun i ↦ (ball (0 : E) 1).domRestrict (e (i + n)) ∘ Homeomorph.unitBall
  have hθ (i : ℕ) : IsOpenEmbedding (θ i) :=
    ((isOpen_ball (x := (0 : E))).isOpenEmbedding_domRestrict_of_continuousOn_of_injOn (E := E)
      (F := E) ((hec _).mono ball_subset_closedBall) ((hei _).mono ball_subset_closedBall)
      rfl).comp Homeomorph.unitBall.isOpenEmbedding
  have hθr (i : ℕ) : range (θ i) = e (i + n) '' ball 0 1 := by
    rw [range_comp, Homeomorph.range_coe, image_univ, range_domRestrict]
  obtain ⟨g, hgc, hgs, hgf, hgU⟩ := exists_collapse_iInter (K := fun i ↦ Q (i + n)) hθ
    (fun i ↦ hQc _) (fun i ↦ by rw [hθr, add_right_comm]; exact hsub _)
    (fun i ↦ by rw [hθr]; exact image_mono ball_subset_closedBall)
  rw [hQanti.iInter_nat_add] at hgf
  refine ⟨g, hgc, hgs, hgf, fun x hx ↦ hgU x fun h ↦ hx (hn ?_)⟩
  rw [hθr, zero_add] at h
  exact image_mono ball_subset_closedBall h

/-- **A map collapsing only a cellular set is a homeomorphism up to that collapse.** Let `M` be a
metric space which is a topological manifold modelled on a finite-dimensional real normed space
`E`, let `K ⊆ M` be compact, and let `X` be a cellular set lying in an open set `U ⊆ K`. If a map
`φ` from `M` to a Hausdorff space is continuous on `K`, collapses `X` to a point and is injective on
`K` otherwise, then `K` is homeomorphic to its image `φ '' K`, by a homeomorphism which agrees with
`φ` outside `U` and sends exactly the points of `U` into `φ '' U`. -/
theorem IsCellularSet.exists_homeomorph_image [ChartedSpace E M] {X : Set M}
    (hX : IsCellularSet E X) {Y : Type*} [TopologicalSpace Y] [T2Space Y] {φ : M → Y}
    {K U : Set M} (hφ : ContinuousOn φ K) (hK : IsCompact K) (hU : IsOpen U) (hXU : X ⊆ U)
    (hUK : U ⊆ K) (hφK : ∀ x ∈ K, ∀ y ∈ K, φ x = φ y ↔ x = y ∨ x ∈ X ∧ y ∈ X) :
    ∃ h : K ≃ₜ φ '' K, (∀ x : K, (x : M) ∉ U → (h x : Y) = φ x) ∧
      ∀ x : K, (h x : Y) ∈ φ '' U ↔ (x : M) ∈ U := by
  -- The homeomorphism is `φ` composed with the inverse of the collapse `c` of `X` supported in
  -- `U`, which has the same fibres as `φ` on `K`.
  obtain ⟨c, hcc, hcs, hcf, hcU⟩ := hX.exists_collapse hU hXU
  -- The collapse `c` maps `U` onto itself, hence `K` onto itself.
  have hcUU (x : M) (hx : x ∈ U) : c x ∈ U := by
    by_contra h
    rcases (hcf (c x) x).1 (hcU _ h) with h' | h'
    · exact h (by rwa [h'])
    · exact h (hXU h'.1)
  have hcU' (x : M) (hx : c x ∈ U) : x ∈ U := by
    by_contra h
    exact h (hcU x h ▸ hx)
  have hcK : MapsTo c K K := fun x hx ↦ by
    by_cases h : x ∈ U
    · exact hUK (hcUU x h)
    · rwa [hcU x h]
  have hcKs : Surjective (hcK.restrict c K K) := hcK.restrict_surjective_iff.2 fun y hy ↦ by
    obtain ⟨x, rfl⟩ := hcs y
    by_cases h : x ∈ U
    · exact ⟨x, hUK h, rfl⟩
    · exact ⟨x, by rwa [hcU x h] at hy, rfl⟩
  -- On `K`, the map `φ` has the same fibres as `c`, so `φ '' K` is identified with `K` by a
  -- homeomorphism `e` sending `φ x` to `c x`.
  obtain ⟨e, he⟩ := exists_homeomorph_image_of_forall_eq_iff hφ hK (hcK.restrict c K K)
    (hcc.restrict hcK) hcKs fun a b ↦ by
      rw [Subtype.ext_iff]
      exact (hcf a b).trans (hφK a a.2 b b.2).symm
  have hψ (a : K) : (e.symm (hcK.restrict c K K a) : Y) = φ a := by
    rw [← he, e.symm_apply_apply]
  -- Outside `U` the collapse is the identity, so `e.symm` agrees with `φ` there.
  have hoff (x : K) (hx : (x : M) ∉ U) : (e.symm x : Y) = φ x := by
    rw [← hψ, show hcK.restrict c K K x = x from Subtype.ext (hcU x hx)]
  have hin (x : K) : (e.symm x : Y) ∈ φ '' U ↔ (x : M) ∈ U := by
    obtain ⟨a, rfl⟩ := hcKs x
    rw [hψ]
    refine ⟨fun ⟨u, hu, hua⟩ ↦ hcUU a ?_, fun hx ↦ mem_image_of_mem φ (hcU' a hx)⟩
    rcases (hφK u (hUK hu) a a.2).1 hua with h | h
    · exact h ▸ hu
    · exact hXU h.2
  exact ⟨e.symm, hoff, hin⟩

/-- **Collapsing a cellular set in a compact manifold.** Let `M` be a compact metric space which is
a topological manifold modelled on a finite-dimensional real normed space `E`, and `X ⊆ M` a
cellular set. If a continuous surjection `f : M → Y` onto a Hausdorff space collapses `X` to a point
and is injective elsewhere, then `Y` is homeomorphic to `M`: the quotient of `M` collapsing `X` to a
point is `M` again. -/
theorem IsCellularSet.nonempty_homeomorph [ChartedSpace E M] [CompactSpace M] {X : Set M}
    (hX : IsCellularSet E X) {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : M → Y}
    (hf : Continuous f) (hfs : Surjective f) (hfX : ∀ x y, f x = f y ↔ x = y ∨ x ∈ X ∧ y ∈ X) :
    Nonempty (M ≃ₜ Y) := by
  obtain ⟨h, -, -⟩ := hX.exists_homeomorph_image hf.continuousOn isCompact_univ isOpen_univ
    (subset_univ X) subset_rfl fun x _ y _ ↦ hfX x y
  exact ⟨((Homeomorph.Set.univ M).symm.trans h).trans
    ((Homeomorph.setCongr (image_univ_of_surjective hfs)).trans (Homeomorph.Set.univ Y))⟩

/-- **Collapsing a cellular set inside a Euclidean open set.** Let `X` be a compact Hausdorff
space, `κ : E → X` an open embedding of a finite-dimensional real normed space, and `A ⊆ E` a
cellular set. If a continuous surjection `f : X → Y` onto a Hausdorff space collapses `κ '' A` to a
point and is injective elsewhere, then `Y` is homeomorphic to `X`. Unlike
`TauCeti.IsCellularSet.nonempty_homeomorph`, `X` need not be a manifold or a metric space: the
collapse of `A` in `E` is transported to `X` along `κ`. -/
theorem IsCellularSet.nonempty_homeomorph_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] {A : Set E}
    (hA : IsCellularSet E A) {κ : E → X} (hκ : IsOpenEmbedding κ) {f : X → Y} (hf : Continuous f)
    (hfs : Surjective f) (hfA : ∀ x y, f x = f y ↔ x = y ∨ x ∈ κ '' A ∧ y ∈ κ '' A) :
    Nonempty (X ≃ₜ Y) := by
  -- A collapse `g` of `A` in `E` which is the identity outside a ball, transported to `X`.
  obtain ⟨r, hr⟩ := hA.isCompact.isBounded.subset_ball 0
  obtain ⟨g, hgc, hgs, hgf, hgU⟩ := hA.exists_collapse (M := E) isOpen_ball hr
  have hK : IsClosed (κ '' closedBall 0 r) :=
    ((isCompact_closedBall 0 r).image hκ.continuous).isClosed
  obtain ⟨Φ, hΦκ, hΦK⟩ := hκ.exists_continuousMap_extend_id hK.isOpen_compl
    (fun _ hx h ↦ hx (image_subset_range _ _ h)) ⟨fun p : Unit × E ↦ g p.2, hgc.comp continuous_snd⟩
    fun _ a ha ↦ hgU a fun hb ↦ ha ⟨a, ball_subset_closedBall hb, rfl⟩
  set G : X → X := fun x ↦ Φ ((), x)
  have hGκ (a : E) : G (κ a) = κ (g a) := hΦκ () a
  have hGo {x : X} (hx : x ∉ range κ) : G x = x :=
    hΦK () x fun h ↦ hx (image_subset_range _ _ h)
  have hG : Continuous G := Φ.continuous.comp (.prodMk continuous_const continuous_id)
  have hGs : Surjective G := fun y ↦ by
    by_cases hyκ : y ∈ range κ
    · obtain ⟨b, rfl⟩ := hyκ
      obtain ⟨a, rfl⟩ := hgs b
      exact ⟨κ a, hGκ a⟩
    · exact ⟨y, hGo hyκ⟩
  -- `G` and `f` have the same fibres.
  have hκA {a : E} : κ a ∈ κ '' A ↔ a ∈ A := hκ.injective.mem_set_image
  have hGf (x y : X) : G x = G y ↔ f x = f y := by
    rw [hfA]
    by_cases hx : x ∈ range κ <;> by_cases hy : y ∈ range κ
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [hGκ, hGκ, hκ.injective.eq_iff, hgf, hκ.injective.eq_iff, hκA, hκA]
    · obtain ⟨a, rfl⟩ := hx
      rw [hGκ, hGo hy]
      exact iff_of_false (fun h ↦ hy ⟨g a, h⟩) fun h ↦ h.elim (fun h ↦ hy ⟨a, h⟩)
        fun h ↦ hy (image_subset_range _ _ h.2)
    · obtain ⟨b, rfl⟩ := hy
      rw [hGκ, hGo hx]
      exact iff_of_false (fun h ↦ hx ⟨g b, h.symm⟩) fun h ↦ h.elim (fun h ↦ hx ⟨b, h.symm⟩)
        fun h ↦ hx (image_subset_range _ _ h.1)
    · rw [hGo hx, hGo hy]
      exact ⟨.inl, fun h ↦ h.resolve_right fun h ↦ hx (image_subset_range _ _ h.1)⟩
  -- So `f` identifies the image of `G`, which is `X`, with `Y`.
  obtain ⟨h, -⟩ := exists_homeomorph_image_of_forall_eq_iff hG.continuousOn isCompact_univ
    (fun x : (univ : Set X) ↦ f x) (hf.comp continuous_subtype_val)
    (fun y ↦ let ⟨x, hx⟩ := hfs y; ⟨⟨x, mem_univ x⟩, hx⟩) fun x y ↦ (hGf x y).symm
  exact ⟨((Homeomorph.setCongr (image_univ_of_surjective hGs)).trans
    (Homeomorph.Set.univ X)).symm.trans h⟩

omit [FiniteDimensional ℝ E] in
/-- A closed ball `closedBall x r` with `r ≥ 0` is cellular in `E`: it is the intersection of the
closed balls `closedBall x (r + 1 / (i + 1))`, each in the interior of the previous one. -/
theorem isCellularSet_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    IsCellularSet E (closedBall x r) := by
  have hpos (i : ℕ) : 0 < r + 1 / ((i : ℝ) + 1) := by positivity
  -- The `i`-th cell is the affine image `x + (r + 1 / (i + 1)) • y` of the unit ball.
  have himg (i : ℕ) (S : Set E) :
      (fun y ↦ x + (r + 1 / ((i : ℝ) + 1)) • y) '' S = x +ᵥ (r + 1 / ((i : ℝ) + 1)) • S := by
    rw [← image_smul, ← image_vadd, image_image]
    rfl
  refine (isCellularSet_iff E).2 ⟨fun i y ↦ x + (r + 1 / ((i : ℝ) + 1)) • y, fun i ↦ by fun_prop,
    fun i y _ z _ h ↦ smul_right_injective E (hpos i).ne' (add_left_cancel h), fun i ↦ ?_, ?_⟩
  · rw [himg, himg, affinity_unitClosedBall (hpos _).le, affinity_unitBall (hpos i)]
    refine closedBall_subset_ball ?_
    push_cast
    gcongr
    linarith
  · simp_rw [himg, fun i ↦ affinity_unitClosedBall (hpos i).le x]
    ext p
    simp only [mem_iInter, mem_closedBall]
    refine ⟨fun h ↦ le_of_forall_pos_lt_add fun ε hε ↦ ?_,
      fun hp i ↦ hp.trans (le_add_of_nonneg_right (by positivity))⟩
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
    exact (h i).trans_lt (by linarith)

end TauCeti
