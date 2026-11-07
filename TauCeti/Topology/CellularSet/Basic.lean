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
import TauCeti.Topology.Homeomorph.Shrink

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
map onto `M`, so it identifies the quotient of `M` collapsing `X` to a point with `M` itself. This
is the first step of M. Brown's proof of the generalized Schoenflies theorem, where the
complementary regions of a bicollared sphere are recognized as cells by collapsing cellular sets.

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
* `TauCeti.exists_collapse_iInter`: the intersection of a nested sequence of compact sets with
  Euclidean interiors is collapsed to one point by a continuous surjection whose other fibres are
  singletons.
* `TauCeti.IsCellularSet.exists_collapse`: a cellular subset of a manifold is collapsed to one point
  by a continuous surjection, supported in any of its neighbourhoods, whose other fibres are
  singletons.
* `TauCeti.isCellularSet_closedBall`: closed balls are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
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

/-- The nested images `G k '' K (k + 1)` of compact sets with diameters tending to `0` shrink to a
point `q`, and every `G m x` with `m ≥ k` and `x ∈ K (k + 1)` lies within `1 / (k + 1)` of `q`. -/
private theorem exists_mem_image_and_dist_lt {K : ℕ → Set M} (hK : ∀ i, IsCompact (K i))
    (hKsucc : ∀ i, K (i + 1) ⊆ K i) (hKne : ∀ i, (K i).Nonempty) {G : ℕ → M → M}
    (hG : ∀ k, Continuous (G k))
    (hGimg : ∀ k m, k ≤ m → G m '' K (k + 1) = G k '' K (k + 1))
    (hGdiam : ∀ k, diam (G k '' K (k + 1)) < 1 / ((k : ℝ) + 1)) :
    ∃ q : M, (∀ k, q ∈ G k '' K (k + 1)) ∧
      ∀ k m, k ≤ m → ∀ x ∈ K (k + 1), dist (G m x) q < 1 / ((k : ℝ) + 1) := by
  have hScpt (k : ℕ) : IsCompact (G k '' K (k + 1)) := (hK _).image (hG k)
  have hSanti (k : ℕ) : G (k + 1) '' K (k + 1 + 1) ⊆ G k '' K (k + 1) := by
    rw [← hGimg k (k + 1) (by omega)]
    exact image_mono (hKsucc _)
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k ↦ G k '' K (k + 1)) hSanti (fun k ↦ (hKne _).image _) (hScpt 0)
    fun k ↦ (hScpt k).isClosed
  refine ⟨q, fun k ↦ mem_iInter.1 hq k, fun k m hkm x hx ↦ ?_⟩
  have hmem : G m x ∈ G k '' K (k + 1) := hGimg k m hkm ▸ mem_image_of_mem _ hx
  exact (dist_le_diam_of_mem (hScpt k).isBounded hmem (mem_iInter.1 hq k)).trans_lt (hGdiam k)

/-- **Continuity of a collapse.** Let `K₀ ⊇ K₁ ⊇ ⋯` be closed sets with open sets `U i` satisfying
`K (i + 1) ⊆ U i ⊆ K i`, and let `G k` be continuous maps such that all `G m` with `m ≥ k` lie
within `1 / (k + 1)` of `q` on `K (k + 1)`. A map `g` which is constant `q` on `⋂ i, K i` and
agrees with `G k` outside `K (k + 1)`, for every `k`, is continuous. -/
private theorem continuous_of_eq_of_notMem {U K : ℕ → Set M} (hU : ∀ i, IsOpen (U i))
    (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K (i + 1) ⊆ U i) (hUK : ∀ i, U i ⊆ K i)
    {G : ℕ → M → M} (hG : ∀ k, Continuous (G k)) {q : M} {g : M → M}
    (hdist : ∀ k m, k ≤ m → ∀ x ∈ K (k + 1), dist (G m x) q < 1 / ((k : ℝ) + 1))
    (hgX : ∀ x ∈ ⋂ i, K i, g x = q) (hgG : ∀ k x, x ∉ K (k + 1) → g x = G k x) :
    Continuous g := by
  have hKsucc (i : ℕ) : K (i + 1) ⊆ K i := (hKU i).trans (hUK i)
  have hKanti : Antitone K := antitone_nat_of_succ_le hKsucc
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ ⋂ i, K i
  · rw [ContinuousAt, hgX x hx, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hxU : x ∈ U (k + 1) := hKU (k + 1) (mem_iInter.1 hx (k + 2))
    filter_upwards [(hU (k + 1)).mem_nhds hxU] with y hy
    by_cases hyX : y ∈ ⋂ i, K i
    · rwa [hgX y hyX, dist_self]
    obtain ⟨j, hj⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hyX
    rw [hgG (max j k) y fun h ↦ hj (hKanti (by omega) h)]
    exact (hdist k (max j k) (le_max_right j k) y (hUK (k + 1) hy)).trans hk
  · obtain ⟨k, hk⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hx
    exact (hG k).continuousAt.congr (eventually_of_mem
      ((hK (k + 1)).isOpen_compl.mem_nhds hk) fun y hy ↦ (hgG k y hy).symm)

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
