/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative
public import TauCeti.Topology.Homotopy.StarConvexComplement
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Geometry.Manifold.ModelTransport.Homeomorph

/-!
# Local homology of compact sets in manifolds with boundary

Let `f` be a nonzero continuous linear functional on a real normed space `E` of finite dimension
`n`, and let `H = {x | 0 ≤ f x}` be the closed half-space it bounds. A topological `n`-manifold
with boundary is a Hausdorff space `M` charted on `H`. This file proves that the local homology
`Hₖ(M, M ∖ A)` of every compact `A ⊆ M` vanishes for `k > n`
(`TauCeti.isZero_localHomology_of_isCompact_halfSpace`), with coefficients in a module. This is
the version for manifolds with boundary of Hatcher's Lemma 3.27(b), whose boundaryless case is
`TauCeti.isZero_localHomology_of_isCompact`.

The argument is Hatcher's, run on the half-space model.

* **Boundary pieces.** If a bounded set `K ⊆ H` is star-convex about a point `p` of the boundary
  hyperplane `f = 0`, then `H ∖ K` is contractible
  (`StarConvex.contractibleSpace_halfSpace_diff`), and so is `H`. Hence `Hₖ(H, H ∖ K)` vanishes
  in *every* degree (`TauCeti.isZero_localHomology_halfSpace_of_starConvex`). In particular the
  local homology of `H` at a boundary point vanishes
  (`TauCeti.isZero_localHomology_halfSpace_singleton`): a boundary point is not detected by local
  homology, which is why the orientation sheaf of a manifold with boundary is defined by pushing
  forward the orientation sheaf of its interior.
* **Interior pieces.** A compact convex set in the open half-space `f > 0` lies in an open subset
  of `H` which is also open in `E`, so by excision its local homology is computed in `E`, where it
  vanishes above the dimension (`TauCeti.isZero_localHomology_symm_image_iUnion`).
* **Convex pieces of a chart.** Every compact convex set in `H` is of one of these two kinds, so
  local homology along it vanishes above the dimension
  (`TauCeti.isZero_localHomology_halfSpace_of_convex`). A chart `φ : M → H` transports this to
  `M` (`TauCeti.isZero_localHomology_symm_image_halfSpace`).
* **Mayer–Vietoris.** For a family of closed sets that is closed under intersections and along
  which local homology vanishes above the dimension, the relative Mayer–Vietoris sequence passes
  the vanishing to finite unions (`TauCeti.isZero_localHomology_biUnion`).
* **Compactness.** With module coefficients a class along `A` comes from a neighbourhood of `A`
  (`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq`), so the vanishing passes to `A` from
  sets between `A` and any of its neighbourhoods
  (`TauCeti.isZero_localHomology_of_forall_mem_nhdsSet`). Finite unions of closed balls of a chart
  give such sets for compact subsets of the chart source
  (`TauCeti.isZero_localHomology_of_subset_source_halfSpace`), and covering a compact set by
  finitely many compact pieces in chart sources gives the theorem
  (`TauCeti.isZero_localHomology_of_isCompact_of_forall_mem_nhds`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.27.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Appendix A.6, where the orientation
  sheaf of a topological manifold with boundary and the vanishing of its local homology above the
  dimension enter the duality for closed subsets.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology

universe w v u

namespace TauCeti

/-! ### The half-space model -/

section HalfSpace

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : StrongDual ℝ E}

/-- **Local homology of the half-space along a boundary piece vanishes.** Let `f ≠ 0` and let
`K` be a subset of the half-space `H = {x | 0 ≤ f x}` which is bounded and star-convex about a
point `p` of the boundary hyperplane `f = 0`. Then `Hₖ(H, H ∖ K)` vanishes in every degree:
`H` and `H ∖ K` are both contractible (`StarConvex.contractibleSpace_halfSpace_diff`). -/
theorem isZero_localHomology_halfSpace_of_starConvex (hf : f ≠ 0)
    {K : Set ↥{x : E | 0 ≤ f x}} {p : E} (hK : StarConvex ℝ p (Subtype.val '' K))
    (hp : p ∈ Subtype.val '' K) (hfp : f p = 0) (hKb : Bornology.IsBounded (Subtype.val '' K))
    (k : ℕ) : IsZero (localHomology R K k) := by
  let P := TopPair.ofSubset (Kᶜ : Set (TopCat.of ↥{x : E | 0 ≤ f x}))
  have : ContractibleSpace P.fst :=
    (convex_halfSpace_ge f.toLinearMap.isLinear 0).contractibleSpace ⟨0, by simp⟩
  -- The complement of `K` in the subspace `H` is the complement `H ∖ K` taken in `E`.
  have : ContractibleSpace P.snd :=
    ((IsEmbedding.subtypeVal.homeomorphImage Kᶜ).trans
      (.setCongr image_val_compl)).contractibleSpace_iff.2
      (hK.contractibleSpace_halfSpace_diff hp hKb hf hfp)
  rcases k with _ | k
  · exact TopPair.isZero_singularHomology_zero P R
  · exact (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.snd k).of_iso
      (asIso (P.reducedSingularHomologyδ R k))

/-- **The local homology of a half-space at a boundary point vanishes** in every degree. -/
theorem isZero_localHomology_halfSpace_singleton (hf : f ≠ 0) {x : ↥{x : E | 0 ≤ f x}}
    (hx : f x = 0) (k : ℕ) : IsZero (localHomology R {x} k) :=
  isZero_localHomology_halfSpace_of_starConvex R hf (p := x) (by simpa using starConvex_singleton _)
    (by simp) hx (by simp) k

variable [FiniteDimensional ℝ E] {n : ℕ}

/-- Local homology of the half-space along a compact convex set in the open half-space `f > 0`
vanishes above the dimension. The open half-space is open both in `H = {x | 0 ≤ f x}` and in `E`,
so excision computes the local homology in `E`. -/
private theorem isZero_localHomology_halfSpace_of_pos (hn : finrank ℝ E = n)
    {K : Set ↥{x : E | 0 ≤ f x}} (hKv : Convex ℝ (Subtype.val '' K)) (hKc : IsCompact K)
    (hKf : ∀ x ∈ K, 0 < f x) {k : ℕ} (hk : n < k) : IsZero (localHomology R K k) := by
  let O : Set ↥{x : E | 0 ≤ f x} := {x | 0 < f x}
  have hO : IsOpen O := isOpen_lt continuous_const (f.continuous.comp continuous_subtypeVal)
  -- The inclusions of the open half-space into `H` and into `E`.
  let j : C(O, ↥{x : E | 0 ≤ f x}) := ⟨Subtype.val, continuous_subtypeVal⟩
  let j' : C(O, E) := ⟨fun z ↦ z.val.val, continuous_subtypeVal.comp continuous_subtypeVal⟩
  have hj : IsOpenEmbedding j := hO.isOpenEmbedding_subtypeVal
  have hj' : IsOpenEmbedding j' := by
    refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
    have : range j' = {y : E | 0 < f y} := by
      ext y
      refine ⟨?_, fun (hy : 0 < f y) ↦ ⟨⟨⟨y, hy.le⟩, hy⟩, rfl⟩⟩
      rintro ⟨z, rfl⟩
      exact z.property
    rw [this]
    exact isOpen_lt continuous_const f.continuous
  have hKj : j ⁻¹' K = j' ⁻¹' (Subtype.val '' K) := by
    ext z
    exact (Subtype.val_injective.mem_set_image (a := z.val) (s := K)).symm
  have hKE : IsZero (localHomology R (Subtype.val '' K) k) := by
    have := isZero_localHomology_symm_image_iUnion R (OpenPartialHomeomorph.refl E) hn
      (K := fun _ : Unit ↦ Subtype.val '' K) (fun _ ↦ hKv)
      (fun _ ↦ hKc.image continuous_subtypeVal) (fun _ ↦ subset_univ _) hk
    simpa [iUnion_const] using this
  refine (isZero_localHomology_iff_of_isOpenEmbedding R j hj rfl hKc.isClosed
    (fun x hx ↦ ⟨⟨x, hKf x hx⟩, rfl⟩) k).1 ?_
  exact (isZero_localHomology_iff_of_isOpenEmbedding R j' hj' hKj.symm
    (hKc.image continuous_subtypeVal).isClosed (fun y ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hKf x hx⟩, hxy⟩)
    k).2 hKE

/-- **Local homology of the half-space along a compact convex set vanishes above the
dimension.** Let `f ≠ 0` be a functional on a real normed space of finite dimension `n`, and let
`K` be a compact subset of the half-space `H = {x | 0 ≤ f x}` which is convex in `E`. Then
`Hₖ(H, H ∖ K)` vanishes for `k > n`: if `K` meets the boundary hyperplane it vanishes in every
degree (`TauCeti.isZero_localHomology_halfSpace_of_starConvex`), and otherwise `K` lies in the
open half-space, where local homology is that of `E`. -/
theorem isZero_localHomology_halfSpace_of_convex (hf : f ≠ 0) (hn : finrank ℝ E = n)
    {K : Set ↥{x : E | 0 ≤ f x}} (hKv : Convex ℝ (Subtype.val '' K)) (hKc : IsCompact K)
    {k : ℕ} (hk : n < k) : IsZero (localHomology R K k) := by
  by_cases h : ∃ x ∈ K, f x = 0
  · obtain ⟨x, hx, hfx⟩ := h
    exact isZero_localHomology_halfSpace_of_starConvex R hf (hKv.starConvex ⟨x, hx, rfl⟩)
      ⟨x, hx, rfl⟩ hfx (hKc.image continuous_subtypeVal).isBounded k
  · simp only [not_exists, not_and] at h
    exact isZero_localHomology_halfSpace_of_pos R hn hKv hKc
      (fun x hx ↦ x.property.lt_of_ne' (h x hx)) hk

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  (φ : OpenPartialHomeomorph M ↥{x : E | 0 ≤ f x})

/-- **Local homology along a convex piece of a half-space chart vanishes above the dimension.**
For a chart `φ : M → H = {x | 0 ≤ f x}` and a compact set `K ⊆ φ.target` which is convex in `E`,
`Hₖ(M, M ∖ φ⁻¹(K))` vanishes for `k > n`. Excision along the source of `φ`, which `φ` identifies
with the open subset `φ.target` of `H`, computes it in `H`
(`TauCeti.isZero_localHomology_halfSpace_of_convex`). -/
theorem isZero_localHomology_symm_image_halfSpace (hf : f ≠ 0) (hn : finrank ℝ E = n)
    {K : Set ↥{x : E | 0 ≤ f x}} (hKv : Convex ℝ (Subtype.val '' K)) (hKc : IsCompact K)
    (hKφ : K ⊆ φ.target) {k : ℕ} (hk : n < k) : IsZero (localHomology R (φ.symm '' K) k) := by
  -- The inclusion of the chart source into `M` and the chart itself on its source.
  let j : C(φ.source, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let j' : C(φ.source, ↥{x : E | 0 ≤ f x}) := ⟨φ.source.domRestrict φ, φ.continuousOn.domRestrict⟩
  have hj : IsOpenEmbedding j := φ.open_source.isOpenEmbedding_subtypeVal
  have hj' : IsOpenEmbedding j' := φ.isOpenEmbedding_restrict
  have hL : φ.symm '' K = φ.source ∩ φ ⁻¹' K := φ.symm_image_eq_source_inter_preimage hKφ
  have hLc : IsCompact (φ.symm '' K) := hKc.image_of_continuousOn (φ.continuousOn_symm.mono hKφ)
  have hKj : j ⁻¹' (φ.symm '' K) = j' ⁻¹' K := by
    ext z
    rw [hL]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨z.property, h⟩⟩
  refine (isZero_localHomology_iff_of_isOpenEmbedding R j hj rfl hLc.isClosed
    (fun x hx ↦ ⟨⟨x, (hL ▸ hx).1⟩, rfl⟩) k).1 ?_
  exact (isZero_localHomology_iff_of_isOpenEmbedding R j' hj' hKj.symm hKc.isClosed
    (fun y hy ↦ ⟨⟨φ.symm y, φ.map_target (hKφ hy)⟩, φ.right_inv (hKφ hy)⟩) k).2
    (isZero_localHomology_halfSpace_of_convex R hf hn hKv hKc hk)

end HalfSpace

section HalfSpaceModule

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : StrongDual ℝ E} {n : ℕ} {M : Type w} [TopologicalSpace M] [T2Space M]

/-- A closed ball of the half-space `{x | 0 ≤ f x}` is compact, and convex in `E`. -/
private lemma isCompact_and_convex_closedBall_halfSpace (x : ↥{x : E | 0 ≤ f x}) (r : ℝ) :
    IsCompact (closedBall x r) ∧ Convex ℝ (Subtype.val '' closedBall x r) := by
  have hH : IsClosed {x : E | 0 ≤ f x} := isClosed_le continuous_const f.continuous
  have hball : closedBall x r = Subtype.val ⁻¹' closedBall (x : E) r := by
    ext y
    simp [Subtype.dist_eq]
  rw [hball, Subtype.image_preimage_coe]
  exact ⟨hH.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall _ _),
    (convex_halfSpace_ge f.toLinearMap.isLinear 0).inter (convex_closedBall _ _)⟩

/-- **Local homology along compact subsets of a half-space chart vanishes above the
dimension.** For a chart `φ : M → H = {x | 0 ≤ f x}` with `f ≠ 0` and `E` of dimension `n`, and a
compact set `A` in the source of `φ`, `Hₖ(M, M ∖ A)` vanishes for `k > n`. Every neighbourhood of
`A` contains a finite union of preimages of closed balls of `H` covering `A`
(`OpenPartialHomeomorph.exists_finset_closedBall_cover`); these are compact and convex in `E`, and
so are their intersections. -/
theorem isZero_localHomology_of_subset_source_halfSpace (hf : f ≠ 0) (hn : finrank ℝ E = n)
    (φ : OpenPartialHomeomorph M ↥{x : E | 0 ≤ f x}) {A : Set M} (hA : IsCompact A)
    (hAφ : A ⊆ φ.source) {k : ℕ} (hk : n < k) : IsZero (localHomology N A k) := by
  refine isZero_localHomology_of_forall_mem_nhdsSet N fun U hU ↦ ?_
  obtain ⟨t, r, ht, hAt⟩ := φ.exists_finset_closedBall_cover hA hAφ hU
  -- The preimages of compact subsets of the chart target which are convex in `E`.
  let 𝒢 : Set (Set M) := {G | ∃ K ⊆ φ.target, IsCompact K ∧ Convex ℝ (Subtype.val '' K) ∧
    G = φ.symm '' K}
  have hc : ∀ G ∈ 𝒢, IsClosed G := by
    rintro _ ⟨K, hKφ, hKc, -, rfl⟩
    exact (hKc.image_of_continuousOn (φ.continuousOn_symm.mono hKφ)).isClosed
  have hi : ∀ G ∈ 𝒢, ∀ G' ∈ 𝒢, G ∩ G' ∈ 𝒢 := by
    rintro _ ⟨K, hKφ, hKc, hKv, rfl⟩ _ ⟨K', hKφ', hKc', hKv', rfl⟩
    refine ⟨K ∩ K', inter_subset_left.trans hKφ, hKc.inter_right hKc'.isClosed, ?_,
      (φ.symm.injOn.image_inter hKφ hKφ').symm⟩
    rw [image_inter Subtype.val_injective]
    exact hKv.inter hKv'
  have hz : ∀ G ∈ 𝒢, ∀ k, n < k → IsZero (localHomology N G k) := by
    rintro _ ⟨K, hKφ, hKc, hKv, rfl⟩ k hk
    exact isZero_localHomology_symm_image_halfSpace N φ hf hn hKv hKc hKφ hk
  refine ⟨⋃ a ∈ t, φ.symm '' closedBall (φ a) (r a), ?_, iUnion₂_subset fun a ha ↦ (ht a ha).2.2.2,
    isZero_localHomology_biUnion hc hi hz t (fun a ha ↦ ?_) hk⟩
  · rwa [← image_iUnion₂]
  · obtain ⟨hcpt, hconv⟩ := isCompact_and_convex_closedBall_halfSpace (φ a) (r a)
    exact ⟨_, (ht a ha).2.2.1, hcpt, hconv, rfl⟩

/-- **Local homology of a compact subset of a manifold with boundary vanishes above the
dimension** (Hatcher, Lemma 3.27(b), for manifolds with boundary). Let `f ≠ 0` be a continuous
linear functional on a real normed space `E` of finite dimension `n`, and let `M` be a Hausdorff
space charted on the half-space `{x | 0 ≤ f x}`, a topological `n`-manifold with boundary. For
every compact `A ⊆ M`, `Hₖ(M, M ∖ A)` vanishes for `k > n`. -/
theorem isZero_localHomology_of_isCompact_halfSpace [ChartedSpace ↥{x : E | 0 ≤ f x} M]
    (hf : f ≠ 0) (hn : finrank ℝ E = n) {A : Set M} (hA : IsCompact A) {k : ℕ} (hk : n < k) :
    IsZero (localHomology N A k) :=
  isZero_localHomology_of_isCompact_of_forall_mem_nhds N
    (fun x ↦ ⟨_, chart_source_mem_nhds _ x, fun _ hB hBc _ hk ↦
      isZero_localHomology_of_subset_source_halfSpace N hf hn _ hBc hB hk⟩) hA hk

/-- **Local homology of a compact subset of a manifold with boundary vanishes above the
dimension**, for Mathlib's model `EuclideanHalfSpace n` of manifolds with boundary: for a
Hausdorff space `M` charted on `EuclideanHalfSpace n` and a compact `A ⊆ M`, `Hₖ(M, M ∖ A)`
vanishes for `k > n`. -/
theorem isZero_localHomology_of_isCompact_euclideanHalfSpace {Λ : Type} [Ring Λ]
    (N : ModuleCat.{0} Λ) {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace n) M] {A : Set M} (hA : IsCompact A) {k : ℕ}
    (hk : n < k) : IsZero (localHomology N A k) := by
  have hf : (EuclideanSpace.proj (0 : Fin n) : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ≠ 0 :=
    fun h ↦ by simpa using congrArg (· (EuclideanSpace.single (0 : Fin n) (1 : ℝ))) h
  -- Transport the charts along the identity homeomorphism from `EuclideanHalfSpace n`, the
  -- subtype `{x | 0 ≤ x 0}`, to the half-space of the coordinate functional
  -- `EuclideanSpace.proj 0`.
  let H := ↥{x : EuclideanSpace ℝ (Fin n) | 0 ≤ EuclideanSpace.proj (0 : Fin n) x}
  let e : EuclideanHalfSpace n ≃ₜ H := (Homeomorph.refl _).subtype fun x ↦ by simp
  let _ : ChartedSpace H M := e.chartedSpaceComp M
  exact isZero_localHomology_of_isCompact_halfSpace N hf finrank_euclideanSpace_fin hA hk

end HalfSpaceModule

end TauCeti
