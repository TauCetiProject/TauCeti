/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Category.TopCat.Paracompact
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.Category.TopCat.Lindelof
import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.Topology.Compactness.Lindelof

/-!
# The skeletal filtration of the fat realization

The `n`-skeleton of the fat realization `‖X‖` of a semi-simplicial space `X` is the union of the
images of the characteristic maps `Xₖ × Δᵏ → ‖X‖` for `k ≤ n` (`TauCeti.fatRealization.skeleton`).
The skeleta present `‖X‖` as a space built by successive closed attachments:

* each skeleton is closed (`TauCeti.fatRealization.isClosed_skeleton`), and `‖X‖` is the colimit
  in `TopCat` of its skeleta along their inclusions (`TauCeti.fatRealization.isColimitSkeleton`);
* the `(n + 1)`-skeleton is obtained from the `n`-skeleton by attaching `Xₙ₊₁ × Δⁿ⁺¹` along
  `Xₙ₊₁ × ∂Δⁿ⁺¹`: the square formed by the attaching map, the boundary inclusion, the skeleton
  inclusion and the characteristic map is a pushout in `TopCat`
  (`TauCeti.fatRealization.isPushout_skeleton`);
* the `0`-skeleton is a copy of `X₀ × Δ⁰` (`TauCeti.fatRealization.isHomeomorph_skeletonι_zero`).

As the fat realization has no degeneracies, the attaching subspace is all of `Xₙ₊₁ × ∂Δⁿ⁺¹`; no
latching object enters. Attaching along closed subspaces preserves normality, `T1` and the
Lindelöf property, and a sequential colimit of normal `T1` Lindelöf spaces along closed embeddings
is paracompact. Hence the fat realization of a semi-simplicial space with regular, `T1`, Lindelöf
levels is paracompact and `T4` (`TauCeti.fatRealization.paracompactSpace`,
`TauCeti.fatRealization.t4Space`). For the topological nerve of a groupoid whose arrows form a
second-countable Hausdorff manifold, this makes the fat classifying space paracompact Hausdorff,
as needed for partitions of unity and numerable covers on it.

The combinatorial input concerns topological simplices. Every point of `Δⁿ` lies off the boundary
of a unique face, its carrier, spanned by the vertices at which its barycentric coordinates
(`SemiSimplexCategory.toTopWeights`) are nonzero (`SemiSimplexCategory.exists_toTop_map_eq`,
`SemiSimplexCategory.eq_and_eq_of_toTop_map_eq`). Consequently distinct points `(x, t)` of
`Xₙ × Δⁿ` with `t` off the boundary `∂Δⁿ` (`SemiSimplexCategory.toTopBoundary`) have distinct
images in `‖X‖` (`TauCeti.fatRealization.injOn_ι`), so the characteristic map of level `n + 1` is
injective off the attaching subspace.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory Limits Opposite Set Topology Convexity

open scoped Finset

open scoped Simplicial

universe u

namespace TauCeti.fatRealization

open SemiSimplexCategory TauCeti.TopCat

variable (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u})

/-- The `n`-skeleton of the fat realization `‖X‖`: the union of the images of the characteristic
maps `Xₖ × Δᵏ → ‖X‖` for `k ≤ n`. -/
def skeleton (n : ℕ) : Set (fatRealization X) :=
  ⋃ (k : ℕ) (_ : k ≤ n), range (ι X ⦋k⦌ₛ)

variable {X}

/-- A point lies in the `n`-skeleton exactly when it is in the image of the characteristic map of
some level `k ≤ n`. -/
theorem mem_skeleton_iff {p : fatRealization X} {n : ℕ} :
    p ∈ skeleton X n ↔ ∃ k ≤ n, p ∈ range (ι X ⦋k⦌ₛ) := by
  simp [skeleton]

/-- The image of the characteristic map of a level `k ≤ n` lies in the `n`-skeleton. -/
theorem range_ι_subset_skeleton {k n : ℕ} (h : k ≤ n) : range (ι X ⦋k⦌ₛ) ⊆ skeleton X n :=
  fun _ hp ↦ mem_skeleton_iff.2 ⟨k, h, hp⟩

/-- The skeleta of the fat realization increase. -/
theorem monotone_skeleton : Monotone (skeleton X) := fun _ _ h _ hp ↦ by
  obtain ⟨k, hk, hp⟩ := mem_skeleton_iff.1 hp
  exact range_ι_subset_skeleton (hk.trans h) hp

/-- The skeleta exhaust the fat realization. -/
theorem iUnion_skeleton : ⋃ n, skeleton X n = univ :=
  eq_univ_of_forall fun p ↦ by
    obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
    exact mem_iUnion.2 ⟨n.len, range_ι_subset_skeleton le_rfl ⟨(x, t), rfl⟩⟩

/-- The number of nonzero barycentric coordinates of a point of the fat realization, that is, the
number of vertices of the face of a simplex carrying it. -/
private def card : fatRealization X → ℕ :=
  lift (fun _ p ↦ #(toTopWeights p.2).support) fun _ _ f _ t ↦
    (card_support_toTopWeights_toTop_map f t).symm

/-- A point `[x, t]` lies in the `n`-skeleton exactly when at most `n + 1` barycentric coordinates
of `t` are nonzero. -/
theorem ι_mem_skeleton_iff {m : SemiSimplexCategory} {x : X.obj (op m)} {t : toTop.{u}.obj m}
    {n : ℕ} : ι X m (x, t) ∈ skeleton X n ↔ #(toTopWeights t).support ≤ n + 1 := by
  constructor
  · intro hp
    obtain ⟨k, hk, ⟨y, s⟩, h⟩ := mem_skeleton_iff.1 hp
    have hcard : card (ι X ⦋k⦌ₛ (y, s)) = card (ι X m (x, t)) := congrArg _ h
    simp only [card, lift_ι] at hcard
    have : _ ≤ k + 1 := card_support_toTopWeights_le s
    omega
  · intro h
    obtain ⟨a, f, s, hs, rfl⟩ := exists_toTop_map_eq t
    rw [card_support_toTopWeights_toTop_map, notMem_toTopBoundary_iff.1 hs] at h
    rw [← ι_map]
    exact range_ι_subset_skeleton (show a.len ≤ n by omega) ⟨_, rfl⟩

/-- For a level `n`, the points `(y, u)` of `Xₙ × Δⁿ` with `u` off the boundary which represent a
given point of the fat realization. -/
private def reps (n : SemiSimplexCategory) :
    fatRealization X → Set (X.obj (op n) × toTop.{u}.obj n) :=
  lift (fun m p ↦ {q | q.2 ∉ toTopBoundary n ∧
      ∃ f : n ⟶ m, toTop.map f q.2 = p.2 ∧ X.map f.op p.1 = q.1}) <| by
    intro m m' f x t
    refine Set.ext fun q ↦ and_congr_right fun hv ↦ ⟨?_, ?_⟩
    · rintro ⟨g, hg, hgx⟩
      refine ⟨g ≫ f, ?_, ?_⟩
      · rw [Functor.map_comp, ConcreteCategory.comp_apply, hg]
      · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hgx]
    · rintro ⟨g, hg, hgx⟩
      -- The carrier face of `t` is the carrier face of `f_* t`, so it is the face `g`.
      obtain ⟨a, e, s, hs, rfl⟩ := exists_toTop_map_eq t
      have hg' : toTop.map (e ≫ f) s = toTop.map g q.2 := by
        rw [Functor.map_comp, ConcreteCategory.comp_apply, hg]
      obtain rfl := eq_of_toTop_map_eq hs hv hg'
      obtain ⟨rfl, rfl⟩ := eq_and_eq_of_toTop_map_eq hs hv hg'
      refine ⟨e, rfl, ?_⟩
      rw [← hgx, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem reps_ι_of_notMem {n : SemiSimplexCategory} {x : X.obj (op n)}
    {u : toTop.{u}.obj n} (hu : u ∉ toTopBoundary n) : reps n (ι X n (x, u)) = {(x, u)} := by
  rw [reps, lift_ι]
  refine Set.ext fun ⟨y, v⟩ ↦ ⟨fun ⟨hv, g, hg, hgx⟩ ↦ ?_, ?_⟩
  · dsimp only at hv hg hgx ⊢
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_toTop_map_eq (g := 𝟙 n) hv hu
      (by rw [hg, CategoryTheory.Functor.map_id, TopCat.id_app])
    rw [← hgx, op_id, CategoryTheory.Functor.map_id, TopCat.id_app]
    rfl
  · rintro ⟨⟩
    exact ⟨hu, 𝟙 n, by rw [CategoryTheory.Functor.map_id, TopCat.id_app],
      by rw [op_id, CategoryTheory.Functor.map_id, TopCat.id_app]⟩

/-- The characteristic map of level `n` is injective off `Xₙ × ∂Δⁿ`: distinct points `(x, t)` of
`Xₙ × Δⁿ` with `t` off the boundary have distinct images in `‖X‖`. -/
theorem injOn_ι (n : SemiSimplexCategory) : InjOn (ι X n) {p | p.2 ∉ toTopBoundary n} :=
  fun p hp q hq h ↦ by
    have := congrArg (reps n) h
    rwa [reps_ι_of_notMem hp, reps_ι_of_notMem hq, singleton_eq_singleton_iff] at this

/-- A subset of the `n`-skeleton is closed as soon as its preimages under the characteristic maps
of the levels `k ≤ n` are closed. -/
theorem isClosed_of_subset_skeleton {n : ℕ} {C : Set (fatRealization X)} (hC : C ⊆ skeleton X n)
    (h : ∀ k ≤ n, IsClosed (ι X ⦋k⦌ₛ ⁻¹' C)) : IsClosed C := by
  rw [isClosed_iff]
  intro m
  -- A point of `Xₘ × Δᵐ` over `C` is the image of a point of a face of dimension at most `n`.
  have : ι X m ⁻¹' C = ⋃ (k : ℕ) (_ : k ≤ n) (f : ⦋k⦌ₛ ⟶ m),
      Prod.map id (toTop.map f) '' (Prod.map (X.map f.op) id ⁻¹' (ι X ⦋k⦌ₛ ⁻¹' C)) := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, mem_iUnion, Set.mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · intro hxt
      obtain ⟨a, f, s, hs, rfl⟩ := exists_toTop_map_eq t
      have := ι_mem_skeleton_iff.1 (hC hxt)
      rw [card_support_toTopWeights_toTop_map, notMem_toTopBoundary_iff.1 hs] at this
      exact ⟨a.len, by omega, f, x, s, by rwa [ι_map], rfl, rfl⟩
    · rintro ⟨k, -, f, y, s, hys, rfl, rfl⟩
      rwa [← ι_map]
  rw [this]
  refine (finite_le_nat n).isClosed_biUnion fun k hk ↦ isClosed_iUnion_of_finite fun f ↦ ?_
  exact (IsClosedEmbedding.id.prodMap (isClosedEmbedding_toTop_map f)).isClosedMap _
    ((h k hk).preimage (by fun_prop))

/-- The skeleta of the fat realization are closed. -/
theorem isClosed_skeleton (n : ℕ) : IsClosed (skeleton X n) :=
  isClosed_of_subset_skeleton subset_rfl fun _ hk ↦ by
    rw [preimage_eq_univ_iff.2 (range_ι_subset_skeleton hk)]
    exact isClosed_univ

variable (X) in
/-- The characteristic map `Xₖ × Δᵏ → skₙ ‖X‖` of a level `k ≤ n`, into the `n`-skeleton. -/
def skeletonιOfLE {k n : ℕ} (h : k ≤ n) :
    TopCat.of (X.obj (op ⦋k⦌ₛ) × toTop.{u}.obj ⦋k⦌ₛ) ⟶ TopCat.of (skeleton X n) :=
  TopCat.ofHom ⟨fun p ↦ ⟨ι X ⦋k⦌ₛ p, range_ι_subset_skeleton h ⟨p, rfl⟩⟩,
    (ι X ⦋k⦌ₛ).continuous.subtype_mk _⟩

@[simp]
theorem coe_skeletonιOfLE_apply {k n : ℕ} (h : k ≤ n)
    (p : X.obj (op ⦋k⦌ₛ) × toTop.{u}.obj ⦋k⦌ₛ) :
    (skeletonιOfLE X h p : fatRealization X) = ι X ⦋k⦌ₛ p :=
  (rfl)

variable (X) in
/-- The characteristic map `Xₙ × Δⁿ → skₙ ‖X‖` of the level `n`, into the `n`-skeleton. -/
def skeletonι (n : ℕ) :
    TopCat.of (X.obj (op ⦋n⦌ₛ) × toTop.{u}.obj ⦋n⦌ₛ) ⟶ TopCat.of (skeleton X n) :=
  skeletonιOfLE X le_rfl

/-- The characteristic map of the level `n` into the `n`-skeleton is the case `k = n` of
`skeletonιOfLE`. -/
theorem skeletonι_eq_skeletonιOfLE (n : ℕ) : skeletonι X n = skeletonιOfLE X le_rfl :=
  (rfl)

@[simp]
theorem coe_skeletonι_apply (n : ℕ) (p : X.obj (op ⦋n⦌ₛ) × toTop.{u}.obj ⦋n⦌ₛ) :
    (skeletonι X n p : fatRealization X) = ι X ⦋n⦌ₛ p :=
  (rfl)

/-- The preimage of a subset of the `n`-skeleton under the characteristic map of a level `k ≤ n`
is its preimage under the corestriction of that map to the skeleton. -/
private theorem preimage_ι_image_val {n k : ℕ} (hk : k ≤ n) (C : Set (skeleton X n)) :
    ι X ⦋k⦌ₛ ⁻¹' (Subtype.val '' C) = skeletonιOfLE X hk ⁻¹' C := by
  ext p
  refine ⟨fun ⟨q, hq, hqp⟩ ↦ ?_, fun hp ↦ ⟨_, hp, rfl⟩⟩
  rwa [show q = skeletonιOfLE X hk p from Subtype.ext hqp] at hq

/-- A subset of the `n`-skeleton is closed in the skeleton as soon as its preimages under the
corestrictions of the characteristic maps of the levels `k ≤ n` are closed. -/
private theorem isClosed_of_preimage {n : ℕ} {C : Set (skeleton X n)}
    (h : ∀ k (hk : k ≤ n), IsClosed (skeletonιOfLE X hk ⁻¹' C)) :
    IsClosed C :=
  (isClosed_skeleton n).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.2 <|
    isClosed_of_subset_skeleton (Subtype.coe_image_subset _ C) fun k hk ↦ by
      rw [preimage_ι_image_val hk]
      exact h k hk

/-- The points of `Xₙ₊₁ × ∂Δⁿ⁺¹` are mapped into the `n`-skeleton. -/
theorem ι_mem_skeleton_of_mem_toTopBoundary {n : ℕ} (x : X.obj (op ⦋n + 1⦌ₛ))
    {t : toTop.{u}.obj ⦋n + 1⦌ₛ} (ht : t ∈ toTopBoundary ⦋n + 1⦌ₛ) :
    ι X ⦋n + 1⦌ₛ (x, t) ∈ skeleton X n := by
  have : _ < n + 1 + 1 := mem_toTopBoundary_iff_card_lt.1 ht
  exact ι_mem_skeleton_iff.2 (by omega)

variable (X) in
/-- The attaching map `Xₙ₊₁ × ∂Δⁿ⁺¹ → skₙ ‖X‖` of the level `n + 1`. -/
def skeletonAttach (n : ℕ) :
    TopCat.of (X.obj (op ⦋n + 1⦌ₛ) × toTopBoundary.{u} ⦋n + 1⦌ₛ) ⟶ TopCat.of (skeleton X n) :=
  TopCat.ofHom ⟨fun p ↦
      ⟨ι X ⦋n + 1⦌ₛ (p.1, p.2), ι_mem_skeleton_of_mem_toTopBoundary p.1 p.2.property⟩,
    ((ι X _).continuous.comp (continuous_fst.prodMk (continuous_subtypeVal.comp
      continuous_snd))).subtype_mk _⟩

@[simp]
theorem coe_skeletonAttach_apply (n : ℕ)
    (p : X.obj (op ⦋n + 1⦌ₛ) × toTopBoundary.{u} ⦋n + 1⦌ₛ) :
    (skeletonAttach X n p : fatRealization X) = ι X ⦋n + 1⦌ₛ (p.1, p.2) :=
  (rfl)

variable (X) in
/-- **The skeletal pushout.** The `(n + 1)`-skeleton of the fat realization is obtained from the
`n`-skeleton by attaching `Xₙ₊₁ × Δⁿ⁺¹` along `Xₙ₊₁ × ∂Δⁿ⁺¹`: the square of the attaching map, the
boundary inclusion, the skeleton inclusion and the characteristic map is a pushout in `TopCat`. -/
theorem isPushout_skeleton (n : ℕ) :
    IsPushout (skeletonAttach X n)
      (TopCat.ofHom ((ContinuousMap.id _).prodMap (ContinuousMap.subtypeVal _)))
      ((subspaceDiagram (monotone_skeleton (X := X))).map (homOfLE n.le_succ))
      (skeletonι X (n + 1)) := by
  refine IsPushout.of_isPushout_forget ?_ fun s hs hs' ↦ ?_
  · -- The instance argument `Mono` of the inclusion of skeleta is not found by unification, so
    -- it is left as the last goal.
    apply +allowSynthFailures Types.isPushout_of_isPullback_of_mono'
    case h₁ =>
      refine (Types.isPullback_iff _ _ _ _).2 ⟨rfl, ?_, ?_⟩
      · rintro p q ⟨-, h⟩
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact Prod.ext h₁ (Subtype.ext h₂)
      · rintro ⟨p, hp⟩ ⟨x, t⟩ h
        obtain rfl : p = ι X _ (x, t) := congrArg Subtype.val h
        have : _ ≤ n + 1 := ι_mem_skeleton_iff.1 hp
        exact ⟨(x, ⟨t, mem_toTopBoundary_iff_card_lt.2 (show _ < n + 1 + 1 by omega)⟩), rfl, rfl⟩
    case h₂ =>
      refine eq_univ_of_forall fun ⟨p, hp⟩ ↦ ?_
      obtain ⟨k, hk, q, rfl⟩ := mem_skeleton_iff.1 hp
      rcases Nat.of_le_succ hk with hk | rfl
      · exact Or.inl ⟨skeletonιOfLE X hk q, rfl⟩
      · exact Or.inr ⟨q, rfl⟩
    case H =>
      rintro ⟨x, t⟩ ⟨y, t'⟩ ht ht' h
      refine injOn_ι _ (fun hb ↦ ht ⟨(x, ⟨t, hb⟩), rfl⟩) (fun hb ↦ ht' ⟨(y, ⟨t', hb⟩), rfl⟩)
        (congrArg Subtype.val h)
    exact (mono_iff_injective _).2 (inclusion_injective (monotone_skeleton n.le_succ))
  · -- The complement of `s` is closed, as its preimages under the characteristic maps of the
    -- levels `k ≤ n` factor through the `n`-skeleton.
    rw [← isClosed_compl_iff] at hs hs' ⊢
    refine isClosed_of_preimage fun k hk ↦ ?_
    rcases Nat.of_le_succ hk with hk | rfl
    · -- The bonding map of the diagram of skeleta is `Set.inclusion`, so the characteristic map of
      -- level `k` into the `(n + 1)`-skeleton is definitionally that into the `n`-skeleton
      -- followed by the bonding map.
      exact hs.preimage (skeletonιOfLE X hk).hom.continuous
    · rwa [← skeletonι_eq_skeletonιOfLE]

/-- The `0`-skeleton of the fat realization is a copy of `X₀ × Δ⁰`. -/
theorem isHomeomorph_skeletonι_zero : IsHomeomorph (skeletonι X 0) := by
  have hΔ (t : toTop.{u}.obj ⦋0⦌ₛ) : t ∉ toTopBoundary ⦋0⦌ₛ := fun ht ↦ by
    have : _ < 0 + 1 := mem_toTopBoundary_iff_card_lt.1 ht
    have := Finset.card_pos.2 (support_toTopWeights_nonempty t)
    omega
  have hinj : Function.Injective (skeletonι X 0) := fun p q h ↦
    injOn_ι _ (hΔ p.2) (hΔ q.2) (congrArg Subtype.val h)
  refine isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨(skeletonι X 0).hom.continuous, fun D hD ↦ isClosed_of_preimage fun k hk ↦ ?_, hinj, ?_⟩
  · obtain rfl : k = 0 := Nat.le_zero.1 hk
    rw [← skeletonι_eq_skeletonιOfLE, hinj.preimage_image]
    exact hD
  · rintro ⟨p, hp⟩
    obtain ⟨k, hk, q, rfl⟩ := mem_skeleton_iff.1 hp
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact ⟨q, rfl⟩

variable (X) in
/-- The fat realization is the colimit in `TopCat` of its skeleta along their inclusions: its
topology is coherent with the skeleta. -/
def isColimitSkeleton : IsColimit (subspaceCocone (monotone_skeleton (X := X))) :=
  isColimitOfIsCoherentWith _ iUnion_skeleton <| .of_isClosed fun _ hC ↦ (isClosed_iff X).2 fun m ↦
    -- As `m` is definitionally `⦋m.len⦌ₛ`, the characteristic map `ι X m` is definitionally the
    -- corestriction `skeletonιOfLE X le_rfl` followed by `Subtype.val`.
    (hC _ ⟨m.len, rfl⟩).preimage (skeletonιOfLE X le_rfl).hom.continuous

/-- The boundary inclusion `Xₙ × ∂Δⁿ → Xₙ × Δⁿ` is a closed embedding. -/
private theorem isClosedEmbedding_boundary (n : ℕ) :
    IsClosedEmbedding (TopCat.ofHom ((ContinuousMap.id (X.obj (op ⦋n⦌ₛ))).prodMap
      (ContinuousMap.subtypeVal (toTopBoundary.{u} ⦋n⦌ₛ)))) :=
  IsClosedEmbedding.id.prodMap (isClosed_toTopBoundary _).isClosedEmbedding_subtypeVal

/-- The inclusions of the skeleta of the fat realization are closed embeddings. -/
private theorem isClosedEmbedding_skeleton_map (n : ℕ) :
    IsClosedEmbedding ((subspaceDiagram (monotone_skeleton (X := X))).map (homOfLE n.le_succ)) :=
  isClosedEmbedding_of_isPushout (isPushout_skeleton X n) (isClosedEmbedding_boundary _)

section Paracompact

variable [∀ n, RegularSpace (X.obj n)] [∀ n, T1Space (X.obj n)] [∀ n, LindelofSpace (X.obj n)]

/-- Every skeleton of the fat realization is normal, `T1` and Lindelöf, by induction along the
skeletal pushouts. -/
private theorem normalSpace_t1Space_lindelofSpace_skeleton (n : ℕ) :
    NormalSpace (skeleton X n) ∧ T1Space (skeleton X n) ∧ LindelofSpace (skeleton X n) := by
  induction n with
  | zero =>
    let e := isHomeomorph_skeletonι_zero.homeomorph (skeletonι X 0)
    exact ⟨e.symm.isClosedEmbedding.normalSpace, e.symm.isEmbedding.t1Space,
      .of_continuous_surjective e.continuous e.surjective⟩
  | succ n ih =>
    obtain ⟨_, _, _⟩ := ih
    exact ⟨normalSpace_of_isPushout (isPushout_skeleton X n) (isClosedEmbedding_boundary _),
      t1Space_of_isPushout (isPushout_skeleton X n) (isClosedEmbedding_boundary _),
      lindelofSpace_of_isPushout (isPushout_skeleton X n)⟩

private instance normalSpace_skeleton (n : ℕ) :
    NormalSpace ((subspaceDiagram (monotone_skeleton (X := X))).obj n) :=
  (normalSpace_t1Space_lindelofSpace_skeleton n).1

private instance t1Space_skeleton (n : ℕ) :
    T1Space ((subspaceDiagram (monotone_skeleton (X := X))).obj n) :=
  (normalSpace_t1Space_lindelofSpace_skeleton n).2.1

private instance lindelofSpace_skeleton (n : ℕ) :
    LindelofSpace ((subspaceDiagram (monotone_skeleton (X := X))).obj n) :=
  (normalSpace_t1Space_lindelofSpace_skeleton n).2.2

/-- **Paracompactness of fat realizations.** The fat realization of a semi-simplicial space whose
levels are regular, `T1` and Lindelöf is paracompact. -/
instance paracompactSpace : ParacompactSpace (fatRealization X) :=
  paracompactSpace_of_isColimit isClosedEmbedding_skeleton_map (isColimitSkeleton X)

/-- The fat realization of a semi-simplicial space whose levels are regular, `T1` and Lindelöf is
normal and `T1`, in particular Hausdorff. -/
instance t4Space : T4Space (fatRealization X) :=
  t4Space_of_isColimit isClosedEmbedding_skeleton_map (isColimitSkeleton X)

end Paracompact

end TauCeti.fatRealization
