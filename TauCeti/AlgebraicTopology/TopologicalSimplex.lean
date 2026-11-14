/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Metrizable.Real
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex
public import TauCeti.Topology.Category.TopCat.Action

/-!
# The topological simplices and the singular simplices of a space

The topological `n`-simplex is a standard simplex on a finite nonempty type, up to a universe
lift, hence compact, Hausdorff, second-countable, metrizable, contractible and locally path
connected. Every monomorphism in `SimplexCategory` induces a closed embedding of topological
simplices (`SimplexCategory.isClosedEmbedding_toTop_map_of_mono`), and every point of a
topological simplex lies in the open interior (`SimplexCategory.toTopInterior`) of a unique face
(`SimplexCategory.exists_mono_toTop_map_mem_toTopInterior`,
`SimplexCategory.unique_mono_toTop_map_dim`, `SimplexCategory.unique_mono_toTop_map_hom`). The
geometric realization `|Δ[n]|` of the standard simplicial simplex, being homeomorphic to the
topological simplex, is contractible as well. This file also names its initial vertex, and the
continuous map on the topological `n`-simplex that underlies a singular `n`-simplex of a space.

## Main declarations

* `SimplexCategory.compactSpace`, `SimplexCategory.t2Space`,
  `SimplexCategory.secondCountableTopology`, `SimplexCategory.metrizableSpace`: topological
  finiteness and separation instances on `SimplexCategory.toTop.obj n`.
* `SimplexCategory.isClosedEmbedding_toTop_map_of_mono`: face maps of topological simplices are
  closed embeddings.
* `SimplexCategory.toTopInterior`, `SimplexCategory.toTopBoundary`,
  `SimplexCategory.toTopBoundary_eq_iUnion_range_δ`: the open interior and relative boundary of
  the topological simplex.
* `SimplexCategory.exists_mono_toTop_map_mem_toTopInterior`,
  `SimplexCategory.unique_mono_toTop_map_dim`, `SimplexCategory.unique_mono_toTop_map_hom`:
  existence and uniqueness of the interior face containing a point of `Δⁿ`.
* `SimplexCategory.toTopInitialVertex`: the initial vertex of the topological `n`-simplex, and
  `SimplexCategory.toTop_map_toTopInitialVertex_down`: its image under a morphism of simplices.
* `TauCeti.TopCat.simplexMap`: the continuous map underlying a singular simplex, with its
  behaviour under reindexing, pushforward and the lax monoidal structure of `TopCat.toSSet`, and
  the endpoints of the parametrization `SSet.stdSimplex.toSSetObjI` of the unit interval.
* `TauCeti.TopCat.mulActionToSSetObj`: a continuous action on a space acts on its singular
  simplices by translation, freely if it is free on the space
  (`TauCeti.TopCat.isCancelSMul_toSSetObj`).
-/

public section

open CategoryTheory Convexity Topology

open scoped Simplicial

universe u

namespace SimplexCategory

/-- Every topological simplex is compact, being a universe lift of a standard simplex on a finite
type. -/
instance compactSpace (n : SimplexCategory) : CompactSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).symm.compactSpace

/-- Every topological simplex is metrizable, as it embeds into a finite product of copies of `ℝ`. -/
instance metrizableSpace (n : SimplexCategory) :
    TopologicalSpace.MetrizableSpace (toTop.{u}.obj n) :=
  ((StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).comp
    (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).isEmbedding).metrizableSpace

/-- Every topological simplex is Hausdorff. -/
instance t2Space (n : SimplexCategory) : T2Space (toTop.{u}.obj n) := inferInstance

/-- Every topological simplex is second-countable, as it embeds into a finite product of copies
of `ℝ`. -/
instance secondCountableTopology (n : SimplexCategory) :
    SecondCountableTopology (toTop.{u}.obj n) :=
  ((StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).comp
    (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).isEmbedding).secondCountableTopology

/-- Every topological simplex is contractible, being a universe lift of a standard simplex on a
finite nonempty type. -/
instance contractibleSpace (n : SimplexCategory) : ContractibleSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).contractibleSpace

/-- The geometric realization `|Δ[n]|` of every standard simplex is contractible, being
homeomorphic to a standard simplex on a finite nonempty type. -/
instance contractibleSpace_toTop_stdSimplex (n : SimplexCategory) :
    ContractibleSpace |SSet.stdSimplex.{u}.obj n| :=
  n.toTopHomeo.contractibleSpace

/-- Every topological simplex is locally path connected, being a universe lift of a standard
simplex on a finite type. -/
instance locallyPathConnectedSpace (n : SimplexCategory) :
    LocallyPathConnectedSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).symm.locallyPathConnectedSpace

/-- Unlifting the action of a morphism on `SimplexCategory.toTop` gives `StdSimplex.map`. -/
theorem toTop_map_down {m n : SimplexCategory} (f : m ⟶ n) (t : toTop.{u}.obj m) :
    (toTop.{u}.map f t).down = StdSimplex.map f.toOrderHom t.down := (rfl)

/-- Pushing a point of a topological simplex forward along `f` takes the image of its coordinate
support under `f`. -/
theorem support_toTop_map {m n : SimplexCategory} (f : m ⟶ n) (t : toTop.{u}.obj m) :
    (toTop.{u}.map f t).down.weights.support =
      t.down.weights.support.image f.toOrderHom := by
  rw [toTop_map_down, StdSimplex.weights_map]
  exact Finsupp.support_mapDomain_of_nonneg (fun i ↦ t.down.nonneg i) f.toOrderHom

/-- Every monomorphism in `SimplexCategory` induces an injective map of topological simplices. -/
theorem toTop_map_injective_of_mono {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    Function.Injective (toTop.{u}.map f) := fun s t h ↦ by
  apply ULift.ext
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective (mono_iff_injective.mp ‹Mono f›)
    (congrArg (fun p : toTop.{u}.obj n ↦ p.down.weights) h)

/-- Every monomorphism in `SimplexCategory` induces a closed embedding of topological simplices,
since topological simplices are compact and Hausdorff. -/
theorem isClosedEmbedding_toTop_map_of_mono {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    IsClosedEmbedding (toTop.{u}.map f) :=
  (toTop.{u}.map f).hom.continuous.isClosedEmbedding (toTop_map_injective_of_mono f)

/-- A point of `Δⁿ` lies in the image of `f : m ⟶ n` if and only if all of its coordinates
outside the range of `f` vanish. -/
theorem mem_range_toTop_map_iff {m n : SimplexCategory} (f : m ⟶ n) (t : toTop.{u}.obj n) :
    t ∈ Set.range (toTop.{u}.map f) ↔ ∀ i, i ∉ Set.range f.toOrderHom → t.down.weights i = 0 := by
  rw [← StdSimplex.mem_range_map_iff f.toOrderHom t.down]
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨s.down, congrArg ULift.down hs⟩,
    fun ⟨s, hs⟩ ↦ ⟨ULift.up s, ULift.ext hs⟩⟩

/-- The open interior of the topological simplex `n`: the points with all barycentric coordinates
strictly positive. -/
def toTopInterior (n : SimplexCategory) : Set (toTop.{u}.obj n) :=
  {t | ∀ i, 0 < t.down.weights i}

/-- A point of a topological simplex lies in its open interior if and only if its weight support
is all vertices. -/
theorem mem_toTopInterior_iff_support_eq_univ {n : SimplexCategory} {t : toTop.{u}.obj n} :
    t ∈ toTopInterior n ↔ t.down.weights.support = Finset.univ := by
  simp only [toTopInterior, Set.mem_ofPred_eq, Finset.eq_univ_iff_forall, Finsupp.mem_support_iff]
  exact forall_congr' fun i ↦ (t.down.nonneg i).lt_iff_ne'

/-- Every epimorphism in `SimplexCategory` carries interior points to interior points. -/
theorem toTop_map_mem_toTopInterior_of_epi {m n : SimplexCategory} (f : m ⟶ n) [Epi f]
    {t : toTop.{u}.obj m} (ht : t ∈ toTopInterior m) :
    toTop.{u}.map f t ∈ toTopInterior n := by
  rw [mem_toTopInterior_iff_support_eq_univ] at ht ⊢
  rw [support_toTop_map, ht]
  exact Finset.image_univ_of_surjective (epi_iff_surjective.mp ‹Epi f›)

/-- The relative boundary of the topological simplex `n`, the complement of `toTopInterior n`. -/
def toTopBoundary (n : SimplexCategory) : Set (toTop.{u}.obj n) :=
  (toTopInterior n)ᶜ

/-- A point of a topological simplex lies on its relative boundary if and only if at least one
barycentric coordinate vanishes. -/
theorem mem_toTopBoundary_iff {n : SimplexCategory} {t : toTop.{u}.obj n} :
    t ∈ toTopBoundary n ↔ ∃ i, t.down.weights i = 0 := by
  simp only [toTopBoundary, toTopInterior, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt]
  exact exists_congr fun i ↦ ⟨fun h ↦ le_antisymm h (t.down.nonneg i), fun h ↦ h.le⟩

/-- The relative boundary of every topological simplex is closed. -/
theorem isClosed_toTopBoundary (n : SimplexCategory) : IsClosed (toTopBoundary.{u} n) := by
  have h : toTopBoundary.{u} n = ⋃ i : Fin (n.len + 1), {t | t.down.weights i = 0} := by
    ext t
    simp [mem_toTopBoundary_iff]
  rw [h]
  refine isClosed_iUnion_of_finite fun i ↦ isClosed_eq ?_ continuous_const
  exact (continuous_apply i).comp
    ((StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).continuous.comp
      continuous_uliftDown)

/-- The relative boundary of `Δⁿ⁺¹` is the union of the images of its `n + 2` codimension-one
faces `δ i`. -/
theorem toTopBoundary_eq_iUnion_range_δ (n : ℕ) :
    toTopBoundary.{u} ⦋n + 1⦌ = ⋃ i : Fin (n + 2), Set.range (toTop.{u}.map (δ i)) := by
  ext t
  rw [mem_toTopBoundary_iff, Set.mem_iUnion]
  refine exists_congr fun i ↦ ?_
  rw [mem_range_toTop_map_iff]
  have hrange : Set.range (δ i).toOrderHom = {i}ᶜ := Fin.range_succAbove i
  rw [hrange]
  exact ⟨fun hi j hj ↦ (Set.notMem_compl_iff.mp hj : j = i) ▸ hi,
    fun h ↦ h i (Set.notMem_compl_iff.mpr rfl)⟩

/-- Any morphism from a strictly lower-dimensional simplex lands in the relative boundary. -/
theorem toTop_map_mem_toTopBoundary_of_len_lt {m n : SimplexCategory} (f : m ⟶ n)
    (hm : m.len < n.len) (t : toTop.{u}.obj m) :
    toTop.{u}.map f t ∈ toTopBoundary n := by
  rw [mem_toTopBoundary_iff]
  by_contra! h
  have hsurj : Function.Surjective f.toOrderHom := fun i ↦ by
    by_contra hi
    exact h i ((mem_range_toTop_map_iff f (toTop.map f t)).mp ⟨t, rfl⟩ i hi)
  have hcard := Fintype.card_le_of_surjective f.toOrderHom hsurj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Every point of `Δⁿ` lies in the open interior of the image of some face `μ : ⦋k⦌ ⟶ ⦋n⦌`. -/
theorem exists_mono_toTop_map_mem_toTopInterior {n : ℕ} (t : toTop.{u}.obj ⦋n⦌) :
    ∃ (k : ℕ) (μ : ⦋k⦌ ⟶ ⦋n⦌) (_ : Mono μ) (u : toTop.{u}.obj ⦋k⦌),
      u ∈ toTopInterior ⦋k⦌ ∧ toTop.{u}.map μ u = t := by
  set S := t.down.weights.support
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finsupp.support_eq_empty]
    intro hzero
    have htot := t.down.total
    rw [hzero, Finsupp.sum_zero_index] at htot
    exact zero_ne_one htot
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e := S.orderEmbOfFin hk
  let μ : ⦋k⦌ ⟶ ⦋n⦌ := mkHom e.toOrderHom
  have hmono : Mono μ := mono_iff_injective.mpr e.injective
  have hrange : Set.range μ.toOrderHom = (S : Set (Fin (n + 1))) := S.range_orderEmbOfFin hk
  have hmem : t ∈ Set.range (toTop.{u}.map μ) := by
    rw [mem_range_toTop_map_iff, hrange]
    intro i hi
    exact Finsupp.notMem_support_iff.mp hi
  obtain ⟨u, hu⟩ := hmem
  refine ⟨k, μ, hmono, u, ?_, hu⟩
  rw [mem_toTopInterior_iff_support_eq_univ]
  apply Finset.eq_univ_of_card
  have himg := congrArg Finset.card (hu ▸ support_toTop_map μ u)
  have hcard := Finset.card_image_of_injective u.down.weights.support (f := μ.toOrderHom)
    e.injective
  exact hcard.symm.trans (himg.symm.trans (hk.trans (Fintype.card_fin (k + 1)).symm))

/-- The dimension of the face whose open interior contains a point of `Δⁿ` is unique. -/
theorem unique_mono_toTop_map_dim {n k₁ k₂ : ℕ} {μ₁ : ⦋k₁⦌ ⟶ ⦋n⦌} [Mono μ₁]
    {u₁ : toTop.{u}.obj ⦋k₁⦌} (hu₁ : u₁ ∈ toTopInterior ⦋k₁⦌)
    {μ₂ : ⦋k₂⦌ ⟶ ⦋n⦌} [Mono μ₂] {u₂ : toTop.{u}.obj ⦋k₂⦌} (hu₂ : u₂ ∈ toTopInterior ⦋k₂⦌)
    (h : toTop.{u}.map μ₁ u₁ = toTop.{u}.map μ₂ u₂) : k₁ = k₂ := by
  have hs := congrArg (fun p : toTop.{u}.obj ⦋n⦌ ↦ p.down.weights.support.card) h
  rw [support_toTop_map, support_toTop_map,
    mem_toTopInterior_iff_support_eq_univ.mp hu₁,
    mem_toTopInterior_iff_support_eq_univ.mp hu₂,
    Finset.card_image_of_injective _ (mono_iff_injective.mp ‹Mono μ₁›),
    Finset.card_image_of_injective _ (mono_iff_injective.mp ‹Mono μ₂›)] at hs
  simpa using hs

/-- The face morphism `⦋k⦌ ⟶ ⦋n⦌` whose open interior contains a point of `Δⁿ` is unique. -/
theorem unique_mono_toTop_map_hom {n k : ℕ} {μ₁ μ₂ : ⦋k⦌ ⟶ ⦋n⦌} [Mono μ₁]
    {u₁ u₂ : toTop.{u}.obj ⦋k⦌} (hu₁ : u₁ ∈ toTopInterior ⦋k⦌)
    (h : toTop.{u}.map μ₁ u₁ = toTop.{u}.map μ₂ u₂) : μ₁ = μ₂ := by
  have hs := congrArg (fun p : toTop.{u}.obj ⦋n⦌ ↦ p.down.weights.support) h
  rw [support_toTop_map, support_toTop_map, mem_toTopInterior_iff_support_eq_univ.mp hu₁] at hs
  have hinj₁ : Function.Injective μ₁.toOrderHom := mono_iff_injective.mp ‹Mono μ₁›
  have hcard₁ : (Finset.univ.image μ₁.toOrderHom).card = k + 1 := by
    simpa using Finset.card_image_of_injective Finset.univ hinj₁
  have hsub : Finset.univ.image μ₁.toOrderHom ⊆ Finset.univ.image μ₂.toOrderHom :=
    hs ▸ Finset.image_subset_image (Finset.subset_univ _)
  have hcard₂ : (Finset.univ.image μ₂.toOrderHom).card = k + 1 :=
    le_antisymm (Finset.card_image_le.trans (by simp))
      (hcard₁.symm.le.trans (Finset.card_le_card hsub))
  have heq_img : Finset.univ.image μ₁.toOrderHom = Finset.univ.image μ₂.toOrderHom :=
    Finset.eq_of_subset_of_card_le hsub (hcard₂.trans hcard₁.symm).le
  have hinj₂ : Function.Injective μ₂.toOrderHom := fun i j hij ↦
    Finset.card_image_iff.mp (hcard₂.trans (by simp)) (Finset.mem_univ i) (Finset.mem_univ j) hij
  have heq := (Finset.orderEmbOfFin_unique hcard₁ (f := μ₁.toOrderHom)
    (fun i ↦ Finset.mem_image_of_mem μ₁.toOrderHom (Finset.mem_univ i))
    (μ₁.toOrderHom.monotone.strictMono_of_injective hinj₁)).trans
    (Finset.orderEmbOfFin_unique hcard₁ (f := μ₂.toOrderHom)
      (fun i ↦ heq_img.symm ▸ Finset.mem_image_of_mem μ₂.toOrderHom (Finset.mem_univ i))
      (μ₂.toOrderHom.monotone.strictMono_of_injective hinj₂)).symm
  ext i : 3
  exact congrFun heq i

/-- The initial vertex of the topological `n`-simplex: the universe lift of the standard-simplex
vertex `StdSimplex.single 0`. -/
noncomputable def toTopInitialVertex (n : SimplexCategory) : toTop.{u}.obj n :=
  ULift.up (StdSimplex.single 0)

/-- The initial vertex of the topological `n`-simplex lifts the standard-simplex vertex
`StdSimplex.single 0`. -/
@[simp]
lemma toTopInitialVertex_down (n : SimplexCategory) :
    (toTopInitialVertex.{u} n).down = StdSimplex.single 0 := (rfl)

/-- A map of topological simplices carries the initial vertex to the vertex indexed by
its value at zero. -/
-- Compute the vertex image before `toTop_map` unfolds the inner map.
@[simp↓]
lemma toTop_map_toTopInitialVertex_down {m n : SimplexCategory} (α : m ⟶ n) :
    (toTop.{u}.map α (toTopInitialVertex m)).down = StdSimplex.single (α.toOrderHom 0) := by
  -- The lifted affine map is read in standard-simplex coordinates.
  rw [toTop_map]
  change StdSimplex.map α.toOrderHom (toTopInitialVertex.{u} m).down = _
  rw [toTopInitialVertex_down, StdSimplex.map_single]

/-- A morphism of simplices fixing `0` fixes the initial vertex of the topological simplex. -/
lemma toTop_map_toTopInitialVertex {m n : SimplexCategory} (α : m ⟶ n)
    (hα : α.toOrderHom 0 = 0) : toTop.{u}.map α (toTopInitialVertex m) = toTopInitialVertex n :=
  ULift.ext (by rw [toTop_map_toTopInitialVertex_down, hα, toTopInitialVertex_down])

/-- A coface map other than the zeroth one fixes `0`. -/
lemma δ_toOrderHom_zero {n : ℕ} {i : Fin (n + 2)} (hi : i ≠ 0) : (δ i).toOrderHom 0 = 0 :=
  Fin.succAbove_ne_zero_zero hi

/-- Every codegeneracy map fixes `0`. -/
lemma σ_toOrderHom_zero {n : ℕ} (i : Fin (n + 1)) : (σ i).toOrderHom 0 = 0 :=
  Fin.predAbove_right_zero (i := i)

/-- The first edge of a topological simplex starts at its initial vertex. -/
lemma toTop_map_mkOfLe_toTopInitialVertex (k : ℕ) :
    toTop.{u}.map (mkOfLe (n := k + 1) 0 1 (by simp)) (toTopInitialVertex ⦋1⦌) =
      toTopInitialVertex ⦋k + 1⦌ :=
  toTop_map_toTopInitialVertex _ rfl

/-- The first edge of a topological simplex ends at vertex `1`, the initial vertex of the zeroth
face. -/
lemma toTop_map_mkOfLe_toTop_map_δ_zero (k : ℕ) :
    toTop.{u}.map (mkOfLe (n := k + 1) 0 1 (by simp))
        (toTop.map (δ 0) (toTopInitialVertex ⦋0⦌)) =
      toTop.map (δ 0) (toTopInitialVertex ⦋k⦌) := by
  refine ULift.ext ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, toTop_map_toTopInitialVertex_down,
    toTop_map_toTopInitialVertex_down]
  rfl

end SimplexCategory

namespace TauCeti.TopCat

variable {X Y : TopCat.{u}} {m n : SimplexCategoryᵒᵖ}

/-- The continuous map underlying a singular simplex, defined on the topological simplex
`SimplexCategory.toTop.obj n.unop` rather than on the unlifted model used by
`TopCat.toSSetObjEquiv`, so that it composes directly with the maps `SimplexCategory.toTop.map`. -/
-- The body must stay exposed: the endpoints of a transport inside a simplex, as they appear in
-- `TauCeti.LocalCoefficientSystem.pathTransport_map` and `map_pathTransport`, agree only
-- definitionally, so without it those statements are not type-correct.
@[expose]
noncomputable def simplexMap (σ : (TopCat.toSSet.obj X).obj n) :
    C(SimplexCategory.toTop.{u}.obj n.unop, X) := σ.down.hom

/-- A singular simplex is determined by its underlying continuous map. -/
lemma simplexMap_injective :
    Function.Injective (simplexMap : (TopCat.toSSet.obj X).obj n → _) := by
  intro σ τ h
  exact ULift.ext (ConcreteCategory.hom_injective h)

/-- Every continuous map on the topological simplex underlies a singular simplex. -/
lemma simplexMap_surjective :
    Function.Surjective (simplexMap : (TopCat.toSSet.obj X).obj n → _) :=
  fun f ↦ ⟨ULift.up (TopCat.ofHom f), rfl⟩

/-- Reindexing a singular simplex precomposes the underlying continuous map with the induced map
of topological simplices. -/
@[simp]
lemma simplexMap_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    simplexMap ((TopCat.toSSet.obj X).map α σ) =
      (simplexMap σ).comp (SimplexCategory.toTop.map α.unop).hom := rfl

/-- The image of a reindexed singular simplex, for instance of a face, lies in the image of the
original simplex. -/
lemma range_simplexMap_map_subset (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    Set.range (simplexMap ((TopCat.toSSet.obj X).map α σ)) ⊆ Set.range (simplexMap σ) := by
  rw [simplexMap_map, ContinuousMap.coe_comp]
  exact Set.range_comp_subset_range _ _

/-- Pushing a singular simplex forward along a continuous map postcomposes the underlying
continuous map with that map. -/
@[simp]
lemma simplexMap_app (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n) :
    simplexMap ((TopCat.toSSet.map f).app n σ) = f.hom.comp (simplexMap σ) := rfl

/-- The singular simplex of a product built from two singular simplices by the lax monoidal
structure of the singular simplicial set functor has these two simplices as components. -/
lemma simplexMap_μ_apply (a : (TopCat.toSSet.obj X).obj n) (b : (TopCat.toSSet.obj Y).obj n)
    (p : SimplexCategory.toTop.{u}.obj n.unop) :
    simplexMap ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n ⟨a, b⟩) p =
      ((simplexMap a p, simplexMap b p) : X × Y) :=
  Prod.ext congr(simplexMap $(congr($(Functor.Monoidal.μ_fst TopCat.toSSet X Y).app n ⟨a, b⟩)) p)
    congr(simplexMap $(congr($(Functor.Monoidal.μ_snd TopCat.toSSet X Y).app n ⟨a, b⟩)) p)

/-- The singular `0`-simplex corresponding to a point is the constant map at that point. -/
@[simp]
lemma simplexMap_toSSetObj₀Equiv_symm_apply (x : X) (p : SimplexCategory.toTop.{u}.obj ⦋0⦌) :
    simplexMap (TopCat.toSSetObj₀Equiv.symm x) p = x := rfl

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` sends the vertex `ε` to the point `ε` of `Δ[1]`. -/
lemma simplexMap_toSSetObjI_objMk₁_toTop_map {ε : Fin 2} (v : ⦋0⦌ ⟶ ⦋1⦌)
    (hv : v.toOrderHom 0 = ε) (p : SimplexCategory.toTop.{u}.obj ⦋0⦌) :
    simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌) (SSet.stdSimplex.objMk₁ 1))
        (SimplexCategory.toTop.map v p) =
      simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋0⦌) (SSet.stdSimplex.const 1 ε _)) p := by
  have hb : (Δ[1] : SSet.{u}).map v.op (SSet.stdSimplex.objMk₁ (1 : Fin 3)) =
      SSet.stdSimplex.const 1 ε _ := by
    ext k : 1
    fin_cases k
    refine (SSet.stdSimplex.objMk₁_apply.{u} _ _).trans ?_
    dsimp
    simp only [hv]
    fin_cases ε <;> rfl
  rw [← hb, NatTrans.naturality_apply SSet.stdSimplex.toSSetObjI.{u} v.op, simplexMap_map]
  rfl

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` starts at `0`. -/
lemma homeomorph_simplexMap_toSSetObjI_toTopInitialVertex :
    TopCat.I.homeomorph (simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌)
      (SSet.stdSimplex.objMk₁ 1)) (SimplexCategory.toTopInitialVertex ⦋1⦌)) = 0 := by
  rw [← SimplexCategory.toTop_map_toTopInitialVertex (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) rfl,
    simplexMap_toSSetObjI_objMk₁_toTop_map _ (ε := 0) rfl,
    SSet.stdSimplex.toSSetObj_app_const_zero, simplexMap_toSSetObj₀Equiv_symm_apply,
    TopCat.I.homeomorph_zero]

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` ends at `1`. -/
lemma homeomorph_simplexMap_toSSetObjI_toTop_map_δ_zero :
    TopCat.I.homeomorph (simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌)
      (SSet.stdSimplex.objMk₁ 1)) (SimplexCategory.toTop.map (SimplexCategory.δ 0)
        (SimplexCategory.toTopInitialVertex ⦋0⦌))) = 1 := by
  rw [simplexMap_toSSetObjI_objMk₁_toTop_map _ (ε := 1) rfl,
    SSet.stdSimplex.toSSetObj_app_const_one, simplexMap_toSSetObj₀Equiv_symm_apply,
    TopCat.I.homeomorph_one]

section Action

variable (E : _root_.TopCat.{u}) (G : Type*) [Monoid G] [MulAction G E] [ContinuousConstSMul G E]

/-- The action of `G` on the singular simplices of a `G`-space `E` by translation, induced from
the functor `SingleObj G ⥤ Type u` they form: `g` pushes a simplex forward along `g • ·`
(`TauCeti.TopCat.toSSetObj_smul_def`). -/
noncomputable instance mulActionToSSetObj (n : SimplexCategoryᵒᵖ) :
    MulAction G ((_root_.TopCat.toSSet.obj E).obj n) :=
  inferInstanceAs (MulAction G
    (((E.actionFunctor G ⋙ _root_.TopCat.toSSet) ⋙ (evaluation _ _).obj n).obj
      (SingleObj.star G)))

variable {E G}

/-- An element `g` acts on a singular simplex by pushing it forward along `g • ·`. -/
lemma toSSetObj_smul_def {n : SimplexCategoryᵒᵖ} (g : G) (σ : (_root_.TopCat.toSSet.obj E).obj n) :
    g • σ = (_root_.TopCat.toSSet.map
      (_root_.TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩)).app n σ :=
  (rfl)

end Action

section Free

variable {E : _root_.TopCat.{u}} {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]

/-- **A free action on a space is free on its singular simplices**: two translates of a simplex
that agree also agree at one point of the topological simplex. -/
instance isCancelSMul_toSSetObj [IsCancelSMul G E] (n : SimplexCategoryᵒᵖ) :
    IsCancelSMul G ((_root_.TopCat.toSSet.obj E).obj n) where
  right_cancel' g h σ hσ := by
    have hx := congr(simplexMap $hσ (SimplexCategory.toTopInitialVertex n.unop))
    simp only [toSSetObj_smul_def, simplexMap_app] at hx
    exact IsCancelSMul.right_cancel g h _ hx

end Free

end TauCeti.TopCat

namespace TauCeti

/-- The topological `n`-simplex, the model of the simplicial singular chains in degree `n`. -/
noncomputable abbrev simplexModel (n : ℕ) : TopCat.{u} := SimplexCategory.toTop.{u}.obj ⦋n⦌

/-- The identity singular simplex of the topological simplex. -/
noncomputable def idSimplex (n : ℕ) : (TopCat.toSSet.obj (simplexModel.{u} n)) _⦋n⦌ :=
  ULift.up (𝟙 _)

/-- A singular simplex, as a map from the model simplex.  The type of the underlying map of a
singular simplex is only propositionally the type of maps out of `simplexModel n`; this
declaration fixes the type for use in instance and rewrite problems. -/
abbrev simplexToHom {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexModel.{u} n ⟶ X := σ.down

/-- The identity simplex of the topological simplex is the identity map. -/
@[simp]
theorem simplexMap_idSimplex (n : ℕ) (x : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    TopCat.simplexMap (idSimplex.{u} n) x = x :=
  (rfl)

/-- A singular simplex is the push-forward of the identity simplex along itself. -/
theorem toSSet_map_down_idSimplex {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map σ.down).app _ (idSimplex n) = σ := by
  apply TopCat.simplexMap_injective
  rw [TopCat.simplexMap_app]
  rfl

end TauCeti
