/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.AlgebraicTopology.TopologicalSimplex

import TauCeti.Data.Set.Function
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# The fat realization of a semi-simplicial space

A semi-simplicial space is a functor `X : SemiSimplexCategoryᵒᵖ ⥤ TopCat`: a space `Xₙ` for each
`n` with face maps along the order embeddings `⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, but no degeneracies. Its fat
realization `‖X‖` is the quotient of the disjoint union `Σ n, Xₙ × Δⁿ` by the identifications
`(X(f) x, t) ∼ (x, f_* t)` for every order embedding `f : ⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, where `f_*` is the induced
face inclusion of topological simplices (`SemiSimplexCategory.toTop`). This is a concrete model of
the coend of `Xₘ × Δⁿ` over the semi-simplex category: `TauCeti.fatRealization.desc` and
`TauCeti.fatRealization.hom_ext` are its universal property. A simplicial space has a fat
realization through `SemiSimplexCategory.toSimplexCategory`, which forgets its degeneracies; this
is the model of the classifying space of a topological groupoid built from the topological nerve.

This file constructs `TauCeti.fatRealization X` with its characteristic maps
`TauCeti.fatRealization.ι X n : C(Xₙ × Δⁿ, ‖X‖)`, its universal property
(`TauCeti.fatRealization.desc`, and `TauCeti.fatRealization.lift` for its underlying set), its
quotient topology (`TauCeti.fatRealization.isOpen_iff`, `TauCeti.fatRealization.continuous_iff`)
and its functoriality (`TauCeti.fatRealizationFunctor`). An augmentation `ε : X ⟶ const Z`
induces the map `TauCeti.fatRealization.augment ε : ‖X‖ ⟶ Z` sending `[x, t]` to `ε x`. A family
of maps `φ s : X ⟶ Y`, `s ∈ [0, 1]`, depending continuously on `s` in each level, induces a
homotopy `TauCeti.fatRealization.homotopy` from `‖φ 0‖` to `‖φ 1‖`: since `[0, 1]` is locally
compact, the product of `‖X‖` with `[0, 1]` is still a quotient of `Σ n, Xₙ × Δⁿ × [0, 1]`.

For the topological simplices `SemiSimplexCategory.toTop.obj n`, the file also provides the
barycentric coordinates (`SemiSimplexCategory.toTopWeights`), the boundary `∂Δⁿ`
(`SemiSimplexCategory.toTopBoundary`) and carrier faces: every point of `Δⁿ` is the image under a
unique face inclusion of a point off the boundary of that face
(`SemiSimplexCategory.exists_toTop_map_eq`, `SemiSimplexCategory.eq_and_eq_of_toTop_map_eq`).

The main results are the open and closed restriction theorems. If `φ : Y ⟶ X` is levelwise an
open (respectively closed) embedding and its image is closed under passing from a face back to the
simplex, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is an open (respectively closed) embedding
(`TauCeti.fatRealization.isOpenEmbedding_map`, `TauCeti.fatRealization.isClosedEmbedding_map`).
In particular, if the image of `φ` in each level is the preimage of a set `V ⊆ Z` under an
augmentation, then `‖Y‖` is homeomorphic, through `‖φ‖`, to the subspace of `‖X‖` lying over `V`
(`TauCeti.fatRealization.preimage_augment_eq_range_map`,
`TauCeti.fatRealization.isOpenEmbedding_map_of_range_eq_preimage` and
`TauCeti.fatRealization.isClosedEmbedding_map_of_range_eq_preimage`). For the nerve of a groupoid
augmented by the orbit map to its coarse space, this identifies the preimage of a saturated open
or closed set with the fat realization of the nerve of the restricted groupoid.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

universe u

namespace SemiSimplexCategory

/-- The functor sending `⦋n⦌ₛ` to the topological `n`-simplex and an order embedding to the
induced face inclusion of topological simplices. -/
@[expose] def toTop : SemiSimplexCategory ⥤ TopCat.{u} :=
  toSimplexCategory ⋙ SimplexCategory.toTop

/-- The topological simplex of `⦋n⦌ₛ` is that of `⦋n⦌`. -/
theorem toTop_obj (n : SemiSimplexCategory) :
    toTop.{u}.obj n = SimplexCategory.toTop.obj (toSimplexCategory.obj n) :=
  (rfl)

/-- The face inclusion along an order embedding is the map of topological simplices induced by
the underlying morphism of the simplex category. -/
theorem toTop_map {m n : SemiSimplexCategory} (f : m ⟶ n) :
    toTop.{u}.map f = SimplexCategory.toTop.map (toSimplexCategory.map f) :=
  (rfl)

section TopologicalSimplex

open Convexity

open scoped Finset

variable {m n : SemiSimplexCategory}

/-- Topological simplices are compact. -/
instance (n : SemiSimplexCategory) : CompactSpace (toTop.{u}.obj n) :=
  inferInstanceAs (CompactSpace (SimplexCategory.toTop.obj _))

/-- Topological simplices are Hausdorff. -/
instance (n : SemiSimplexCategory) : T2Space (toTop.{u}.obj n) :=
  inferInstanceAs (T2Space (SimplexCategory.toTop.obj _))

/-- There are finitely many face inclusions between two objects of the semi-simplex category. -/
instance : Finite (m ⟶ n) :=
  Finite.of_injective (fun f ↦ ⇑(homEquiv f)) fun _ _ h ↦ hom_ext (DFunLike.coe_injective h)

/-- A face inclusion of topological simplices pushes a point of the standard simplex forward
along the order embedding. -/
@[simp]
theorem toTop_map_down (f : m ⟶ n) (t : toTop.{u}.obj m) :
    (toTop.map f t).down = t.down.map (homEquiv f) :=
  -- `toTop` is `SimplexCategory.toTop`, the universe lift of `StdSimplex.map`.
  (rfl)

/-- The barycentric coordinates of a point of the topological simplex `Δⁿ`, indexed by its
`n + 1` vertices. -/
def toTopWeights (t : toTop.{u}.obj n) : Fin (n.len + 1) →₀ ℝ :=
  t.down.weights

/-- The barycentric coordinates of a point of `Δⁿ` are those of the underlying point of the
standard simplex. -/
theorem toTopWeights_def (t : toTop.{u}.obj n) : toTopWeights t = t.down.weights :=
  (rfl)

/-- A point of a topological simplex is determined by its barycentric coordinates. -/
theorem toTopWeights_injective : Function.Injective (toTopWeights.{u} (n := n)) := fun _ _ h ↦
  ULift.ext (StdSimplex.ext h)

/-- Each barycentric coordinate is continuous on the topological simplex. -/
@[continuity, fun_prop]
theorem continuous_toTopWeights_apply (i : Fin (n.len + 1)) :
    Continuous fun t : toTop.{u}.obj n ↦ toTopWeights t i :=
  (StdSimplex.continuous_weights_apply ℝ i).comp continuous_uliftDown

/-- Some barycentric coordinate of a point of a topological simplex is nonzero. -/
theorem support_toTopWeights_nonempty (t : toTop.{u}.obj n) : (toTopWeights t).support.Nonempty :=
  t.down.support_weights_nonempty

/-- The barycentric coordinates of the image of a point under a face inclusion are pushed forward
along the order embedding. -/
@[simp]
theorem toTopWeights_toTop_map (f : m ⟶ n) (t : toTop.{u}.obj m) :
    toTopWeights (toTop.map f t) = (toTopWeights t).mapDomain (homEquiv f) :=
  (congrArg StdSimplex.weights (toTop_map_down f t)).trans (StdSimplex.weights_map _ _)

/-- The boundary `∂Δⁿ` of the topological simplex `Δⁿ`: the points with a vanishing barycentric
coordinate, that is, the union of the proper faces of `Δⁿ`. -/
def toTopBoundary (n : SemiSimplexCategory) : Set (toTop.{u}.obj n) :=
  {t | ∃ i, toTopWeights t i = 0}

/-- A point lies on `∂Δⁿ` exactly when one of its barycentric coordinates vanishes. -/
theorem mem_toTopBoundary_iff {t : toTop.{u}.obj n} :
    t ∈ toTopBoundary n ↔ ∃ i, toTopWeights t i = 0 :=
  Iff.rfl

/-- The boundary of a topological simplex is closed. -/
theorem isClosed_toTopBoundary (n : SemiSimplexCategory) : IsClosed (toTopBoundary.{u} n) := by
  have : toTopBoundary.{u} n = ⋃ i, {t : toTop.{u}.obj n | toTopWeights t i = 0} := by
    ext; simp [toTopBoundary]
  rw [this]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_eq (continuous_toTopWeights_apply i)
    continuous_const

/-- A point of `Δⁿ` lies off the boundary exactly when all `n + 1` of its barycentric coordinates
are nonzero. -/
theorem notMem_toTopBoundary_iff {t : toTop.{u}.obj n} :
    t ∉ toTopBoundary n ↔ #(toTopWeights t).support = n.len + 1 := by
  have := Finset.card_eq_iff_eq_univ (toTopWeights t).support
  rw [Fintype.card_fin] at this
  rw [this, Finset.eq_univ_iff_forall]
  simp [toTopBoundary]

/-- A point of `Δⁿ` has at most `n + 1` nonzero barycentric coordinates. -/
theorem card_support_toTopWeights_le (t : toTop.{u}.obj n) :
    #(toTopWeights t).support ≤ n.len + 1 :=
  (Finset.card_le_univ _).trans (by simp)

/-- A point of `Δⁿ` lies on the boundary exactly when fewer than `n + 1` of its barycentric
coordinates are nonzero. -/
theorem mem_toTopBoundary_iff_card_lt {t : toTop.{u}.obj n} :
    t ∈ toTopBoundary n ↔ #(toTopWeights t).support < n.len + 1 := by
  rw [← not_iff_not, notMem_toTopBoundary_iff, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ (card_support_toTopWeights_le t).antisymm h⟩

/-- A face inclusion preserves the number of nonzero barycentric coordinates. -/
theorem card_support_toTopWeights_toTop_map (f : m ⟶ n) (t : toTop.{u}.obj m) :
    #(toTopWeights (toTop.map f t)).support = #(toTopWeights t).support := by
  classical
  rw [toTopWeights_toTop_map, Finsupp.mapDomain_support_of_injective (homEquiv f).injective,
    Finset.card_image_of_injective _ (homEquiv f).injective]

/-- Face inclusions of topological simplices are injective. -/
theorem toTop_map_injective (f : m ⟶ n) : Function.Injective (toTop.{u}.map f) := fun _ _ h ↦
  ULift.ext <| StdSimplex.map_injective (homEquiv f).injective <|
    (toTop_map_down f _).symm.trans ((congrArg ULift.down h).trans (toTop_map_down f _))

/-- Face inclusions of topological simplices are closed embeddings. -/
theorem isClosedEmbedding_toTop_map (f : m ⟶ n) : IsClosedEmbedding (toTop.{u}.map f) :=
  (toTop.map f).hom.continuous.isClosedEmbedding (toTop_map_injective f)

open scoped Simplicial in
/-- **Carrier faces.** Every point of a topological simplex is the image, under a face inclusion,
of a point off the boundary of that face: the face spanned by its nonzero barycentric
coordinates. -/
theorem exists_toTop_map_eq (t : toTop.{u}.obj n) :
    ∃ (a : SemiSimplexCategory) (f : a ⟶ n) (s : toTop.{u}.obj a),
      s ∉ toTopBoundary a ∧ toTop.map f s = t := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, #(toTopWeights t).support = k + 1 :=
    Nat.exists_eq_add_one.2 (Finset.card_pos.2 (support_toTopWeights_nonempty t))
  set e := (toTopWeights t).support.orderEmbOfFin hk
  have he : Set.BijOn e (e ⁻¹' ↑(toTopWeights t).support) ↑(toTopWeights t).support :=
    Set.bijOn_preimage_iff.2 ⟨e.injective.injOn, (Finset.range_orderEmbOfFin _ hk).superset⟩
  refine ⟨⦋k⦌ₛ, homEquiv.symm e, ⟨StdSimplex.comap t.down he⟩, ?_,
    ULift.ext ((toTop_map_down _ _).trans (StdSimplex.map_comap t.down he))⟩
  rintro ⟨i, hi⟩
  exact Finsupp.mem_support_iff.1 ((toTopWeights t).support.orderEmbOfFin_mem hk i)
    ((StdSimplex.weights_comap_apply t.down he i).symm.trans hi)

/-- **Uniqueness of carrier faces, dimension.** If a point of `Δⁿ` is the image of points off the
boundaries of two faces, the two faces have the same dimension. -/
theorem eq_of_toTop_map_eq {a b : SemiSimplexCategory} {f : a ⟶ n} {g : b ⟶ n}
    {s : toTop.{u}.obj a} {s' : toTop.{u}.obj b} (hs : s ∉ toTopBoundary a)
    (hs' : s' ∉ toTopBoundary b) (h : toTop.map f s = toTop.map g s') : a = b := by
  have := card_support_toTopWeights_toTop_map f s
  rw [h, card_support_toTopWeights_toTop_map, notMem_toTopBoundary_iff.1 hs,
    notMem_toTopBoundary_iff.1 hs'] at this
  exact SemiSimplexCategory.ext (by omega)

/-- **Uniqueness of carrier faces.** If a point of `Δⁿ` is the image of points off the boundary of
`Δᵐ` under two face inclusions, the face inclusions and the points coincide. -/
theorem eq_and_eq_of_toTop_map_eq {f g : m ⟶ n} {s s' : toTop.{u}.obj m}
    (hs : s ∉ toTopBoundary m) (hs' : s' ∉ toTopBoundary m) (h : toTop.map f s = toTop.map g s') :
    f = g ∧ s = s' := by
  classical
  have hrange (f : m ⟶ n) (s : toTop.{u}.obj m) (hs : s ∉ toTopBoundary m) :
      range (homEquiv f) = ((toTopWeights (toTop.map f s)).support : Set _) := by
    simp [Finsupp.mapDomain_support_of_injective (homEquiv f).injective,
      (Finset.card_eq_iff_eq_univ _).1
        ((notMem_toTopBoundary_iff.1 hs).trans (Fintype.card_fin _).symm)]
  obtain rfl : f = g := hom_ext <| OrderEmbedding.range_inj_of_wellFoundedLT.1 <| by
    rw [hrange f s hs, hrange g s' hs', h]
  exact ⟨rfl, toTop_map_injective f h⟩

end TopologicalSimplex

end SemiSimplexCategory

namespace TauCeti

open SemiSimplexCategory (toTop)

variable (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u})

/-- The face identifications `(X(f) x, t) ∼ (x, f_* t)` on `Σ n, Xₙ × Δⁿ`. -/
private inductive FatRealizationRel :
    (Σ n : SemiSimplexCategory, X.obj (op n) × toTop.{u}.obj n) →
      (Σ n : SemiSimplexCategory, X.obj (op n) × toTop.{u}.obj n) → Prop
  | mk {m n : SemiSimplexCategory} (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m) :
      FatRealizationRel ⟨m, X.map f.op x, t⟩ ⟨n, x, toTop.map f t⟩

/-- The fat realization `‖X‖` of a semi-simplicial space `X`: the quotient of `Σ n, Xₙ × Δⁿ` by
the identifications `(X(f) x, t) ∼ (x, f_* t)` along the face maps, with the quotient topology. -/
def fatRealization : TopCat.{u} :=
  TopCat.of (Quot (FatRealizationRel X))

namespace fatRealization

/-- The characteristic map `Xₙ × Δⁿ → ‖X‖` of level `n` of the fat realization. -/
def ι (n : SemiSimplexCategory) : C(X.obj (op n) × toTop.{u}.obj n, fatRealization X) :=
  ⟨fun p ↦ Quot.mk (FatRealizationRel X) ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The characteristic maps are compatible with the face identifications. -/
@[simp]
theorem ι_map {m n : SemiSimplexCategory} (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  Quot.sound (FatRealizationRel.mk f x t)

/-- Every point of the fat realization lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : fatRealization X) : ∃ n x t, ι X n (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The fat realization carries the quotient topology of `Σ n, Xₙ × Δⁿ`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : SemiSimplexCategory, X.obj (op n) × toTop.{u}.obj n ↦
      ι X p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A set in the fat realization is open exactly when its preimage under every characteristic map
is open. -/
theorem isOpen_iff {s : Set (fatRealization X)} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A set in the fat realization is closed exactly when its preimage under every characteristic
map is closed. -/
theorem isClosed_iff {s : Set (fatRealization X)} :
    IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of the fat realization is continuous exactly when its composite with every
characteristic map is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : fatRealization X → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) := by
  rw [(isQuotientMap_sigma X).continuous_iff, continuous_sigma_iff]
  rfl

/-- Two continuous maps out of the fat realization agree as soon as they agree on the image of
every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat} {g h : fatRealization X ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h := by
  ext p
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  exact H n x t

section Lift

variable {X} {Z : Sort*} (g : ∀ n, X.obj (op n) × toTop.{u}.obj n → Z)
  (hg : ∀ ⦃m n : SemiSimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the underlying set of the fat realization: functions on the sets
`Xₙ × Δⁿ` compatible with the face identifications descend to a function on `‖X‖`. -/
def lift : fatRealization X → Z :=
  Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)

@[simp]
theorem lift_ι (n : SemiSimplexCategory) (p : X.obj (op n) × toTop.{u}.obj n) :
    lift g hg (ι X n p) = g n p :=
  (rfl)

end Lift

section Desc

variable {X} {Z : Type*} [TopologicalSpace Z] (g : ∀ n, C(X.obj (op n) × toTop.{u}.obj n, Z))
  (hg : ∀ ⦃m n : SemiSimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the fat realization: continuous maps `Xₙ × Δⁿ → Z` compatible with
the face identifications descend to a continuous map `‖X‖ → Z`. -/
def desc : C(fatRealization X, Z) where
  toFun := lift (fun n ↦ g n) hg
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n ↦ (g n).continuous)

@[simp]
theorem desc_ι (n : SemiSimplexCategory) (p : X.obj (op n) × toTop.{u}.obj n) :
    desc g hg (ι X n p) = g n p :=
  (rfl)

end Desc

section Map

variable {X} {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}}

/-- The map of fat realizations induced by a map of semi-simplicial spaces. -/
def map (φ : X ⟶ Y) : fatRealization X ⟶ fatRealization Y :=
  TopCat.ofHom <|
    desc (Z := fatRealization Y) (fun n ↦ (ι Y n).comp ((φ.app (op n)).hom.prodMap (.id _))) <| by
    intro m n f x t
    simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (n : SemiSimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op n) x, t) :=
  (rfl)

@[simp]
theorem map_id : map (𝟙 X) = 𝟙 (fatRealization X) := by
  ext; simp

@[simp]
theorem map_comp {W : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ := by
  ext; simp

end Map

end fatRealization

/-- The fat realization as a functor from semi-simplicial spaces to spaces. -/
@[expose, simps]
def fatRealizationFunctor : (SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj := fatRealization
  map := fatRealization.map

namespace fatRealization

section Augment

variable {X} {Z : TopCat.{u}}

/-- The map `‖X‖ ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : fatRealization X ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun n ↦ (ε.app (op n)).hom.comp ContinuousMap.fst) <| by
    intro m n f x t
    simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : SemiSimplexCategory) (x : X.obj (op n))
    (t : toTop.{u}.obj n) : augment ε (ι X n (x, t)) = ε.app (op n) x :=
  (rfl)

/-- If an augmentation is a quotient map in one degree, its realization is a quotient map.
No condition on the other degrees or the face maps is needed. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (n : SemiSimplexCategory)
    (hε : IsQuotientMap (ε.app (op n))) : IsQuotientMap (augment ε) := by
  obtain ⟨t⟩ : Nonempty (SimplexCategory.toTop.{u}.obj
    (SemiSimplexCategory.toSimplexCategory.obj n)) := inferInstance
  let j : X.obj (op n) → fatRealization X := fun x ↦ ι X n (x, t)
  have hj : Continuous j := (ι X n).continuous.comp (continuous_id.prodMk continuous_const)
  have heq : (augment ε) ∘ j = fun x ↦ ε.app (op n) x :=
    funext fun x ↦ augment_ι ε n x t
  exact IsQuotientMap.of_comp hj (augment ε).hom.continuous (heq.symm ▸ hε)

/-- The augmentation of `‖X‖` induced by `ε` restricts along `‖φ‖` to the augmentation of `‖Y‖`
induced by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by
  ext; simp

end Augment

section Homotopy

variable {X} {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}}

/-- A family `φ s : X ⟶ Y` of maps of semi-simplicial spaces, indexed by `s ∈ [0, 1]` and
continuous jointly in `s` and the point in each level, induces the homotopy
`(s, [x, t]) ↦ [φ s x, t]` from `‖φ 0‖` to `‖φ 1‖`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SemiSimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.1).app (op n) p.2) :
    ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom where
  toFun p := map (φ p.1) p.2
  continuous_toFun := (isQuotientMap_sigma X).continuous_lift_prod_right <| by
    -- `[0, 1]` is locally compact, so it suffices to check continuity on each `Xₙ × Δⁿ × [0, 1]`.
    have : Continuous fun q : Σ n : SemiSimplexCategory,
        (X.obj (op n) × toTop.{u}.obj n) × unitInterval ↦
          ι Y q.1 ((φ q.2.2).app (op q.1) q.2.1.1, q.2.1.2) :=
      continuous_sigma fun n ↦ (ι Y n).continuous.comp <|
        ((hφ n).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst)
    exact (this.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)).congr
      fun ⟨_, n, x, t⟩ ↦ (map_ι _ n x t).symm
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp]
theorem homotopy_apply_ι (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SemiSimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.1).app (op n) p.2)
    (s : unitInterval) (n : SemiSimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op n) x, t) :=
  (rfl)

end Homotopy

section Restriction

variable {X} {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)

/-- The points of `‖X‖` in the image of `‖φ‖` are those of the form `[φ y, t]`. -/
theorem range_map :
    range (map φ) = {p | ∃ n y t, ι X n (φ.app (op n) y, t) = p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    exact ⟨n, y, t, rfl⟩
  · rintro ⟨n, y, t, rfl⟩
    exact ⟨ι Y n (y, t), rfl⟩

/-- If a simplex of `X` lies in the image of `φ`, so does each of its faces. -/
private theorem map_mem_range {m n : SemiSimplexCategoryᵒᵖ} (f : m ⟶ n) {x : X.obj m}
    (hx : x ∈ range (φ.app m)) : X.map f x ∈ range (φ.app n) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Y.map f y, NatTrans.naturality_apply φ f y⟩

section PartialInv

variable {φ} (hinj : ∀ n, Function.Injective (φ.app n))
  (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
    X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m))

include hinj hsat

open scoped Classical in
/-- A partial inverse of `‖φ‖`, defined on the points `[φ y, t]`. -/
private def partialInv : fatRealization X → Option (fatRealization Y) :=
  Quot.lift
    (fun p ↦ if hx : p.2.1 ∈ range (φ.app (op p.1)) then some (ι Y p.1 (hx.choose, p.2.2))
      else none) <| by
    rintro _ _ ⟨f, x, t⟩
    dsimp only
    split_ifs with hx' hx hx
    · -- The chosen preimage of the face `X(f) x` is the face of the chosen preimage of `x`.
      have hchoose : hx'.choose = Y.map f.op hx.choose :=
        hinj _ (by rw [hx'.choose_spec, NatTrans.naturality_apply, hx.choose_spec])
      rw [hchoose, ι_map]
    · exact absurd (hsat f.op x hx') hx
    · exact absurd (map_mem_range φ f.op hx) hx'
    · rfl

open scoped Classical in
private theorem partialInv_ι (n : SemiSimplexCategory) (x : X.obj (op n))
    (t : toTop.{u}.obj n) :
    partialInv hinj hsat (ι X n (x, t)) =
      if hx : x ∈ range (φ.app (op n)) then some (ι Y n (hx.choose, t)) else none :=
  (rfl)

private theorem partialInv_map (q : fatRealization Y) :
    partialInv hinj hsat (map φ q) = some q := by
  obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
  rw [map_ι, partialInv_ι]
  split_ifs with hx
  · rw [hinj _ hx.choose_spec]
  · exact absurd ⟨y, rfl⟩ hx

private theorem exists_eq_of_partialInv_eq_some {n : SemiSimplexCategory} {x : X.obj (op n)}
    {t : toTop.{u}.obj n} {q : fatRealization Y}
    (h : partialInv hinj hsat (ι X n (x, t)) = some q) :
    ∃ y, φ.app (op n) y = x ∧ ι Y n (y, t) = q := by
  rw [partialInv_ι] at h
  split_ifs at h with hx
  exact ⟨hx.choose, hx.choose_spec, Option.some.inj h⟩

/-- If `φ : Y ⟶ X` is levelwise injective and a simplex of `X` lies in the image of `φ` whenever
one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is injective. -/
theorem map_injective : Function.Injective (map φ) := fun q q' h ↦ Option.some.inj <| by
  rw [← partialInv_map hinj hsat q, ← partialInv_map hinj hsat q', h]

/-- Under the same hypotheses, the preimage in level `n` of the image of `W ⊆ ‖Y‖` under `‖φ‖`
is the image under `φ × id` of the preimage of `W`. -/
private theorem preimage_ι_image_map (W : Set (fatRealization Y)) (n : SemiSimplexCategory) :
    ι X n ⁻¹' (map φ '' W) = Prod.map (φ.app (op n)) id '' (ι Y n ⁻¹' W) := by
  ext ⟨x, t⟩
  constructor
  · rintro ⟨q, hq, hqx⟩
    have h := partialInv_map hinj hsat q
    rw [hqx] at h
    obtain ⟨y, rfl, rfl⟩ := exists_eq_of_partialInv_eq_some hinj hsat h
    exact ⟨(y, t), hq, rfl⟩
  · rintro ⟨⟨y, t'⟩, hy, hyx⟩
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hyx
    obtain ⟨rfl, rfl⟩ := hyx
    exact ⟨ι Y n (y, t'), hy, rfl⟩

end PartialInv

variable {φ}

/-- **Open restriction.** If `φ : Y ⟶ X` is levelwise an open embedding and a simplex of `X` lies
in the image of `φ` whenever one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is an open embedding:
`‖Y‖` is an open subspace of `‖X‖`, with the quotient topology of its own fat realization. -/
theorem isOpenEmbedding_map (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) :
    IsOpenEmbedding (map φ) := by
  have hinj : ∀ n, Function.Injective (φ.app n) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isOpenMap (map φ).hom.continuous (map_injective hinj hsat)
    fun W hW ↦ ?_
  rw [isOpen_iff] at hW ⊢
  intro n
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op n)).prodMap .id).isOpenMap _ (hW n)

/-- **Closed restriction.** If `φ : Y ⟶ X` is levelwise a closed embedding and a simplex of `X`
lies in the image of `φ` whenever one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is a closed
embedding: `‖Y‖` is a closed subspace of `‖X‖`, with the quotient topology of its own fat
realization. -/
theorem isClosedEmbedding_map (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) :
    IsClosedEmbedding (map φ) := by
  have hinj : ∀ n, Function.Injective (φ.app n) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isClosedMap (map φ).hom.continuous (map_injective hinj hsat)
    fun W hW ↦ ?_
  rw [isClosed_iff] at hW ⊢
  intro n
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op n)).prodMap .id).isClosedMap _ (hW n)

variable {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) {V : Set Z}

/-- If the image of `φ` in every level is the preimage of `V` under an augmentation `ε`, then the
part of `‖X‖` lying over `V` is exactly the image of `‖Y‖`. -/
theorem preimage_augment_eq_range_map (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) :
    augment ε ⁻¹' V = range (map φ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
    obtain ⟨y, rfl⟩ : x ∈ range (φ.app (op n)) := by rwa [hrange]
    exact ⟨ι Y n (y, t), rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    rw [mem_preimage, ← ConcreteCategory.comp_apply, map_comp_augment, augment_ι]
    exact (hrange (op n)).subset ⟨y, rfl⟩

/-- If the image of `φ` in every level is the preimage of a set under an augmentation, then a
simplex lies in the image of `φ` whenever one of its faces does. -/
private theorem mem_range_of_map_mem_range (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V)
    ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m)
    (hx : X.map f x ∈ range (φ.app n)) : x ∈ range (φ.app m) := by
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `‖φ‖` is an open embedding; by `preimage_augment_eq_range_map` its image is the part of
`‖X‖` lying over `V`. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsOpenEmbedding (map φ) :=
  isOpenEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

/-- If `φ` is levelwise a closed embedding whose image is the preimage of `V` under an
augmentation `ε`, then `‖φ‖` is a closed embedding; by `preimage_augment_eq_range_map` its image
is the part of `‖X‖` lying over `V`. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsClosedEmbedding (map φ) :=
  isClosedEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

end Restriction

end fatRealization

end TauCeti
