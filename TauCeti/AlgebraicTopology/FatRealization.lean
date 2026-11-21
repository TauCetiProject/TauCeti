/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Category.TopCat.FunctorTensor

import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# The fat realization of a semi-simplicial space

A semi-simplicial space is a functor `X : SemiSimplexCategoryᵒᵖ ⥤ TopCat`: a space `Xₙ` for each
`n` with face maps along the order embeddings `⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, but no degeneracies. Its fat
realization `‖X‖` (`TauCeti.fatRealization X`) is the functor tensor product
`TauCeti.functorTensor SemiSimplexCategory.toTop X`: the quotient of the disjoint union
`Σ n, Xₙ × Δⁿ` by the identifications `(X(f) x, t) ∼ (x, f_* t)` for every order embedding
`f : ⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, where `f_*` is the induced face inclusion of topological simplices
(`SemiSimplexCategory.toTop`).

Characteristic maps (`TauCeti.fatRealization.ι`), universal property (`TauCeti.fatRealization.desc`,
`TauCeti.fatRealization.lift`, `TauCeti.fatRealization.hom_ext`), functoriality
(`TauCeti.fatRealizationFunctor`, `TauCeti.fatRealization.map`), augmentations
(`TauCeti.fatRealization.augment`), homotopies (`TauCeti.fatRealization.homotopy`), and
open/closed restrictions for saturated subfunctors (`TauCeti.fatRealization.isOpenEmbedding_map`,
`TauCeti.fatRealization.isClosedEmbedding_map`) are inherited directly from
`TauCeti.Topology.Category.TopCat.FunctorTensor`.

For the topological simplices `SemiSimplexCategory.toTop.obj n`, the file also provides the
barycentric coordinates (`SemiSimplexCategory.toTopWeights`), the boundary `∂Δⁿ`
(`SemiSimplexCategory.toTopBoundary`) and carrier faces: every point of `Δⁿ` is the image under a
unique face inclusion of a point off the boundary of that face
(`SemiSimplexCategory.exists_toTop_map_eq`, `SemiSimplexCategory.eq_and_eq_of_toTop_map_eq`).

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

/-- Every topological simplex of `SemiSimplexCategory` is nonempty. -/
instance nonempty_toTop_obj (n : SemiSimplexCategory) : Nonempty (toTop.{u}.obj n) :=
  inferInstanceAs (Nonempty (SimplexCategory.toTop.{u}.obj (toSimplexCategory.obj n)))

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
  have he : ((toTopWeights t).support : Set (Fin (n.len + 1))) ⊆ range e := by
    simp [e, Finset.range_orderEmbOfFin]
  refine ⟨⦋k⦌ₛ, homEquiv.symm e, ⟨StdSimplex.comap e.injective t.down he⟩, ?_,
    ULift.ext ((toTop_map_down _ _).trans (StdSimplex.map_comap e.injective t.down he))⟩
  rintro ⟨i, hi⟩
  exact Finsupp.mem_support_iff.1 ((toTopWeights t).support.orderEmbOfFin_mem hk i)
    ((StdSimplex.weights_comap_apply e.injective t.down he i).symm.trans hi)

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

/-- The fat realization `‖X‖` of a semi-simplicial space `X`: the functor tensor product of
`SemiSimplexCategory.toTop` and `X`. -/
abbrev fatRealization (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) : TopCat.{u} :=
  functorTensor toTop X

/-- The fat realization as a functor from semi-simplicial spaces to spaces. -/
abbrev fatRealizationFunctor : (SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} :=
  functorTensorFunctor toTop

namespace fatRealization

section Basic

variable (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u})

/-- The characteristic map `Xₙ × Δⁿ → ‖X‖` of level `n` of the fat realization. -/
abbrev ι (n : SemiSimplexCategory) : C(X.obj (op n) × toTop.{u}.obj n, fatRealization X) :=
  functorTensor.ι toTop X n

/-- The characteristic maps are compatible with the face identifications. -/
theorem ι_map {m n : SemiSimplexCategory} (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  functorTensor.ι_map toTop X f x t

/-- Every point of the fat realization lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : fatRealization X) : ∃ n x t, ι X n (x, t) = p :=
  functorTensor.ι_jointly_surjective toTop X p

/-- The fat realization carries the quotient topology of `Σ n, Xₙ × Δⁿ`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : SemiSimplexCategory, X.obj (op n) × toTop.{u}.obj n ↦
      ι X p.fst p.snd :=
  functorTensor.isQuotientMap_sigma toTop X

/-- A set in the fat realization is open exactly when its preimage under every characteristic map
is open. -/
theorem isOpen_iff {s : Set (fatRealization X)} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) :=
  functorTensor.isOpen_iff

/-- A set in the fat realization is closed exactly when its preimage under every characteristic
map is closed. -/
theorem isClosed_iff {s : Set (fatRealization X)} : IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) :=
  functorTensor.isClosed_iff

/-- A map out of the fat realization is continuous exactly when its composite with every
characteristic map is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : fatRealization X → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) :=
  functorTensor.continuous_iff

/-- Two continuous maps out of the fat realization agree as soon as they agree on the image of
every characteristic map. -/
theorem hom_ext {Z : TopCat} {g h : fatRealization X ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h :=
  functorTensor.hom_ext H

end Basic

section Lift

variable {X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} {Z : Sort*}
  (g : ∀ n, X.obj (op n) × toTop.{u}.obj n → Z)
  (hg : ∀ ⦃m n : SemiSimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the underlying set of the fat realization: functions on the sets
`Xₙ × Δⁿ` compatible with the face identifications descend to a function on `‖X‖`. -/
abbrev lift : fatRealization X → Z :=
  functorTensor.lift g hg

theorem lift_ι (n : SemiSimplexCategory) (p : X.obj (op n) × toTop.{u}.obj n) :
    lift g hg (ι X n p) = g n p :=
  functorTensor.lift_ι g hg n p

end Lift

section Desc

variable {X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} {Z : Type*} [TopologicalSpace Z]
  (g : ∀ n, C(X.obj (op n) × toTop.{u}.obj n, Z))
  (hg : ∀ ⦃m n : SemiSimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the fat realization: continuous maps `Xₙ × Δⁿ → Z` compatible with
the face identifications descend to a continuous map `‖X‖ → Z`. -/
abbrev desc : C(fatRealization X, Z) :=
  functorTensor.desc g hg

theorem desc_ι (n : SemiSimplexCategory) (p : X.obj (op n) × toTop.{u}.obj n) :
    desc g hg (ι X n p) = g n p :=
  functorTensor.desc_ι g hg n p

end Desc

section Map

variable {X Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}}

/-- The map of fat realizations induced by a map of semi-simplicial spaces. -/
abbrev map (φ : X ⟶ Y) : fatRealization X ⟶ fatRealization Y :=
  functorTensor.map toTop φ

theorem map_ι (φ : X ⟶ Y) (n : SemiSimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op n) x, t) :=
  functorTensor.map_ι toTop φ n x t

theorem map_id : map (𝟙 X) = 𝟙 (fatRealization X) :=
  functorTensor.map_id toTop X

theorem map_comp {W : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ :=
  functorTensor.map_comp toTop φ ψ

end Map

section Augment

variable {X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} {Z : TopCat.{u}}

/-- The map `‖X‖ ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
abbrev augment (ε : X ⟶ (Functor.const _).obj Z) : fatRealization X ⟶ Z :=
  functorTensor.augment toTop ε

theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : SemiSimplexCategory) (x : X.obj (op n))
    (t : toTop.{u}.obj n) : augment ε (ι X n (x, t)) = ε.app (op n) x :=
  functorTensor.augment_ι toTop ε n x t

/-- If an augmentation is a quotient map in one degree, its realization is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (n : SemiSimplexCategory)
    (hε : IsQuotientMap (ε.app (op n))) : IsQuotientMap (augment ε) :=
  functorTensor.isQuotientMap_augment ε n hε

/-- The augmentation of `‖X‖` induced by `ε` restricts along `‖φ‖` to the augmentation of `‖Y‖`
induced by `φ ≫ ε`. -/
@[reassoc]
theorem map_comp_augment {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) :=
  functorTensor.map_comp_augment toTop φ ε

end Augment

section Homotopy

variable {X Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}}

/-- A family `φ s : X ⟶ Y` of maps of semi-simplicial spaces, indexed by `s ∈ [0, 1]` and
continuous jointly in `s` and the point in each level, induces the homotopy
`(s, [x, t]) ↦ [φ s x, t]` from `‖φ 0‖` to `‖φ 1‖`. -/
abbrev homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SemiSimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.fst).app (op n) p.snd) :
    ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom :=
  functorTensor.homotopy toTop φ hφ

theorem homotopy_apply_ι (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SemiSimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.fst).app (op n) p.snd)
    (s : unitInterval) (n : SemiSimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op n) x, t) :=
  functorTensor.homotopy_apply_ι toTop φ hφ s n x t

end Homotopy

section Restriction

variable {X Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)

/-- The points of `‖X‖` in the image of `‖φ‖` are those of the form `[φ y, t]`. -/
theorem range_map :
    range (map φ) = {p | ∃ n y t, ι X n (φ.app (op n) y, t) = p} :=
  functorTensor.range_map toTop φ

variable {φ}

/-- If `φ : Y ⟶ X` is levelwise injective and a simplex of `X` lies in the image of `φ` whenever
one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is injective. -/
theorem map_injective (hinj : ∀ n, Function.Injective (φ.app n))
    (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) : Function.Injective (map φ) :=
  functorTensor.map_injective hinj hsat

/-- **Open restriction.** If `φ : Y ⟶ X` is levelwise an open embedding and a simplex of `X` lies
in the image of `φ` whenever one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is an open embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) : IsOpenEmbedding (map φ) :=
  functorTensor.isOpenEmbedding_map hφ hsat

/-- **Closed restriction.** If `φ : Y ⟶ X` is levelwise a closed embedding and a simplex of `X`
lies in the image of `φ` whenever one of its faces does, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is a closed
embedding. -/
theorem isClosedEmbedding_map (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SemiSimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) : IsClosedEmbedding (map φ) :=
  functorTensor.isClosedEmbedding_map hφ hsat

variable {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) {V : Set Z}

/-- If the image of `φ` in every level is the preimage of `V` under an augmentation `ε`, then the
part of `‖X‖` lying over `V` is exactly the image of `‖Y‖`. -/
theorem preimage_augment_eq_range_map (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) :
    augment ε ⁻¹' V = range (map φ) :=
  functorTensor.preimage_augment_eq_range_map ε hrange

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `‖φ‖` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsOpenEmbedding (map φ) :=
  functorTensor.isOpenEmbedding_map_of_range_eq_preimage ε hφ hrange

/-- If `φ` is levelwise a closed embedding whose image is the preimage of `V` under an
augmentation `ε`, then `‖φ‖` is a closed embedding. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsClosedEmbedding (map φ) :=
  functorTensor.isClosedEmbedding_map_of_range_eq_preimage ε hφ hrange

end Restriction

end fatRealization

end TauCeti
