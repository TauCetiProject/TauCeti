/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Category.TopCat.FunctorTensor

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
`TauCeti.fatRealization.hom_ext`), functoriality (`TauCeti.fatRealizationFunctor`,
`TauCeti.fatRealization.map`), augmentations (`TauCeti.fatRealization.augment`), homotopies
(`TauCeti.fatRealization.homotopy`), and open/closed restrictions for saturated subfunctors
(`TauCeti.fatRealization.isOpenEmbedding_map`, `TauCeti.fatRealization.isClosedEmbedding_map`) are
inherited directly from `TauCeti.Topology.Category.TopCat.FunctorTensor`.

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
