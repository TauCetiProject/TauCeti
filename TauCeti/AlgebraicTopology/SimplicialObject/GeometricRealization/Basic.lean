/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Topology.Compactness.Lindelof
import TauCeti.AlgebraicTopology.SimplexCategory.Basic

/-!
# Geometric realization of a simplicial space

For a simplicial space `X : SimplicialObject TopCat`, its thin *geometric realization*
`X.geometricRealization` (classically `|X|`) is the functor tensor product
`TauCeti.functorTensor SimplexCategory.toTop X`: the quotient of `Σ n : ℕ, X _⦋n⦌ × Δⁿ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` along morphisms `f : ⦋m⦌ ⟶ ⦋n⦌` in
`SimplexCategory`, with the quotient topology. Collapsing degeneracies yields the canonical
reindexing quotient comparison map `X.fatToGeometricRealization` from the fat realization of `X`.

This file specializes `TauCeti.functorTensor` to `SimplexCategory.toTop` with `ℕ`-indexed
characteristic maps (`geometricRealization.ι`), universal property (`geometricRealization.desc`),
functoriality (`geometricRealizationFunctor`), augmentations (`geometricRealization.augment`),
`[0, 1]`-homotopies (`geometricRealization.homotopy`), Lindelöf and compactly-generated instances,
and open restriction (`geometricRealization.isOpenEmbedding_map`,
`geometricRealization.isOpenEmbedding_map_of_range_eq_preimage`). Unconditional injectivity and
closed embeddings are proved via normal forms in
`TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, LNM **271**, Springer, 1972, §11.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial Topology

universe v u

namespace CategoryTheory.SimplicialObject

open SimplexCategory (toTop)

variable (X : SimplicialObject TopCat.{u})

/-- The thin geometric realization `|X|` of a simplicial space `X`: the functor tensor product
`TauCeti.functorTensor SimplexCategory.toTop X`. -/
abbrev geometricRealization : TopCat.{u} :=
  TauCeti.functorTensor toTop X

namespace geometricRealization

/-- The characteristic map `X _⦋n⦌ × Δⁿ → |X|` in degree `n`. -/
@[expose] def ι (n : ℕ) : C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, X.geometricRealization) :=
  TauCeti.functorTensor.ι toTop X ⦋n⦌

@[simp] theorem ι_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  TauCeti.functorTensor.ι_map toTop X f x t

theorem ι_jointly_surjective (p : X.geometricRealization) : ∃ n x t, ι X n (x, t) = p := by
  obtain ⟨⟨n⟩, x, t, rfl⟩ := TauCeti.functorTensor.ι_jointly_surjective toTop X p
  exact ⟨n, x, t, rfl⟩

theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2 :=
  have he : (fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2) ∘
      (fun q : Σ d : SimplexCategory, X.obj (op d) × toTop.{u}.obj d ↦ ⟨q.1.len, q.2⟩) =
      fun q ↦ TauCeti.functorTensor.ι toTop X q.1 q.2 :=
    funext fun ⟨⟨_⟩, _⟩ ↦ rfl
  IsQuotientMap.of_comp
    (continuous_sigma fun d ↦
      continuous_sigmaMk (σ := fun n : ℕ ↦ X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) (i := d.len))
    (continuous_sigma fun n ↦ (ι X n).continuous)
    (he.symm ▸ TauCeti.functorTensor.isQuotientMap_sigma toTop X)

theorem isOpen_iff {s : Set X.geometricRealization} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) :=
  TauCeti.functorTensor.isOpen_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

theorem isClosed_iff {s : Set X.geometricRealization} : IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) :=
  TauCeti.functorTensor.isClosed_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : X.geometricRealization → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) :=
  TauCeti.functorTensor.continuous_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

@[ext] theorem hom_ext {Z : TopCat} {g h : X.geometricRealization ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h :=
  TauCeti.functorTensor.hom_ext fun ⟨n⟩ x t ↦ H n x t

instance [h : ∀ n : ℕ, LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    LindelofSpace X.geometricRealization :=
  @TauCeti.functorTensor.instLindelofSpace _ _ toTop X _ fun ⟨n⟩ ↦ h n

/-- If every level `X _⦋n⦌` is Lindelöf, then `X.geometricRealization` is Lindelöf. -/
instance (priority := 90) instLindelofSpace_of_levels [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    LindelofSpace X.geometricRealization :=
  have (n : ℕ) : LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :=
    have := hX n
    inferInstance
  inferInstance

instance [h : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} X.geometricRealization :=
  @TauCeti.functorTensor.instUCompactlyGeneratedSpace _ _ toTop X fun ⟨n⟩ ↦ h n

section Desc

variable {X}

section DescFun

variable {Z : Type*} (g : ∀ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ → Z)
  (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- Set-level universal property of the geometric realization. -/
def descFun : X.geometricRealization → Z :=
  TauCeti.functorTensor.lift (fun d ↦ g d.len) fun _ _ f x t ↦ hg f x t

@[simp] theorem descFun_ι (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :
    descFun g hg (ι X n p) = g n p :=
  TauCeti.functorTensor.lift_ι _ _ ⦋n⦌ p

end DescFun

variable {Z : Type*} [TopologicalSpace Z] (g : ∀ n : ℕ, C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, Z))
  (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- Universal property of the geometric realization: continuous maps `X _⦋n⦌ × Δⁿ → Z` compatible
with all simplicial operators descend to a continuous map `|X| → Z`. -/
def desc : C(X.geometricRealization, Z) :=
  TauCeti.functorTensor.desc (fun d ↦ g d.len) fun _ _ f x t ↦ hg f x t

@[simp] theorem desc_ι (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :
    desc g hg (ι X n p) = g n p :=
  TauCeti.functorTensor.desc_ι _ _ ⦋n⦌ p

end Desc

section Map

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The map of geometric realizations induced by a morphism of simplicial spaces. -/
def map (φ : X ⟶ Y) : X.geometricRealization ⟶ Y.geometricRealization :=
  TauCeti.functorTensor.map toTop φ

@[simp] theorem map_ι (φ : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op ⦋n⦌) x, t) :=
  TauCeti.functorTensor.map_ι toTop φ ⦋n⦌ x t

@[simp] theorem map_id : map (𝟙 X) = 𝟙 X.geometricRealization :=
  TauCeti.functorTensor.map_id toTop X

@[simp] theorem map_comp {W : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ :=
  TauCeti.functorTensor.map_comp toTop φ ψ

end Map

end geometricRealization

/-- Geometric realization as a functor from simplicial spaces to topological spaces. -/
@[expose, simps] def geometricRealizationFunctor : SimplicialObject TopCat.{u} ⥤ TopCat.{u} where
  obj := geometricRealization
  map := geometricRealization.map

open SemiSimplexCategory (toSimplexCategory)

/-- The canonical quotient comparison map `‖X‖ ⟶ |X|` from the fat realization of the underlying
semi-simplicial space to the thin geometric realization, collapsing degenerate simplices. -/
def fatToGeometricRealization :
    TauCeti.fatRealization (toSimplexCategory.op ⋙ X) ⟶ X.geometricRealization :=
  TauCeti.functorTensor.reindex toSimplexCategory toTop X

@[simp↓] theorem fatToGeometricRealization_ι (m : SemiSimplexCategory)
    (x : (toSimplexCategory.op ⋙ X).obj (op m)) (t : SemiSimplexCategory.toTop.{u}.obj m) :
    X.fatToGeometricRealization (TauCeti.functorTensor.ι SemiSimplexCategory.toTop _ m (x, t)) =
      geometricRealization.ι X (toSimplexCategory.obj m).len (x, t) :=
  TauCeti.functorTensor.reindex_ι toSimplexCategory toTop X m x t

/-- The comparison map `‖X‖ ⟶ |X|` is a quotient map: `|X|` is a topological quotient of `‖X‖`. -/
theorem isQuotientMap_fatToGeometricRealization : IsQuotientMap X.fatToGeometricRealization :=
  TauCeti.functorTensor.isQuotientMap_reindex toSimplexCategory toTop X fun ⟨n⟩ ↦ ⟨.mk n, rfl⟩

/-- The comparison map `‖X‖ ⟶ |X|` is surjective. -/
theorem fatToGeometricRealization_surjective : Function.Surjective X.fatToGeometricRealization :=
  (isQuotientMap_fatToGeometricRealization X).surjective

/-- The comparison map `‖X‖ ⟶ |X|` is natural in the simplicial space `X`. -/
@[reassoc (attr := simp)] theorem fatRealization_map_comp_fatToGeometricRealization
    {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    TauCeti.functorTensor.map SemiSimplexCategory.toTop
        (Functor.whiskerLeft toSimplexCategory.op φ) ≫
      Y.fatToGeometricRealization = X.fatToGeometricRealization ≫ geometricRealization.map φ :=
  TauCeti.functorTensor.map_comp_reindex toSimplexCategory toTop φ

namespace geometricRealization

section Augment

variable {X} {Z : TopCat.{u}}

/-- The map `|X| ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : X.geometricRealization ⟶ Z :=
  TauCeti.functorTensor.augment toTop ε

@[simp] theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : ℕ) (x : X _⦋n⦌)
    (t : toTop.{u}.obj ⦋n⦌) : augment ε (ι X n (x, t)) = ε.app (op ⦋n⦌) x :=
  TauCeti.functorTensor.augment_ι toTop ε ⦋n⦌ x t

/-- If an augmentation is a quotient map in one degree, its thin realization is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) {n : ℕ}
    (hε : IsQuotientMap (ε.app (op ⦋n⦌))) : IsQuotientMap (augment ε) :=
  TauCeti.functorTensor.isQuotientMap_augment ε ⦋n⦌ hε

@[reassoc (attr := simp)] theorem map_comp_augment {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) :=
  TauCeti.functorTensor.map_comp_augment toTop φ ε

/-- The fat augmentation factors through the thin augmentation along `fatToGeometricRealization`. -/
@[reassoc (attr := simp)] theorem fatToGeometricRealization_comp_augment
    (ε : X ⟶ (Functor.const _).obj Z) :
    X.fatToGeometricRealization ≫ augment ε =
      TauCeti.functorTensor.augment SemiSimplexCategory.toTop
        (Functor.whiskerLeft toSimplexCategory.op ε) :=
  TauCeti.functorTensor.reindex_comp_augment toSimplexCategory toTop ε

end Augment

section Homotopy

variable {X} {Y : SimplicialObject TopCat.{u}} (φ : unitInterval → (X ⟶ Y))
  (hφ : ∀ n : ℕ, Continuous fun p : unitInterval × X _⦋n⦌ ↦ (φ p.1).app (op ⦋n⦌) p.2)

/-- A `[0, 1]`-family `φ s : X ⟶ Y` jointly continuous in `s` and the simplex in each degree
induces a homotopy `(s, [x, t]) ↦ [φ s x, t]` from `|φ 0|` to `|φ 1|`. -/
def homotopy : ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom :=
  TauCeti.functorTensor.homotopy toTop φ fun ⟨n⟩ ↦ hφ n

@[simp] theorem homotopy_apply_ι (s : unitInterval) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op ⦋n⦌) x, t) :=
  TauCeti.functorTensor.homotopy_apply_ι toTop φ _ s ⦋n⦌ x t

end Homotopy

section Restriction

variable {X} {Y : SimplicialObject TopCat.{u}} {φ : Y ⟶ X}

variable (φ) in
/-- The image of `|φ|` consists of the points of `|X|` of the form `[φ y, t]`. -/
theorem range_map : range (map φ) = {p | ∃ n y t, ι X n (φ.app (op ⦋n⦌) y, t) = p} :=
  (TauCeti.functorTensor.range_map toTop φ).trans <| Set.ext fun _ ↦
    ⟨fun ⟨⟨n⟩, y, t, h⟩ ↦ ⟨n, y, t, h⟩, fun ⟨n, y, t, h⟩ ↦ ⟨⦋n⦌, y, t, h⟩⟩

/-- **Open restriction for thin geometric realization.** If `φ : Y ⟶ X` is levelwise an open
embedding and backwards-closed along simplicial operators, then `|φ| : |Y| ⟶ |X|` is an open
embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌))) :
    IsOpenEmbedding (map φ) :=
  TauCeti.functorTensor.isOpenEmbedding_map (fun ⟨⟨n⟩⟩ ↦ hφ n) fun _ _ f x hx ↦
    hsat f.unop x hx

variable {Z : TopCat.{u}} {ε : X ⟶ (Functor.const _).obj Z} {V : Set Z}

/-- If the image of `φ` in every degree is the preimage of `V ⊆ Z` under an augmentation `ε`, then
the preimage of `V` in `|X|` is the image of `|Y|`. -/
theorem preimage_augment_eq_range_map
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    augment ε ⁻¹' V = range (map φ) :=
  TauCeti.functorTensor.preimage_augment_eq_range_map ε fun ⟨⟨n⟩⟩ ↦ hrange n

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `|φ|` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    IsOpenEmbedding (map φ) :=
  TauCeti.functorTensor.isOpenEmbedding_map_of_range_eq_preimage (ε := ε)
    (fun ⟨⟨n⟩⟩ ↦ hφ n) fun ⟨⟨n⟩⟩ ↦ hrange n

end Restriction

end geometricRealization

end CategoryTheory.SimplicialObject
