/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Compactness.Lindelof

/-!
# Thin geometric realization of simplicial spaces

Let `X : SimplicialObject TopCat.{u}` be a simplicial topological space. Its *thin geometric
realization* `TauCeti.thinRealization X` is the quotient of `Σ n : SimplexCategory, Xₙ × Δⁿ` by
the identifications `(X(f) x, t) ∼ (x, f_* t)` along **all** morphisms `f : m ⟶ n` of
`SimplexCategory`—both face and degeneracy operators—equipped with the quotient topology.

Unlike the fat realization `TauCeti.fatRealization` (which quotients only by injective operators of
`SemiSimplexCategory`), the thin realization collapses degenerate simplices along codegeneracies.
Forgetting degeneracies therefore induces a canonical surjective quotient map
`TauCeti.thinRealization.fatToThin` from the fat realization to the thin realization.

## Main definitions

* `TauCeti.thinRealization`: the thin geometric realization `|X|` of a simplicial space `X`.
* `TauCeti.thinRealization.ι`, `TauCeti.thinRealization.desc`: characteristic maps and universal
  property.
* `TauCeti.thinRealization.map`, `TauCeti.thinRealizationFunctor`: functoriality in `X`.
* `TauCeti.thinRealization.fatToThin`: the canonical quotient map from the fat realization of the
  underlying semi-simplicial space to the thin realization.
* `TauCeti.thinRealization.augment`: descent of an augmentation `X ⟶ const Z` to `|X| ⟶ Z`.
* `TauCeti.thinRealization.homotopy`: homotopy of maps of thin realizations induced by a levelwise
  jointly continuous `[0, 1]`-family of simplicial maps.

## Main results

* `TauCeti.thinRealization.isQuotientMap_sigma`, `TauCeti.thinRealization.isQuotientMap_fatToThin`,
  `TauCeti.thinRealization.isQuotientMap_augment`: quotient-topology characterizations.
* `TauCeti.thinRealization.isOpenEmbedding_map`, `TauCeti.thinRealization.isClosedEmbedding_map`,
  `TauCeti.thinRealization.preimage_augment_eq_range_map`,
  `TauCeti.thinRealization.isOpenEmbedding_map_of_range_eq_preimage`,
  `TauCeti.thinRealization.isClosedEmbedding_map_of_range_eq_preimage`: open and closed
  restrictions of thin realizations.
* `TauCeti.thinRealization.instLindelofSpace`,
  `TauCeti.thinRealization.instUCompactlyGeneratedSpace`: Lindelöfness and compact generation of
  the thin realization.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. (2) **65**
  (1957), 357–362.
* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology
open scoped Simplicial

universe v u

namespace TauCeti

open SimplexCategory (toTop)

variable (X : SimplicialObject TopCat.{u})

/-- The face and degeneracy identifications `(X(f) x, t) ∼ (x, f_* t)` on `Σ n, Xₙ × Δⁿ`. -/
private inductive ThinRealizationRel :
    (Σ n : SimplexCategory, X.obj (op n) × toTop.{u}.obj n) →
      (Σ n : SimplexCategory, X.obj (op n) × toTop.{u}.obj n) → Prop where
  | mk ⦃m n : SimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m) :
      ThinRealizationRel ⟨m, X.map f.op x, t⟩ ⟨n, x, toTop.map f t⟩

/-- The thin geometric realization `|X|` of a simplicial space `X`: the quotient of
`Σ n, Xₙ × Δⁿ` by `(X(f) x, t) ∼ (x, f_* t)` for all morphisms `f` in `SimplexCategory`, with the
quotient topology. -/
def thinRealization : TopCat.{u} :=
  TopCat.of (Quot (ThinRealizationRel X))

namespace thinRealization

/-- The characteristic map `Xₙ × Δⁿ → |X|` in degree `n` of the thin realization. -/
def ι (n : SimplexCategory) : C(X.obj (op n) × toTop.{u}.obj n, thinRealization X) :=
  ⟨fun p ↦ Quot.mk (ThinRealizationRel X) ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The characteristic maps coequalize all simplicial operators against topological simplex maps. -/
@[simp]
theorem ι_map {m n : SimplexCategory} (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  Quot.sound (ThinRealizationRel.mk f x t)

/-- Every point of the thin realization lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : thinRealization X) : ∃ n x t, ι X n (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The thin realization carries the quotient topology of `Σ n : SimplexCategory, Xₙ × Δⁿ`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : SimplexCategory, X.obj (op n) × toTop.{u}.obj n ↦
      ι X p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A set in the thin realization is open if and only if its preimage under every characteristic
map is open. -/
theorem isOpen_iff {s : Set (thinRealization X)} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A set in the thin realization is closed if and only if its preimage under every characteristic
map is closed. -/
theorem isClosed_iff {s : Set (thinRealization X)} :
    IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of the thin realization is continuous if and only if its composite with every
characteristic map is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : thinRealization X → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) := by
  rw [(isQuotientMap_sigma X).continuous_iff, continuous_sigma_iff]
  rfl

/-- Two morphisms out of the thin realization agree once they agree on every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat.{u}} {g h : thinRealization X ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h := by
  ext p
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  exact H n x t

/-- If every level of `X` is Lindelöf, then its thin realization is Lindelöf: each `Xₙ × Δⁿ` is
a product of a Lindelöf space with a compact simplex, and `SimplexCategory` is countable. -/
instance instLindelofSpace [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    LindelofSpace (thinRealization X) := by
  have hcell (n : SimplexCategory) : LindelofSpace (X.obj (op n) × toTop.{u}.obj n) := by
    have : LindelofSpace (X.obj (op ⦋n.len⦌)) := hX n.len
    infer_instance
  exact LindelofSpace.of_continuous_surjective (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).surjective

/-- If each cell space `Xₙ × Δⁿ` is compactly generated (for instance when each `Xₙ` is first
countable, or Hausdorff and weakly locally compact), then `thinRealization X` is compactly
generated. -/
instance instUCompactlyGeneratedSpace
    [hX : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} (thinRealization X) := by
  have hcell (n : SimplexCategory) :
      UCompactlyGeneratedSpace.{v} (X.obj (op n) × toTop.{u}.obj n) := hX n.len
  exact uCompactlyGeneratedSpace_of_coinduced (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).eq_coinduced

section Desc

variable {X} {Z : Type*} [TopologicalSpace Z] (g : ∀ n, C(X.obj (op n) × toTop.{u}.obj n, Z))
  (hg : ∀ ⦃m n : SimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the thin realization: continuous maps `Xₙ × Δⁿ → Z` compatible with
all simplicial operators descend to a continuous map `|X| → Z`. -/
def desc : C(thinRealization X, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n ↦ (g n).continuous)

@[simp]
theorem desc_ι (n : SimplexCategory) (p : X.obj (op n) × toTop.{u}.obj n) :
    desc g hg (ι X n p) = g n p :=
  (rfl)

end Desc

section Map

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The morphism of thin realizations induced by a morphism of simplicial spaces. -/
def map (φ : X ⟶ Y) : thinRealization X ⟶ thinRealization Y :=
  TopCat.ofHom <|
    desc (Z := thinRealization Y) (fun n ↦ (ι Y n).comp ((φ.app (op n)).hom.prodMap (.id _))) <| by
    intro m n f x t
    simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (n : SimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op n) x, t) :=
  (rfl)

@[simp]
theorem map_id : map (𝟙 X) = 𝟙 (thinRealization X) := by
  ext; simp

@[simp]
theorem map_comp {W : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ := by
  ext; simp

end Map

section FatToThin

/-- The canonical comparison map from the fat realization of the underlying semi-simplicial space
to the thin realization, collapsing codegeneracy identifications. -/
def fatToThin :
    fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) ⟶ thinRealization X :=
  TopCat.ofHom <| fatRealization.desc
    (fun n ↦ ι X (SemiSimplexCategory.toSimplexCategory.obj n))
    (fun _ _ f x t ↦ ι_map X (SemiSimplexCategory.toSimplexCategory.map f) x t)

@[simp↓]
theorem fatToThin_ι (n : SemiSimplexCategory)
    (x : X.obj (op (SemiSimplexCategory.toSimplexCategory.obj n)))
    (t : SemiSimplexCategory.toTop.{u}.obj n) :
    fatToThin X (fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X) n (x, t)) =
      ι X (SemiSimplexCategory.toSimplexCategory.obj n) (x, t) :=
  fatRealization.desc_ι (X := SemiSimplexCategory.toSimplexCategory.op ⋙ X) _ _ n (x, t)

/-- The comparison map from the fat realization to the thin realization is a quotient map. -/
theorem isQuotientMap_fatToThin : IsQuotientMap (fatToThin X) := by
  let s : (Σ n : SimplexCategory, X.obj (op n) × toTop.{u}.obj n) →
      fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) :=
    fun p ↦ fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X)
      (SemiSimplexCategory.mk p.1.len) p.2
  have hs : Continuous s := continuous_sigma fun n ↦
    (fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X)
      (SemiSimplexCategory.mk n.len)).continuous
  have heq : (fatToThin X) ∘ s = fun p ↦ ι X p.1 p.2 :=
    funext fun p ↦ fatToThin_ι X (SemiSimplexCategory.mk p.1.len) p.2.1 p.2.2
  exact IsQuotientMap.of_comp hs (fatToThin X).hom.continuous (heq.symm ▸ isQuotientMap_sigma X)

/-- The comparison map from the fat realization to the thin realization is surjective. -/
theorem fatToThin_surjective : Function.Surjective (fatToThin X) :=
  (isQuotientMap_fatToThin X).surjective

/-- `fatToThin` is natural in the simplicial space. -/
@[reassoc (attr := simp)]
theorem fatToThin_naturality {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    fatRealization.map (Functor.whiskerLeft _ φ) ≫ fatToThin Y = fatToThin X ≫ map φ := by
  apply fatRealization.hom_ext
  intro n x t
  simp only [CategoryTheory.comp_apply, fatRealization.map_ι, Functor.whiskerLeft_app,
    fatToThin_ι]
  rfl

end FatToThin

end thinRealization

/-- The thin geometric realization as a functor from simplicial spaces to spaces. -/
@[expose, simps]
def thinRealizationFunctor : SimplicialObject TopCat.{u} ⥤ TopCat.{u} where
  obj := thinRealization
  map := thinRealization.map

namespace thinRealization

section Augment

variable {X} {Z : TopCat.{u}}

/-- The morphism `|X| ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to
`ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : thinRealization X ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun n ↦ (ε.app (op n)).hom.comp ContinuousMap.fst) <| by
    intro m n f x t
    simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : SimplexCategory) (x : X.obj (op n))
    (t : toTop.{u}.obj n) : augment ε (ι X n (x, t)) = ε.app (op n) x :=
  (rfl)

/-- Pulling a thin augmentation back along `fatToThin` recovers the fat augmentation of the
underlying semi-simplicial space. -/
@[reassoc (attr := simp)]
theorem fatToThin_comp_augment (ε : X ⟶ (Functor.const _).obj Z) :
    fatToThin X ≫ augment ε =
      fatRealization.augment (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op ε) := by
  apply fatRealization.hom_ext
  intro n x t
  simp only [CategoryTheory.comp_apply, fatToThin_ι, fatRealization.augment_ι,
    Functor.whiskerLeft_app]
  rfl

/-- If an augmentation is a quotient map in one degree, its thin realization is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (n : SimplexCategory)
    (hε : IsQuotientMap (ε.app (op n))) : IsQuotientMap (augment ε) := by
  obtain ⟨t⟩ : Nonempty (toTop.{u}.obj n) := inferInstance
  let j : X.obj (op n) → thinRealization X := fun x ↦ ι X n (x, t)
  have hj : Continuous j := (ι X n).continuous.comp (continuous_id.prodMk continuous_const)
  have heq : (augment ε) ∘ j = fun x ↦ ε.app (op n) x :=
    funext fun x ↦ augment_ι ε n x t
  exact IsQuotientMap.of_comp hj (augment ε).hom.continuous (heq.symm ▸ hε)

/-- An augmentation restricts along `map φ` to the augmentation by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by
  ext; simp

end Augment

section Homotopy

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- A family `φ s : X ⟶ Y` of maps of simplicial spaces, indexed by `s ∈ [0, 1]` and jointly
continuous in `s` and the simplex in each degree, induces a homotopy `(s, [x, t]) ↦ [φ s x, t]`
from `map (φ 0)` to `map (φ 1)`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.1).app (op n) p.2) :
    ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom where
  toFun p := map (φ p.1) p.2
  continuous_toFun := (isQuotientMap_sigma X).continuous_lift_prod_right <| by
    have : Continuous fun q : Σ n : SimplexCategory,
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
    (hφ : ∀ n : SimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.1).app (op n) p.2)
    (s : unitInterval) (n : SimplexCategory) (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op n) x, t) :=
  (rfl)

end Homotopy

section Restriction

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The points of `|X|` in the image of `map φ` are those of the form `[φ y, t]`. -/
theorem range_map (φ : Y ⟶ X) :
    range (map φ) = {p | ∃ n y t, ι X n (φ.app (op n) y, t) = p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    exact ⟨n, y, t, rfl⟩
  · rintro ⟨n, y, t, rfl⟩
    exact ⟨ι Y n (y, t), rfl⟩

variable {φ : Y ⟶ X}

section Saturated

variable (hinj : ∀ n, Function.Injective (φ.app n))
  (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
    X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m))

include hinj hsat

/-- Under levelwise injectivity and saturation, membership in the image of `W ⊆ |Y|` lifts to a
well-defined predicate on `|X|` detected in each degree. -/
private def liftPred (W : Set (thinRealization Y)) : thinRealization X → Prop :=
  Quot.lift (fun p ↦ ∃ y, φ.app (op p.1) y = p.2.1 ∧ ι Y p.1 (y, p.2.2) ∈ W) <| by
    rintro _ _ ⟨f, x, t⟩
    dsimp only
    refine propext ⟨?_, ?_⟩
    · rintro ⟨y', hy', hW⟩
      obtain ⟨y, rfl⟩ := hsat f.op x ⟨y', hy'⟩
      have hyeq : y' = Y.map f.op y :=
        hinj _ (hy'.trans (NatTrans.naturality_apply φ f.op y).symm)
      exact ⟨y, rfl, by rwa [← ι_map, ← hyeq]⟩
    · rintro ⟨y, hy, hW⟩
      exact ⟨Y.map f.op y, (NatTrans.naturality_apply φ f.op y).trans (congrArg (X.map f.op) hy),
        by rwa [ι_map]⟩

private theorem liftPred_ι (W : Set (thinRealization Y)) (n : SimplexCategory)
    (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    liftPred hinj hsat W (ι X n (x, t)) ↔ ∃ y, φ.app (op n) y = x ∧ ι Y n (y, t) ∈ W :=
  Iff.rfl

private theorem liftPred_map_iff (W : Set (thinRealization Y)) (q : thinRealization Y) :
    liftPred hinj hsat W (map φ q) ↔ q ∈ W := by
  obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
  exact ⟨fun ⟨y', hy', hW⟩ ↦ hinj _ hy' ▸ hW, fun hW ↦ ⟨y, rfl, hW⟩⟩

private theorem map_injective_of_saturated : Function.Injective (map φ) := fun q q' h ↦
  ((liftPred_map_iff hinj hsat {q} q').1 (h ▸ (liftPred_map_iff hinj hsat {q} q).2 rfl)).symm

private theorem preimage_ι_image_map (W : Set (thinRealization Y)) (n : SimplexCategory) :
    ι X n ⁻¹' (map φ '' W) = Prod.map (φ.app (op n)) id '' (ι Y n ⁻¹' W) := by
  ext ⟨x, t⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨y, rfl, hyW⟩ :=
      (liftPred_ι hinj hsat W n x t).1 (hqx ▸ (liftPred_map_iff hinj hsat W q).2 hq)
    exact ⟨(y, t), hyW, rfl⟩
  · rintro ⟨⟨y, t'⟩, hyW, hyt⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyt
    exact ⟨ι Y n (y, t'), hyW, rfl⟩

end Saturated

/-- **Open restriction.** If `φ : Y ⟶ X` is levelwise an open embedding and saturated under
simplicial operators, then `map φ : |Y| ⟶ |X|` is an open embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) :
    IsOpenEmbedding (map φ) := by
  have hinj : ∀ n, Function.Injective (φ.app n) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isOpenMap (map φ).hom.continuous
    (map_injective_of_saturated hinj hsat) fun W hW ↦ (isOpen_iff X).2 fun n ↦ ?_
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op n)).prodMap .id).isOpenMap _ ((isOpen_iff Y).1 hW n)

/-- **Closed restriction.** If `φ : Y ⟶ X` is levelwise a closed embedding and saturated under
simplicial operators, then `map φ : |Y| ⟶ |X|` is a closed embedding. -/
theorem isClosedEmbedding_map (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
      X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m)) :
    IsClosedEmbedding (map φ) := by
  have hinj : ∀ n, Function.Injective (φ.app n) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isClosedMap (map φ).hom.continuous
    (map_injective_of_saturated hinj hsat) fun W hW ↦ (isClosed_iff X).2 fun n ↦ ?_
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op n)).prodMap .id).isClosedMap _ ((isClosed_iff Y).1 hW n)

variable (φ) {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) {V : Set Z}

/-- If the image of `φ` in every degree is the preimage of `V` under an augmentation `ε`, then the
preimage of `V` in `|X|` is the image of `|Y|`. -/
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

variable {φ}

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `map φ` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsOpenEmbedding (map φ) :=
  isOpenEmbedding_map hφ fun _ _ f x hx ↦ by
    rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
    rw [hrange]
    simpa using hx

/-- If `φ` is levelwise a closed embedding whose image is the preimage of `V` under an
augmentation `ε`, then `map φ` is a closed embedding. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsClosedEmbedding (map φ) :=
  isClosedEmbedding_map hφ fun _ _ f x hx ↦ by
    rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
    rw [hrange]
    simpa using hx

end Restriction

end thinRealization

end TauCeti
