/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Compactness.Lindelof
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# Geometric realization of a simplicial space

For a simplicial space `X : SimplicialObject TopCat`, its thin *geometric realization*
`X.geometricRealization` (classically written `|X|`) is the quotient of the disjoint union
`Σ n : ℕ, X _⦋n⦌ × Δⁿ` by all simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` along morphisms
`f : ⦋m⦌ ⟶ ⦋n⦌` in `SimplexCategory`, with the quotient topology. Unlike the fat realization
`TauCeti.fatRealization`, which quotients only along face inclusions in `SemiSimplexCategory`, the
thin realization collapses degenerate simplices as well, giving a canonical quotient comparison map
`X.fatToGeometricRealization` from the fat realization of the underlying semi-simplicial space.

This file constructs `X.geometricRealization` with its characteristic maps
`geometricRealization.ι X n`, universal property (`geometricRealization.desc`,
`geometricRealization.hom_ext`), quotient-topology characterizations
(`geometricRealization.isOpen_iff`, `geometricRealization.isClosed_iff`,
`geometricRealization.continuous_iff`), functoriality (`geometricRealization.map`,
`geometricRealizationFunctor`), augmentations (`geometricRealization.augment`), `[0, 1]`-homotopies
(`geometricRealization.homotopy`), and unconditional Lindelöf and compactly-generated instances.

It also establishes the open restriction theorem (`geometricRealization.isOpenEmbedding_map`): a
levelwise open embedding `φ : Y ⟶ X` whose image is backwards-closed along simplicial operators
induces an open embedding `|Y| ⟶ |X|`, and in particular identifies the preimage of an open subset
under an augmentation with the realization of the levelwise preimage
(`geometricRealization.preimage_augment_eq_range_map`,
`geometricRealization.isOpenEmbedding_map_of_range_eq_preimage`). Unconditional injectivity and
closed embeddings (`geometricRealization.map_injective`,
`geometricRealization.isClosedEmbedding_map`), which need no backwards-closure hypothesis, are
proved via normal forms in
`TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics **271**,
  Springer, 1972, §11.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial Topology

universe v u

namespace CategoryTheory.SimplicialObject

open SimplexCategory (toTop)

variable (X : SimplicialObject TopCat.{u})

/-- The simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` on `Σ n : ℕ, X _⦋n⦌ × Δⁿ` along all
morphisms `f : ⦋m⦌ ⟶ ⦋n⦌` in `SimplexCategory`. -/
private inductive GeometricRealizationRel :
    (Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) → (Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) → Prop where
  | mk {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
      GeometricRealizationRel ⟨m, X.map f.op x, t⟩ ⟨n, x, toTop.map f t⟩

/-- The thin geometric realization `|X|` of a simplicial space `X`: the quotient of
`Σ n : ℕ, X _⦋n⦌ × Δⁿ` by `(X(f) x, t) ∼ (x, f_* t)` along all morphisms `f : ⦋m⦌ ⟶ ⦋n⦌` in
`SimplexCategory`, equipped with the quotient topology. -/
def geometricRealization : TopCat.{u} :=
  TopCat.of (Quot (GeometricRealizationRel X))

namespace geometricRealization

/-- The characteristic map `X _⦋n⦌ × Δⁿ → |X|` in degree `n`. -/
def ι (n : ℕ) : C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, X.geometricRealization) :=
  ⟨fun p ↦ Quot.mk (GeometricRealizationRel X) ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The characteristic maps intertwine all simplicial operators on `X` with the induced maps of
topological simplices. -/
@[simp]
theorem ι_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  Quot.sound (GeometricRealizationRel.mk f x t)

/-- Every point of `|X|` lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : X.geometricRealization) : ∃ n x t, ι X n (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The geometric realization carries the quotient topology of `Σ n : ℕ, X _⦋n⦌ × Δⁿ`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A subset of `|X|` is open if and only if its preimage under every characteristic map is
open. -/
theorem isOpen_iff {s : Set X.geometricRealization} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A subset of `|X|` is closed if and only if its preimage under every characteristic map is
closed. -/
theorem isClosed_iff {s : Set X.geometricRealization} :
    IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of `|X|` is continuous if and only if its composite with every characteristic map is
continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : X.geometricRealization → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) := by
  rw [(isQuotientMap_sigma X).continuous_iff, continuous_sigma_iff]
  rfl

/-- Two morphisms out of `|X|` agree once they agree on every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat} {g h : X.geometricRealization ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h := by
  ext p
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  exact H n x t

instance [∀ n : ℕ, LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    LindelofSpace X.geometricRealization :=
  Quot.lindelofSpace

instance [∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} X.geometricRealization :=
  uCompactlyGeneratedSpace_of_coinduced continuous_quot_mk rfl

section Desc

/-- Set-level universal property of the geometric realization: functions `X _⦋n⦌ × Δⁿ → Z`
compatible with all simplicial operators descend to a function `|X| → Z`. -/
def descFun {X : SimplicialObject TopCat.{u}} {Z : Type*}
    (g : ∀ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ → Z)
    (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
      g m (X.map f.op x, t) = g n (x, toTop.map f t)) :
    X.geometricRealization → Z :=
  Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)

@[simp]
theorem descFun_ι {X : SimplicialObject TopCat.{u}} {Z : Type*}
    (g : ∀ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ → Z)
    (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
      g m (X.map f.op x, t) = g n (x, toTop.map f t))
    (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) : descFun g hg (ι X n p) = g n p :=
  (rfl)

variable {X} {Z : Type*} [TopologicalSpace Z] (g : ∀ n : ℕ, C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, Z))
  (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- Universal property of the geometric realization: continuous maps `X _⦋n⦌ × Δⁿ → Z` compatible
with all simplicial operators descend to a continuous map `|X| → Z`. -/
def desc : C(X.geometricRealization, Z) where
  toFun := descFun (fun n ↦ g n) hg
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n ↦ (g n).continuous)

@[simp]
theorem desc_ι (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) : desc g hg (ι X n p) = g n p :=
  (rfl)

end Desc

section Map

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The map of geometric realizations induced by a morphism of simplicial spaces. -/
def map (φ : X ⟶ Y) : X.geometricRealization ⟶ Y.geometricRealization :=
  TopCat.ofHom <| desc (Z := Y.geometricRealization)
    (fun n ↦ (ι Y n).comp ((φ.app (op ⦋n⦌)).hom.prodMap (.id _))) <| by
      intro m n f x t
      simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op ⦋n⦌) x, t) :=
  (rfl)

@[simp]
theorem map_id : map (𝟙 X) = 𝟙 X.geometricRealization := by
  ext; simp

@[simp]
theorem map_comp {W : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ := by
  ext; simp

end Map

end geometricRealization

/-- Geometric realization as a functor from simplicial spaces to topological spaces. -/
@[expose, simps]
def geometricRealizationFunctor : SimplicialObject TopCat.{u} ⥤ TopCat.{u} where
  obj := geometricRealization
  map := geometricRealization.map

/-- The canonical quotient comparison map `‖X‖ ⟶ |X|` from the fat realization of the underlying
semi-simplicial space to the thin geometric realization, collapsing degenerate simplices. -/
def fatToGeometricRealization :
    TauCeti.fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) ⟶
      X.geometricRealization :=
  TopCat.ofHom <| TauCeti.fatRealization.desc (Z := X.geometricRealization)
    (fun m ↦ geometricRealization.ι X (SemiSimplexCategory.toSimplexCategory.obj m).len) <| by
      intro m n f x t
      exact geometricRealization.ι_map X (SemiSimplexCategory.toSimplexCategory.map f) x t

namespace geometricRealization

@[simp↓]
theorem fatToGeometricRealization_ι (m : SemiSimplexCategory)
    (x : (SemiSimplexCategory.toSimplexCategory.op ⋙ X).obj (op m))
    (t : SemiSimplexCategory.toTop.{u}.obj m) :
    X.fatToGeometricRealization (TauCeti.fatRealization.ι _ m (x, t)) =
      ι X (SemiSimplexCategory.toSimplexCategory.obj m).len (x, t) :=
  TauCeti.fatRealization.desc_ι _ _ m (x, t)

/-- The comparison map `‖X‖ ⟶ |X|` is surjective. -/
theorem fatToGeometricRealization_surjective :
    Function.Surjective X.fatToGeometricRealization := fun p ↦ by
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  exact ⟨TauCeti.fatRealization.ι _ (SemiSimplexCategory.mk n) (x, t),
    fatToGeometricRealization_ι X (SemiSimplexCategory.mk n) x t⟩

/-- The comparison map `‖X‖ ⟶ |X|` is a quotient map: `|X|` is a topological quotient of `‖X‖`. -/
theorem isQuotientMap_fatToGeometricRealization :
    IsQuotientMap X.fatToGeometricRealization := by
  rw [isQuotientMap_iff]
  refine ⟨⟨TopologicalSpace.ext_iff.mpr fun s ↦
    ⟨fun hs ↦ isOpen_coinduced.mpr (hs.preimage X.fatToGeometricRealization.hom.continuous),
      fun hs ↦ ?_⟩⟩, fatToGeometricRealization_surjective X⟩
  rw [isOpen_coinduced, TauCeti.fatRealization.isOpen_iff] at hs
  rw [isOpen_iff]
  intro n
  have heq : ⇑(ι X n) =
      X.fatToGeometricRealization ∘ TauCeti.fatRealization.ι _ (SemiSimplexCategory.mk n) :=
    funext fun ⟨x, t⟩ ↦ (fatToGeometricRealization_ι X (SemiSimplexCategory.mk n) x t).symm
  rw [heq]
  exact hs (SemiSimplexCategory.mk n)

/-- The comparison map `‖X‖ ⟶ |X|` is natural in the simplicial space `X`. -/
@[reassoc (attr := simp)]
theorem map_comp_fatToGeometricRealization {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    TauCeti.fatRealization.map (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op φ) ≫
      Y.fatToGeometricRealization =
    X.fatToGeometricRealization ≫ map φ := by
  ext m x t
  simp only [TopCat.coe_comp, Function.comp_apply, TauCeti.fatRealization.map_ι,
    fatToGeometricRealization_ι]
  rfl

section Augment

variable {X} {Z : TopCat.{u}}

/-- The map `|X| ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : X.geometricRealization ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun n ↦ (ε.app (op ⦋n⦌)).hom.comp ContinuousMap.fst) <| by
    intro m n f x t
    simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : ℕ) (x : X _⦋n⦌)
    (t : toTop.{u}.obj ⦋n⦌) : augment ε (ι X n (x, t)) = ε.app (op ⦋n⦌) x :=
  (rfl)

/-- If an augmentation is a quotient map in one degree, its thin geometric realization is a
quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) {n : ℕ}
    (hε : IsQuotientMap (ε.app (op ⦋n⦌))) : IsQuotientMap (augment ε) := by
  obtain ⟨t⟩ : Nonempty (toTop.{u}.obj ⦋n⦌) := inferInstance
  let j : X _⦋n⦌ → X.geometricRealization := fun x ↦ ι X n (x, t)
  have hj : Continuous j := (ι X n).continuous.comp (continuous_id.prodMk continuous_const)
  have heq : augment ε ∘ j = fun x ↦ ε.app (op ⦋n⦌) x := funext fun x ↦ augment_ι ε n x t
  exact IsQuotientMap.of_comp hj (augment ε).hom.continuous (heq.symm ▸ hε)

@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by
  ext; simp

/-- The fat augmentation factors through the thin augmentation along `fatToGeometricRealization`. -/
@[reassoc (attr := simp)]
theorem fatToGeometricRealization_comp_augment (ε : X ⟶ (Functor.const _).obj Z) :
    X.fatToGeometricRealization ≫ augment ε =
      TauCeti.fatRealization.augment
        (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op ε) := by
  ext m x t
  simp only [TopCat.coe_comp, Function.comp_apply, fatToGeometricRealization_ι,
    TauCeti.fatRealization.augment_ι]
  rfl

end Augment

section Homotopy

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- A `[0, 1]`-family `φ s : X ⟶ Y` of morphisms of simplicial spaces that is jointly continuous
in `s` and the simplex in each degree induces a homotopy `(s, [x, t]) ↦ [φ s x, t]` from `|φ 0|`
to `|φ 1|`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : ℕ, Continuous fun p : unitInterval × X _⦋n⦌ ↦ (φ p.1).app (op ⦋n⦌) p.2) :
    ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom where
  toFun p := map (φ p.1) p.2
  continuous_toFun := (isQuotientMap_sigma X).continuous_lift_prod_right <| by
    have : Continuous fun q : Σ n : ℕ, (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) × unitInterval ↦
        ι Y q.1 ((φ q.2.2).app (op ⦋q.1⦌) q.2.1.1, q.2.1.2) :=
      continuous_sigma fun n ↦ (ι Y n).continuous.comp <|
        ((hφ n).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst)
    exact (this.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)).congr
      fun ⟨_, n, x, t⟩ ↦ (map_ι _ n x t).symm
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp]
theorem homotopy_apply_ι (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : ℕ, Continuous fun p : unitInterval × X _⦋n⦌ ↦ (φ p.1).app (op ⦋n⦌) p.2)
    (s : unitInterval) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op ⦋n⦌) x, t) :=
  (rfl)

end Homotopy

section Restriction

variable {X} {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)

/-- The image of `|φ|` consists of the points of `|X|` of the form `[φ y, t]`. -/
theorem range_map :
    range (map φ) = {p | ∃ n y t, ι X n (φ.app (op ⦋n⦌) y, t) = p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    exact ⟨n, y, t, rfl⟩
  · rintro ⟨n, y, t, rfl⟩
    exact ⟨ι Y n (y, t), rfl⟩

private theorem map_mem_range {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) {x : X.obj m}
    (hx : x ∈ range (φ.app m)) : X.map f x ∈ range (φ.app n) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Y.map f y, NatTrans.naturality_apply φ f y⟩

section PartialInv

variable {φ} (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
  (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
    X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌)))

include hinj hsat

open scoped Classical in
/-- Partial inverse of `|φ|`, defined on the points `[φ y, t]`. -/
private def partialInv : X.geometricRealization → Option Y.geometricRealization :=
  Quot.lift
    (fun p ↦ if hx : p.2.1 ∈ range (φ.app (op ⦋p.1⦌)) then some (ι Y p.1 (hx.choose, p.2.2))
      else none) <| by
    rintro _ _ ⟨f, x, t⟩
    dsimp only
    split_ifs with hx' hx hx
    · have hchoose : hx'.choose = Y.map f.op hx.choose :=
        hinj _ (by rw [hx'.choose_spec, NatTrans.naturality_apply, hx.choose_spec])
      rw [hchoose, ι_map]
    · exact absurd (hsat f x hx') hx
    · exact absurd (map_mem_range φ f.op hx) hx'
    · rfl

open scoped Classical in
private theorem partialInv_ι (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    partialInv hinj hsat (ι X n (x, t)) =
      if hx : x ∈ range (φ.app (op ⦋n⦌)) then some (ι Y n (hx.choose, t)) else none :=
  (rfl)

private theorem partialInv_map (q : Y.geometricRealization) :
    partialInv hinj hsat (map φ q) = some q := by
  obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
  rw [map_ι, partialInv_ι]
  split_ifs with hx
  · rw [hinj n hx.choose_spec]
  · exact absurd ⟨y, rfl⟩ hx

private theorem exists_eq_of_partialInv_eq_some {n : ℕ} {x : X _⦋n⦌} {t : toTop.{u}.obj ⦋n⦌}
    {q : Y.geometricRealization} (h : partialInv hinj hsat (ι X n (x, t)) = some q) :
    ∃ y, φ.app (op ⦋n⦌) y = x ∧ ι Y n (y, t) = q := by
  rw [partialInv_ι] at h
  split_ifs at h with hx
  exact ⟨hx.choose, hx.choose_spec, Option.some.inj h⟩

private theorem map_injective_of_sat : Function.Injective (map φ) :=
  fun q q' h ↦ Option.some.inj <| by
    rw [← partialInv_map hinj hsat q, ← partialInv_map hinj hsat q', h]

private theorem preimage_ι_image_map (W : Set Y.geometricRealization) (n : ℕ) :
    ι X n ⁻¹' (map φ '' W) = Prod.map (φ.app (op ⦋n⦌)) id '' (ι Y n ⁻¹' W) := by
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

/-- **Open restriction for thin geometric realization.** If `φ : Y ⟶ X` is levelwise an open
embedding and backwards-closed along simplicial operators, then `|φ| : |Y| ⟶ |X|` is an open
embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌))) :
    IsOpenEmbedding (map φ) := by
  have hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isOpenMap (map φ).hom.continuous
    (map_injective_of_sat hinj hsat) fun W hW ↦ ?_
  rw [isOpen_iff] at hW ⊢
  intro n
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ n).prodMap .id).isOpenMap _ (hW n)

variable {Z : TopCat.{u}} {ε : X ⟶ (Functor.const _).obj Z} {V : Set Z}

/-- If the image of `φ` in every degree is the preimage of `V ⊆ Z` under an augmentation `ε`, then
the preimage of `V` in `|X|` is the image of `|Y|`. -/
theorem preimage_augment_eq_range_map
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    augment ε ⁻¹' V = range (map φ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
    obtain ⟨y, rfl⟩ : x ∈ range (φ.app (op ⦋n⦌)) := by rwa [hrange]
    exact ⟨ι Y n (y, t), rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    rw [mem_preimage, ← ConcreteCategory.comp_apply, map_comp_augment, augment_ι]
    exact (hrange n).subset ⟨y, rfl⟩

private theorem mem_range_of_map_mem_range
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : X _⦋n⦌) (hx : X.map f.op x ∈ range (φ.app (op ⦋m⦌))) : x ∈ range (φ.app (op ⦋n⦌)) := by
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `|φ|` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    IsOpenEmbedding (map φ) :=
  isOpenEmbedding_map hφ (mem_range_of_map_mem_range hrange)

end Restriction

end geometricRealization

end CategoryTheory.SimplicialObject
