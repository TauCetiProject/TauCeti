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
`X.geometricRealization` (classically `|X|`) is the quotient of `Σ n : ℕ, X _⦋n⦌ × Δⁿ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` along morphisms `f : ⦋m⦌ ⟶ ⦋n⦌` in
`SimplexCategory`, with the quotient topology. Collapsing degeneracies yields a canonical quotient
comparison map `X.fatToGeometricRealization` from the fat realization of `X`.

This file constructs `X.geometricRealization` with its characteristic maps, universal property
(`geometricRealization.desc`), functoriality (`geometricRealizationFunctor`), augmentations
(`geometricRealization.augment`), `[0, 1]`-homotopies (`geometricRealization.homotopy`), Lindelöf
and compactly-generated instances, and open restriction (`geometricRealization.isOpenEmbedding_map`,
`geometricRealization.isOpenEmbedding_map_of_range_eq_preimage`). Unconditional injectivity and
closed embeddings are proved via normal forms in
`TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, LNM **271**, Springer, 1972, §11.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial Topology

universe v u

namespace CategoryTheory.SimplicialObject

open SimplexCategory (toTop)

variable (X : SimplicialObject TopCat.{u})

private inductive GeometricRealizationRel :
    (Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) → (Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) → Prop where
  | mk {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
      GeometricRealizationRel ⟨m, X.map f.op x, t⟩ ⟨n, x, toTop.map f t⟩

/-- The thin geometric realization `|X|` of a simplicial space `X`: the quotient of
`Σ n : ℕ, X _⦋n⦌ × Δⁿ` by `(X(f) x, t) ∼ (x, f_* t)` along all morphisms in `SimplexCategory`,
equipped with the quotient topology. -/
def geometricRealization : TopCat.{u} :=
  TopCat.of (Quot (GeometricRealizationRel X))

namespace geometricRealization

/-- The characteristic map `X _⦋n⦌ × Δⁿ → |X|` in degree `n`. -/
def ι (n : ℕ) : C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, X.geometricRealization) :=
  ⟨fun p ↦ Quot.mk (GeometricRealizationRel X) ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

@[simp]
theorem ι_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  Quot.sound (GeometricRealizationRel.mk f x t)

theorem ι_jointly_surjective (p : X.geometricRealization) : ∃ n x t, ι X n (x, t) = p := by
  induction p using Quot.ind with | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2 :=
  isQuotientMap_quot_mk

theorem isOpen_iff {s : Set X.geometricRealization} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X).isOpen_preimage, isOpen_sigma_iff]; rfl

theorem isClosed_iff {s : Set X.geometricRealization} :
    IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : X.geometricRealization → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) := by
  rw [(isQuotientMap_sigma X).continuous_iff, continuous_sigma_iff]; rfl

@[ext]
theorem hom_ext {Z : TopCat} {g h : X.geometricRealization ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h := by
  ext p; obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p; exact H n x t

instance [∀ n : ℕ, LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    LindelofSpace X.geometricRealization := Quot.lindelofSpace

instance [∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} X.geometricRealization :=
  uCompactlyGeneratedSpace_of_coinduced continuous_quot_mk rfl

section Desc

variable {X}

/-- Set-level universal property of the geometric realization. -/
def descFun {Z : Type*} (g : ∀ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ → Z)
    (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
      g m (X.map f.op x, t) = g n (x, toTop.map f t)) : X.geometricRealization → Z :=
  Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)

@[simp]
theorem descFun_ι {Z : Type*} (g : ∀ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ → Z)
    (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
      g m (X.map f.op x, t) = g n (x, toTop.map f t))
    (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) : descFun g hg (ι X n p) = g n p := (rfl)

variable {Z : Type*} [TopologicalSpace Z] (g : ∀ n : ℕ, C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, Z))
  (hg : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- Universal property of the geometric realization: continuous maps `X _⦋n⦌ × Δⁿ → Z` compatible
with all simplicial operators descend to a continuous map `|X| → Z`. -/
def desc : C(X.geometricRealization, Z) where
  toFun := descFun (fun n ↦ g n) hg
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n ↦ (g n).continuous)

@[simp]
theorem desc_ι (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) : desc g hg (ι X n p) = g n p := (rfl)

end Desc

section Map

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The map of geometric realizations induced by a morphism of simplicial spaces. -/
def map (φ : X ⟶ Y) : X.geometricRealization ⟶ Y.geometricRealization :=
  TopCat.ofHom <| desc (Z := Y.geometricRealization)
    (fun n ↦ (ι Y n).comp ((φ.app (op ⦋n⦌)).hom.prodMap (.id _))) fun _ _ _ _ _ ↦ by simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    map φ (ι X n (x, t)) = ι Y n (φ.app (op ⦋n⦌) x, t) := (rfl)

@[simp] theorem map_id : map (𝟙 X) = 𝟙 X.geometricRealization := by ext; simp

@[simp]
theorem map_comp {W : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map (φ ≫ ψ) = map φ ≫ map ψ := by ext; simp

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
    (fun m ↦ geometricRealization.ι X (SemiSimplexCategory.toSimplexCategory.obj m).len)
    fun _ _ f x t ↦ geometricRealization.ι_map X (SemiSimplexCategory.toSimplexCategory.map f) x t

namespace geometricRealization

@[simp↓]
theorem fatToGeometricRealization_ι (m : SemiSimplexCategory)
    (x : (SemiSimplexCategory.toSimplexCategory.op ⋙ X).obj (op m))
    (t : SemiSimplexCategory.toTop.{u}.obj m) :
    X.fatToGeometricRealization (TauCeti.fatRealization.ι _ m (x, t)) =
      ι X (SemiSimplexCategory.toSimplexCategory.obj m).len (x, t) :=
  TauCeti.fatRealization.desc_ι _ _ m (x, t)

/-- The comparison map `‖X‖ ⟶ |X|` is a quotient map: `|X|` is a topological quotient of `‖X‖`. -/
theorem isQuotientMap_fatToGeometricRealization : IsQuotientMap X.fatToGeometricRealization := by
  let j : (Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) →
      TauCeti.fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) :=
    fun p ↦ TauCeti.fatRealization.ι _ (SemiSimplexCategory.mk p.1) p.2
  have hj : Continuous j := continuous_sigma fun n ↦
    (TauCeti.fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X) (.mk n)).continuous
  have heq : X.fatToGeometricRealization ∘ j = fun p ↦ ι X p.1 p.2 :=
    funext fun ⟨n, x, t⟩ ↦ fatToGeometricRealization_ι X (.mk n) x t
  exact IsQuotientMap.of_comp hj X.fatToGeometricRealization.hom.continuous
    (heq.symm ▸ isQuotientMap_sigma X)

/-- The comparison map `‖X‖ ⟶ |X|` is surjective. -/
theorem fatToGeometricRealization_surjective : Function.Surjective X.fatToGeometricRealization :=
  (isQuotientMap_fatToGeometricRealization X).surjective

/-- The comparison map `‖X‖ ⟶ |X|` is natural in the simplicial space `X`. -/
@[reassoc (attr := simp)]
theorem map_comp_fatToGeometricRealization {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    TauCeti.fatRealization.map (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op φ) ≫
      Y.fatToGeometricRealization = X.fatToGeometricRealization ≫ map φ := by
  ext m x t
  simp only [TopCat.coe_comp, Function.comp_apply, TauCeti.fatRealization.map_ι,
    fatToGeometricRealization_ι]
  rfl

section Augment

variable {X} {Z : TopCat.{u}}

/-- The map `|X| ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : X.geometricRealization ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun n ↦ (ε.app (op ⦋n⦌)).hom.comp ContinuousMap.fst)
    fun _ _ _ _ _ ↦ by simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : ℕ) (x : X _⦋n⦌)
    (t : toTop.{u}.obj ⦋n⦌) : augment ε (ι X n (x, t)) = ε.app (op ⦋n⦌) x := (rfl)

/-- If an augmentation is a quotient map in one degree, its thin realization is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) {n : ℕ}
    (hε : IsQuotientMap (ε.app (op ⦋n⦌))) : IsQuotientMap (augment ε) := by
  obtain ⟨t⟩ : Nonempty (toTop.{u}.obj ⦋n⦌) := inferInstance
  exact IsQuotientMap.of_comp (f := fun x ↦ ι X n (x, t))
    ((ι X n).continuous.comp (continuous_id.prodMk continuous_const)) (augment ε).hom.continuous hε

@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by ext; simp

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

/-- A `[0, 1]`-family `φ s : X ⟶ Y` jointly continuous in `s` and the simplex in each degree
induces a homotopy `(s, [x, t]) ↦ [φ s x, t]` from `|φ 0|` to `|φ 1|`. -/
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
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op ⦋n⦌) x, t) := (rfl)

end Homotopy

section Restriction

variable {X} {Y : SimplicialObject TopCat.{u}} {φ : Y ⟶ X}

variable (φ) in
/-- The image of `|φ|` consists of the points of `|X|` of the form `[φ y, t]`. -/
theorem range_map : range (map φ) = {p | ∃ n y t, ι X n (φ.app (op ⦋n⦌) y, t) = p} := by
  ext p; refine ⟨?_, fun ⟨n, y, t, hp⟩ ↦ ⟨ι Y n (y, t), hp⟩⟩
  rintro ⟨q, rfl⟩; obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q; exact ⟨n, y, t, rfl⟩

open scoped Classical in
private def partialInv (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌))) :
    X.geometricRealization → Option Y.geometricRealization :=
  descFun (fun n p ↦ if hx : p.1 ∈ range (φ.app (op ⦋n⦌)) then some (ι Y n (hx.choose, p.2))
    else none) fun _ _ f x t ↦ by
    dsimp only; split_ifs with hx' hx hx
    · have hchoose : hx'.choose = Y.map f.op hx.choose :=
        hinj _ (by rw [hx'.choose_spec, NatTrans.naturality_apply, hx.choose_spec])
      rw [hchoose, ι_map]
    · exact absurd (hsat f x hx') hx
    · obtain ⟨y, rfl⟩ := hx; exact absurd ⟨Y.map f.op y, NatTrans.naturality_apply φ f.op y⟩ hx'
    · rfl

private theorem partialInv_map (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌)))
    (q : Y.geometricRealization) : partialInv hinj hsat (map φ q) = some q := by
  obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
  simp only [map_ι, partialInv, descFun_ι]
  split_ifs with hx
  · rw [hinj n hx.choose_spec]
  · exact absurd ⟨y, rfl⟩ hx

/-- **Open restriction for thin geometric realization.** If `φ : Y ⟶ X` is levelwise an open
embedding and backwards-closed along simplicial operators, then `|φ| : |Y| ⟶ |X|` is an open
embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hsat : ∀ ⦃m n : ℕ⦄ (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      X.map f.op x ∈ range (φ.app (op ⦋m⦌)) → x ∈ range (φ.app (op ⦋n⦌))) :
    IsOpenEmbedding (map φ) := by
  have hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isOpenMap (map φ).hom.continuous
    (fun q q' h ↦ Option.some.inj <| by
      rw [← partialInv_map hinj hsat q, ← partialInv_map hinj hsat q', h]) fun W hW ↦ ?_
  rw [isOpen_iff] at hW ⊢
  intro n
  suffices ι X n ⁻¹' (map φ '' W) = Prod.map (φ.app (op ⦋n⦌)) id '' (ι Y n ⁻¹' W) by
    rw [this]; exact ((hφ n).prodMap .id).isOpenMap _ (hW n)
  ext ⟨x, t⟩; constructor
  · rintro ⟨q, hq, hqx⟩
    have h := hqx ▸ partialInv_map hinj hsat q
    simp only [partialInv, descFun_ι] at h
    split_ifs at h with hx
    have hq' : ι Y n (hx.choose, t) = q := Option.some.inj h
    exact ⟨(hx.choose, t), mem_preimage.mpr (hq' ▸ hq), Prod.ext hx.choose_spec rfl⟩
  · rintro ⟨⟨y, t'⟩, hy, hyx⟩
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hyx
    obtain ⟨rfl, rfl⟩ := hyx
    exact ⟨ι Y n (y, t'), hy, rfl⟩

variable {Z : TopCat.{u}} {ε : X ⟶ (Functor.const _).obj Z} {V : Set Z}

/-- If the image of `φ` in every degree is the preimage of `V ⊆ Z` under an augmentation `ε`, then
the preimage of `V` in `|X|` is the image of `|Y|`. -/
theorem preimage_augment_eq_range_map
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    augment ε ⁻¹' V = range (map φ) := by
  ext p; constructor
  · intro hp; obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
    obtain ⟨y, rfl⟩ : x ∈ range (φ.app (op ⦋n⦌)) := by rwa [hrange]
    exact ⟨ι Y n (y, t), rfl⟩
  · rintro ⟨q, rfl⟩; obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    rw [mem_preimage, ← ConcreteCategory.comp_apply, map_comp_augment, augment_ι]
    exact (hrange n).subset ⟨y, rfl⟩

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `|φ|` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n : ℕ, IsOpenEmbedding (φ.app (op ⦋n⦌)))
    (hrange : ∀ n : ℕ, range (φ.app (op ⦋n⦌)) = ε.app (op ⦋n⦌) ⁻¹' V) :
    IsOpenEmbedding (map φ) :=
  isOpenEmbedding_map hφ fun _ _ f x hx ↦ by
    rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx; rw [hrange]; simpa using hx

end Restriction

end geometricRealization

end CategoryTheory.SimplicialObject
