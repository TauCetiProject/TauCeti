/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.TopologicalSimplex

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
(`TauCeti.fatRealization.desc`), its quotient topology (`TauCeti.fatRealization.isOpen_iff`,
`TauCeti.fatRealization.continuous_iff`) and its functoriality
(`TauCeti.fatRealizationFunctor`). An augmentation `ε : X ⟶ const Z` induces the map
`TauCeti.fatRealization.augment ε : ‖X‖ ⟶ Z` sending `[x, t]` to `ε x`.

The main result is the open restriction theorem. If `φ : Y ⟶ X` is levelwise an open embedding
and its image is closed under passing from a face back to the simplex, then `‖φ‖ : ‖Y‖ ⟶ ‖X‖` is
an open embedding (`TauCeti.fatRealization.isOpenEmbedding_map`). In particular, if the image of
`φ` in each level is the preimage of a set `V ⊆ Z` under an augmentation, then `‖Y‖` is
homeomorphic, through `‖φ‖`, to the open subspace of `‖X‖` lying over `V`
(`TauCeti.fatRealization.preimage_augment_eq_range_map` and
`TauCeti.fatRealization.isOpenEmbedding_map_of_range_eq_preimage`). For the nerve of a groupoid
augmented by the orbit map to its coarse space, this identifies the preimage of a saturated open
set with the fat realization of the nerve of the restricted groupoid.

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

section Desc

variable {X} {Z : Type*} [TopologicalSpace Z] (g : ∀ n, C(X.obj (op n) × toTop.{u}.obj n, Z))
  (hg : ∀ ⦃m n : SemiSimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n)) (t : toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, toTop.map f t))

/-- The universal property of the fat realization: continuous maps `Xₙ × Δⁿ → Z` compatible with
the face identifications descend to a continuous map `‖X‖ → Z`. -/
def desc : C(fatRealization X, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
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

/-- The augmentation of `‖X‖` induced by `ε` restricts along `‖φ‖` to the augmentation of `‖Y‖`
induced by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by
  ext; simp

end Augment

section OpenRestriction

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
  -- The preimage of `‖φ‖(W)` in level `n` is the image of the preimage of `W` under `φ × id`.
  convert ((hφ (op n)).prodMap .id).isOpenMap _ (hW n) using 1
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

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `‖φ‖` is an open embedding; by `preimage_augment_eq_range_map` its image is the part of
`‖X‖` lying over `V`. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsOpenEmbedding (map φ) := by
  refine isOpenEmbedding_map hφ fun m n f x hx ↦ ?_
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

end OpenRestriction

end fatRealization

end TauCeti
