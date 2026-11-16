/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Topology.Compactness.Lindelof

/-!
# The thin realization of a simplicial space

A simplicial space is a functor `X : SimplicialObject TopCat`: a space `X _⦋n⦌` for each `n : ℕ`
with simplicial operators along all order-preserving maps `f : ⦋m⦌ ⟶ ⦋n⦌` (both faces and
degeneracies). Its *thin* (or geometric) realization `|X|` (`TauCeti.thinRealization X`) is the
quotient of the disjoint union `Σ n, Xₙ × Δⁿ` by the identifications `(X(f) x, t) ∼ (x, f_* t)`
for every morphism `f : ⦋m⦌ ⟶ ⦋n⦌` in `SimplexCategory`, where `f_*` is the induced affine map
of topological simplices (`SimplexCategory.toTop`). This is a concrete model of the coend of
`Xₘ × Δⁿ` over `SimplexCategory`: `TauCeti.thinRealization.desc` and
`TauCeti.thinRealization.hom_ext` express its universal property.

This file develops the basic API parallel to `TauCeti.AlgebraicTopology.FatRealization`:
characteristic maps `TauCeti.thinRealization.ι`, the quotient topology characterization
(`TauCeti.thinRealization.isOpen_iff`, `TauCeti.thinRealization.isClosed_iff`,
`TauCeti.thinRealization.continuous_iff`), functoriality (`TauCeti.thinRealizationFunctor`),
augmentations (`TauCeti.thinRealization.augment`, `TauCeti.thinRealization.isQuotientMap_augment`),
levelwise homotopies (`TauCeti.thinRealization.homotopy`), and the open and closed restriction
theorems (`TauCeti.thinRealization.isOpenEmbedding_map`,
`TauCeti.thinRealization.isClosedEmbedding_map`, and their augmented versions
`TauCeti.thinRealization.preimage_augment_eq_range_map`,
`TauCeti.thinRealization.isOpenEmbedding_map_of_range_eq_preimage`,
`TauCeti.thinRealization.isClosedEmbedding_map_of_range_eq_preimage`).

Forgetting degeneracies gives the canonical comparison quotient map
`TauCeti.thinRealization.fatToThin` from the fat realization
`‖SemiSimplexCategory.toSimplexCategory.op ⋙ X‖` to `|X|`
(`TauCeti.thinRealization.isQuotientMap_fatToThin`), natural in `X` and compatible with
augmentations. Since `|X|` is a quotient of the countable disjoint union `Σ n, Xₙ × Δⁿ`, it is
immediately Lindelöf whenever each level `Xₙ` is Lindelöf (`TauCeti.thinRealization.lindelofSpace`)
and compactly generated whenever each product `Xₙ × Δⁿ` is compactly generated
(`TauCeti.thinRealization.uCompactlyGeneratedSpace`), without any hypothesis on degeneracies.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics 271, Springer,
  1972, §11.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

open scoped Simplicial

universe u v

namespace TauCeti

variable (X : SimplicialObject TopCat.{u})

/-- The simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` on `Σ n, Xₙ × Δⁿ`. -/
private inductive ThinRealizationRel :
    (Σ n : SimplexCategory, X.obj (op n) × SimplexCategory.toTop.{u}.obj n) →
      (Σ n : SimplexCategory, X.obj (op n) × SimplexCategory.toTop.{u}.obj n) → Prop
  | mk {m n : SimplexCategory} (f : m ⟶ n) (x : X.obj (op n))
      (t : SimplexCategory.toTop.{u}.obj m) :
      ThinRealizationRel ⟨m, X.map f.op x, t⟩ ⟨n, x, SimplexCategory.toTop.map f t⟩

/-- The thin (geometric) realization `|X|` of a simplicial space `X`: the quotient of
`Σ n, Xₙ × Δⁿ` by the identifications `(X(f) x, t) ∼ (x, f_* t)` along all simplicial operators
(faces and degeneracies), with the quotient topology. -/
def thinRealization : TopCat.{u} :=
  TopCat.of (Quot (ThinRealizationRel X))

namespace thinRealization

/-- The characteristic map `Xₙ × Δⁿ → |X|` of level `n` of the thin realization. -/
def ι (n : SimplexCategory) :
    C(X.obj (op n) × SimplexCategory.toTop.{u}.obj n, thinRealization X) :=
  ⟨fun p ↦ Quot.mk (ThinRealizationRel X) ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The characteristic maps are compatible with all simplicial identifications. -/
@[simp]
theorem ι_map {m n : SimplexCategory} (f : m ⟶ n) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj m) :
    ι X m (X.map f.op x, t) = ι X n (x, SimplexCategory.toTop.map f t) :=
  Quot.sound (ThinRealizationRel.mk f x t)

/-- Every point of the thin realization lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : thinRealization X) : ∃ n x t, ι X n (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The thin realization carries the quotient topology of `Σ n, Xₙ × Δⁿ`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : SimplexCategory, X.obj (op n) × SimplexCategory.toTop.{u}.obj n ↦
      ι X p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A set in the thin realization is open exactly when its preimage under every characteristic map
is open. -/
theorem isOpen_iff {s : Set (thinRealization X)} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A set in the thin realization is closed exactly when its preimage under every characteristic
map is closed. -/
theorem isClosed_iff {s : Set (thinRealization X)} :
    IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of the thin realization is continuous exactly when its composite with every
characteristic map is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : thinRealization X → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) := by
  rw [(isQuotientMap_sigma X).continuous_iff, continuous_sigma_iff]
  rfl

/-- Two continuous maps out of the thin realization agree as soon as they agree on the image of
every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat.{u}} {g h : thinRealization X ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h := by
  ext p
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  exact H n x t

section Desc

variable {X} {Z : Type*} [TopologicalSpace Z]
  (g : ∀ n, C(X.obj (op n) × SimplexCategory.toTop.{u}.obj n, Z))
  (hg : ∀ ⦃m n : SimplexCategory⦄ (f : m ⟶ n) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj m),
    g m (X.map f.op x, t) = g n (x, SimplexCategory.toTop.map f t))

/-- The universal property of the thin realization: continuous maps `Xₙ × Δⁿ → Z` compatible with
all simplicial identifications descend to a continuous map `|X| → Z`. -/
def desc : C(thinRealization X, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n ↦ (g n).continuous)

@[simp]
theorem desc_ι (n : SimplexCategory) (p : X.obj (op n) × SimplexCategory.toTop.{u}.obj n) :
    desc g hg (ι X n p) = g n p :=
  (rfl)

end Desc

section Map

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- The map of thin realizations induced by a morphism of simplicial spaces. -/
def map (φ : X ⟶ Y) : thinRealization X ⟶ thinRealization Y :=
  TopCat.ofHom <|
    desc (Z := thinRealization Y) (fun n ↦ (ι Y n).comp ((φ.app (op n)).hom.prodMap (.id _))) <| by
    intro m n f x t
    simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (n : SimplexCategory) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj n) :
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

end thinRealization

/-- The thin realization as a functor from simplicial spaces to spaces. -/
@[expose, simps]
def thinRealizationFunctor : SimplicialObject TopCat.{u} ⥤ TopCat.{u} where
  obj := thinRealization
  map := thinRealization.map

namespace thinRealization

section Augment

variable {X} {Z : TopCat.{u}}

/-- The map `|X| ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending `[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : thinRealization X ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun n ↦ (ε.app (op n)).hom.comp ContinuousMap.fst) <| by
    intro m n f x t
    simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (n : SimplexCategory) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj n) : augment ε (ι X n (x, t)) = ε.app (op n) x :=
  (rfl)

/-- If an augmentation is a quotient map in one degree, its realization is a quotient map.
No condition on the other degrees or simplicial operators is needed. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (n : SimplexCategory)
    (hε : IsQuotientMap (ε.app (op n))) : IsQuotientMap (augment ε) := by
  obtain ⟨t⟩ : Nonempty (SimplexCategory.toTop.{u}.obj n) := inferInstance
  let j : X.obj (op n) → thinRealization X := fun x ↦ ι X n (x, t)
  have hj : Continuous j := (ι X n).continuous.comp (continuous_id.prodMk continuous_const)
  have heq : (augment ε) ∘ j = fun x ↦ ε.app (op n) x :=
    funext fun x ↦ augment_ι ε n x t
  exact IsQuotientMap.of_comp hj (augment ε).hom.continuous (heq.symm ▸ hε)

/-- The augmentation of `|X|` induced by `ε` restricts along `|φ|` to the augmentation of `|Y|`
induced by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map φ ≫ augment ε = augment (φ ≫ ε) := by
  ext; simp

end Augment

section FatToThin

/-- The canonical comparison map from the fat realization of `X` (forgetting degeneracies) to its
thin realization `|X|`. -/
def fatToThin :
    fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) ⟶ thinRealization X :=
  TopCat.ofHom <|
    fatRealization.desc (Z := thinRealization X)
      (fun n ↦ ι X (SemiSimplexCategory.toSimplexCategory.obj n)) fun _ _ f x t ↦
        ι_map X (SemiSimplexCategory.toSimplexCategory.map f) x t

/-- The fat-to-thin comparison sends each simplex `(x, t)` to its thin equivalence class. -/
theorem fatToThin_ι (n : SemiSimplexCategory)
    (x : X.obj (op (SemiSimplexCategory.toSimplexCategory.obj n)))
    (t : SemiSimplexCategory.toTop.{u}.obj n) :
    fatToThin X (fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X) n (x, t)) =
      ι X (SemiSimplexCategory.toSimplexCategory.obj n) (x, t) :=
  fatRealization.desc_ι (X := SemiSimplexCategory.toSimplexCategory.op ⋙ X) _ _ n (x, t)

/-- The canonical comparison from the fat realization to the thin realization is a quotient map. -/
theorem isQuotientMap_fatToThin : IsQuotientMap (fatToThin X) := by
  let g : (Σ n : SimplexCategory, X.obj (op n) × SimplexCategory.toTop.{u}.obj n) →
      fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) :=
    fun p ↦ fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X)
      (SemiSimplexCategory.mk p.1.len) p.2
  have hg : Continuous g := continuous_sigma fun n ↦
    (fatRealization.ι (SemiSimplexCategory.toSimplexCategory.op ⋙ X)
      (SemiSimplexCategory.mk n.len)).continuous
  have hcomp : fatToThin X ∘ g = fun p ↦ ι X p.1 p.2 :=
    funext fun ⟨n, x, t⟩ ↦ fatToThin_ι X (SemiSimplexCategory.mk n.len) x t
  exact IsQuotientMap.of_comp hg (fatToThin X).hom.continuous (hcomp.symm ▸ isQuotientMap_sigma X)

/-- The comparison from fat realization to thin realization is natural in the simplicial space. -/
@[reassoc (attr := simp)]
theorem fatToThin_naturality {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    fatRealization.map (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op φ) ≫
        fatToThin Y =
      fatToThin X ≫ map φ := by
  ext n x t
  simp only [ConcreteCategory.comp_apply, fatRealization.map_ι, Functor.whiskerLeft_app,
    fatToThin_ι]
  rfl

/-- The comparison from fat realization to thin realization commutes with augmentations. -/
@[reassoc (attr := simp)]
theorem fatToThin_comp_augment {X : SimplicialObject TopCat.{u}} {Z : TopCat.{u}}
    (ε : X ⟶ (Functor.const _).obj Z) :
    fatToThin X ≫ augment ε =
      fatRealization.augment (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op ε) := by
  ext n x t
  simp only [ConcreteCategory.comp_apply, fatToThin_ι, fatRealization.augment_ι,
    Functor.whiskerLeft_app]
  rfl

end FatToThin

section Homotopy

variable {X} {Y : SimplicialObject TopCat.{u}}

/-- A family `φ s : X ⟶ Y` of morphisms of simplicial spaces, indexed by `s ∈ [0, 1]` and
continuous jointly in `s` and the point in each level, induces the homotopy
`(s, [x, t]) ↦ [φ s x, t]` from `|φ 0|` to `|φ 1|`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ n : SimplexCategory,
      Continuous fun p : unitInterval × X.obj (op n) ↦ (φ p.1).app (op n) p.2) :
    ContinuousMap.Homotopy (map (φ 0)).hom (map (φ 1)).hom where
  toFun p := map (φ p.1) p.2
  continuous_toFun := (isQuotientMap_sigma X).continuous_lift_prod_right <| by
    -- `[0, 1]` is locally compact, so it suffices to check continuity on each `Xₙ × Δⁿ × [0, 1]`.
    have : Continuous fun q : Σ n : SimplexCategory,
        (X.obj (op n) × SimplexCategory.toTop.{u}.obj n) × unitInterval ↦
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
    (s : unitInterval) (n : SimplexCategory) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj n) :
    homotopy φ hφ (s, ι X n (x, t)) = ι Y n ((φ s).app (op n) x, t) :=
  (rfl)

end Homotopy

section Restriction

variable {X} {Y : SimplicialObject TopCat.{u}} (φ : Y ⟶ X)

/-- The points of `|X|` in the image of `|φ|` are those of the form `[φ y, t]`. -/
theorem range_map :
    range (map φ) = {p | ∃ n y t, ι X n (φ.app (op n) y, t) = p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
    exact ⟨n, y, t, rfl⟩
  · rintro ⟨n, y, t, rfl⟩
    exact ⟨ι Y n (y, t), rfl⟩

/-- If a simplex of `X` lies in the image of `φ`, so does its image under every simplicial
operator. -/
private theorem map_mem_range {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) {x : X.obj m}
    (hx : x ∈ range (φ.app m)) : X.map f x ∈ range (φ.app n) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Y.map f y, NatTrans.naturality_apply φ f y⟩

section PartialInv

variable {φ} (hinj : ∀ n, Function.Injective (φ.app n))
  (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
    X.map f x ∈ range (φ.app n) → x ∈ range (φ.app m))

include hinj hsat

open scoped Classical in
/-- A partial inverse of `|φ|`, defined on the points `[φ y, t]`. -/
private def partialInv : thinRealization X → Option (thinRealization Y) :=
  Quot.lift
    (fun p ↦ if hx : p.2.1 ∈ range (φ.app (op p.1)) then some (ι Y p.1 (hx.choose, p.2.2))
      else none) <| by
    rintro _ _ ⟨f, x, t⟩
    dsimp only
    split_ifs with hx' hx hx
    · -- The chosen preimage of `X(f) x` is `Y(f)` applied to the chosen preimage of `x`.
      have hchoose : hx'.choose = Y.map f.op hx.choose :=
        hinj _ (by rw [hx'.choose_spec, NatTrans.naturality_apply, hx.choose_spec])
      rw [hchoose, ι_map]
    · exact absurd (hsat f.op x hx') hx
    · exact absurd (map_mem_range φ f.op hx) hx'
    · rfl

open scoped Classical in
private theorem partialInv_ι (n : SimplexCategory) (x : X.obj (op n))
    (t : SimplexCategory.toTop.{u}.obj n) :
    partialInv hinj hsat (ι X n (x, t)) =
      if hx : x ∈ range (φ.app (op n)) then some (ι Y n (hx.choose, t)) else none :=
  (rfl)

private theorem partialInv_map (q : thinRealization Y) :
    partialInv hinj hsat (map φ q) = some q := by
  obtain ⟨n, y, t, rfl⟩ := ι_jointly_surjective Y q
  rw [map_ι, partialInv_ι]
  split_ifs with hx
  · rw [hinj _ hx.choose_spec]
  · exact absurd ⟨y, rfl⟩ hx

private theorem exists_eq_of_partialInv_eq_some {n : SimplexCategory} {x : X.obj (op n)}
    {t : SimplexCategory.toTop.{u}.obj n} {q : thinRealization Y}
    (h : partialInv hinj hsat (ι X n (x, t)) = some q) :
    ∃ y, φ.app (op n) y = x ∧ ι Y n (y, t) = q := by
  rw [partialInv_ι] at h
  split_ifs at h with hx
  exact ⟨hx.choose, hx.choose_spec, Option.some.inj h⟩

/-- If `φ : Y ⟶ X` is levelwise injective and a simplex of `X` lies in the image of `φ` whenever
its image under a simplicial operator does, then `|φ| : |Y| ⟶ |X|` is injective. -/
theorem map_injective : Function.Injective (map φ) := fun q q' h ↦ Option.some.inj <| by
  rw [← partialInv_map hinj hsat q, ← partialInv_map hinj hsat q', h]

/-- Under the same hypotheses, the preimage in level `n` of the image of `W ⊆ |Y|` under `|φ|` is
the image under `φ × id` of the preimage of `W`. -/
private theorem preimage_ι_image_map (W : Set (thinRealization Y)) (n : SimplexCategory) :
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
in the image of `φ` whenever its image under a simplicial operator does, then `|φ| : |Y| ⟶ |X|`
is an open embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
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
lies in the image of `φ` whenever its image under a simplicial operator does, then
`|φ| : |Y| ⟶ |X|` is a closed embedding. -/
theorem isClosedEmbedding_map (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hsat : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m),
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
part of `|X|` lying over `V` is exactly the image of `|Y|`. -/
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
simplex lies in the image of `φ` whenever its image under a simplicial operator does. -/
private theorem mem_range_of_map_mem_range (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V)
    ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x : X.obj m)
    (hx : X.map f x ∈ range (φ.app n)) : x ∈ range (φ.app m) := by
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `|φ|` is an open embedding; by `preimage_augment_eq_range_map` its image is the part of
`|X|` lying over `V`. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsOpenEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsOpenEmbedding (map φ) :=
  isOpenEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

/-- If `φ` is levelwise a closed embedding whose image is the preimage of `V` under an
augmentation `ε`, then `|φ|` is a closed embedding; by `preimage_augment_eq_range_map` its image
is the part of `|X|` lying over `V`. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ n, IsClosedEmbedding (φ.app n))
    (hrange : ∀ n, range (φ.app n) = ε.app n ⁻¹' V) : IsClosedEmbedding (map φ) :=
  isClosedEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

end Restriction

section QuotientProperties

/-- The thin realization of a simplicial space with Lindelöf levels is Lindelöf, as a quotient of
the countable disjoint union of the Lindelöf products `Xₙ × Δⁿ`. -/
theorem lindelofSpace [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    LindelofSpace (thinRealization X) := by
  have : Countable SimplexCategory := Function.Injective.countable fun _ _ h ↦ SimplexCategory.ext h
  have : ∀ n : SimplexCategory, LindelofSpace (X.obj (op n) × SimplexCategory.toTop.{u}.obj n) := by
    rintro ⟨k⟩
    have := hX k
    have : CompactSpace (SimplexCategory.toTop.{u}.obj ⦋k⦌) :=
      inferInstanceAs (CompactSpace (ULift (Convexity.StdSimplex ℝ (Fin (k + 1)))))
    exact lindelofSpace_prod_of_compactSpace_right
  exact LindelofSpace.of_continuous_surjective (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).surjective

/-- The thin realization of a simplicial space is compactly generated whenever each product
`Xₙ × Δⁿ` is compactly generated, as a quotient of `Σ n, Xₙ × Δⁿ`. -/
theorem uCompactlyGeneratedSpace
    [hX : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} (thinRealization X) := by
  have : ∀ n : SimplexCategory,
      UCompactlyGeneratedSpace.{v} (X.obj (op n) × SimplexCategory.toTop.{u}.obj n) :=
    fun ⟨k⟩ ↦ hX k
  exact uCompactlyGeneratedSpace_of_coinduced (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).eq_coinduced

end QuotientProperties

end thinRealization

end TauCeti
