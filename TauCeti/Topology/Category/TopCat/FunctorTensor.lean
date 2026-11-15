/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Basic

/-!
# Functor tensor products (coends) in `TopCat`

Given a small index category `D`, a covariant diagram of model spaces `K : D ⥤ TopCat.{u}` and a
contravariant diagram of spaces `X : Dᵒᵖ ⥤ TopCat.{u}`, their *functor tensor product* (or concrete
coend) `TauCeti.functorTensor K X` is the quotient of the disjoint union `Σ d : D, X(d) × K(d)` by
the identifications `(X(f) x, t) ∼ (x, K(f) t)` for every morphism `f : c ⟶ d` in `D`, equipped
with the quotient topology.

Specializing `D` and `K` recovers:
* the fat geometric realization `TauCeti.fatRealization` of a semi-simplicial space (`D =
  SemiSimplexCategory`, `K = SemiSimplexCategory.toTop`),
* the thin geometric realization `TauCeti.thinRealization` of a simplicial space (`D =
  SimplexCategory`, `K = SimplexCategory.toTop`), and
* the `k`-skeleton `TauCeti.thinRealization.skeleton X k` (`D = SimplexCategory.Truncated k`),

while reindexing along a functor `F : C ⥤ D` (`TauCeti.functorTensor.reindex`) uniformly supplies
the fat-to-thin comparison map, the skeletal transition maps, and the skeletal cocone legs.

## Main definitions

* `TauCeti.functorTensor`: the coend quotient space `∫^{d : D} X(d) × K(d)` in `TopCat`.
* `TauCeti.functorTensor.ι`, `TauCeti.functorTensor.desc`: characteristic maps and universal
  property.
* `TauCeti.functorTensor.map`, `TauCeti.functorTensorFunctor`: functoriality in `X`.
* `TauCeti.functorTensor.reindex`: canonical comparison map along `F : C ⥤ D`.
* `TauCeti.functorTensor.augment`: descent of an augmentation `X ⟶ const Z` to
  `functorTensor K X ⟶ Z`.
* `TauCeti.functorTensor.homotopy`: homotopy induced by a levelwise jointly continuous
  `[0, 1]`-family of natural transformations.

## Main results

* `TauCeti.functorTensor.isQuotientMap_sigma`, `TauCeti.functorTensor.isQuotientMap_reindex`,
  `TauCeti.functorTensor.isQuotientMap_augment`: quotient-topology characterizations.
* `TauCeti.functorTensor.instLindelofSpace`,
  `TauCeti.functorTensor.instUCompactlyGeneratedSpace`: Lindelöfness (for countable `D`) and
  compact generation of the functor tensor product.
* `TauCeti.functorTensor.isOpenEmbedding_map`, `TauCeti.functorTensor.isClosedEmbedding_map`,
  `TauCeti.functorTensor.preimage_augment_eq_range_map`,
  `TauCeti.functorTensor.isOpenEmbedding_map_of_range_eq_preimage`,
  `TauCeti.functorTensor.isClosedEmbedding_map_of_range_eq_preimage`: open and closed subspace
  restrictions for saturated subfunctors.

## References

* S. Mac Lane, *Categories for the Working Mathematician*, second edition, Section IX.6.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics **271**,
  Section 11.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

universe w w' v u

namespace TauCeti

variable {D : Type} [Category.{w} D]

/-- The coend identifications `(X(f) x, t) ∼ (x, K(f) t)` on `Σ d : D, X(d) × K(d)`. -/
private inductive FunctorTensorRel (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) :
    (Σ d : D, X.obj (op d) × K.obj d) → (Σ d : D, X.obj (op d) × K.obj d) → Prop where
  | mk ⦃c d : D⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c) :
      FunctorTensorRel K X ⟨c, X.map f.op x, t⟩ ⟨d, x, K.map f t⟩

/-- The functor tensor product (coend) `∫^{d : D} X(d) × K(d)` of `K : D ⥤ TopCat.{u}` and
`X : Dᵒᵖ ⥤ TopCat.{u}`: the quotient of `Σ d : D, X(d) × K(d)` by `(X(f) x, t) ∼ (x, K(f) t)` for
all morphisms `f` of `D`, equipped with the quotient topology. -/
def functorTensor (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) : TopCat.{u} :=
  TopCat.of (Quot (FunctorTensorRel K X))

namespace functorTensor

section Basic

variable (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u})

/-- The characteristic map `X(d) × K(d) → functorTensor K X` at `d : D`. -/
def ι (d : D) : C(X.obj (op d) × K.obj d, functorTensor K X) :=
  ⟨fun p ↦ Quot.mk (FunctorTensorRel K X) ⟨d, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The characteristic maps coequalize the contravariant action of `X` and the covariant action of
`K`. -/
@[simp]
theorem ι_map {c d : D} (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c) :
    ι K X c (X.map f.op x, t) = ι K X d (x, K.map f t) :=
  Quot.sound (FunctorTensorRel.mk f x t)

/-- Every point of `functorTensor K X` lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : functorTensor K X) : ∃ d x t, ι K X d (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- `functorTensor K X` carries the quotient topology of `Σ d : D, X(d) × K(d)`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ d : D, X.obj (op d) × K.obj d ↦ ι K X p.1 p.2 :=
  isQuotientMap_quot_mk

variable {K X}

/-- A set in `functorTensor K X` is open if and only if its preimage under every characteristic map
is open. -/
theorem isOpen_iff {s : Set (functorTensor K X)} : IsOpen s ↔ ∀ d, IsOpen (ι K X d ⁻¹' s) := by
  rw [← (isQuotientMap_sigma K X).isOpen_preimage, isOpen_sigma_iff]
  -- `ι K X d` is `(Quot.mk _) ∘ Sigma.mk d` by definition.
  rfl

/-- A set in `functorTensor K X` is closed if and only if its preimage under every characteristic
map is closed. -/
theorem isClosed_iff {s : Set (functorTensor K X)} :
    IsClosed s ↔ ∀ d, IsClosed (ι K X d ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of `functorTensor K X` is continuous if and only if its composite with every
characteristic map is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : functorTensor K X → Z} :
    Continuous g ↔ ∀ d, Continuous (g ∘ ι K X d) := by
  rw [(isQuotientMap_sigma K X).continuous_iff, continuous_sigma_iff]
  -- `ι K X d` is `(Quot.mk _) ∘ Sigma.mk d` by definition.
  rfl

/-- Two morphisms out of `functorTensor K X` agree once they agree on every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat.{u}} {g h : functorTensor K X ⟶ Z}
    (H : ∀ d x t, g (ι K X d (x, t)) = h (ι K X d (x, t))) : g = h := by
  ext p
  obtain ⟨d, x, t, rfl⟩ := ι_jointly_surjective K X p
  exact H d x t

variable (K X) in
/-- If `D` is countable and each product `X(d) × K(d)` is Lindelöf, then `functorTensor K X` is
Lindelöf. -/
instance instLindelofSpace [Countable D] [∀ d : D, LindelofSpace (X.obj (op d) × K.obj d)] :
    LindelofSpace (functorTensor K X) :=
  LindelofSpace.of_continuous_surjective (isQuotientMap_sigma K X).continuous
    (isQuotientMap_sigma K X).surjective

variable (K X) in
/-- If each product `X(d) × K(d)` is compactly generated, then `functorTensor K X` is compactly
generated. -/
instance instUCompactlyGeneratedSpace
    [∀ d : D, UCompactlyGeneratedSpace.{v} (X.obj (op d) × K.obj d)] :
    UCompactlyGeneratedSpace.{v} (functorTensor K X) :=
  uCompactlyGeneratedSpace_of_coinduced (isQuotientMap_sigma K X).continuous
    (isQuotientMap_sigma K X).eq_coinduced

end Basic

section Desc

variable {K : D ⥤ TopCat.{u}} {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : Type*} [TopologicalSpace Z]
  (g : ∀ d, C(X.obj (op d) × K.obj d, Z))
  (hg : ∀ ⦃c d : D⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c),
    g c (X.map f.op x, t) = g d (x, K.map f t))

/-- The universal property of `functorTensor K X`: continuous maps `X(d) × K(d) → Z` compatible
with all morphisms of `D` descend to a continuous map `functorTensor K X → Z`. -/
def desc : C(functorTensor K X, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun d ↦ (g d).continuous)

@[simp]
theorem desc_ι (d : D) (p : X.obj (op d) × K.obj d) :
    desc g hg (ι K X d p) = g d p :=
  (rfl)

end Desc

section Map

variable (K : D ⥤ TopCat.{u}) {X Y : Dᵒᵖ ⥤ TopCat.{u}}

/-- The morphism of functor tensor products induced by a natural transformation `φ : X ⟶ Y`. -/
def map (φ : X ⟶ Y) : functorTensor K X ⟶ functorTensor K Y :=
  TopCat.ofHom <|
    desc (Z := functorTensor K Y) (fun d ↦ (ι K Y d).comp ((φ.app (op d)).hom.prodMap (.id _))) <|
      by
        intro c d f x t
        simp

@[simp]
theorem map_ι (φ : X ⟶ Y) (d : D) (x : X.obj (op d)) (t : K.obj d) :
    map K φ (ι K X d (x, t)) = ι K Y d (φ.app (op d) x, t) :=
  (rfl)

@[simp]
theorem map_id (X : Dᵒᵖ ⥤ TopCat.{u}) : map K (𝟙 X) = 𝟙 (functorTensor K X) := by
  ext; simp

@[simp]
theorem map_comp {W : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    map K (φ ≫ ψ) = map K φ ≫ map K ψ := by
  ext; simp

end Map

end functorTensor

/-- The functor tensor product with `K` as a functor `(Dᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u}`. -/
@[expose, simps]
def functorTensorFunctor (K : D ⥤ TopCat.{u}) : (Dᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj := functorTensor K
  map := functorTensor.map K

namespace functorTensor

section Reindex

variable {C : Type} [Category.{w'} C] (F : C ⥤ D) (K : D ⥤ TopCat.{u})

/-- Reindexing along a functor `F : C ⥤ D` induces a canonical comparison morphism from the
restricted functor tensor product over `C` to the functor tensor product over `D`. -/
def reindex (X : Dᵒᵖ ⥤ TopCat.{u}) :
    functorTensor (F ⋙ K) (F.op ⋙ X) ⟶ functorTensor K X :=
  TopCat.ofHom <| desc (fun c ↦ ι K X (F.obj c)) (fun _ _ f x t ↦ ι_map K X (F.map f) x t)

/-- `reindex F K X` sends each `c`-characteristic map to the `F.obj c`-characteristic map. -/
-- Simplify before the restricted functor-object types in the characteristic map are normalized.
@[simp↓]
theorem reindex_ι (X : Dᵒᵖ ⥤ TopCat.{u}) (c : C)
    (x : (F.op ⋙ X).obj (op c)) (t : (F ⋙ K).obj c) :
    reindex F K X (ι (F ⋙ K) (F.op ⋙ X) c (x, t)) = ι K X (F.obj c) (x, t) :=
  (rfl)

/-- When `F : C ⥤ D` is surjective on objects, `reindex F K X` is a quotient map. -/
theorem isQuotientMap_reindex (X : Dᵒᵖ ⥤ TopCat.{u}) (hF : Function.Surjective F.obj) :
    IsQuotientMap (reindex F K X) := by
  let σ : (Σ d : D, X.obj (op d) × K.obj d) → functorTensor (F ⋙ K) (F.op ⋙ X) :=
    fun ⟨d, x, t⟩ ↦
      ι (F ⋙ K) (F.op ⋙ X) (hF d).choose
        (X.map (eqToHom (hF d).choose_spec).op x,
          K.map (eqToHom (hF d).choose_spec.symm) t)
  have hσ : Continuous σ := continuous_sigma fun d ↦
    (ι (F ⋙ K) (F.op ⋙ X) (hF d).choose).continuous.comp
      (((X.map _).hom.continuous.comp continuous_fst).prodMk
        ((K.map _).hom.continuous.comp continuous_snd))
  have heq : (reindex F K X) ∘ σ = fun p ↦ ι K X p.1 p.2 := by
    funext ⟨d, x, t⟩
    simp only [Function.comp_apply, σ, reindex_ι]
    generalize (hF d).choose = c, (hF d).choose_spec = hcd
    subst hcd
    simp
  exact IsQuotientMap.of_comp hσ (reindex F K X).hom.continuous
    (heq.symm ▸ isQuotientMap_sigma K X)

private theorem whiskerLeft_op_app_op_apply {X Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (c : C)
    (x : (F.op ⋙ X).obj (op c)) :
    (Functor.whiskerLeft F.op φ).app (op c) x = φ.app (op (F.obj c)) x :=
  (rfl)

/-- Naturality of `reindex F K` with respect to morphisms `φ : X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem map_comp_reindex {X Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) :
    map (F ⋙ K) (Functor.whiskerLeft F.op φ) ≫ reindex F K Y = reindex F K X ≫ map K φ := by
  ext c x t
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, map_ι, reindex_ι, reindex_ι, map_ι,
    whiskerLeft_op_app_op_apply]

/-- Reindexing along the identity functor is the identity morphism. -/
@[simp]
theorem reindex_id (X : Dᵒᵖ ⥤ TopCat.{u}) :
    reindex (𝟭 D) K X = 𝟙 (functorTensor K X) :=
  hom_ext fun d x t ↦ (reindex_ι (𝟭 D) K X d x t).trans (CategoryTheory.id_apply _).symm

/-- Reindexing along a composite functor `G ⋙ F` factors as two reindexing morphisms. -/
theorem reindex_comp {B : Type} [Category B] (G : B ⥤ C) (X : Dᵒᵖ ⥤ TopCat.{u}) :
    reindex (G ⋙ F) K X = reindex G (F ⋙ K) (F.op ⋙ X) ≫ reindex F K X :=
  hom_ext fun b x t ↦
    (reindex_ι (G ⋙ F) K X b x t).trans <|
      (reindex_ι F K X (G.obj b) x t).symm.trans <|
        congrArg (reindex F K X) (reindex_ι G (F ⋙ K) (F.op ⋙ X) b x t).symm

end Reindex

section Augment

variable (K : D ⥤ TopCat.{u}) {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : TopCat.{u}}

/-- The morphism `functorTensor K X ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`, sending
`[x, t]` to `ε x`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) : functorTensor K X ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun d ↦ (ε.app (op d)).hom.comp ContinuousMap.fst) <| by
    intro c d f x t
    simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) (d : D) (x : X.obj (op d)) (t : K.obj d) :
    augment K ε (ι K X d (x, t)) = ε.app (op d) x :=
  (rfl)

/-- Pulling an augmentation back along `reindex F K X` recovers the augmentation of the restricted
diagram. -/
@[reassoc (attr := simp)]
theorem reindex_comp_augment {C : Type} [Category.{w'} C] (F : C ⥤ D) (K : D ⥤ TopCat.{u})
    (ε : X ⟶ (Functor.const _).obj Z) :
    reindex F K X ≫ augment K ε = augment (F ⋙ K) (Functor.whiskerLeft F.op ε) := by
  ext c x t
  rw [CategoryTheory.comp_apply, reindex_ι, augment_ι, augment_ι, whiskerLeft_op_app_op_apply]

/-- An augmentation restricts along `map K φ` to the augmentation by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) : map K φ ≫ augment K ε = augment K (φ ≫ ε) := by
  ext; simp

variable {K} in
/-- If an augmentation is a quotient map at an object `d` whose model space `K.obj d` is nonempty,
then the induced map `augment K ε` is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (d : D) [Nonempty (K.obj d)]
    (hε : IsQuotientMap (ε.app (op d))) : IsQuotientMap (augment K ε) := by
  obtain ⟨t⟩ := ‹Nonempty (K.obj d)›
  let j : X.obj (op d) → functorTensor K X := fun x ↦ ι K X d (x, t)
  have hj : Continuous j := (ι K X d).continuous.comp (continuous_id.prodMk continuous_const)
  have heq : (augment K ε) ∘ j = fun x ↦ ε.app (op d) x :=
    funext fun x ↦ augment_ι K ε d x t
  exact IsQuotientMap.of_comp hj (augment K ε).hom.continuous (heq.symm ▸ hε)

end Augment

section Homotopy

variable (K : D ⥤ TopCat.{u}) {X Y : Dᵒᵖ ⥤ TopCat.{u}}

/-- A family `φ s : X ⟶ Y` of natural transformations indexed by `s ∈ [0, 1]` and jointly
continuous in `s` and `X(d)` at every `d : D` induces a homotopy `(s, [x, t]) ↦ [φ s x, t]` from
`map K (φ 0)` to `map K (φ 1)`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ d : D, Continuous fun p : unitInterval × X.obj (op d) ↦ (φ p.1).app (op d) p.2) :
    ContinuousMap.Homotopy (map K (φ 0)).hom (map K (φ 1)).hom where
  toFun p := map K (φ p.1) p.2
  continuous_toFun := (isQuotientMap_sigma K X).continuous_lift_prod_right <| by
    have : Continuous fun q : Σ d : D, (X.obj (op d) × K.obj d) × unitInterval ↦
        ι K Y q.1 ((φ q.2.2).app (op q.1) q.2.1.1, q.2.1.2) :=
      continuous_sigma fun d ↦ (ι K Y d).continuous.comp <|
        ((hφ d).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst)
    exact (this.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)).congr
      fun ⟨_, d, x, t⟩ ↦ (map_ι K _ d x t).symm
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp]
theorem homotopy_apply_ι (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ d : D, Continuous fun p : unitInterval × X.obj (op d) ↦ (φ p.1).app (op d) p.2)
    (s : unitInterval) (d : D) (x : X.obj (op d)) (t : K.obj d) :
    homotopy K φ hφ (s, ι K X d (x, t)) = ι K Y d ((φ s).app (op d) x, t) :=
  (rfl)

end Homotopy

section Restriction

variable {K : D ⥤ TopCat.{u}} {X Y : Dᵒᵖ ⥤ TopCat.{u}}

variable (K) in
/-- The points of `functorTensor K X` in the image of `map K φ` are those of the form `[φ y, t]`. -/
theorem range_map (φ : Y ⟶ X) :
    range (map K φ) = {p | ∃ d y t, ι K X d (φ.app (op d) y, t) = p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
    exact ⟨d, y, t, rfl⟩
  · rintro ⟨d, y, t, rfl⟩
    exact ⟨ι K Y d (y, t), rfl⟩

variable {φ : Y ⟶ X}

section Saturated

variable (hinj : ∀ d, Function.Injective (φ.app d))
  (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
    X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c))

include hinj hsat

/-- Under levelwise injectivity and saturation, membership in the image of `W ⊆ functorTensor K Y`
lifts to a well-defined predicate on `functorTensor K X` detected in each degree. -/
private def liftPred (W : Set (functorTensor K Y)) : functorTensor K X → Prop :=
  Quot.lift (fun p ↦ ∃ y, φ.app (op p.1) y = p.2.1 ∧ ι K Y p.1 (y, p.2.2) ∈ W) <| by
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

private theorem liftPred_ι (W : Set (functorTensor K Y)) (d : D)
    (x : X.obj (op d)) (t : K.obj d) :
    liftPred hinj hsat W (ι K X d (x, t)) ↔ ∃ y, φ.app (op d) y = x ∧ ι K Y d (y, t) ∈ W :=
  Iff.rfl

private theorem liftPred_map_iff (W : Set (functorTensor K Y)) (q : functorTensor K Y) :
    liftPred hinj hsat W (map K φ q) ↔ q ∈ W := by
  obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
  exact ⟨fun ⟨y', hy', hW⟩ ↦ hinj _ hy' ▸ hW, fun hW ↦ ⟨y, rfl, hW⟩⟩

/-- If `φ : Y ⟶ X` is levelwise injective and saturated under morphisms of `Dᵒᵖ`, then `map K φ`
is injective. -/
theorem map_injective : Function.Injective (map K φ) := fun q q' h ↦
  ((liftPred_map_iff hinj hsat {q} q').1 (h ▸ (liftPred_map_iff hinj hsat {q} q).2 rfl)).symm

private theorem preimage_ι_image_map (W : Set (functorTensor K Y)) (d : D) :
    ι K X d ⁻¹' (map K φ '' W) = Prod.map (φ.app (op d)) id '' (ι K Y d ⁻¹' W) := by
  ext ⟨x, t⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨y, rfl, hyW⟩ :=
      (liftPred_ι hinj hsat W d x t).1 (hqx ▸ (liftPred_map_iff hinj hsat W q).2 hq)
    exact ⟨(y, t), hyW, rfl⟩
  · rintro ⟨⟨y, t'⟩, hyW, hyt⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyt
    exact ⟨ι K Y d (y, t'), hyW, rfl⟩

end Saturated

/-- **Open restriction.** If `φ : Y ⟶ X` is levelwise an open embedding and saturated under
morphisms of `Dᵒᵖ`, then `map K φ` is an open embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ d, IsOpenEmbedding (φ.app d))
    (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
      X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c)) :
    IsOpenEmbedding (map K φ) := by
  have hinj : ∀ d, Function.Injective (φ.app d) := fun d ↦ (hφ d).injective
  refine .of_continuous_injective_isOpenMap (map K φ).hom.continuous
    (map_injective hinj hsat) fun W hW ↦ isOpen_iff.2 fun d ↦ ?_
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op d)).prodMap .id).isOpenMap _ (isOpen_iff.1 hW d)

/-- **Closed restriction.** If `φ : Y ⟶ X` is levelwise a closed embedding and saturated under
morphisms of `Dᵒᵖ`, then `map K φ` is a closed embedding. -/
theorem isClosedEmbedding_map (hφ : ∀ d, IsClosedEmbedding (φ.app d))
    (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
      X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c)) :
    IsClosedEmbedding (map K φ) := by
  have hinj : ∀ d, Function.Injective (φ.app d) := fun d ↦ (hφ d).injective
  refine .of_continuous_injective_isClosedMap (map K φ).hom.continuous
    (map_injective hinj hsat) fun W hW ↦ isClosed_iff.2 fun d ↦ ?_
  rw [preimage_ι_image_map hinj hsat]
  exact ((hφ (op d)).prodMap .id).isClosedMap _ (isClosed_iff.1 hW d)

variable {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) {V : Set Z}

/-- If the image of `φ` at every object is the preimage of `V` under an augmentation `ε`, then the
preimage of `V` in `functorTensor K X` is the image of `map K φ`. -/
theorem preimage_augment_eq_range_map (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V) :
    augment K ε ⁻¹' V = range (map K φ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨d, x, t, rfl⟩ := ι_jointly_surjective K X p
    obtain ⟨y, rfl⟩ : x ∈ range (φ.app (op d)) := by rwa [hrange]
    exact ⟨ι K Y d (y, t), rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
    rw [mem_preimage, ← ConcreteCategory.comp_apply, map_comp_augment, augment_ι]
    exact (hrange (op d)).subset ⟨y, rfl⟩

/-- If the image of `φ` at every object is the preimage of `V` under an augmentation `ε`, then `φ`
is saturated under morphisms of `Dᵒᵖ`. -/
theorem mem_range_of_map_mem_range (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V)
    ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c) (hx : X.map f x ∈ range (φ.app d)) :
    x ∈ range (φ.app c) := by
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]
  simpa using hx

/-- If `φ` is levelwise an open embedding whose image is the preimage of `V` under an augmentation
`ε`, then `map K φ` is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ d, IsOpenEmbedding (φ.app d))
    (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V) : IsOpenEmbedding (map K φ) :=
  isOpenEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

/-- If `φ` is levelwise a closed embedding whose image is the preimage of `V` under an
augmentation `ε`, then `map K φ` is a closed embedding. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ d, IsClosedEmbedding (φ.app d))
    (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V) : IsClosedEmbedding (map K φ) :=
  isClosedEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

end Restriction

end functorTensor

end TauCeti
