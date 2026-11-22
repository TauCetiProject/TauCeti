/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Basic

/-!
# Functor tensor products (coends) in `TopCat`

For a `u`-small index category `D : Type u₁` (`[Small.{u} D]`, covering in particular any
`D : Type u₁` with `u₁ ≤ u`), `K : D ⥤ TopCat.{u}` and `X : Dᵒᵖ ⥤ TopCat.{u}`, their
*functor tensor product* (coend) `TauCeti.functorTensor K X` is the quotient of
`Σ d : D, X(d) × K(d)` by `(X(f) x, t) ∼ (x, K(f) t)` for all morphisms `f : c ⟶ d`, shrunk into
`Type u` with the quotient topology.

Specializing `(D, K)` yields `TauCeti.fatRealization` (`SemiSimplexCategory`),
`CategoryTheory.SimplicialObject.geometricRealization` (`SimplexCategory`), and
`CategoryTheory.SimplicialObject.geometricRealization.skeleton` (`SimplexCategory.Truncated k`),
while `TauCeti.functorTensor.reindex` yields the fat-to-thin comparison
(`CategoryTheory.SimplicialObject.fatToGeometricRealization`), skeletal transition maps, and
skeletal cocone legs
(`CategoryTheory.SimplicialObject.geometricRealization.skeleton.toRealization`).
The file establishes the generating relation and equality characterization (`Rel`, `ι`, `ι_eq_iff`),
the universal property (`lift`, `desc`, `fun_ext`, `continuousMap_ext`, `hom_ext`) and Mathlib coend
cowedge (`prodBifunctor`, `cowedge`, `isColimitCowedge`), functoriality (`map`,
`functorTensorFunctor`), quotient topology (`isQuotientMap_sigma`, `isQuotientMap_reindex`,
`isQuotientMap_augment`), `LindelofSpace` and `UCompactlyGeneratedSpace` instances, augmentations
(`augment`), homotopies (`homotopy`), and open/closed embeddings for saturated subfunctors
(`preimage_ι_image_map`, `isOpenEmbedding_map`, `isClosedEmbedding_map`).

## References

* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IX.6.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics **271**, §11.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

universe w w' w'' v u₁ u₂ u₃ u

namespace TauCeti

variable {D : Type u₁} [Category.{w} D]

/-- The generating coend identifications `(X(f) x, t) ∼ (x, K(f) t)` on `Σ d : D, X(d) × K(d)`. -/
inductive functorTensor.Rel (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) :
    (Σ d : D, X.obj (op d) × K.obj d) → (Σ d : D, X.obj (op d) × K.obj d) → Prop where
  | mk ⦃c d : D⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c) :
      functorTensor.Rel K X ⟨c, X.map f.op x, t⟩ ⟨d, x, K.map f t⟩

private instance instTopologicalSpaceShrinkQuot (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u})
    [Small.{u} D] : TopologicalSpace (Shrink.{u} (Quot (functorTensor.Rel K X))) :=
  TopologicalSpace.coinduced (equivShrink (Quot (functorTensor.Rel K X))) inferInstance

/-- The functor tensor product (coend) `∫^{d : D} X(d) × K(d)` of `K : D ⥤ TopCat.{u}` and
`X : Dᵒᵖ ⥤ TopCat.{u}`: the quotient of `Σ d : D, X(d) × K(d)` by `(X(f) x, t) ∼ (x, K(f) t)` for
all morphisms `f` of `D`, equipped with the quotient topology. -/
def functorTensor (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] : TopCat.{u} :=
  TopCat.of (Shrink.{u} (Quot (functorTensor.Rel K X)))

namespace functorTensor

section Basic

variable (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D]

private def quotHomeomorph : Quot (Rel K X) ≃ₜ functorTensor K X where
  toEquiv := equivShrink _
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_def.2 fun s hs ↦ by
    change IsOpen (equivShrink (Quot (Rel K X)) ⁻¹' ((equivShrink (Quot (Rel K X))).symm ⁻¹' s))
    rw [isOpen_coinduced, (equivShrink _).preimage_symm_preimage]
    exact hs

/-- The characteristic map `X(d) × K(d) → functorTensor K X` at `d : D`. -/
def ι (d : D) : C(X.obj (op d) × K.obj d, functorTensor K X) :=
  ⟨fun p ↦ quotHomeomorph K X (Quot.mk (Rel K X) ⟨d, p⟩),
    (quotHomeomorph K X).continuous.comp (continuous_quot_mk.comp continuous_sigmaMk)⟩

/-- The characteristic maps coequalize the contravariant action of `X` and the covariant action of
`K`. -/
@[simp]
theorem ι_map {c d : D} (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c) :
    ι K X c (X.map f.op x, t) = ι K X d (x, K.map f t) :=
  congrArg (quotHomeomorph K X) (Quot.sound (Rel.mk f x t))

/-- Two representatives in `Σ d, X(d) × K(d)` map to the same point of `functorTensor K X` iff
they are connected by a zigzag of generating coend identifications `Rel K X`. -/
theorem ι_eq_iff {c d : D} {x : X.obj (op c)} {t : K.obj c} {y : X.obj (op d)} {s : K.obj d} :
    ι K X c (x, t) = ι K X d (y, s) ↔ Relation.EqvGen (Rel K X) ⟨c, x, t⟩ ⟨d, y, s⟩ :=
  (quotHomeomorph K X).injective.eq_iff.trans Quot.eq

/-- Every point of `functorTensor K X` lies in the image of a characteristic map. -/
theorem ι_jointly_surjective (p : functorTensor K X) : ∃ d x t, ι K X d (x, t) = p := by
  obtain ⟨q, hq⟩ := (quotHomeomorph K X).surjective p
  obtain ⟨⟨d, x, t⟩⟩ := q
  exact ⟨d, x, t, hq⟩

/-- `functorTensor K X` carries the quotient topology of `Σ d : D, X(d) × K(d)`. -/
theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ d : D, X.obj (op d) × K.obj d ↦ ι K X p.fst p.snd :=
  (quotHomeomorph K X).isQuotientMap.comp isQuotientMap_quot_mk

variable {K X}

/-- A set in `functorTensor K X` is open iff its preimage under every characteristic map is
open. -/
theorem isOpen_iff {s : Set (functorTensor K X)} : IsOpen s ↔ ∀ d, IsOpen (ι K X d ⁻¹' s) := by
  rw [← (isQuotientMap_sigma K X).isOpen_preimage, isOpen_sigma_iff]
  -- `ι K X d` is `(quotHomeomorph K X) ∘ (Quot.mk _) ∘ Sigma.mk d` by definition.
  rfl

/-- A set in `functorTensor K X` is closed iff its preimage under every characteristic map is
closed. -/
theorem isClosed_iff {s : Set (functorTensor K X)} :
    IsClosed s ↔ ∀ d, IsClosed (ι K X d ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of `functorTensor K X` is continuous iff its composite with every characteristic map
is continuous. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : functorTensor K X → Z} :
    Continuous g ↔ ∀ d, Continuous (g ∘ ι K X d) := by
  rw [(isQuotientMap_sigma K X).continuous_iff, continuous_sigma_iff]
  -- `ι K X d` is `(quotHomeomorph K X) ∘ (Quot.mk _) ∘ Sigma.mk d` by definition.
  rfl

/-- Two functions out of `functorTensor K X` agree once they agree on every characteristic map. -/
theorem fun_ext {Z : Sort*} {g h : functorTensor K X → Z}
    (H : ∀ d x t, g (ι K X d (x, t)) = h (ι K X d (x, t))) : g = h :=
  funext fun p ↦ by obtain ⟨d, x, t, rfl⟩ := ι_jointly_surjective K X p; exact H d x t

/-- Two continuous maps out of `functorTensor K X` agree once they agree on every characteristic
map. -/
@[ext]
theorem continuousMap_ext {Z : Type*} [TopologicalSpace Z] {g h : C(functorTensor K X, Z)}
    (H : ∀ d x t, g (ι K X d (x, t)) = h (ι K X d (x, t))) : g = h :=
  ContinuousMap.coe_injective (fun_ext H)

/-- Two morphisms out of `functorTensor K X` agree once they agree on every characteristic map. -/
@[ext]
theorem hom_ext {Z : TopCat.{u}} {g h : functorTensor K X ⟶ Z}
    (H : ∀ d x t, g (ι K X d (x, t)) = h (ι K X d (x, t))) : g = h :=
  TopCat.hom_ext (continuousMap_ext H)

variable (K X) in
/-- If `D` is countable and each `X(d) × K(d)` is Lindelöf, then `functorTensor K X` is
Lindelöf. -/
instance instLindelofSpace [Countable D] [∀ d : D, LindelofSpace (X.obj (op d) × K.obj d)] :
    LindelofSpace (functorTensor K X) :=
  LindelofSpace.of_continuous_surjective (isQuotientMap_sigma K X).continuous
    (isQuotientMap_sigma K X).surjective

variable (K X) in
/-- If each `X(d) × K(d)` is compactly generated, then `functorTensor K X` is compactly
generated. -/
instance instUCompactlyGeneratedSpace
    [∀ d : D, UCompactlyGeneratedSpace.{v} (X.obj (op d) × K.obj d)] :
    UCompactlyGeneratedSpace.{v} (functorTensor K X) :=
  uCompactlyGeneratedSpace_of_coinduced (isQuotientMap_sigma K X).continuous
    (isQuotientMap_sigma K X).eq_coinduced

end Basic

section Lift

variable {K : D ⥤ TopCat.{u}} {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : Sort*}
  (g : ∀ d, X.obj (op d) × K.obj d → Z)
  (hg : ∀ ⦃c d : D⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c),
    g c (X.map f.op x, t) = g d (x, K.map f t)) [Small.{u} D]

/-- The universal property of the underlying set of `functorTensor K X`: compatible maps on
`X(d) × K(d)` descend to a function on `functorTensor K X`. -/
def lift : functorTensor K X → Z :=
  Quot.lift (fun p ↦ g p.fst p.snd) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t) ∘
    (quotHomeomorph K X).symm

@[simp]
theorem lift_ι (d : D) (p : X.obj (op d) × K.obj d) : lift g hg (ι K X d p) = g d p := by
  dsimp [lift, ι]
  rw [Homeomorph.symm_apply_apply]

end Lift

section Desc

variable {K : D ⥤ TopCat.{u}} {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : Type*} [TopologicalSpace Z]
  (g : ∀ d, C(X.obj (op d) × K.obj d, Z))
  (hg : ∀ ⦃c d : D⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : K.obj c),
    g c (X.map f.op x, t) = g d (x, K.map f t)) [Small.{u} D]

/-- The universal property of `functorTensor K X`: compatible continuous maps `X(d) × K(d) → Z`
descend to a continuous map `functorTensor K X → Z`. -/
def desc : C(functorTensor K X, Z) where
  toFun := lift (fun d ↦ g d) hg
  continuous_toFun := continuous_iff.2 fun d ↦
    ((g d).continuous).congr fun p ↦ (lift_ι (fun d ↦ ⇑(g d)) hg d p).symm

@[simp]
theorem desc_ι (d : D) (p : X.obj (op d) × K.obj d) : desc g hg (ι K X d p) = g d p := by
  dsimp [desc]
  exact lift_ι _ _ d p

end Desc

section Coend

variable (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u})

/-- The product bifunctor `Dᵒᵖ ⥤ D ⥤ TopCat.{u}` sending `(c, d)` to `X(c) × K(d)`. -/
@[expose, simps]
def prodBifunctor : Dᵒᵖ ⥤ D ⥤ TopCat.{u} where
  obj c :=
    { obj := fun d ↦ TopCat.of (X.obj c × K.obj d)
      map := fun f ↦ TopCat.ofHom ((ContinuousMap.id _).prodMap (K.map f).hom) }
  map f :=
    { app := fun _ ↦ TopCat.ofHom ((X.map f).hom.prodMap (ContinuousMap.id _)) }

variable [Small.{u} D]

/-- The characteristic maps `X(d) × K(d) ⟶ functorTensor K X` packaged as a cowedge for
`prodBifunctor K X`. -/
@[expose]
def cowedge : Limits.Cowedge (prodBifunctor K X) :=
  Limits.Cowedge.mk (functorTensor K X) (fun d ↦ TopCat.ofHom (ι K X d)) fun _ _ f ↦ by
    ext ⟨x, t⟩
    exact ι_map K X f x t

@[simp]
theorem cowedge_π (d : D) : (cowedge K X).π d = TopCat.ofHom (ι K X d) := (rfl)

/-- The cowedge `cowedge K X` exhibits `functorTensor K X` as a coend of `prodBifunctor K X` in
`TopCat`. -/
def isColimitCowedge : Limits.IsColimit (cowedge K X) :=
  let descMap (s : Limits.Cowedge (prodBifunctor K X)) : functorTensor K X ⟶ s.pt :=
    TopCat.ofHom <| desc (fun d : D ↦ (Limits.Multicofork.π s d).hom) fun _ _ f x t ↦
      ConcreteCategory.congr_hom (Limits.Cowedge.condition s f) (x, t)
  Limits.Multicofork.IsColimit.mk (cowedge K X) descMap
    (fun s (d : D) ↦ TopCat.hom_ext <| ContinuousMap.ext fun p ↦ by
      have hp : desc (fun d : D ↦ (Limits.Multicofork.π s d).hom)
          (fun _ _ f x t ↦ ConcreteCategory.congr_hom (Limits.Cowedge.condition s f) (x, t))
          (ι K X d p) = (Limits.Multicofork.π s d).hom p :=
        desc_ι _ _ d p
      exact hp)
    (fun s m hm ↦ hom_ext fun d x t ↦ by
      have h : m (ι K X d (x, t)) = (Limits.Multicofork.π s d) (x, t) :=
        ConcreteCategory.congr_hom (hm d) (x, t)
      have hd : descMap s (ι K X d (x, t)) = (Limits.Multicofork.π s d) (x, t) :=
        desc_ι (fun d : D ↦ (Limits.Multicofork.π s d).hom) _ d (x, t)
      exact h.trans hd.symm)

end Coend

section Map

variable (K : D ⥤ TopCat.{u}) {X Y : Dᵒᵖ ⥤ TopCat.{u}}

/-- The morphism of functor tensor products induced by a natural transformation `φ : X ⟶ Y`. -/
def map (φ : X ⟶ Y) [Small.{u} D] : functorTensor K X ⟶ functorTensor K Y :=
  TopCat.ofHom <|
    desc (Z := functorTensor K Y) (fun d ↦ (ι K Y d).comp ((φ.app (op d)).hom.prodMap (.id _)))
      fun _ _ _ _ _ ↦ by simp

@[simp]
theorem map_ι (φ : X ⟶ Y) [Small.{u} D] (d : D) (x : X.obj (op d)) (t : K.obj d) :
    map K φ (ι K X d (x, t)) = ι K Y d (φ.app (op d) x, t) := by
  change desc _ _ (ι K X d (x, t)) = _
  rw [desc_ι]
  rfl

@[simp]
theorem map_id (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] :
    map K (𝟙 X) = 𝟙 (functorTensor K X) := by ext; simp

@[simp]
theorem map_comp {W : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ W) [Small.{u} D] :
    map K (φ ≫ ψ) = map K φ ≫ map K ψ := by ext; simp

end Map

end functorTensor

/-- The functor tensor product with `K` as a functor `(Dᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u}`. -/
def functorTensorFunctor (K : D ⥤ TopCat.{u}) [Small.{u} D] :
    (Dᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj X := functorTensor K X
  map φ := functorTensor.map K φ

@[simp]
theorem functorTensorFunctor_obj (K : D ⥤ TopCat.{u}) [Small.{u} D] (X : Dᵒᵖ ⥤ TopCat.{u}) :
    (functorTensorFunctor K).obj X = functorTensor K X :=
  -- `(rfl)`, not `rfl`: the body of `functorTensorFunctor` is not `@[expose]`d.
  (rfl)

@[simp]
theorem functorTensorFunctor_map (K : D ⥤ TopCat.{u}) [Small.{u} D]
    {X Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) :
    (functorTensorFunctor K).map φ =
      eqToHom (functorTensorFunctor_obj K X) ≫
        functorTensor.map K φ ≫
          eqToHom (functorTensorFunctor_obj K Y).symm := by
  apply (conj_eqToHom_iff_heq _ _ (functorTensorFunctor_obj K X)
    (functorTensorFunctor_obj K Y)).2
  rw [functorTensorFunctor.eq_def]

namespace functorTensor

section Reindex

section

variable {C : Type u₂} [Category.{w'} C] (F : C ⥤ D) (K : D ⥤ TopCat.{u})

/-- Reindexing along `F : C ⥤ D` induces a canonical comparison morphism from the restricted
functor tensor product over `C` to that over `D`. -/
def reindex (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] [Small.{u} C] :
    functorTensor (F ⋙ K) (F.op ⋙ X) ⟶ functorTensor K X :=
  TopCat.ofHom <| desc (fun c ↦ ι K X (F.obj c)) (fun _ _ f x t ↦ ι_map K X (F.map f) x t)

/-- `reindex F K X` sends each `c`-characteristic map to the `F.obj c`-characteristic map. -/
-- Simplify before the restricted functor-object types in the characteristic map are normalized.
@[simp↓]
theorem reindex_ι (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] [Small.{u} C] (c : C)
    (x : (F.op ⋙ X).obj (op c)) (t : (F ⋙ K).obj c) :
    reindex F K X (ι (F ⋙ K) (F.op ⋙ X) c (x, t)) = ι K X (F.obj c) (x, t) := by
  change desc _ _ (ι (F ⋙ K) (F.op ⋙ X) c (x, t)) = _
  exact desc_ι _ _ c (x, t)

/-- When `F : C ⥤ D` is surjective on objects, `reindex F K X` is a quotient map. -/
theorem isQuotientMap_reindex (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] [Small.{u} C]
    (hF : Function.Surjective F.obj) :
    IsQuotientMap (reindex F K X) := by
  let σ : (Σ d : D, X.obj (op d) × K.obj d) → functorTensor (F ⋙ K) (F.op ⋙ X) :=
    fun ⟨d, x, t⟩ ↦ ι (F ⋙ K) (F.op ⋙ X) (hF d).choose
      (X.map (eqToHom (hF d).choose_spec).op x, K.map (eqToHom (hF d).choose_spec.symm) t)
  refine IsQuotientMap.of_comp (f := σ) (continuous_sigma fun d ↦ (ι _ _ _).continuous.comp
    (((X.map _).hom.continuous.comp continuous_fst).prodMk
      ((K.map _).hom.continuous.comp continuous_snd))) (reindex F K X).hom.continuous ?_
  have heq : (reindex F K X) ∘ σ = fun p ↦ ι K X p.fst p.snd := funext fun ⟨d, x, t⟩ ↦ by
    simp only [Function.comp_apply, σ, reindex_ι]
    generalize (hF d).choose = c, (hF d).choose_spec = hcd; subst hcd; simp
  exact heq.symm ▸ isQuotientMap_sigma K X

private theorem whiskerLeft_op_app_op_apply {X Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) (c : C)
    (x : (F.op ⋙ X).obj (op c)) :
    (Functor.whiskerLeft F.op φ).app (op c) x = φ.app (op (F.obj c)) x := (rfl)

/-- Naturality of `reindex F K` with respect to morphisms `φ : X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem map_comp_reindex {X Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : X ⟶ Y) [Small.{u} D] [Small.{u} C] :
    map (F ⋙ K) (Functor.whiskerLeft F.op φ) ≫ reindex F K Y = reindex F K X ≫ map K φ := by
  ext c x t
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, map_ι, reindex_ι, reindex_ι, map_ι,
    whiskerLeft_op_app_op_apply]

end

/-- Reindexing along the identity functor is the identity morphism. -/
@[simp]
theorem reindex_id (K : D ⥤ TopCat.{u}) (X : Dᵒᵖ ⥤ TopCat.{u}) [Small.{u} D] :
    reindex (𝟭 D) K X = 𝟙 (functorTensor K X) :=
  hom_ext fun d x t ↦ (reindex_ι (𝟭 D) K X d x t).trans (CategoryTheory.id_apply _).symm

/-- Reindexing along a composite functor `G ⋙ F` factors as two reindexing morphisms. -/
theorem reindex_comp {C : Type u₂} [Category.{w'} C] (F : C ⥤ D) (K : D ⥤ TopCat.{u})
    {B : Type u₃} [Category.{w''} B] (G : B ⥤ C) (X : Dᵒᵖ ⥤ TopCat.{u})
    [Small.{u} D] [Small.{u} C] [Small.{u} B] :
    reindex (G ⋙ F) K X = reindex G (F ⋙ K) (F.op ⋙ X) ≫ reindex F K X :=
  hom_ext fun b x t ↦ by
    rw [CategoryTheory.comp_apply]
    exact (reindex_ι (G ⋙ F) K X b x t).trans
      ((reindex_ι F K X (G.obj b) x t).symm.trans
        (congrArg (reindex F K X) (reindex_ι G (F ⋙ K) (F.op ⋙ X) b x t).symm))

end Reindex

section Augment

section

variable (K : D ⥤ TopCat.{u}) {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : TopCat.{u}}

/-- The morphism `functorTensor K X ⟶ Z` induced by an augmentation `ε : X ⟶ const Z`. -/
def augment (ε : X ⟶ (Functor.const _).obj Z) [Small.{u} D] : functorTensor K X ⟶ Z :=
  TopCat.ofHom <| desc (Z := Z) (fun d ↦ (ε.app (op d)).hom.comp ContinuousMap.fst)
    fun _ _ _ _ _ ↦ by simp

@[simp]
theorem augment_ι (ε : X ⟶ (Functor.const _).obj Z) [Small.{u} D]
    (d : D) (x : X.obj (op d)) (t : K.obj d) :
    augment K ε (ι K X d (x, t)) = ε.app (op d) x := by
  change desc _ _ (ι K X d (x, t)) = _
  rw [desc_ι]
  rfl

/-- An augmentation restricts along `map K φ` to the augmentation by `φ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem map_comp_augment {Y : Dᵒᵖ ⥤ TopCat.{u}} (φ : Y ⟶ X)
    (ε : X ⟶ (Functor.const _).obj Z) [Small.{u} D] :
    map K φ ≫ augment K ε = augment K (φ ≫ ε) := by ext; simp

variable {K} in
/-- If an augmentation is a quotient map at an object `d` with nonempty `K.obj d`, then
`augment K ε` is a quotient map. -/
theorem isQuotientMap_augment (ε : X ⟶ (Functor.const _).obj Z) (d : D) [Small.{u} D]
    [Nonempty (K.obj d)] (hε : IsQuotientMap (ε.app (op d))) : IsQuotientMap (augment K ε) := by
  obtain ⟨t⟩ := ‹Nonempty (K.obj d)›
  have heq : ((augment K ε) ∘ ι K X d ∘ fun x ↦ (x, t)) = ε.app (op d) :=
    funext fun x ↦ augment_ι K ε d x t
  exact IsQuotientMap.of_comp ((ι K X d).continuous.comp (.prodMk_left t))
    (augment K ε).hom.continuous (heq ▸ hε)

end

/-- Pulling an augmentation back along `reindex F K X` recovers the restricted augmentation. -/
@[reassoc (attr := simp)]
theorem reindex_comp_augment {C : Type u₂} [Category.{w'} C] (F : C ⥤ D)
    (K : D ⥤ TopCat.{u}) {X : Dᵒᵖ ⥤ TopCat.{u}} {Z : TopCat.{u}}
    (ε : X ⟶ (Functor.const _).obj Z) [Small.{u} D] [Small.{u} C] :
    reindex F K X ≫ augment K ε = augment (F ⋙ K) (Functor.whiskerLeft F.op ε) := by
  ext c x t
  rw [CategoryTheory.comp_apply, reindex_ι, augment_ι, augment_ι, whiskerLeft_op_app_op_apply]

end Augment

section Homotopy

variable (K : D ⥤ TopCat.{u}) {X Y : Dᵒᵖ ⥤ TopCat.{u}}

/-- A levelwise jointly continuous `[0, 1]`-family of natural transformations `φ s : X ⟶ Y` induces
a homotopy `(s, [x, t]) ↦ [φ s x, t]` from `map K (φ 0)` to `map K (φ 1)`. -/
def homotopy (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ d : D,
      Continuous fun p : unitInterval × X.obj (op d) ↦ (φ p.fst).app (op d) p.snd)
    [Small.{u} D] :
    ContinuousMap.Homotopy (map K (φ 0)).hom (map K (φ 1)).hom where
  toFun p := map K (φ p.fst) p.snd
  continuous_toFun := (isQuotientMap_sigma K X).continuous_lift_prod_right <| by
    have : Continuous fun q : Σ d : D, (X.obj (op d) × K.obj d) × unitInterval ↦
        ι K Y q.fst ((φ q.snd.snd).app (op q.fst) q.snd.fst.fst, q.snd.fst.snd) :=
      continuous_sigma fun d ↦ (ι K Y d).continuous.comp <|
        ((hφ d).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst)
    exact (this.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)).congr
      fun ⟨_, d, x, t⟩ ↦ (map_ι K _ d x t).symm
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp]
theorem homotopy_apply_ι (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ d : D,
      Continuous fun p : unitInterval × X.obj (op d) ↦ (φ p.fst).app (op d) p.snd)
    [Small.{u} D] (s : unitInterval) (d : D) (x : X.obj (op d)) (t : K.obj d) :
    homotopy K φ hφ (s, ι K X d (x, t)) = ι K Y d ((φ s).app (op d) x, t) :=
  map_ι K (φ s) d x t

end Homotopy

section Restriction

variable {K : D ⥤ TopCat.{u}} {X Y : Dᵒᵖ ⥤ TopCat.{u}}

variable (K) in
/-- The points of `functorTensor K X` in the image of `map K φ` are those of the form `[φ y, t]`. -/
theorem range_map (φ : Y ⟶ X) [Small.{u} D] :
    range (map K φ) = {p | ∃ d y t, ι K X d (φ.app (op d) y, t) = p} := by
  ext p
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun ⟨d, y, t, h⟩ ↦ ?_⟩
  · obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
    exact ⟨d, y, t, (map_ι K φ d y t).symm.trans hq⟩
  · exact ⟨ι K Y d (y, t), (map_ι K φ d y t).trans h⟩

variable {φ : Y ⟶ X}

section Saturated

variable (hinj : ∀ d, Function.Injective (φ.app d))
  (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
    X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c)) [Small.{u} D]

include hinj hsat

private def liftPred (W : Set (functorTensor K Y)) : functorTensor K X → Prop :=
  lift (fun d p ↦ ∃ y, φ.app (op d) y = p.fst ∧ ι K Y d (y, p.snd) ∈ W) <| by
    intro c d f x t
    refine propext ⟨?_, fun ⟨y, hy, hW⟩ ↦
      ⟨Y.map f.op y, (NatTrans.naturality_apply φ f.op y).trans (congrArg (X.map f.op) hy),
        by rwa [ι_map]⟩⟩
    rintro ⟨y', hy', hW⟩
    obtain ⟨y, rfl⟩ := hsat f.op x ⟨y', hy'⟩
    have hyeq : y' = Y.map f.op y :=
      hinj _ (hy'.trans (NatTrans.naturality_apply φ f.op y).symm)
    exact ⟨y, rfl, by rwa [← ι_map, ← hyeq]⟩

private theorem liftPred_ι (W : Set (functorTensor K Y)) (d : D) (x : X.obj (op d)) (t : K.obj d) :
    liftPred hinj hsat W (ι K X d (x, t)) ↔
      ∃ y, φ.app (op d) y = x ∧ ι K Y d (y, t) ∈ W := by
  dsimp [liftPred]
  rw [lift_ι]

private theorem liftPred_map_iff (W : Set (functorTensor K Y)) (q : functorTensor K Y) :
    liftPred hinj hsat W (map K φ q) ↔ q ∈ W := by
  obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
  rw [map_ι, liftPred_ι]
  exact ⟨fun ⟨y', hy', hW⟩ ↦ hinj _ hy' ▸ hW, fun hW ↦ ⟨y, rfl, hW⟩⟩

/-- If `φ : Y ⟶ X` is levelwise injective and saturated under morphisms of `Dᵒᵖ`, then `map K φ`
is injective. -/
theorem map_injective : Function.Injective (map K φ) := fun q q' h ↦
  ((liftPred_map_iff hinj hsat {q} q').1 (h ▸ (liftPred_map_iff hinj hsat {q} q).2 rfl)).symm

/-- The preimage of the image of `W` under a levelwise injective, saturated map `map K φ` in each
characteristic chart is the image of the chart preimage under `φ.app (op d) × id`. -/
theorem preimage_ι_image_map (W : Set (functorTensor K Y)) (d : D) :
    ι K X d ⁻¹' (map K φ '' W) = Prod.map (φ.app (op d)) id '' (ι K Y d ⁻¹' W) := by
  ext ⟨x, t⟩
  refine ⟨fun ⟨q, hq, hqx⟩ ↦ ?_, fun ⟨⟨y, t'⟩, hyW, hyt⟩ ↦ ?_⟩
  · obtain ⟨y, hy, hyW⟩ := (liftPred_ι hinj hsat W d x t).1
      (hqx ▸ (liftPred_map_iff hinj hsat W q).2 hq)
    exact ⟨(y, t), hyW, Prod.ext hy rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyt
    exact ⟨ι K Y d (y, t'), hyW, map_ι K φ d y t'⟩

end Saturated

/-- **Open restriction.** If `φ : Y ⟶ X` is levelwise an open embedding and saturated under
morphisms of `Dᵒᵖ`, then `map K φ` is an open embedding. -/
theorem isOpenEmbedding_map (hφ : ∀ d, IsOpenEmbedding (φ.app d))
    (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
      X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c)) [Small.{u} D] :
    IsOpenEmbedding (map K φ) :=
  .of_continuous_injective_isOpenMap (map K φ).hom.continuous
    (map_injective (fun d ↦ (hφ d).injective) hsat) fun W hW ↦ isOpen_iff.2 fun d ↦
      preimage_ι_image_map (fun d ↦ (hφ d).injective) hsat W d ▸
        ((hφ (op d)).prodMap .id).isOpenMap _ (isOpen_iff.1 hW d)

/-- **Closed restriction.** If `φ : Y ⟶ X` is levelwise a closed embedding and saturated under
morphisms of `Dᵒᵖ`, then `map K φ` is a closed embedding. -/
theorem isClosedEmbedding_map (hφ : ∀ d, IsClosedEmbedding (φ.app d))
    (hsat : ∀ ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c),
      X.map f x ∈ range (φ.app d) → x ∈ range (φ.app c)) [Small.{u} D] :
    IsClosedEmbedding (map K φ) :=
  .of_continuous_injective_isClosedMap (map K φ).hom.continuous
    (map_injective (fun d ↦ (hφ d).injective) hsat) fun W hW ↦ isClosed_iff.2 fun d ↦
      preimage_ι_image_map (fun d ↦ (hφ d).injective) hsat W d ▸
        ((hφ (op d)).prodMap .id).isClosedMap _ (isClosed_iff.1 hW d)

variable {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) {V : Set Z}

/-- If the image of `φ` at every object is the preimage of `V` under `ε`, then the preimage of `V`
in `functorTensor K X` is the image of `map K φ`. -/
theorem preimage_augment_eq_range_map (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V)
    [Small.{u} D] :
    augment K ε ⁻¹' V = range (map K φ) := by
  ext p
  refine ⟨fun hp ↦ ?_, fun ⟨q, hq⟩ ↦ ?_⟩
  · obtain ⟨d, x, t, rfl⟩ := ι_jointly_surjective K X p
    obtain ⟨y, rfl⟩ : x ∈ range (φ.app (op d)) := by rw [hrange]; simpa using hp
    exact ⟨ι K Y d (y, t), map_ι K φ d y t⟩
  · subst hq; obtain ⟨d, y, t, rfl⟩ := ι_jointly_surjective K Y q
    rw [mem_preimage, map_ι, augment_ι]
    exact (hrange (op d)).subset ⟨y, rfl⟩

/-- If the image of `φ` at every object is the preimage of `V` under an augmentation `ε`, then `φ`
is saturated under morphisms of `Dᵒᵖ`. -/
theorem mem_range_of_map_mem_range (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V)
    ⦃c d : Dᵒᵖ⦄ (f : c ⟶ d) (x : X.obj c) (hx : X.map f x ∈ range (φ.app d)) :
    x ∈ range (φ.app c) := by
  rw [hrange, mem_preimage, NatTrans.naturality_apply] at hx
  rw [hrange]; simpa using hx

/-- If `φ` is levelwise an open embedding with `range (φ.app d) = ε.app d ⁻¹' V`, then `map K φ`
is an open embedding. -/
theorem isOpenEmbedding_map_of_range_eq_preimage (hφ : ∀ d, IsOpenEmbedding (φ.app d))
    (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V) [Small.{u} D] :
    IsOpenEmbedding (map K φ) :=
  isOpenEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

/-- If `φ` is levelwise a closed embedding with `range (φ.app d) = ε.app d ⁻¹' V`, then `map K φ`
is a closed embedding. -/
theorem isClosedEmbedding_map_of_range_eq_preimage (hφ : ∀ d, IsClosedEmbedding (φ.app d))
    (hrange : ∀ d, range (φ.app d) = ε.app d ⁻¹' V) [Small.{u} D] :
    IsClosedEmbedding (map K φ) :=
  isClosedEmbedding_map hφ (mem_range_of_map_mem_range ε hrange)

end Restriction

end functorTensor

end TauCeti
