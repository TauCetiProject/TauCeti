/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Slice

/-!
# Coslices of simplicial sets

For a simplicial set `C` and a diagram `p : K ⟶ C`, the coslice `C_{p/}` is the simplicial set
whose `n`-simplices are the maps `K ⋆ Δ[n] ⟶ C` from the join that restrict to `p` on `K`. Its
vertices are the cocones under `p`, with cone point the image of `Δ[0]`, and its edges are
morphisms of cocones. A colimit of `p` in a quasicategory is an initial object of `C_{p/}`, and for
a vertex `y` of `C` the coslice under `y : Δ[0] ⟶ C` is the quasicategory of objects under `y`,
through which finality of maps into `C` is tested.

The coslice is dual to the slice `C_{/p}` of `SSet.slice`: it is defined as the opposite
`(Cᵒᵖ_{/pᵒᵖ})ᵒᵖ`, and its universal property (`SSet.coslice.homEquiv`), maps `X ⟶ C_{p/}`
correspond to maps `K ⋆ X ⟶ C` extending `p`, naturally in `X`, is deduced from that of the slice
through the isomorphism `(K ⋆ X)ᵒᵖ ≅ Xᵒᵖ ⋆ Kᵒᵖ` (`SSet.join.opIso`).

For the inclusion of a vertex `x : Δ[0] ⟶ C`, the fibre `{x} ×_C C_{y/}` over a vertex `y` of the
projection from the coslice under `y` is the left mapping space `Hom^L_C(y, x)`: maps to it are the
maps `Δ[0] ⋆ Z ⟶ C` sending the cone point to `y` and `Z` to `x`, and its vertices are the edges
from `y` to `x`. If `C` is strict Segal, for instance the nerve of a category, it is the discrete
simplicial set on these edges.

## Main definitions

* `SSet.coslice.functor p`: the maps `K ⋆ X ⟶ C` extending `p`, as a presheaf in `X`.
* `SSet.coslice p`: the coslice `C_{p/}`, whose simplices are described by `SSet.coslice.objEquiv`.
* `SSet.coslice.π p`: the projection `C_{p/} ⟶ C`, restricting a simplex `K ⋆ Δ[n] ⟶ C` to
  `Δ[n]`.
* `SSet.coslice.map i g h`: the map of coslices `C_{p/} ⟶ D_{q/}` induced by `i : L ⟶ K` and
  `g : C ⟶ D` with `i ≫ p ≫ g = q`, restricting along `i` and composing with `g`; it is functorial
  (`SSet.coslice.map_id`, `SSet.coslice.map_comp`).
* `SSet.coslice.pullbackConstHomEquiv x y`: maps to the fibre `{x} ×_C C_{y/}` are the maps
  `Δ[0] ⋆ Z ⟶ C` sending the cone point to `y` and `Z` to `x`.
* `SSet.coslice.pullbackConstObj₀Equiv x y`: the vertices of this fibre are the edges from `y`
  to `x`.
* `SSet.coslice.constEdgeIso x y`: for a strict Segal `C`, this fibre is the discrete simplicial
  set on the edges from `y` to `x`.
* `SSet.coslice.opSliceIso p`: the identification of `C_{p/}` with `(Cᵒᵖ_{/pᵒᵖ})ᵒᵖ`.

## Main results

* `SSet.coslice.homEquiv`: **the universal property of the coslice**, maps `X ⟶ C_{p/}` correspond
  to maps `K ⋆ X ⟶ C` extending `p`, naturally in `X` (`SSet.coslice.homEquiv_comp_coe`); that is,
  `C_{p/}` represents `SSet.coslice.functor p` (`SSet.coslice.representableBy`).
* `SSet.coslice.objEquiv_app_coe`: the simplices of the image of a map `F : X ⟶ C_{p/}` are the
  restrictions of the corresponding map `K ⋆ X ⟶ C`.
* `SSet.coslice.comp_π`: under the universal property, the projection to `C` is the restriction to
  `X`.
* `SSet.coslice.isIso_π`: the coslice under the empty diagram is the whole simplicial set.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (left mapping spaces) and §1.2.9.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X Y K C : SSet.{u}}

variable (p : K ⟶ C)

namespace coslice

/-- The maps `K ⋆ X ⟶ C` extending `p : K ⟶ C` along the inclusion `K ⟶ K ⋆ X`, as a presheaf on
simplicial sets, acting by precomposition with `K ⋆ g`. -/
@[expose]
def functor : SSet.{u}ᵒᵖ ⥤ Type u where
  obj X := {τ : join K X.unop ⟶ C // join.inl K X.unop ≫ τ = p}
  map g := ↾fun τ ↦ ⟨join.map (𝟙 K) g.unop ≫ τ.1, by rw [join.inl_map_assoc, Category.id_comp, τ.2]⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    exact (congrArg (· ≫ τ.1) join.map_id).trans (Category.id_comp _)
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    refine (congrArg (· ≫ τ.1) ?_).trans (Category.assoc _ _ _)
    simpa using join.map_comp (𝟙 K) g.unop (𝟙 K) f.unop

@[simp]
lemma functor_map_coe {X Y : SSet.{u}ᵒᵖ} (g : X ⟶ Y) (τ : (functor p).obj X) :
    ((functor p).map g τ).1 = join.map (𝟙 K) g.unop ≫ τ.1 :=
  (rfl)

end coslice

/-- The coslice `C_{p/}` of a simplicial set `C` under a diagram `p : K ⟶ C`. Its `n`-simplices are
the maps `K ⋆ Δ[n] ⟶ C` extending `p` along the inclusion of `K` (`SSet.coslice.objEquiv`); in
particular its vertices are the cocones `K ⋆ Δ[0] ⟶ C` under `p`. It is defined as the opposite of
the slice `Cᵒᵖ_{/pᵒᵖ}`. -/
def coslice : SSet.{u} :=
  (slice (opFunctor.map p)).op

namespace coslice

/-- The coslice `C_{p/}` is the opposite of the slice `Cᵒᵖ_{/pᵒᵖ}`. Through this isomorphism,
statements about the coslice are deduced from the dual statements about slices. -/
def opSliceIso : coslice p ≅ (slice (opFunctor.map p)).op :=
  Iso.refl _

variable {p}

/-- Maps `K ⋆ X ⟶ C` extending `p` correspond to maps `Xᵒᵖ ⋆ Kᵒᵖ ⟶ Cᵒᵖ` extending `pᵒᵖ`, through
the opposite of maps and the isomorphism `(K ⋆ X)ᵒᵖ ≅ Xᵒᵖ ⋆ Kᵒᵖ`. -/
private noncomputable def opEquiv :
    {τ : join K X ⟶ C // join.inl K X ≫ τ = p} ≃
      {τ : join X.op K.op ⟶ C.op // join.inr X.op K.op ≫ τ = opFunctor.map p} where
  toFun τ := ⟨(join.opIso K X).inv ≫ opFunctor.map τ.1, by
    rw [← join.opFunctor_map_inl_comp_opIso_hom_assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      τ.2]⟩
  invFun τ := ⟨opFunctor.preimage ((join.opIso K X).hom ≫ τ.1), by
    apply opFunctor.map_injective
    simp [τ.2]⟩
  left_inv τ := by simp
  right_inv τ := by simp

/-- Maps `X ⟶ C_{p/}` correspond to maps `Xᵒᵖ ⟶ Cᵒᵖ_{/pᵒᵖ}` by taking opposites, since the
coslice is the opposite of this slice. -/
private def opHomEquiv : (X ⟶ coslice p) ≃ (X.op ⟶ slice (opFunctor.map p)) :=
  (opEquivalence.toAdjunction.homEquiv X (slice (opFunctor.map p))).symm

private lemma opHomEquiv_comp (f : Y ⟶ X) (F : X ⟶ coslice p) :
    opHomEquiv (f ≫ F) = opFunctor.map f ≫ opHomEquiv F :=
  opEquivalence.toAdjunction.homEquiv_naturality_left_symm f F

/-- **The universal property of the coslice**: maps `X ⟶ C_{p/}` correspond to maps `K ⋆ X ⟶ C`
extending `p`. -/
noncomputable def homEquiv : (X ⟶ coslice p) ≃ {τ : join K X ⟶ C // join.inl K X ≫ τ = p} :=
  opHomEquiv.trans (slice.homEquiv.trans opEquiv.symm)

/-- Under the opposite, the map `K ⋆ X ⟶ C` corresponding to `F : X ⟶ C_{p/}` is the map
`Xᵒᵖ ⋆ Kᵒᵖ ⟶ Cᵒᵖ` corresponding to the map `Xᵒᵖ ⟶ Cᵒᵖ_{/pᵒᵖ}` opposite to `F`. -/
private lemma opIso_inv_comp_opFunctor_map_homEquiv_coe (F : X ⟶ coslice p) :
    (join.opIso K X).inv ≫ opFunctor.map (homEquiv F).1 = (slice.homEquiv (opHomEquiv F)).1 :=
  congrArg Subtype.val (opEquiv.apply_symm_apply _)

/-- The universal property of the coslice is natural in `X`: precomposing with `f : Y ⟶ X`
corresponds to precomposing with `K ⋆ f`. -/
@[simp]
lemma homEquiv_comp_coe (f : Y ⟶ X) (F : X ⟶ coslice p) :
    (homEquiv (f ≫ F)).1 = join.map (𝟙 K) f ≫ (homEquiv F).1 := by
  -- Pass to opposites, where the claim is the naturality of the universal property of the slice
  -- (`SSet.slice.homEquiv_comp_coe`) transported along the natural isomorphism `SSet.join.opIso`.
  apply opFunctor.map_injective
  rw [← cancel_epi (join.opIso K Y).inv, opIso_inv_comp_opFunctor_map_homEquiv_coe,
    opHomEquiv_comp, slice.homEquiv_comp_coe, Functor.map_comp,
    ← opIso_inv_comp_opFunctor_map_homEquiv_coe, ← cancel_epi (join.opIso K Y).hom,
    Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_id opFunctor K,
    ← join.opFunctor_map_map_comp_opIso_hom_assoc, Iso.hom_inv_id_assoc]

variable (p) in
/-- The coslice `C_{p/}` represents the presheaf of maps `K ⋆ X ⟶ C` extending `p`. -/
noncomputable def representableBy : (functor p).RepresentableBy (coslice p) where
  homEquiv := homEquiv
  homEquiv_comp f g := Subtype.ext (homEquiv_comp_coe f g)

/-- Maps to the coslice are equal when the corresponding maps `K ⋆ X ⟶ C` are equal. -/
lemma hom_ext {F G : X ⟶ coslice p} (h : (homEquiv F).1 = (homEquiv G).1) : F = G :=
  homEquiv.injective (Subtype.ext h)

/-- The `n`-simplices of the coslice `C_{p/}` are the maps `K ⋆ Δ[n] ⟶ C` extending `p`. -/
noncomputable def objEquiv {n : SimplexCategoryᵒᵖ} :
    (coslice p).obj n ≃ {σ : join K (stdSimplex.obj n.unop) ⟶ C // join.inl K _ ≫ σ = p} :=
  yonedaEquiv.symm.trans homEquiv

/-- The simplex of `C_{p/}` given by `σ` corresponds to the map `Δ[n] ⟶ C_{p/}` given by `σ`. -/
lemma objEquiv_apply {n : SimplexCategory} (σ : (coslice p).obj (op n)) :
    objEquiv σ = homEquiv (yonedaEquiv.symm σ) :=
  (rfl)

/-- The simplex of the coslice that a map `F : X ⟶ C_{p/}` assigns to a simplex `x` of `X` is the
restriction along `K ⋆ x` of the map `K ⋆ X ⟶ C` corresponding to `F`. -/
lemma objEquiv_app_coe {n : SimplexCategory} (F : X ⟶ coslice p) (x : X.obj (op n)) :
    (objEquiv (F.app _ x)).1 = join.map (𝟙 K) (yonedaEquiv.symm x) ≫ (homEquiv F).1 := by
  rw [objEquiv_apply, ← yonedaEquiv_symm_comp, homEquiv_comp_coe]

/-- The map to the coslice given by `τ : K ⋆ X ⟶ C` sends a simplex `x` of `X` to the simplex
`(K ⋆ x) ≫ τ`. -/
@[simp]
lemma homEquiv_symm_app_coe {n : SimplexCategory}
    (τ : {τ : join K X ⟶ C // join.inl K X ≫ τ = p}) (x : X.obj (op n)) :
    (objEquiv ((homEquiv.symm τ).app _ x)).1 = join.map (𝟙 K) (yonedaEquiv.symm x) ≫ τ.1 := by
  rw [objEquiv_app_coe, Equiv.apply_symm_apply]

/-- The faces and degeneracies of the coslice act on a simplex `σ : K ⋆ Δ[n] ⟶ C` by precomposition
with the induced maps of joins. -/
@[simp]
lemma objEquiv_map_coe {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (σ : (coslice p).obj n) :
    (objEquiv ((coslice p).map f σ)).1 =
      join.map (𝟙 K) (stdSimplex.map f.unop) ≫ (objEquiv σ).1 := by
  have h := yonedaEquiv_symm_naturality_left (X := coslice p) f.unop σ
  rw [Quiver.Hom.op_unop] at h
  rw [objEquiv_apply, objEquiv_apply, ← h, homEquiv_comp_coe]

variable (p) in
/-- The projection `C_{p/} ⟶ C`, restricting a simplex `K ⋆ Δ[n] ⟶ C` of the coslice to `Δ[n]`
(`SSet.coslice.π_app`). -/
noncomputable def π : coslice p ⟶ C :=
  join.inr K (coslice p) ≫ (homEquiv (𝟙 (coslice p))).1

/-- The projection of the coslice to `C` corresponds, under the universal property, to restricting
along the inclusion `X ⟶ K ⋆ X`. -/
@[reassoc (attr := simp)]
lemma comp_π (F : X ⟶ coslice p) : F ≫ π p = join.inr K X ≫ (homEquiv F).1 := by
  rw [π, ← join.inr_map_assoc (𝟙 K) F, ← homEquiv_comp_coe, Category.comp_id]

variable (p) in
/-- The coslice under the empty diagram is the whole simplicial set: when `K` is empty, the
projection `C_{p/} ⟶ C` is an isomorphism. -/
lemma isIso_π (hK : ¬ K.Nonempty) : IsIso (π p) := by
  refine isIso_of_yoneda_map_bijective _ fun X ↦ ⟨fun F G h ↦ hom_ext ?_, fun g ↦ ?_⟩
  · have := join.isIso_inr (L := X) hK
    simpa only [comp_π, cancel_epi] using h
  · have := join.isIso_inr (L := X) hK
    refine ⟨homEquiv.symm ⟨inv (join.inr K X) ≫ g, (isInitialOfNotNonempty hK).hom_ext _ _⟩, ?_⟩
    simp

/-- The projection to `C` sends a simplex `σ : K ⋆ Δ[n] ⟶ C` of the coslice to its restriction to
`Δ[n]`. -/
@[simp]
lemma π_app {n : SimplexCategoryᵒᵖ} (σ : (coslice p).obj n) :
    (π p).app n σ = yonedaEquiv (join.inr K _ ≫ (objEquiv σ).1) := by
  rw [objEquiv_apply, ← comp_π, yonedaEquiv_comp, Equiv.apply_symm_apply]

variable {L D : SSet.{u}} {q : L ⟶ D}

/-- The map of coslices `C_{p/} ⟶ D_{q/}` induced by maps `i : L ⟶ K` and `g : C ⟶ D` with
`i ≫ p ≫ g = q`: it restricts a simplex `K ⋆ Δ[n] ⟶ C` of `C_{p/}` along `i ⋆ Δ[n]` and composes
with `g`. For `g = 𝟙 C` this is the restriction of cocones along `i`. -/
noncomputable def map (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) : coslice p ⟶ coslice q :=
  homEquiv.symm ⟨join.map i (𝟙 _) ≫ (homEquiv (𝟙 (coslice p))).1 ≫ g, by
    rw [join.inl_map_assoc, reassoc_of% (homEquiv (𝟙 (coslice p))).2, h]⟩

/-- Under the universal property, the map of coslices induced by `i` and `g` is restriction along
`i ⋆ X` followed by composition with `g`. -/
@[simp high]
lemma homEquiv_comp_map_coe (F : X ⟶ coslice p) (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) :
    (homEquiv (F ≫ map i g h)).1 = join.map i (𝟙 X) ≫ (homEquiv F).1 ≫ g := by
  have hF := homEquiv_comp_coe F (𝟙 (coslice p))
  rw [Category.comp_id] at hF
  rw [map, homEquiv_comp_coe, Equiv.apply_symm_apply, hF, Category.assoc,
    ← join.map_comp_assoc, ← join.map_comp_assoc]
  simp

/-- The map of coslices induced by identities is the identity. -/
@[simp]
lemma map_id (h : 𝟙 K ≫ p ≫ 𝟙 C = p) : map (𝟙 K) (𝟙 C) h = 𝟙 (coslice p) :=
  hom_ext (by rw [← Category.id_comp (map _ _ h), homEquiv_comp_map_coe]; simp)

/-- Maps of coslices compose by composing the restrictions and the postcompositions. -/
@[reassoc]
lemma map_comp {M E : SSet.{u}} {r : M ⟶ E} (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q)
    (i' : M ⟶ L) (g' : D ⟶ E) (h' : i' ≫ q ≫ g' = r) :
    map i g h ≫ map i' g' h' = map (i' ≫ i) (g ≫ g') (by simp [← h', ← h]) := by
  refine hom_ext ?_
  rw [← Category.id_comp (map i g h ≫ _), ← Category.assoc, homEquiv_comp_map_coe,
    homEquiv_comp_map_coe, ← Category.id_comp (map (i' ≫ i) _ _), homEquiv_comp_map_coe]
  simp [← join.map_comp_assoc]

/-- The map of coslices induced by `i` and `g` lies over `g`. -/
-- Not `@[simp]`: `SSet.coslice.comp_π` rewrites the left-hand side.
@[reassoc]
lemma map_π (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) : map i g h ≫ π q = π p ≫ g := by
  rw [comp_π, ← Category.id_comp (map i g h), homEquiv_comp_map_coe, join.inr_map_assoc,
    Category.id_comp, π, Category.assoc]

end coslice

/-! ### Fibres of the inclusion of a vertex -/

namespace coslice

open Limits

variable {L Z : SSet.{u}} (x y : L _⦋0⦌)

/-- Maps from `Z` to the fibre `{x} ×_L L_{y/}` over `y` of the inclusion of the vertex `x` are
the maps `Δ[0] ⋆ Z ⟶ L` sending the cone point to `y` and `Z` to `x`. This is the universal
property of the left mapping space `Hom^L_L(y, x)`. -/
noncomputable def pullbackConstHomEquiv :
    (Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) ≃
      {τ : join Δ[0] Z ⟶ L // join.inl _ _ ≫ τ = const y ∧ join.inr _ _ ≫ τ = const x} where
  toFun g := ⟨(homEquiv (g ≫ pullback.snd _ _)).1, (homEquiv _).2, by
    rw [← comp_π, Category.assoc, ← pullback.condition, comp_const, comp_const]⟩
  invFun τ := pullback.lift (stdSimplex.isTerminalObj₀.from Z) (homEquiv.symm ⟨τ.1, τ.2.1⟩) (by
    rw [comp_π, Equiv.apply_symm_apply, τ.2.2, comp_const])
  left_inv g := pullback.hom_ext stdSimplex.ext₀ (by
    rw [pullback.lift_snd]
    exact homEquiv.symm_apply_apply _)
  right_inv τ := Subtype.ext (by simp)

/-- The universal property of the fibre `{x} ×_L L_{y/}` is natural: precomposing with
`g : Z' ⟶ Z` corresponds to precomposing with `Δ[0] ⋆ g`. -/
@[simp]
lemma pullbackConstHomEquiv_comp_coe {Z' : SSet.{u}} (g : Z' ⟶ Z)
    (h : Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) :
    (pullbackConstHomEquiv x y (g ≫ h)).1 = join.map (𝟙 _) g ≫ (pullbackConstHomEquiv x y h).1 := by
  simp only [pullbackConstHomEquiv, Equiv.coe_fn_mk, homEquiv_comp_coe]
  rw [← join.map_comp_assoc, Category.comp_id]

/-- The map `Δ[0] ⋆ Z ⟶ L` attached to `g : Z ⟶ {x} ×_L L_{y/}` is the map attached by the
universal property of the coslice to the projection `g ≫ pullback.snd _ _` of `g` to `L_{y/}`. -/
lemma pullbackConstHomEquiv_apply_coe
    (g : Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) :
    (pullbackConstHomEquiv x y g).1 = (homEquiv (g ≫ pullback.snd _ _)).1 :=
  (rfl)

/-- The projection to the coslice `L_{y/}` of the map to the fibre `{x} ×_L L_{y/}` attached to
`τ : Δ[0] ⋆ Z ⟶ L` is the map attached to `τ` by the universal property of the coslice. -/
@[simp]
lemma pullbackConstHomEquiv_symm_comp_snd
    (τ : {τ : join Δ[0] Z ⟶ L // join.inl _ _ ≫ τ = const y ∧ join.inr _ _ ≫ τ = const x}) :
    (pullbackConstHomEquiv x y).symm τ ≫ pullback.snd _ _ = homEquiv.symm ⟨τ.1, τ.2.1⟩ :=
  pullback.lift_snd _ _ _

/-- The vertices of the fibre `{x} ×_L L_{y/}` over `y` of the inclusion of the vertex `x` are the
edges from `y` to `x`. -/
noncomputable def pullbackConstObj₀Equiv :
    (pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) _⦋0⦌ ≃ Edge y x :=
  yonedaEquiv.symm.trans ((pullbackConstHomEquiv x y).trans (join.coneEdgeEquiv x y))

/-- The edge attached to a vertex `s` of the fibre `{x} ×_L L_{y/}` is the map
`Δ[1] ≅ Δ[0] ⋆ Δ[0] ⟶ L` corresponding to `s`. -/
@[simp]
lemma pullbackConstObj₀Equiv_apply_edge
    (s : (pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) _⦋0⦌) :
    (pullbackConstObj₀Equiv x y s).edge =
      yonedaEquiv ((join.stdSimplexIso 0 0).inv ≫
        (pullbackConstHomEquiv x y (yonedaEquiv.symm s)).1) :=
  join.coneEdgeEquiv_apply_edge x y _

/-- The map `Δ[0] ⋆ Δ[0] ⟶ L` attached to the vertex of the fibre `{x} ×_L L_{y/}` corresponding to
an edge `e` from `y` to `x` is the map attached to `e` by `SSet.join.coneEdgeEquiv`. -/
@[simp]
lemma pullbackConstHomEquiv_const_pullbackConstObj₀Equiv_symm (e : Edge y x) :
    pullbackConstHomEquiv x y (const ((pullbackConstObj₀Equiv x y).symm e)) =
      (join.coneEdgeEquiv x y).symm e := by
  simpa [pullbackConstObj₀Equiv] using congrArg (pullbackConstHomEquiv x y)
    (yonedaEquiv_symm_zero ((pullbackConstObj₀Equiv x y).symm e)).symm

/-- If `L` is strict Segal, every simplex of the fibre `{x} ×_L L_{y/}` is totally degenerate: a
map `Δ[0] ⋆ Δ[n] ⟶ L` sending `Δ[n]` to `x` is determined by its edge from the cone point to the
vertex `0`. -/
private lemma surjective_pullback_map_const [L.IsStrictSegal] (n : ℕ) :
    Function.Surjective ((pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))).map
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op) := by
  intro s
  refine ⟨(pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))).map
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s, ?_⟩
  apply yonedaEquiv.symm.injective
  rw [← (pullbackConstHomEquiv x y).apply_eq_iff_eq, Subtype.ext_iff]
  simp only [← yonedaEquiv_symm_naturality_left, pullbackConstHomEquiv_comp_coe]
  apply join.hom_ext_of_isStrictSegal
  · -- The vertex `0` is fixed by the operator collapsing `⦋n⦌` onto its vertex `0`.
    simp only [← join.map_comp_assoc, Category.comp_id, ← Functor.map_comp,
      SimplexCategory.const_comp, SimplexCategory.const_apply]
  · simp only [join.inr_map_assoc, (pullbackConstHomEquiv x y _).2.2, comp_const]

/-- If `L` is strict Segal, sending an edge from `y` to `x` to the totally degenerate simplices at
the corresponding vertex of the fibre `{x} ×_L L_{y/}` is an isomorphism from the discrete
simplicial set on these edges. -/
instance isIso_constHomEquiv_symm [L.IsStrictSegal] :
    IsIso ((constHomEquiv (Edge y x)).symm (pullbackConstObj₀Equiv x y).symm) :=
  SSet.isIso_constHomEquiv_symm (pullbackConstObj₀Equiv x y).symm.bijective
    (surjective_pullback_map_const x y)

/-- If `L` is strict Segal, for instance the nerve of a category, the fibre `{x} ×_L L_{y/}` over
`y` of the inclusion of the vertex `x` is the discrete simplicial set on the edges from `y`
to `x`. -/
noncomputable def constEdgeIso [L.IsStrictSegal] :
    (Functor.const SimplexCategoryᵒᵖ).obj (Edge y x) ≅
      pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L)) :=
  asIso ((constHomEquiv (Edge y x)).symm (pullbackConstObj₀Equiv x y).symm)

/-- On vertices, the discreteness isomorphism sends an edge from `y` to `x` to the corresponding
vertex of the fibre `{x} ×_L L_{y/}`. -/
@[simp]
lemma constEdgeIso_hom_app_zero [L.IsStrictSegal] (e : Edge y x) :
    dsimp% (constEdgeIso x y).hom.app (op ⦋0⦌) e = (pullbackConstObj₀Equiv x y).symm e :=
  constHomEquiv_symm_app_zero (Edge y x) (pullbackConstObj₀Equiv x y).symm e

/-- On vertices, the inverse of the discreteness isomorphism sends a vertex of the fibre
`{x} ×_L L_{y/}` to the corresponding edge from `y` to `x`. -/
@[simp]
lemma constEdgeIso_inv_app_zero [L.IsStrictSegal]
    (s : (pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) _⦋0⦌) :
    dsimp% (constEdgeIso x y).inv.app (op ⦋0⦌) s = pullbackConstObj₀Equiv x y s := by
  apply (pullbackConstObj₀Equiv x y).symm.injective
  rw [Equiv.symm_apply_apply, ← constEdgeIso_hom_app_zero]
  simp

end coslice

end SSet
