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
* `SSet.coslice.restrictionMap i p σ`: for `p : X ⟶ S` and `σ : K ⟶ X`, the map
  `X_{σ/} ⟶ X_{i ≫ σ/} ×_{S_{i ≫ σ ≫ p/}} S_{σ ≫ p/}`, dual to `SSet.slice.restrictionMap`.
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
* `SSet.coslice.isTerminal`: the coslice of a terminal simplicial set is terminal.
* `SSet.coslice.opSliceIso_inv_comp_map`: through `SSet.coslice.opSliceIso`, a map of coslices
  is the image under the reversal functor `SSet.opFunctor` of a map of slices.
* `SSet.coslice.opSliceIsoOfEq p hp`: for a diagram `p'` equal to `pᵒᵖ`, the identification of
  the opposite of the slice `Cᵒᵖ_{/p'}` with the coslice `C_{p/}`; it is natural in maps of slices
  (`SSet.coslice.opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom`).
* `SSet.coslice.opSliceRestrictionMapArrowIso j p τ`: applying the reversal functor
  `SSet.opFunctor` to the relative slice map for `jᵒᵖ`, `pᵒᵖ` and `τᵒᵖ` gives an arrow isomorphic
  to the relative coslice map for `j`, `p` and `τ`.
* `SSet.coslice.hasLiftingProperty_restrictionMap_iff_slice`: a map `i` lifts against the relative
  coslice map for `j`, `p` and `τ` exactly when `iᵒᵖ` lifts against the relative slice map for
  `jᵒᵖ`, `pᵒᵖ` and `τᵒᵖ`.
* `SSet.coslice.isIso_restrictionMap`: for an isomorphism `p`, the relative coslice map is an
  isomorphism.
* `SSet.coslice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout`: for maps `j : A ⟶ B`,
  `i : L ⟶ K` and `p : X ⟶ S`, the map `i` lifts against every relative coslice map for `j`
  exactly when the map `(A ⋆ K) ⨿_{A ⋆ L} (B ⋆ L) ⟶ B ⋆ K` from the pushout-join of `j` and `i`
  lifts against `p`. It is deduced from the slice criterion
  `SSet.slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout` by passing to opposites.
  Hence `j` lifts against every relative slice map for `i` exactly when `i` lifts against every
  relative coslice map for `j` (`SSet.slice.forall_hasLiftingProperty_restrictionMap_iff`).

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
  map g := ↾fun τ ↦ ⟨join.map (𝟙 K) g.unop ≫ τ.val, by rw [join.inl_map_assoc, Category.id_comp,
      τ.property]⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    exact (congrArg (· ≫ τ.val) join.map_id).trans (Category.id_comp _)
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    refine (congrArg (· ≫ τ.val) ?_).trans (Category.assoc _ _ _)
    simpa using join.map_comp (𝟙 K) g.unop (𝟙 K) f.unop

@[simp]
lemma functor_map_coe {X Y : SSet.{u}ᵒᵖ} (g : X ⟶ Y) (τ : (functor p).obj X) :
    ((functor p).map g τ).val = join.map (𝟙 K) g.unop ≫ τ.val :=
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
  toFun τ := ⟨(join.opIso K X).inv ≫ opFunctor.map τ.val, by
    rw [← join.opFunctor_map_inl_comp_opIso_hom_assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      τ.property]⟩
  invFun τ := ⟨opFunctor.preimage ((join.opIso K X).hom ≫ τ.val), by
    apply opFunctor.map_injective
    simp [τ.property]⟩
  left_inv τ := by simp
  right_inv τ := by simp

/-- Maps `X ⟶ C_{p/}` correspond to maps `Xᵒᵖ ⟶ Cᵒᵖ_{/pᵒᵖ}` by taking opposites, since the
coslice is the opposite of this slice. -/
private def opHomEquiv : (X ⟶ coslice p) ≃ (X.op ⟶ slice (opFunctor.map p)) :=
  (opSliceIso p).homToEquiv.trans
    (opEquivalence.toAdjunction.homEquiv X (slice (opFunctor.map p))).symm

private lemma opHomEquiv_comp (f : Y ⟶ X) (F : X ⟶ coslice p) :
    opHomEquiv (f ≫ F) = opFunctor.map f ≫ opHomEquiv F := by
  -- `opHomEquiv` postcomposes with `(opSliceIso p).hom` before the adjunction bijection.
  have h : (f ≫ F) ≫ (opSliceIso p).hom = f ≫ F ≫ (opSliceIso p).hom := Category.assoc _ _ _
  exact (congrArg (opEquivalence.toAdjunction.homEquiv Y (slice (opFunctor.map p))).symm h).trans
    (opEquivalence.toAdjunction.homEquiv_naturality_left_symm f (F ≫ (opSliceIso p).hom))

/-- **The universal property of the coslice**: maps `X ⟶ C_{p/}` correspond to maps `K ⋆ X ⟶ C`
extending `p`. -/
noncomputable def homEquiv : (X ⟶ coslice p) ≃ {τ : join K X ⟶ C // join.inl K X ≫ τ = p} :=
  opHomEquiv.trans (slice.homEquiv.trans opEquiv.symm)

/-- Under the opposite, the map `K ⋆ X ⟶ C` corresponding to `F : X ⟶ C_{p/}` is the map
`Xᵒᵖ ⋆ Kᵒᵖ ⟶ Cᵒᵖ` corresponding to the map `Xᵒᵖ ⟶ Cᵒᵖ_{/pᵒᵖ}` opposite to `F`. -/
private lemma opIso_inv_comp_opFunctor_map_homEquiv_coe (F : X ⟶ coslice p) :
    (join.opIso K X).inv ≫ opFunctor.map (homEquiv F).val = (slice.homEquiv (opHomEquiv F)).val :=
  congrArg Subtype.val (opEquiv.apply_symm_apply _)

/-- The universal property of the coslice is natural in `X`: precomposing with `f : Y ⟶ X`
corresponds to precomposing with `K ⋆ f`. -/
@[simp]
lemma homEquiv_comp_coe (f : Y ⟶ X) (F : X ⟶ coslice p) :
    (homEquiv (f ≫ F)).val = join.map (𝟙 K) f ≫ (homEquiv F).val := by
  -- Pass to opposites, where the claim is the naturality of the universal property of the slice
  -- (`SSet.slice.homEquiv_comp_coe`) transported along the natural isomorphism `SSet.join.opIso`.
  apply opFunctor.map_injective
  rw [← cancel_epi (join.opIso K Y).inv, opIso_inv_comp_opFunctor_map_homEquiv_coe,
    opHomEquiv_comp, slice.homEquiv_comp_coe, Functor.map_comp,
    ← opIso_inv_comp_opFunctor_map_homEquiv_coe, join.opIso_inv_comp_opFunctor_map_map_assoc,
    CategoryTheory.Functor.map_id]

variable (p) in
/-- The coslice `C_{p/}` represents the presheaf of maps `K ⋆ X ⟶ C` extending `p`. -/
noncomputable def representableBy : (functor p).RepresentableBy (coslice p) where
  homEquiv := homEquiv
  homEquiv_comp f g := Subtype.ext (homEquiv_comp_coe f g)

/-- Maps to the coslice are equal when the corresponding maps `K ⋆ X ⟶ C` are equal. -/
lemma hom_ext {F G : X ⟶ coslice p} (h : (homEquiv F).val = (homEquiv G).val) : F = G :=
  homEquiv.injective (Subtype.ext h)

variable (p) in
/-- The coslice of a terminal simplicial set is terminal: over the point there is exactly one
cocone under every diagram. -/
noncomputable def isTerminal (hC : Limits.IsTerminal C) : Limits.IsTerminal (coslice p) :=
  Limits.IsTerminal.ofUniqueHom (fun _ ↦ homEquiv.symm ⟨hC.from _, hC.hom_ext _ _⟩)
    fun _ _ ↦ hom_ext (hC.hom_ext _ _)

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
    (objEquiv (F.app _ x)).val = join.map (𝟙 K) (yonedaEquiv.symm x) ≫ (homEquiv F).val := by
  rw [objEquiv_apply, ← yonedaEquiv_symm_comp, homEquiv_comp_coe]

/-- The map to the coslice given by `τ : K ⋆ X ⟶ C` sends a simplex `x` of `X` to the simplex
`(K ⋆ x) ≫ τ`. -/
@[simp]
lemma homEquiv_symm_app_coe {n : SimplexCategory}
    (τ : {τ : join K X ⟶ C // join.inl K X ≫ τ = p}) (x : X.obj (op n)) :
    (objEquiv ((homEquiv.symm τ).app _ x)).val = join.map (𝟙 K) (yonedaEquiv.symm x) ≫ τ.val := by
  rw [objEquiv_app_coe, Equiv.apply_symm_apply]

/-- The faces and degeneracies of the coslice act on a simplex `σ : K ⋆ Δ[n] ⟶ C` by precomposition
with the induced maps of joins. -/
@[simp]
lemma objEquiv_map_coe {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (σ : (coslice p).obj n) :
    (objEquiv ((coslice p).map f σ)).val =
      join.map (𝟙 K) (stdSimplex.map f.unop) ≫ (objEquiv σ).val := by
  have h := yonedaEquiv_symm_naturality_left (X := coslice p) f.unop σ
  rw [Quiver.Hom.op_unop] at h
  rw [objEquiv_apply, objEquiv_apply, ← h, homEquiv_comp_coe]

variable (p) in
/-- The projection `C_{p/} ⟶ C`, restricting a simplex `K ⋆ Δ[n] ⟶ C` of the coslice to `Δ[n]`
(`SSet.coslice.π_app`). -/
noncomputable def π : coslice p ⟶ C :=
  join.inr K (coslice p) ≫ (homEquiv (𝟙 (coslice p))).val

/-- The projection of the coslice to `C` corresponds, under the universal property, to restricting
along the inclusion `X ⟶ K ⋆ X`. -/
@[reassoc (attr := simp)]
lemma comp_π (F : X ⟶ coslice p) : F ≫ π p = join.inr K X ≫ (homEquiv F).val := by
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
    (π p).app n σ = yonedaEquiv (join.inr K _ ≫ (objEquiv σ).val) := by
  rw [objEquiv_apply, ← comp_π, yonedaEquiv_comp, Equiv.apply_symm_apply]

variable {L D : SSet.{u}} {q : L ⟶ D}

/-- The map of coslices `C_{p/} ⟶ D_{q/}` induced by maps `i : L ⟶ K` and `g : C ⟶ D` with
`i ≫ p ≫ g = q`: it restricts a simplex `K ⋆ Δ[n] ⟶ C` of `C_{p/}` along `i ⋆ Δ[n]` and composes
with `g`. For `g = 𝟙 C` this is the restriction of cocones along `i`. -/
noncomputable def map (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) : coslice p ⟶ coslice q :=
  homEquiv.symm ⟨join.map i (𝟙 _) ≫ (homEquiv (𝟙 (coslice p))).val ≫ g, by
    rw [join.inl_map_assoc, reassoc_of% (homEquiv (𝟙 (coslice p))).property, h]⟩

/-- Under the universal property, the map of coslices induced by `i` and `g` is restriction along
`i ⋆ X` followed by composition with `g`. -/
@[simp high]
lemma homEquiv_comp_map_coe (F : X ⟶ coslice p) (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) :
    (homEquiv (F ≫ map i g h)).val = join.map i (𝟙 X) ≫ (homEquiv F).val ≫ g := by
  have hF := homEquiv_comp_coe F (𝟙 (coslice p))
  rw [Category.comp_id] at hF
  rw [map, homEquiv_comp_coe, Equiv.apply_symm_apply, hF, Category.assoc,
    ← join.map_comp_assoc, ← join.map_comp_assoc]
  simp

/-- The map of coslices induced by `i` and `g` sends a simplex `σ : K ⋆ Δ[n] ⟶ C` to its
restriction along `i ⋆ Δ[n]`, composed with `g`. -/
@[simp]
lemma objEquiv_map_app_coe {n : SimplexCategory} (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q)
    (σ : (coslice p).obj (op n)) :
    (objEquiv ((map i g h).app _ σ)).val = join.map i (𝟙 _) ≫ (objEquiv σ).val ≫ g := by
  rw [objEquiv_apply, ← yonedaEquiv_symm_comp, homEquiv_comp_map_coe, ← objEquiv_apply]

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

/-- Composing a map `F : X ⟶ C_{p/}` with the opposite of a map of slices
`M : Cᵒᵖ_{/pᵒᵖ} ⟶ Dᵒᵖ_{/qᵒᵖ}` corresponds, on opposites, to composing with `M`. -/
private lemma opHomEquiv_comp_opFunctor_map (F : X ⟶ coslice p)
    (M : slice (opFunctor.map p) ⟶ slice (opFunctor.map q)) :
    opHomEquiv (F ≫ (opSliceIso p).hom ≫ opFunctor.map M ≫ (opSliceIso q).inv) =
      opHomEquiv F ≫ M := by
  have h : (F ≫ (opSliceIso p).hom ≫ opFunctor.map M ≫ (opSliceIso q).inv) ≫
      (opSliceIso q).hom = (F ≫ (opSliceIso p).hom) ≫ opFunctor.map M := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (opEquivalence.toAdjunction.homEquiv X (slice (opFunctor.map q))).symm h).trans
    (opEquivalence.toAdjunction.homEquiv_naturality_right_symm (F ≫ (opSliceIso p).hom) M)

/-- **Maps of coslices are opposite to maps of slices**: through the identification of coslices
with opposite slices (`SSet.coslice.opSliceIso`), the map of coslices induced by `i` and `g`
corresponds to the opposite of the map of slices induced by `iᵒᵖ` and `gᵒᵖ`. The maps `i'` and `g'`
are any maps equal to `iᵒᵖ` and `gᵒᵖ`, such as `𝟙 Lᵒᵖ` for `i = 𝟙 L`. -/
lemma opSliceIso_inv_comp_map (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q)
    {i' : L.op ⟶ K.op} {g' : C.op ⟶ D.op} (hi : opFunctor.map i = i')
    (hg : opFunctor.map g = g') :
    (opSliceIso p).inv ≫ map i g h = opFunctor.map
      (slice.map i' g' (by simp [← hi, ← hg, ← h]) :
        slice (opFunctor.map p) ⟶ slice (opFunctor.map q)) ≫ (opSliceIso q).inv := by
  subst hi hg
  rw [Iso.inv_comp_eq]
  -- Compare the corresponding maps `L ⋆ C_{p/} ⟶ D` after passing to opposites and precomposing
  -- with the join comparison `C_{p/}ᵒᵖ ⋆ Lᵒᵖ ≅ (L ⋆ C_{p/})ᵒᵖ`.
  refine hom_ext (opFunctor.map_injective ((cancel_epi (join.opIso L (coslice p)).inv).1 ?_))
  calc (join.opIso L (coslice p)).inv ≫ opFunctor.map (homEquiv (map i g h)).val
      = (join.opIso L (coslice p)).inv ≫ opFunctor.map (join.map i (𝟙 _)) ≫
          opFunctor.map ((homEquiv (𝟙 (coslice p))).val ≫ g) := by
        rw [← Functor.map_comp, ← homEquiv_comp_map_coe, Category.id_comp]
    _ = join.map (opFunctor.map (𝟙 _)) (opFunctor.map i) ≫ (join.opIso K (coslice p)).inv ≫
          opFunctor.map ((homEquiv (𝟙 (coslice p))).val ≫ g) := by
        rw [join.opIso_inv_comp_opFunctor_map_map_assoc]
    _ = (slice.homEquiv (opHomEquiv (𝟙 (coslice p)) ≫ slice.map (opFunctor.map i)
          (opFunctor.map g) (by simp [← h]) :
            (coslice p).op ⟶ slice (opFunctor.map q))).val := by
        rw [slice.homEquiv_comp_map_coe, CategoryTheory.Functor.map_id, Functor.map_comp,
          ← Category.assoc ((join.opIso K (coslice p)).inv),
          opIso_inv_comp_opFunctor_map_homEquiv_coe]
    _ = (join.opIso L (coslice p)).inv ≫ opFunctor.map (homEquiv ((opSliceIso p).hom ≫
          opFunctor.map (slice.map (opFunctor.map i) (opFunctor.map g) (by simp [← h]) :
            slice (opFunctor.map p) ⟶ slice (opFunctor.map q)) ≫ (opSliceIso q).inv)).val := by
        rw [opIso_inv_comp_opFunctor_map_homEquiv_coe, ← opHomEquiv_comp_opFunctor_map,
          Category.id_comp]

variable (p) in
/-- For a diagram `p'` equal to `pᵒᵖ`, the identification of the opposite of the slice
`Cᵒᵖ_{/p'}` with the coslice `C_{p/}`: the image under `SSet.opFunctor` of the isomorphism of
slices `Cᵒᵖ_{/p'} ≅ Cᵒᵖ_{/pᵒᵖ}` induced by identities, followed by the inverse of
`SSet.coslice.opSliceIso`. It identifies, for instance, the opposite of the slice indexed by the
composite `jᵒᵖ ≫ τᵒᵖ` with the coslice under `j ≫ τ`. -/
noncomputable def opSliceIsoOfEq {p' : K.op ⟶ C.op} (hp : p' = opFunctor.map p) :
    (slice p').op ≅ coslice p :=
  opFunctor.mapIso (asIso (slice.map (𝟙 _) (𝟙 _) (by simp [hp]) :
    slice p' ⟶ slice (opFunctor.map p))) ≪≫ (opSliceIso p).symm

/-- The isomorphism `SSet.coslice.opSliceIsoOfEq` is the image under `SSet.opFunctor` of the map of
slices induced by identities, followed by the inverse of `SSet.coslice.opSliceIso`. -/
lemma opSliceIsoOfEq_hom {p' : K.op ⟶ C.op} (hp : p' = opFunctor.map p) :
    (opSliceIsoOfEq p hp).hom = opFunctor.map (slice.map (𝟙 _) (𝟙 _) (by simp [hp]) :
      slice p' ⟶ slice (opFunctor.map p)) ≫ (opSliceIso p).inv :=
  (rfl)

variable (p) in
/-- For the diagram `pᵒᵖ` itself, `SSet.coslice.opSliceIsoOfEq` is the inverse of
`SSet.coslice.opSliceIso`. -/
@[simp]
lemma opSliceIsoOfEq_rfl : opSliceIsoOfEq p rfl = (opSliceIso p).symm := by
  ext1
  simp [opSliceIsoOfEq_hom]

/-- **Naturality of `SSet.coslice.opSliceIsoOfEq`**: through these identifications, the opposite
of the map of slices induced by `iᵒᵖ` and `gᵒᵖ` is the map of coslices induced by `i` and `g`. The
maps `i'` and `g'` are any maps equal to `iᵒᵖ` and `gᵒᵖ`. -/
@[reassoc]
lemma opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom {p' : K.op ⟶ C.op} {q' : L.op ⟶ D.op}
    (hp : p' = opFunctor.map p) (hq : q' = opFunctor.map q) (i : L ⟶ K) (g : C ⟶ D)
    (h : i ≫ p ≫ g = q) {i' : L.op ⟶ K.op} {g' : C.op ⟶ D.op} (hi : opFunctor.map i = i')
    (hg : opFunctor.map g = g') (h' : i' ≫ p' ≫ g' = q') :
    opFunctor.map (slice.map i' g' h') ≫ (opSliceIsoOfEq q hq).hom =
      (opSliceIsoOfEq p hp).hom ≫ map i g h := by
  rw [opSliceIsoOfEq_hom, opSliceIsoOfEq_hom, Category.assoc, opSliceIso_inv_comp_map i g h hi hg,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, slice.map_comp, slice.map_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- Restricting cocones along an isomorphism and pushing them forward along an isomorphism is an
isomorphism of coslices: through
`SSet.coslice.opSliceIso`, it is the image under `SSet.opFunctor` of the map of slices pushing
cones forward along `gᵒᵖ` and restricting along `iᵒᵖ`
(`SSet.coslice.opSliceIso_inv_comp_map`), which is an isomorphism
(`SSet.slice.isIso_map`). -/
instance isIso_map (i : L ⟶ K) [IsIso i] (g : C ⟶ D) [IsIso g] (h : i ≫ p ≫ g = q) :
    IsIso (map i g h) := by
  rw [(Iso.inv_comp_eq _).1 (opSliceIso_inv_comp_map i g h rfl rfl)]
  infer_instance

section restrictionMap

variable {S : SSet.{u}}

/-- For maps `i : L ⟶ K`, `p : X ⟶ S` and a diagram `σ : K ⟶ X`, the map
`X_{σ/} ⟶ X_{i ≫ σ/} ×_{S_{i ≫ σ ≫ p/}} S_{σ ≫ p/}` which restricts a cocone under `σ` along `i`
and pushes it forward along `p`. It is dual to `SSet.slice.restrictionMap`. -/
noncomputable def restrictionMap (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    coslice σ ⟶ Limits.pullback (map (𝟙 L) p (by simp) : coslice (i ≫ σ) ⟶ coslice (i ≫ σ ≫ p))
      (map i (𝟙 S) (by simp) : coslice (σ ≫ p) ⟶ coslice (i ≫ σ ≫ p)) :=
  Limits.pullback.lift (map i (𝟙 X) (by simp)) (map (𝟙 K) p (by simp)) (by simp [map_comp])

/-- The first component of the relative coslice map restricts a cocone under `σ` along `i`, to a
cocone under `i ≫ σ`. -/
@[reassoc (attr := simp)]
lemma restrictionMap_fst (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ Limits.pullback.fst _ _ = map i (𝟙 X) (by simp) :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of the relative coslice map pushes a cocone under `σ` forward along `p`,
to a cocone under `σ ≫ p`. -/
@[reassoc (attr := simp)]
lemma restrictionMap_snd (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ Limits.pullback.snd _ _ = map (𝟙 K) p (by simp) :=
  Limits.pullback.lift_snd _ _ _

end restrictionMap

end coslice

/-! ### Lifting problems for relative slices and coslices -/

section lifting

open Limits

variable {A B L P S : SSet.{u}}

namespace coslice

/-- **Relative coslice maps are isomorphic to opposites of relative slice maps**: for maps
`j : A ⟶ B`, `p : X ⟶ S` and `τ : B ⟶ X`, applying the reversal functor `SSet.opFunctor` to the
relative slice map for `jᵒᵖ`, `pᵒᵖ` and `τᵒᵖ` gives an arrow isomorphic to the relative coslice map
`X_{τ/} ⟶ X_{j ≫ τ/} ×_{S_{j ≫ τ ≫ p/}} S_{τ ≫ p/}`. On sources the isomorphism is the
identification of coslices with opposite slices (`SSet.coslice.opSliceIso`). On targets it is the
comparison of pullbacks, since `SSet.opFunctor` preserves pullbacks; the opposites of the slices
indexed by the composites `jᵒᵖ ≫ τᵒᵖ`, `τᵒᵖ ≫ pᵒᵖ` and `jᵒᵖ ≫ τᵒᵖ ≫ pᵒᵖ` are identified with the
coslices under `j ≫ τ`, `τ ≫ p` and `j ≫ τ ≫ p` by `SSet.coslice.opSliceIsoOfEq`, which is
natural in maps of slices (`SSet.coslice.opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom`). -/
noncomputable def opSliceRestrictionMapArrowIso (j : A ⟶ B) (p : X ⟶ S) (τ : B ⟶ X) :
    Arrow.mk (opFunctor.map
      (slice.restrictionMap (opFunctor.map j) (opFunctor.map p) (opFunctor.map τ))) ≅
        Arrow.mk (restrictionMap j p τ) := by
  -- The opposite of the target of the relative slice map is a pullback of coslices.
  have hP := ((IsPullback.of_hasPullback
      (slice.map (𝟙 _) (opFunctor.map p) (by simp) :
        slice (opFunctor.map j ≫ opFunctor.map τ) ⟶
          slice (opFunctor.map j ≫ opFunctor.map τ ≫ opFunctor.map p))
      (slice.map (opFunctor.map j) (𝟙 _) (by simp) :
        slice (opFunctor.map τ ≫ opFunctor.map p) ⟶ _)).map opFunctor).of_iso (Iso.refl _)
    (opSliceIsoOfEq (j ≫ τ) (Functor.map_comp _ _ _).symm)
    (opSliceIsoOfEq (τ ≫ p) (Functor.map_comp _ _ _).symm)
    (opSliceIsoOfEq (j ≫ τ ≫ p) (by simp)) (f' := map (𝟙 A) p (by simp))
    (g' := map j (𝟙 S) (by simp)) (Category.id_comp _).symm (Category.id_comp _).symm
    (opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom _ _ (𝟙 A) p _
      (CategoryTheory.Functor.map_id _ _) rfl _)
    (opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom _ _ j (𝟙 S) _ rfl
      (CategoryTheory.Functor.map_id _ _) _)
  refine Arrow.isoMk (opSliceIso τ).symm hP.isoPullback (pullback.hom_ext ?_ ?_)
  · simp only [Arrow.mk_hom, Iso.symm_hom, Category.assoc]
    simp only [restrictionMap_fst, hP.isoPullback_hom_fst, ← Functor.map_comp_assoc,
      slice.restrictionMap_fst]
    rw [opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom rfl _ j (𝟙 X) _ rfl
        (CategoryTheory.Functor.map_id _ _), opSliceIsoOfEq_rfl, Iso.symm_hom]
  · simp only [Arrow.mk_hom, Iso.symm_hom, Category.assoc]
    simp only [restrictionMap_snd, hP.isoPullback_hom_snd, ← Functor.map_comp_assoc,
      slice.restrictionMap_snd]
    rw [opFunctor_map_slice_map_comp_opSliceIsoOfEq_hom rfl _ (𝟙 B) p _
        (CategoryTheory.Functor.map_id _ _) rfl, opSliceIsoOfEq_rfl, Iso.symm_hom]

/-- On sources, the isomorphism `SSet.coslice.opSliceRestrictionMapArrowIso` is the identification
`(Xᵒᵖ_{/τᵒᵖ})ᵒᵖ ≅ X_{τ/}` of `SSet.coslice.opSliceIso`. -/
@[simp]
lemma opSliceRestrictionMapArrowIso_hom_left (j : A ⟶ B) (p : X ⟶ S) (τ : B ⟶ X) :
    (opSliceRestrictionMapArrowIso j p τ).hom.left = (opSliceIso τ).inv :=
  (rfl)

/-- On targets, the first component of the isomorphism `SSet.coslice.opSliceRestrictionMapArrowIso`
is the opposite of the first projection of the pullback of slices, to `Xᵒᵖ_{/jᵒᵖ ≫ τᵒᵖ}`,
followed by the identification `SSet.coslice.opSliceIsoOfEq` of the opposite of this slice with the
coslice `X_{j ≫ τ/}`. -/
@[reassoc (attr := simp)]
lemma opSliceRestrictionMapArrowIso_hom_right_fst (j : A ⟶ B) (p : X ⟶ S) (τ : B ⟶ X) :
    (opSliceRestrictionMapArrowIso j p τ).hom.right ≫ pullback.fst _ _ =
      opFunctor.map (pullback.fst _ _) ≫
        (opSliceIsoOfEq (j ≫ τ) (Functor.map_comp _ _ _).symm).hom :=
  IsPullback.isoPullback_hom_fst _

/-- On targets, the second component of the isomorphism
`SSet.coslice.opSliceRestrictionMapArrowIso` is the opposite of the second projection of the
pullback of slices, to `Sᵒᵖ_{/τᵒᵖ ≫ pᵒᵖ}`, followed by the identification
`SSet.coslice.opSliceIsoOfEq` of the opposite of this slice with the coslice `S_{τ ≫ p/}`. -/
@[reassoc (attr := simp)]
lemma opSliceRestrictionMapArrowIso_hom_right_snd (j : A ⟶ B) (p : X ⟶ S) (τ : B ⟶ X) :
    (opSliceRestrictionMapArrowIso j p τ).hom.right ≫ pullback.snd _ _ =
      opFunctor.map (pullback.snd _ _) ≫
        (opSliceIsoOfEq (τ ≫ p) (Functor.map_comp _ _ _).symm).hom :=
  IsPullback.isoPullback_hom_snd _

/-- For an isomorphism `p`, the map `SSet.coslice.restrictionMap j p τ` is an isomorphism: through
`SSet.coslice.opSliceRestrictionMapArrowIso`, it is isomorphic to the opposite of a relative slice
map, which is an isomorphism (`SSet.slice.isIso_restrictionMap`). -/
instance isIso_restrictionMap (j : A ⟶ B) (p : X ⟶ S) [IsIso p] (τ : B ⟶ X) :
    IsIso (restrictionMap j p τ) :=
  (Arrow.isIso_iff_isIso_of_isIso (opSliceRestrictionMapArrowIso j p τ).hom).1 inferInstance

/-- **Lifting against relative coslice maps is lifting against relative slice maps**: for maps
`i : L ⟶ K`, `j : A ⟶ B`, `p : X ⟶ S` and `τ : B ⟶ X`, the map `i` lifts against the relative
coslice map `X_{τ/} ⟶ X_{j ≫ τ/} ×_{S_{j ≫ τ ≫ p/}} S_{τ ≫ p/}` exactly when `iᵒᵖ` lifts against the
relative slice map for `jᵒᵖ`, `pᵒᵖ` and `τᵒᵖ`: applying the reversal functor `SSet.opFunctor`
to the second map gives an arrow isomorphic to the first
(`SSet.coslice.opSliceRestrictionMapArrowIso`), and `SSet.opFunctor` is an equivalence. -/
theorem hasLiftingProperty_restrictionMap_iff_slice (i : L ⟶ K) (j : A ⟶ B) (p : X ⟶ S)
    (τ : B ⟶ X) :
    HasLiftingProperty i (restrictionMap j p τ) ↔
      HasLiftingProperty (opFunctor.map i)
        (slice.restrictionMap (opFunctor.map j) (opFunctor.map p) (opFunctor.map τ)) :=
  (HasLiftingProperty.iff_of_arrow_iso_right i (opSliceRestrictionMapArrowIso j p τ).symm).trans
    (opEquivalence.toAdjunction.hasLiftingProperty_iff i _).symm

/-- **Lifting problems for relative coslices are extension problems along a pushout-join.** Let
`j : A ⟶ B`, `i : L ⟶ K` and `p : X ⟶ S`, and let `u : P ⟶ B ⋆ K` be the map induced on a pushout
`P` of `A ⋆ K ← A ⋆ L → B ⋆ L`. Then `i` lifts against every relative coslice map
`X_{τ/} ⟶ X_{j ≫ τ/} ×_{S_{j ≫ τ ≫ p/}} S_{τ ≫ p/}` exactly when `u` lifts against `p`: through
the universal property of the coslice, a lifting problem, ranging over all diagrams `τ`, is a pair
of maps `A ⋆ K ⟶ X` and `B ⋆ L ⟶ X` agreeing on `A ⋆ L`, together with a map `B ⋆ K ⟶ S`
restricting to their composites with `p`, and a solution is a map `B ⋆ K ⟶ X` over `S` extending
both. For a fixed `τ`, the map `B ⋆ L ⟶ X` must restrict to `τ` on `B`. The criterion is
deduced from its slice counterpart
`SSet.slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout` by passing to opposites
(`SSet.coslice.hasLiftingProperty_restrictionMap_iff_slice`). -/
theorem forall_hasLiftingProperty_restrictionMap_iff_of_isPushout (j : A ⟶ B) (i : L ⟶ K)
    (p : X ⟶ S) {f : join A K ⟶ P} {g : join B L ⟶ P}
    (h : IsPushout (join.map (𝟙 A) i) (join.map j (𝟙 L)) f g) {u : P ⟶ join B K}
    (hf : f ≫ u = join.map j (𝟙 K)) (hg : g ≫ u = join.map (𝟙 B) i) :
    (∀ τ : B ⟶ X, HasLiftingProperty i (restrictionMap j p τ)) ↔ HasLiftingProperty u p := by
  -- Pass to opposites, where the claim is the slice criterion for `iᵒᵖ`, `jᵒᵖ` and `pᵒᵖ` along
  -- the opposite pushout square, whose corners are joins of opposites (`SSet.join.opIso`).
  have h' : IsPushout (join.map (𝟙 L.op) (opFunctor.map j)) (join.map (opFunctor.map i) (𝟙 A.op))
      ((join.opIso B L).inv ≫ opFunctor.map g) ((join.opIso A K).inv ≫ opFunctor.map f) :=
    (h.map opFunctor).flip.of_iso (join.opIso A L) (join.opIso B L) (join.opIso A K) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have hu := slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout (opFunctor.map i)
    (opFunctor.map j) (opFunctor.map p) h' (u := opFunctor.map u ≫ (join.opIso B K).hom)
    (by simp [← Functor.map_comp_assoc, hg]) (by simp [← Functor.map_comp_assoc, hf])
  rw [← HasLiftingProperty.iff_of_arrow_iso_left
    (Arrow.isoMk (Iso.refl _) (join.opIso B K) :
      Arrow.mk (opFunctor.map u) ≅ Arrow.mk (opFunctor.map u ≫ (join.opIso B K).hom)),
    opFunctor.hasLiftingProperty_iff_of_isEquivalence] at hu
  rw [← hu]
  refine ⟨fun H σ ↦ ?_, fun H τ ↦ (hasLiftingProperty_restrictionMap_iff_slice i j p τ).2 (H _)⟩
  rw [← opFunctor.map_preimage σ, ← hasLiftingProperty_restrictionMap_iff_slice]
  exact H _

end coslice

namespace slice

/-- **Lifting problems for relative slices and relative coslices correspond.** For maps
`j : A ⟶ B`, `i : L ⟶ K` and `p : X ⟶ S`, the map `j` lifts against every relative slice map
`X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` exactly when `i` lifts against every relative
coslice map `X_{τ/} ⟶ X_{j ≫ τ/} ×_{S_{j ≫ τ ≫ p/}} S_{τ ≫ p/}`: both say that the pushout-join of
`j` and `i` lifts against `p`. -/
theorem forall_hasLiftingProperty_restrictionMap_iff (j : A ⟶ B) (i : L ⟶ K) (p : X ⟶ S) :
    (∀ σ : K ⟶ X, HasLiftingProperty j (restrictionMap i p σ)) ↔
      ∀ τ : B ⟶ X, HasLiftingProperty i (coslice.restrictionMap j p τ) := by
  have h := IsPushout.of_hasPushout (join.map (𝟙 A) i) (join.map j (𝟙 L))
  have hw : join.map (𝟙 A) i ≫ join.map j (𝟙 K) = join.map j (𝟙 L) ≫ join.map (𝟙 B) i := by
    simp [← join.map_comp]
  rw [forall_hasLiftingProperty_restrictionMap_iff_of_isPushout j i p h (pushout.inl_desc _ _ hw)
    (pushout.inr_desc _ _ hw), coslice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout
    j i p h (pushout.inl_desc _ _ hw) (pushout.inr_desc _ _ hw)]

end slice

end lifting

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
  toFun g := ⟨(homEquiv (g ≫ pullback.snd _ _)).val, (homEquiv _).property, by
    rw [← comp_π, Category.assoc, ← pullback.condition, comp_const, comp_const]⟩
  invFun τ := pullback.lift (stdSimplex.isTerminalObj₀.from Z) (homEquiv.symm ⟨τ.val, τ.property.1⟩)
      (by
    rw [comp_π, Equiv.apply_symm_apply, τ.property.2, comp_const])
  left_inv g := pullback.hom_ext stdSimplex.ext₀ (by
    rw [pullback.lift_snd]
    exact homEquiv.symm_apply_apply _)
  right_inv τ := Subtype.ext (by simp)

/-- The universal property of the fibre `{x} ×_L L_{y/}` is natural: precomposing with
`g : Z' ⟶ Z` corresponds to precomposing with `Δ[0] ⋆ g`. -/
@[simp]
lemma pullbackConstHomEquiv_comp_coe {Z' : SSet.{u}} (g : Z' ⟶ Z)
    (h : Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) :
    (pullbackConstHomEquiv x y (g ≫ h)).val = join.map (𝟙 _) g ≫ (pullbackConstHomEquiv x y h).val
        := by
  simp only [pullbackConstHomEquiv, Equiv.coe_fn_mk, homEquiv_comp_coe]
  rw [← join.map_comp_assoc, Category.comp_id]

/-- The map `Δ[0] ⋆ Z ⟶ L` attached to `g : Z ⟶ {x} ×_L L_{y/}` is the map attached by the
universal property of the coslice to the projection `g ≫ pullback.snd _ _` of `g` to `L_{y/}`. -/
lemma pullbackConstHomEquiv_apply_coe
    (g : Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) :
    (pullbackConstHomEquiv x y g).val = (homEquiv (g ≫ pullback.snd _ _)).val :=
  (rfl)

/-- The projection to the coslice `L_{y/}` of the map to the fibre `{x} ×_L L_{y/}` attached to
`τ : Δ[0] ⋆ Z ⟶ L` is the map attached to `τ` by the universal property of the coslice. -/
@[simp]
lemma pullbackConstHomEquiv_symm_comp_snd
    (τ : {τ : join Δ[0] Z ⟶ L // join.inl _ _ ≫ τ = const y ∧ join.inr _ _ ≫ τ = const x}) :
    (pullbackConstHomEquiv x y).symm τ ≫ pullback.snd _ _ = homEquiv.symm ⟨τ.val, τ.property.1⟩ :=
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
        (pullbackConstHomEquiv x y (yonedaEquiv.symm s)).val) :=
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
  · simp only [join.inr_map_assoc, (pullbackConstHomEquiv x y _).property.2, comp_const]

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
