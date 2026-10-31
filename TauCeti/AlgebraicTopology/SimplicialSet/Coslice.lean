/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Op
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

## Main definitions

* `SSet.coslice.functor p`: the maps `K ⋆ X ⟶ C` extending `p`, as a presheaf in `X`.
* `SSet.coslice p`: the coslice `C_{p/}`, whose simplices are described by `SSet.coslice.objEquiv`.
* `SSet.coslice.π p`: the projection `C_{p/} ⟶ C`, restricting a simplex `K ⋆ Δ[n] ⟶ C` to
  `Δ[n]`.

## Main results

* `SSet.coslice.homEquiv`: **the universal property of the coslice**, maps `X ⟶ C_{p/}` correspond
  to maps `K ⋆ X ⟶ C` extending `p`, naturally in `X` (`SSet.coslice.homEquiv_comp_coe`); that is,
  `C_{p/}` represents `SSet.coslice.functor p` (`SSet.coslice.representableBy`).
* `SSet.coslice.objEquiv_app_coe`: the simplices of the image of a map `F : X ⟶ C_{p/}` are the
  restrictions of the corresponding map `K ⋆ X ⟶ C`.
* `SSet.coslice.comp_π`: under the universal property, the projection to `C` is the restriction to
  `X`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.9.
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
abbrev coslice : SSet.{u} :=
  (slice (opFunctor.map p)).op

namespace coslice

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
private def opHomEquiv : (X ⟶ coslice p) ≃ (X.op ⟶ slice (opFunctor.map p)) where
  toFun F := opFunctor.map F ≫ opFunctorCompOpFunctorIso.hom.app _
  invFun G := opFunctorCompOpFunctorIso.inv.app X ≫ opFunctor.map G
  left_inv F := by
    dsimp only
    have h := opFunctorCompOpFunctorIso.inv.naturality F
    rw [Functor.id_map, Functor.comp_map] at h
    rw [Functor.map_comp, opFunctor_map_opFunctorCompOpFunctorIso_hom_app, ← Category.assoc, ← h,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  right_inv G := by
    dsimp only
    have h := opFunctorCompOpFunctorIso.hom.naturality G
    rw [Functor.id_map, Functor.comp_map] at h
    rw [Functor.map_comp, opFunctor_map_opFunctorCompOpFunctorIso_inv_app, Category.assoc, h,
      Iso.inv_hom_id_app_assoc]

private lemma opHomEquiv_comp (f : Y ⟶ X) (F : X ⟶ coslice p) :
    opHomEquiv (f ≫ F) = opFunctor.map f ≫ opHomEquiv F := by
  simp [opHomEquiv]

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

/-- The projection to `C` sends a simplex `σ : K ⋆ Δ[n] ⟶ C` of the coslice to its restriction to
`Δ[n]`. -/
@[simp]
lemma π_app {n : SimplexCategoryᵒᵖ} (σ : (coslice p).obj n) :
    (π p).app n σ = yonedaEquiv (join.inr K _ ≫ (objEquiv σ).1) := by
  rw [objEquiv_apply, ← comp_π, yonedaEquiv_comp, Equiv.apply_symm_apply]

end coslice

end SSet
