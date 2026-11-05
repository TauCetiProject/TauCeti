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
* `SSet.coslice.map i g h`: the map of coslices `C_{p/} ⟶ D_{q/}` induced by `i : L ⟶ K` and
  `g : C ⟶ D` with `i ≫ p ≫ g = q`, restricting along `i` and composing with `g`; it is functorial
  (`SSet.coslice.map_id`, `SSet.coslice.map_comp`).
* `SSet.coslice.restrictionMap i p σ`: for `p : X ⟶ S` and `σ : K ⟶ X`, the map
  `X_{σ/} ⟶ X_{i ≫ σ/} ×_{S_{i ≫ σ ≫ p/}} S_{σ ≫ p/}`, through which coCartesian edges are
  defined.

## Main results

* `SSet.coslice.homEquiv`: **the universal property of the coslice**, maps `X ⟶ C_{p/}` correspond
  to maps `K ⋆ X ⟶ C` extending `p`, naturally in `X` (`SSet.coslice.homEquiv_comp_coe`); that is,
  `C_{p/}` represents `SSet.coslice.functor p` (`SSet.coslice.representableBy`).
* `SSet.coslice.objEquiv_app_coe`: the simplices of the image of a map `F : X ⟶ C_{p/}` are the
  restrictions of the corresponding map `K ⋆ X ⟶ C`.
* `SSet.coslice.comp_π`: under the universal property, the projection to `C` is the restriction to
  `X`.
* `SSet.coslice.isPullback_map`: coslices preserve pullback squares.
* `SSet.coslice.isPullback_restrictionMap`, `SSet.coslice.restrictionMap_comp` and
  `SSet.coslice.isPullback_restrictionMapComp`: the behaviour of restriction maps under base
  change and composition.
* `SSet.coslice.hasLiftingProperty_restrictionMap`: lifting problems against a restriction map are
  extension problems along a pushout-join `(L ⋆ Y) ∪ (K ⋆ B) ⟶ K ⋆ Y`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.9 and the proof of Proposition 2.1.2.1.
-/

public section

open CategoryTheory Limits Opposite Simplicial

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

/-- Under the universal property, `SSet.coslice.map i g h` corresponds to the universal map
`K ⋆ C_{p/} ⟶ C` precomposed with `i ⋆ C_{p/}` and postcomposed with `g`. -/
@[simp]
lemma homEquiv_map_coe (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) :
    (homEquiv (map i g h)).1 = join.map i (𝟙 _) ≫ (homEquiv (𝟙 (coslice p))).1 ≫ g := by
  rw [map, Equiv.apply_symm_apply]

/-- Pushing cocones forward along an isomorphism is an isomorphism of coslices. -/
instance isIso_map (g : C ⟶ D) [IsIso g] {r : K ⟶ D} (h : 𝟙 K ≫ p ≫ g = r) :
    IsIso (map (𝟙 K) g h) :=
  ⟨map (𝟙 K) (inv g) (by simp [← h]), hom_ext (by simp [map_comp]),
    hom_ext (by simp [map_comp])⟩

/-- Coslices preserve pullbacks: for a pullback square of simplicial sets with top-left corner
`C'`, the coslices under a diagram `p' : K ⟶ C'` and under its images in the other corners form a
pullback square. -/
lemma isPullback_map {C' D' : SSet.{u}} {t : C' ⟶ C} {l : C' ⟶ D'} {r : C ⟶ D} {b : D' ⟶ D}
    (sq : IsPullback t l r b) {p' : K ⟶ C'} {pD' : K ⟶ D'} {pD : K ⟶ D}
    (ht : 𝟙 K ≫ p' ≫ t = p) (hl : 𝟙 K ≫ p' ≫ l = pD') (hr : 𝟙 K ≫ p ≫ r = pD)
    (hb : 𝟙 K ≫ pD' ≫ b = pD) :
    IsPullback (map (𝟙 K) t ht) (map (𝟙 K) l hl) (map (𝟙 K) r hr) (map (𝟙 K) b hb) := by
  have hw : map (𝟙 K) t ht ≫ map (𝟙 K) r hr = map (𝟙 K) l hl ≫ map (𝟙 K) b hb :=
    hom_ext (by simp [map_comp, sq.w])
  -- A cone over the cospan consists of maps `K ⋆ T ⟶ C` and `K ⋆ T ⟶ D'` agreeing in `D`, which
  -- lift uniquely to `K ⋆ T ⟶ C'`.
  have hcond (s : PullbackCone (map (𝟙 K) r hr) (map (𝟙 K) b hb)) :
      (homEquiv s.fst).1 ≫ r = (homEquiv s.snd).1 ≫ b := by
    simpa using congrArg (fun F ↦ (homEquiv F).1) s.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ homEquiv.symm ⟨sq.lift _ _ (hcond s), sq.hom_ext
      (by rw [Category.assoc, sq.lift_fst, (homEquiv s.fst).2, ← ht, Category.id_comp])
      (by rw [Category.assoc, sq.lift_snd, (homEquiv s.snd).2, ← hl, Category.id_comp])⟩)
    (fun s ↦ hom_ext (by simp)) (fun s ↦ hom_ext (by simp)) (fun s m hm₁ hm₂ ↦ hom_ext ?_))
  have h₁ := congrArg (fun F ↦ (homEquiv F).1) hm₁
  have h₂ := congrArg (fun F ↦ (homEquiv F).1) hm₂
  simp only [homEquiv_comp_map_coe, join.map_id, Category.id_comp] at h₁ h₂
  rw [Equiv.apply_symm_apply]
  exact sq.hom_ext (by simp [h₁]) (by simp [h₂])

section restrictionMap

variable {L X S : SSet.{u}}

/-- For maps `i : L ⟶ K`, `p : X ⟶ S` and a diagram `σ : K ⟶ X`, the map
`X_{σ/} ⟶ X_{i ≫ σ/} ×_{S_{i ≫ σ ≫ p/}} S_{σ ≫ p/}` which restricts a cocone under `σ` along `i`
and pushes it forward along `p`. For `i` the inclusion of the source vertex of an edge `σ`, this
is the map whose being a trivial fibration makes `σ` a `p`-coCartesian edge. -/
noncomputable def restrictionMap (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    coslice σ ⟶ pullback (map (𝟙 L) p (by simp) : coslice (i ≫ σ) ⟶ coslice (i ≫ σ ≫ p))
      (map i (𝟙 S) (by simp) : coslice (σ ≫ p) ⟶ coslice (i ≫ σ ≫ p)) :=
  pullback.lift (map i (𝟙 X) (by simp)) (map (𝟙 K) p (by simp)) (hom_ext (by simp [map_comp]))

@[reassoc (attr := simp)]
lemma restrictionMap_fst (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ pullback.fst _ _ = map i (𝟙 X) (by simp) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrictionMap_snd (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ pullback.snd _ _ = map (𝟙 K) p (by simp) :=
  pullback.lift_snd _ _ _

/-- For an isomorphism `p`, the map `SSet.coslice.restrictionMap i p σ` is an isomorphism. -/
instance isIso_restrictionMap (i : L ⟶ K) (p : X ⟶ S) [IsIso p] (σ : K ⟶ X) :
    IsIso (restrictionMap i p σ) := by
  have : IsIso (restrictionMap i p σ ≫ pullback.snd _ _) := by
    rw [restrictionMap_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd _ _)

/-- Restriction maps are stable under base change: for a pullback square of simplicial sets
with sides `t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, and a diagram
`σ : K ⟶ X'`, the restriction map for `p'` and `σ` is the base change of the restriction map for
`p` and `σ ≫ t`. -/
lemma isPullback_restrictionMap {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
    {b : S' ⟶ S} (sq : IsPullback t p' p b) (i : L ⟶ K) (σ : K ⟶ X') :
    IsPullback (map (𝟙 K) t (by simp) : coslice σ ⟶ coslice (σ ≫ t)) (restrictionMap i p' σ)
      (restrictionMap i p (σ ≫ t))
      (pullback.map _ _ _ _ (map (𝟙 L) t (by simp)) (map (𝟙 K) b (by simp [sq.w]))
        (map (𝟙 L) b (by simp [sq.w])) (hom_ext (by simp [map_comp, sq.w]))
        (hom_ext (by simp [map_comp]))) := by
  have hK := isPullback_map sq (p' := σ) (p := σ ≫ t) (pD' := σ ≫ p') (pD := (σ ≫ t) ≫ p)
    (by simp) (by simp) (by simp) (by simp [sq.w])
  -- A cone consists of a cocone `F` under `σ ≫ t` and a point `G` of the pullback for `p'`, and
  -- the lift is the cocone under `σ` given by `F` and the second component of `G`.
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := map (𝟙 K) t (by simp)) (snd := restrictionMap i p' σ)
    (pullback.hom_ext (hom_ext (by simp [map_comp])) (hom_ext (by simp [map_comp, sq.w])))
    (fun s ↦ hK.lift s.fst (s.snd ≫ pullback.snd _ _)
      (by simpa [map_comp] using s.condition =≫ pullback.snd _ _))
    (fun s ↦ hK.lift_fst _ _ _) (fun s ↦ pullback.hom_ext ?_ ?_) (fun s m hm₁ hm₂ ↦ ?_))
  · -- Both maps `L ⋆ T ⟶ X'` agree after composing with `t` and with `p'`.
    have h₁ := congrArg (fun F ↦ (homEquiv F).1) (hK.lift_fst s.fst
      (s.snd ≫ pullback.snd _ _) (by simpa [map_comp] using s.condition =≫ pullback.snd _ _))
    have h₂ := congrArg (fun F ↦ (homEquiv F).1) (hK.lift_snd s.fst
      (s.snd ≫ pullback.snd _ _) (by simpa [map_comp] using s.condition =≫ pullback.snd _ _))
    have h₃ := congrArg (fun F ↦ (homEquiv F).1) (s.condition =≫ pullback.fst _ _)
    have h₄ := congrArg (fun F ↦ (homEquiv F).1) (s.snd ≫=
      pullback.condition (f := map (𝟙 L) p' (by simp)) (g := map i (𝟙 S') (by simp)))
    rw [← Category.assoc s.snd, ← Category.assoc s.snd] at h₄
    rw [homEquiv_comp_map_coe, join.map_id, Category.id_comp] at h₁ h₂
    simp only [Category.assoc, restrictionMap_fst, pullback.lift_fst] at h₃
    rw [← Category.assoc s.snd, homEquiv_comp_map_coe, homEquiv_comp_map_coe] at h₃
    rw [homEquiv_comp_map_coe, homEquiv_comp_map_coe] at h₄
    simp only [join.map_id, Category.id_comp, Category.comp_id] at h₃ h₄
    simp only [Category.assoc, restrictionMap_fst]
    refine hom_ext ?_
    rw [homEquiv_comp_map_coe, Category.comp_id]
    exact sq.hom_ext (by simp only [Category.assoc, h₁, h₃])
      (by simp only [Category.assoc, h₂, h₄])
  · simp
  · exact hK.hom_ext (by simpa using hm₁)
      (by simpa using hm₂ =≫ pullback.snd _ _)

/-- **Lifting against a restriction map is extension along a pushout-join.** For a monomorphism
`j : L ⟶ K`, a subcomplex `B` of `Y` and a map `p : X ⟶ S` with the right lifting property with
respect to the inclusion of `(j(L) ⋆ Y) ∪ (K ⋆ B)` into `K ⋆ Y`, the restriction map
`X_{σ/} ⟶ X_{j ≫ σ/} ×_{S_{j ≫ σ ≫ p/}} S_{σ ≫ p/}` has the right lifting property with respect
to `B ⟶ Y`. Indeed, through the universal property of the coslice a lifting square amounts to maps
`K ⋆ B ⟶ X` and `L ⋆ Y ⟶ X`, agreeing on `L ⋆ B` and lying over a map `K ⋆ Y ⟶ S`, and a lift is
an extension of the glued map to `K ⋆ Y` over `S`. -/
theorem hasLiftingProperty_restrictionMap (j : L ⟶ K) [Mono j] {Y : SSet.{u}} (B : Y.Subcomplex)
    (p : X ⟶ S) (σ : K ⟶ X) [HasLiftingProperty ((Subcomplex.range j).unionJoin B).ι p] :
    HasLiftingProperty B.ι (restrictionMap j p σ) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  let A := Subcomplex.range j
  -- The cocone `α` under `σ` on `B`, the cocone `β` under `j ≫ σ` on `Y` and its image `γ` in
  -- `S`, a cocone under `σ ≫ p` on `Y`, with their compatibilities.
  let α := (homEquiv a).1
  let β := (homEquiv (b ≫ pullback.fst _ _)).1
  let γ := (homEquiv (b ≫ pullback.snd _ _)).1
  have hαβ : join.map j (𝟙 _) ≫ α = join.map (𝟙 L) B.ι ≫ β := by
    have h := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.fst _ _)
    simp only [Category.assoc, restrictionMap_fst] at h
    rwa [homEquiv_comp_map_coe, Category.comp_id, homEquiv_comp_coe] at h
  have hαγ : α ≫ p = join.map (𝟙 K) B.ι ≫ γ := by
    have h := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.snd _ _)
    simp only [Category.assoc, restrictionMap_snd] at h
    rwa [homEquiv_comp_map_coe, join.map_id, Category.id_comp, homEquiv_comp_coe] at h
  have hβγ : β ≫ p = join.map j (𝟙 Y) ≫ γ := by
    have h := congrArg (fun F ↦ (homEquiv F).1) (b ≫= pullback.condition)
    simp only [← Category.assoc] at h
    rwa [homEquiv_comp_map_coe, homEquiv_comp_map_coe, join.map_id, Category.id_comp,
      Category.comp_id] at h
  -- Transport `β` along the isomorphism `L ≅ j(L)` and glue it with `α` on the pushout-join.
  have he : inv (Subcomplex.toRange j) ≫ j = A.ι := by
    rw [IsIso.inv_comp_eq, Subcomplex.toRange_ι]
  let β' := join.map (inv (Subcomplex.toRange j)) (𝟙 Y) ≫ β
  have hpush := Subcomplex.unionJoin.isPushout A B
  have hw : join.map (𝟙 (A : SSet)) B.ι ≫ β' = join.map A.ι (𝟙 (B : SSet)) ≫ α :=
    calc join.map (𝟙 (A : SSet)) B.ι ≫ β' =
        join.map (inv (Subcomplex.toRange j)) (𝟙 _) ≫ join.map (𝟙 L) B.ι ≫ β := by
          simp only [β', ← join.map_comp_assoc, Category.id_comp, Category.comp_id]
      _ = join.map A.ι (𝟙 (B : SSet)) ≫ α := by
          rw [← hαβ, ← join.map_comp_assoc, he, Category.id_comp]
  have sq' : CommSq (hpush.desc β' α hw) (A.unionJoin B).ι p γ := ⟨hpush.hom_ext
    (by simp only [IsPushout.inl_desc_assoc, Subcomplex.unionJoin.ι₁_ι_assoc, β',
      Category.assoc, hβγ, ← join.map_comp_assoc, he, Category.id_comp])
    (by simp only [IsPushout.inr_desc_assoc, Subcomplex.unionJoin.ι₂_ι_assoc, hαγ])⟩
  have h₁ : join.map A.ι (𝟙 Y) ≫ sq'.lift = β' := by
    rw [← Subcomplex.unionJoin.ι₁_ι, Category.assoc, sq'.fac_left, IsPushout.inl_desc]
  have h₂ : join.map (𝟙 K) B.ι ≫ sq'.lift = α := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, sq'.fac_left, IsPushout.inr_desc]
  have hj : join.map j (𝟙 Y) = join.map (Subcomplex.toRange j) (𝟙 Y) ≫ join.map A.ι (𝟙 Y) := by
    rw [← join.map_comp, Category.comp_id, Subcomplex.toRange_ι]
  refine ⟨⟨⟨homEquiv.symm ⟨sq'.lift, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inl _ _ ≫ sq'.lift = join.inl _ _ ≫ join.map (𝟙 K) B.ι ≫ sq'.lift := by
          rw [join.inl_map_assoc, Category.id_comp]
      _ = σ := by rw [h₂, (homEquiv a).2]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h₂])
  · refine pullback.hom_ext (hom_ext ?_) (hom_ext ?_)
    · rw [Category.assoc, restrictionMap_fst, homEquiv_comp_map_coe, Equiv.apply_symm_apply,
        Category.comp_id, hj, Category.assoc, h₁]
      simp only [β', β, ← join.map_comp_assoc, IsIso.hom_inv_id, Category.id_comp, join.map_id]
    · rw [Category.assoc, restrictionMap_snd, homEquiv_comp_map_coe, Equiv.apply_symm_apply,
        join.map_id, Category.id_comp]
      exact sq'.fac_right

section comp

variable {Z : SSet.{u}} (i : L ⟶ K) (p : X ⟶ S) (r : S ⟶ Z) (σ : K ⟶ X)

/-- For maps `p : X ⟶ S` and `r : S ⟶ Z`, the map
`X_{i ≫ σ/} ×_{S_{i ≫ σ ≫ p/}} S_{σ ≫ p/} ⟶ X_{i ≫ σ/} ×_{Z_{i ≫ σ ≫ p ≫ r/}} Z_{σ ≫ p ≫ r/}`
pushing the second component forward along `r`. Composed with the restriction map for `p`, it is
the restriction map for `p ≫ r` (`SSet.coslice.restrictionMap_comp`), and it is a base change of
the restriction map for `r` and `σ ≫ p` (`SSet.coslice.isPullback_restrictionMapComp`). -/
noncomputable def restrictionMapComp :
    pullback (map (𝟙 L) p (by simp) : coslice (i ≫ σ) ⟶ coslice (i ≫ σ ≫ p))
        (map i (𝟙 S) (by simp) : coslice (σ ≫ p) ⟶ coslice (i ≫ σ ≫ p)) ⟶
      pullback (map (𝟙 L) (p ≫ r) (by simp) : coslice (i ≫ σ) ⟶ coslice (i ≫ σ ≫ p ≫ r))
        (map i (𝟙 Z) (by simp) : coslice (σ ≫ p ≫ r) ⟶ coslice (i ≫ σ ≫ p ≫ r)) :=
  pullback.map _ _ _ _ (𝟙 _) (map (𝟙 K) r (by simp)) (map (𝟙 L) r (by simp))
    (by simp [map_comp]) (by simp [map_comp])

@[reassoc (attr := simp)]
lemma restrictionMapComp_fst :
    restrictionMapComp i p r σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [restrictionMapComp]

@[reassoc (attr := simp)]
lemma restrictionMapComp_snd :
    restrictionMapComp i p r σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ map (𝟙 K) r (by simp) :=
  pullback.lift_snd _ _ _

/-- The restriction map for a composite `p ≫ r` factors through the restriction map for `p`. -/
lemma restrictionMap_comp :
    restrictionMap i (p ≫ r) σ = restrictionMap i p σ ≫ restrictionMapComp i p r σ :=
  pullback.hom_ext (by simp) (by simp [map_comp])

/-- The map `SSet.coslice.restrictionMapComp i p r σ` is the base change of the restriction map
for `r` and `σ ≫ p` along the map pushing the first component forward along `p`. -/
lemma isPullback_restrictionMapComp :
    IsPullback (pullback.snd _ _) (restrictionMapComp i p r σ) (restrictionMap i r (σ ≫ p))
      (pullback.map _ _ _ _ (map (𝟙 L) p (by simp)) (map (𝟙 K) (𝟙 Z) (by simp))
        (map (𝟙 L) (𝟙 Z) (by simp)) (by simp [map_comp]) (by simp)) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := pullback.snd _ _) (snd := restrictionMapComp i p r σ)
    (pullback.hom_ext (by simpa using pullback.condition.symm) (by simp))
    (fun s ↦ pullback.lift (s.snd ≫ pullback.fst _ _) s.fst ?_)
    (fun s ↦ pullback.lift_snd _ _ _) (fun s ↦ pullback.hom_ext ?_ ?_)
    (fun s m hm₁ hm₂ ↦ pullback.hom_ext ?_ (by simpa using hm₁)))
  · simpa [map_comp] using (s.condition =≫ pullback.fst _ _).symm
  · simp
  · simpa using s.condition =≫ pullback.snd _ _
  · simpa using hm₂ =≫ pullback.fst _ _

end comp

end restrictionMap

end coslice

end SSet
