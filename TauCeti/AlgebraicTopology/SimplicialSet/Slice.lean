/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Basic

/-!
# Slices of simplicial sets

For a simplicial set `C` and a diagram `p : K ⟶ C`, the slice `C_{/p}` is the simplicial set whose
`n`-simplices are the maps `Δ[n] ⋆ K ⟶ C` from the join that restrict to `p` on `K`. Its vertices
are the cones over `p`, with cone point the image of `Δ[0]`, and its edges are morphisms of cones.
A limit of `p` in a quasicategory is a final object of `C_{/p}`, so this is the construction
through which limits are defined; colimits are dually the initial objects of the coslice `C_{p/}`,
built from the joins `K ⋆ Δ[n]`.

The slice is characterized by its universal property (`SSet.slice.homEquiv`): maps of simplicial
sets `X ⟶ C_{/p}` correspond to maps `X ⋆ K ⟶ C` extending `p`, naturally in `X`. In other words,
`C_{/p}` represents the presheaf `SSet.slice.functor p` of such maps
(`SSet.slice.representableBy`), and the definition of `C_{/p}` is the restriction of this presheaf
to standard simplices.

## Main definitions

* `SSet.slice.functor p`: the maps `X ⋆ K ⟶ C` extending `p`, as a presheaf in `X`.
* `SSet.slice p`: the slice `C_{/p}`, whose simplices are described by `SSet.slice.objEquiv`.
* `SSet.slice.π p`: the projection `C_{/p} ⟶ C`, restricting a simplex `Δ[n] ⋆ K ⟶ C` to `Δ[n]`.
* `SSet.slice.map i g h`: the map of slices `C_{/p} ⟶ D_{/q}` induced by `i : L ⟶ K` and
  `g : C ⟶ D` with `i ≫ p ≫ g = q`, restricting cones along `i` and pushing them forward along `g`.
* `SSet.slice.restrictionMap i p σ`: for `p : X ⟶ S` and `σ : K ⟶ X`, the map
  `X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}`, through which Cartesian edges are defined.

## Main results

* `SSet.slice.homEquiv`: **the universal property of the slice**, maps `X ⟶ C_{/p}` correspond
  to maps `X ⋆ K ⟶ C` extending `p`, naturally in `X` (`SSet.slice.homEquiv_comp_coe`).
* `SSet.slice.objEquiv_app_coe`: the simplices of the image of a map `F : X ⟶ C_{/p}` are the
  restrictions of the corresponding map `X ⋆ K ⟶ C`.
* `SSet.slice.comp_π`: under the universal property, the projection to `C` is the restriction to
  `X`.
* `SSet.slice.isIso_π`: the slice over the empty diagram is the whole simplicial set.
* `SSet.slice.isPullback_map`: slices preserve pullback squares.
* `SSet.slice.isPullback_restrictionMap`, `SSet.slice.restrictionMap_comp` and
  `SSet.slice.isPullback_restrictionMapComp`: the behaviour of restriction maps under base change
  and composition.

## Implementation notes

Given `F : X ⟶ C_{/p}`, the map `X ⋆ K ⟶ C` is defined simplexwise. A simplex of `X ⋆ K` either
lies in `K`, where it is sent through `p`, or meets `X`; in the second case it is the image of a
simplex of `Δ[m] ⋆ K` under `g ⋆ K` for a simplex `g : Δ[m] ⟶ X` extending its part in `X`
(`SSet.join.exists_eq_comp_inr_or_exists_eq_comp_map`), and it is sent to the value of `F g` on
that simplex. The extension `g` is chosen along the retraction `SSet.joinFiberZeroRetraction` of
`Δ[m]` onto its part over the vertex `0` of `Δ[1]`, and the value is independent of the choice of
factorization because `F` is compatible with the faces and degeneracies of `X`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.9 and the proof of Proposition 2.4.1.3.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X Y K C : SSet.{u}}

variable (p : K ⟶ C)

namespace slice

/-- The maps `X ⋆ K ⟶ C` extending `p : K ⟶ C` along the inclusion `K ⟶ X ⋆ K`, as a presheaf on
simplicial sets, acting by precomposition with `g ⋆ K`. -/
@[expose]
def functor : SSet.{u}ᵒᵖ ⥤ Type u where
  obj X := {τ : join X.unop K ⟶ C // join.inr X.unop K ≫ τ = p}
  map g := ↾fun τ ↦ ⟨join.map g.unop (𝟙 K) ≫ τ.1, by rw [join.inr_map_assoc, Category.id_comp, τ.2]⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    exact (congrArg (· ≫ τ.1) join.map_id).trans (Category.id_comp _)
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun τ ↦ Subtype.ext ?_
    refine (congrArg (· ≫ τ.1) ?_).trans (Category.assoc _ _ _)
    simpa using join.map_comp g.unop (𝟙 K) f.unop (𝟙 K)

@[simp]
lemma functor_map_coe {X Y : SSet.{u}ᵒᵖ} (g : X ⟶ Y) (τ : (functor p).obj X) :
    ((functor p).map g τ).1 = join.map g.unop (𝟙 K) ≫ τ.1 :=
  (rfl)

end slice

/-- The slice `C_{/p}` of a simplicial set `C` over a diagram `p : K ⟶ C`. Its `n`-simplices are
the maps `Δ[n] ⋆ K ⟶ C` extending `p` along the inclusion of `K`; in particular its vertices are
the cones `Δ[0] ⋆ K ⟶ C` over `p`. -/
@[expose]
def slice : SSet.{u} :=
  stdSimplex.op ⋙ slice.functor p

namespace slice

variable {p}

/-- The `n`-simplices of the slice `C_{/p}` are the maps `Δ[n] ⋆ K ⟶ C` extending `p`. -/
def objEquiv {n : SimplexCategoryᵒᵖ} :
    (slice p).obj n ≃ {σ : join (stdSimplex.obj n.unop) K ⟶ C // join.inr _ K ≫ σ = p} :=
  Equiv.refl _

@[simp]
lemma objEquiv_map_coe {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (σ : (slice p).obj n) :
    (objEquiv ((slice p).map f σ)).1 = join.map (stdSimplex.map f.unop) (𝟙 K) ≫ (objEquiv σ).1 :=
  (rfl)

variable (p) in
/-- The projection `C_{/p} ⟶ C`, restricting a simplex `Δ[n] ⋆ K ⟶ C` of the slice to `Δ[n]`. -/
def π : slice p ⟶ C where
  app n := ↾fun σ ↦ yonedaEquiv (join.inl _ K ≫ (objEquiv σ).1)
  naturality n m f := by
    ext σ
    dsimp
    rw [objEquiv_map_coe, join.inl_map_assoc, ← yonedaEquiv_naturality, Quiver.Hom.op_unop]

@[simp]
lemma π_app {n : SimplexCategoryᵒᵖ} (σ : (slice p).obj n) :
    (π p).app n σ = yonedaEquiv (join.inl _ K ≫ (objEquiv σ).1) :=
  (rfl)

/-- The map to the slice given by a map `τ : X ⋆ K ⟶ C` extending `p`: a simplex `x` of `X` goes to
the restriction of `τ` along `x ⋆ K`. -/
private def ofHom (τ : {τ : join X K ⟶ C // join.inr X K ≫ τ = p}) : X ⟶ slice p where
  app n := ↾fun x ↦ objEquiv.symm ⟨join.map (yonedaEquiv.symm x) (𝟙 K) ≫ τ.1,
    by rw [join.inr_map_assoc, Category.id_comp, τ.2]⟩
  naturality n m f := by
    ext x
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    -- Both sides are the restrictions of `τ` along `Δ[m] ⋆ K ⟶ Δ[n] ⋆ K ⟶ X ⋆ K`.
    refine objEquiv.injective (Subtype.ext ?_)
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    rw [objEquiv_map_coe, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← join.map_comp_assoc,
      Category.comp_id, yonedaEquiv_symm_naturality_left, Quiver.Hom.op_unop]

/-- A map `F : X ⟶ C_{/p}` sends each simplex `g : Δ[a] ⟶ X` to a map `Δ[a] ⋆ K ⟶ C`,
compatibly with precomposition by maps of standard simplices. -/
private lemma objEquiv_app_yonedaEquiv_comp (F : X ⟶ slice p) {a b : SimplexCategory}
    (h : stdSimplex.obj b ⟶ stdSimplex.obj a) (g : stdSimplex.obj a ⟶ X) :
    (objEquiv (F.app _ (yonedaEquiv (h ≫ g)))).1 =
      join.map h (𝟙 K) ≫ (objEquiv (F.app _ (yonedaEquiv g))).1 := by
  obtain ⟨θ, rfl⟩ : ∃ θ, stdSimplex.map θ = h := ⟨_, stdSimplex.map_preimage h⟩
  rw [← yonedaEquiv_naturality, NatTrans.naturality_apply, objEquiv_map_coe, Quiver.Hom.unop_op]

/-- Two retractions along equal maps to `Δ[1]` agree. -/
private lemma joinFiberZeroRetraction_app_coe_congr {m k : ℕ} {q q' : Δ[m] ⟶ Δ[1]}
    (hq : q = q') (h : yonedaEquiv q 0 = 0) (h' : yonedaEquiv q' 0 = 0) (y : Δ[m] _⦋k⦌) :
    ((joinFiberZeroRetraction q h).app _ y).1 = ((joinFiberZeroRetraction q' h').app _ y).1 := by
  subst hq
  rfl

/-- The value on an `m`-simplex of `X ⋆ K`, given by its join data `d`, of the map `X ⋆ K ⟶ C`
attached to `F : X ⟶ C_{/p}`. If the simplex meets `X`, extend its part in `X` to a simplex
`g : Δ[m] ⟶ X` along the retraction of `Δ[m]` onto its part over `0`, and evaluate the simplex
`F g : Δ[m] ⋆ K ⟶ C` of the slice on the simplex of `Δ[m] ⋆ K` with the same splitting. Otherwise
the simplex lies in `K`, and its value is given by `p`. -/
private noncomputable def value (F : X ⟶ slice p) {m : ℕ} (d : JoinData Δ[m] X K) : C _⦋m⦌ :=
  if h : yonedaEquiv d.p 0 = 0 then
    yonedaEquiv (join.homEquiv.symm ⟨d.p, (joinFiber d.p 0).ι, d.right⟩ ≫
      (objEquiv (F.app _ (yonedaEquiv (joinFiberZeroRetraction d.p h ≫ d.left)))).1)
  else p.app _ (d.right.app _ ⟨yonedaEquiv (𝟙 _), by simp [joinFiber_one_eq_top h]⟩)

/-- On a simplex of `X ⋆ K` coming from a simplex `k` of `K`, the value is `p k`. -/
private lemma value_of_eq_comp_inr (F : X ⟶ slice p) {m : ℕ} (d : JoinData Δ[m] X K)
    (k : Δ[m] ⟶ K) (hd : join.homEquiv.symm d = k ≫ join.inr X K) :
    value F d = yonedaEquiv (k ≫ p) := by
  have hd' : d = join.homEquiv (k ≫ join.inr X K) := by rw [← hd, Equiv.apply_symm_apply]
  have h : ¬ yonedaEquiv d.p 0 = 0 := by
    rw [hd', join.homEquiv_p, Category.assoc, join.inr_π, yonedaEquiv_comp,
      stdSimplex.const_app_apply]
    decide
  rw [value, dite_eq_right h, yonedaEquiv_comp]
  refine congrArg (p.app _) ((JoinData.congr_right_app hd' _ _ ?_).trans ?_)
  · simp
  · refine (JoinData.congr_right_app (join.homEquiv_apply _) _ _ ?_).trans ?_
    · simp
    · rw [JoinData.precomp_right_app]
      exact join.univ_right_app_inr_app (k.app _ (yonedaEquiv (𝟙 _))) _

/-- On a simplex of `X ⋆ K` that is the image of a simplex `t` of `Δ[a] ⋆ K` under `g ⋆ K` for a
simplex `g : Δ[a] ⟶ X`, the value is the value of the simplex `F g` of the slice at `t`. -/
private lemma value_of_eq_comp_map (F : X ⟶ slice p) {m : ℕ} (d : JoinData Δ[m] X K)
    {a : SimplexCategory} (t : Δ[m] ⟶ join (stdSimplex.obj a) K) (g : stdSimplex.obj a ⟶ X)
    (hd : join.homEquiv.symm d = t ≫ join.map g (𝟙 K)) :
    value F d = yonedaEquiv (t ≫ (objEquiv (F.app _ (yonedaEquiv g))).1) := by
  set e := join.homEquiv t
  have hd' : d = e.postcomp g (𝟙 K) := by
    rw [← join.homEquiv_comp_map, ← hd, Equiv.apply_symm_apply]
  have hp : d.p = e.p := by rw [hd', JoinData.postcomp_p]
  by_cases h : yonedaEquiv e.p 0 = 0
  · have h' : yonedaEquiv d.p 0 = 0 := hp ▸ h
    have h₁ : (⟨d.p, (joinFiber d.p 0).ι, d.right⟩ : JoinData Δ[m] Δ[m] K) =
        ⟨e.p, (joinFiber e.p 0).ι, e.right⟩ :=
      JoinData.ext hp (fun _ _ _ _ ↦ rfl) fun n x hx hx' ↦
        (JoinData.congr_right_app hd' x hx (by rwa [JoinData.postcomp_p, ← hp])).trans
          (JoinData.postcomp_right_app _ _ _ _ _)
    have h₂ : joinFiberZeroRetraction d.p h' ≫ d.left =
        joinFiberZeroRetraction e.p h ≫ e.left ≫ g := by
      ext n y
      induction n using Opposite.rec with | op n
      induction n using SimplexCategory.rec with | _ n
      have hy := ((joinFiberZeroRetraction d.p h').app _ y).2
      refine (JoinData.congr_left_app hd' _ hy ?_).trans ?_
      · rwa [JoinData.postcomp_p, ← hp]
      · rw [JoinData.postcomp_left_app]
        exact congrArg (g.app _) (congrArg (e.left.app _)
          (Subtype.ext (joinFiberZeroRetraction_app_coe_congr hp h' h y)))
    rw [value, dite_eq_left h', h₁, h₂, ← Category.assoc, objEquiv_app_yonedaEquiv_comp,
      ← Category.assoc, ← join.homEquiv_symm_eq_comp_map, Equiv.symm_apply_apply]
  · obtain ⟨k, rfl⟩ := join.exists_eq_comp_inr t h
    rw [value_of_eq_comp_inr F d k (by rw [hd, Category.assoc, join.inr_map, Category.id_comp]),
      Category.assoc, (objEquiv _).2]

/-- The map `X ⋆ K ⟶ C` attached to a map `F : X ⟶ C_{/p}`. -/
private noncomputable def toHom (F : X ⟶ slice p) : join X K ⟶ C where
  app n := ↾fun s ↦ value F (m := n.unop.len) (join.objEquiv s)
  naturality n n' f := by
    ext s
    induction n using Opposite.rec with | op n
    induction n using SimplexCategory.rec with | _ n
    induction n' using Opposite.rec with | op n'
    induction n' using SimplexCategory.rec with | _ n'
    dsimp
    have hθ (d : JoinData Δ[n] X K) : join.homEquiv.symm (d.precomp (stdSimplex.map f.unop)) =
        stdSimplex.map f.unop ≫ join.homEquiv.symm d := by
      rw [Equiv.symm_apply_eq, join.homEquiv_comp, Equiv.apply_symm_apply]
    rw [join.objEquiv_map]
    rcases join.exists_eq_comp_inr_or_exists_eq_comp_map
      (join.homEquiv.symm (join.objEquiv s)) with ⟨k, hk⟩ | ⟨t, g, ht⟩
    · rw [value_of_eq_comp_inr F _ k hk, value_of_eq_comp_inr F _ (stdSimplex.map f.unop ≫ k)
        (by rw [hθ, hk, Category.assoc]), Category.assoc, ← yonedaEquiv_naturality,
        Quiver.Hom.op_unop]
    · rw [value_of_eq_comp_map F _ t g ht, value_of_eq_comp_map F _ (stdSimplex.map f.unop ≫ t) g
        (by rw [hθ, ht, Category.assoc]), Category.assoc, ← yonedaEquiv_naturality,
        Quiver.Hom.op_unop]

private lemma toHom_app {n : ℕ} (F : X ⟶ slice p) (s : (join X K) _⦋n⦌) :
    (toHom F).app _ s = value F (join.objEquiv s) :=
  (rfl)

private lemma inr_comp_toHom (F : X ⟶ slice p) : join.inr X K ≫ toHom F = p := by
  ext n k
  induction n using Opposite.rec with | op n
  induction n using SimplexCategory.rec with | _ n
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [toHom_app, value_of_eq_comp_inr F _ (yonedaEquiv.symm k)
    (by rw [join.homEquiv_symm_objEquiv, yonedaEquiv_symm_comp]), yonedaEquiv_symm_comp,
    Equiv.apply_symm_apply]

private lemma ofHom_app_coe {n : SimplexCategory}
    (τ : {τ : join X K ⟶ C // join.inr X K ≫ τ = p}) (x : X.obj (op n)) :
    (objEquiv ((ofHom τ).app _ x)).1 = join.map (yonedaEquiv.symm x) (𝟙 K) ≫ τ.1 :=
  (rfl)

/-- **The universal property of the slice**: maps `X ⟶ C_{/p}` correspond to maps `X ⋆ K ⟶ C`
extending `p`. A map `τ : X ⋆ K ⟶ C` corresponds to the map sending a simplex `x : Δ[n] ⟶ X` to the
simplex `(x ⋆ K) ≫ τ` of the slice (`SSet.slice.homEquiv_symm_app_coe`). -/
noncomputable def homEquiv : (X ⟶ slice p) ≃ {τ : join X K ⟶ C // join.inr X K ≫ τ = p} where
  toFun F := ⟨toHom F, inr_comp_toHom F⟩
  invFun τ := ofHom τ
  left_inv F := by
    ext n x
    induction n using Opposite.rec with | op n
    refine objEquiv.injective (Subtype.ext ?_)
    dsimp only
    simp only [TypeCat.Fun.toFun_apply]
    rw [ofHom_app_coe]
    ext m s
    induction m using Opposite.rec with | op m
    induction m using SimplexCategory.rec with | _ m
    simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [toHom_app, value_of_eq_comp_map F _ (yonedaEquiv.symm s) _
      (by rw [join.homEquiv_symm_objEquiv, yonedaEquiv_symm_comp]), Equiv.apply_symm_apply,
      yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  right_inv τ := by
    refine Subtype.ext ?_
    ext m s
    induction m using Opposite.rec with | op m
    induction m using SimplexCategory.rec with | _ m
    dsimp only
    simp only [TypeCat.Fun.toFun_apply]
    rw [toHom_app]
    rcases join.exists_eq_comp_inr_or_exists_eq_comp_map
      (join.homEquiv.symm (join.objEquiv s)) with ⟨k, hk⟩ | ⟨t, g, ht⟩
    · rw [value_of_eq_comp_inr _ _ k hk, ← whisker_eq k τ.2, ← Category.assoc, ← hk,
        join.homEquiv_symm_objEquiv, yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
    · rw [value_of_eq_comp_map _ _ t g ht, ofHom_app_coe, Equiv.symm_apply_apply,
        ← Category.assoc, ← ht, join.homEquiv_symm_objEquiv, yonedaEquiv_symm_comp,
        Equiv.apply_symm_apply]

/-- The map to the slice given by `τ : X ⋆ K ⟶ C` sends a simplex `x` of `X` to the simplex
`(x ⋆ K) ≫ τ`. -/
@[simp]
lemma homEquiv_symm_app_coe {n : SimplexCategory}
    (τ : {τ : join X K ⟶ C // join.inr X K ≫ τ = p}) (x : X.obj (op n)) :
    (objEquiv ((homEquiv.symm τ).app _ x)).1 = join.map (yonedaEquiv.symm x) (𝟙 K) ≫ τ.1 :=
  (rfl)

/-- The universal property of the slice is natural in `X`: precomposing with `f : Y ⟶ X`
corresponds to precomposing with `f ⋆ K`. -/
@[simp]
lemma homEquiv_comp_coe (f : Y ⟶ X) (F : X ⟶ slice p) :
    (homEquiv (f ≫ F)).1 = join.map f (𝟙 K) ≫ (homEquiv F).1 := by
  obtain ⟨τ, rfl⟩ := homEquiv.symm.surjective F
  have : f ≫ homEquiv.symm τ = homEquiv.symm ⟨join.map f (𝟙 K) ≫ τ.1,
      by rw [join.inr_map_assoc, Category.id_comp, τ.2]⟩ := by
    ext n y
    induction n using Opposite.rec with | op n
    refine objEquiv.injective (Subtype.ext ?_)
    simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [homEquiv_symm_app_coe, homEquiv_symm_app_coe, ← join.map_comp_assoc, Category.comp_id,
      yonedaEquiv_symm_comp]
  rw [this, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (p) in
/-- The slice `C_{/p}` represents the presheaf of maps `X ⋆ K ⟶ C` extending `p`. -/
noncomputable def representableBy : (functor p).RepresentableBy (slice p) where
  homEquiv := homEquiv
  homEquiv_comp f g := Subtype.ext (homEquiv_comp_coe f g)

/-- The simplex of the slice that a map `F : X ⟶ C_{/p}` assigns to a simplex `x` of `X` is the
restriction along `x ⋆ K` of the map `X ⋆ K ⟶ C` corresponding to `F`. -/
lemma objEquiv_app_coe {n : SimplexCategory} (F : X ⟶ slice p) (x : X.obj (op n)) :
    (objEquiv (F.app _ x)).1 = join.map (yonedaEquiv.symm x) (𝟙 K) ≫ (homEquiv F).1 := by
  conv_lhs => rw [← homEquiv.symm_apply_apply F]
  exact homEquiv_symm_app_coe _ x

/-- Maps to the slice are equal when the corresponding maps `X ⋆ K ⟶ C` are equal. -/
lemma hom_ext {F G : X ⟶ slice p} (h : (homEquiv F).1 = (homEquiv G).1) : F = G :=
  homEquiv.injective (Subtype.ext h)

/-- The projection of the slice to `C` corresponds, under the universal property, to restricting
along the inclusion `X ⟶ X ⋆ K`. -/
@[reassoc (attr := simp)]
lemma comp_π (F : X ⟶ slice p) : F ≫ π p = join.inl X K ≫ (homEquiv F).1 := by
  conv_lhs => rw [← homEquiv.symm_apply_apply F]
  ext n x
  induction n using Opposite.rec with | op n
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [π_app, homEquiv_symm_app_coe, join.inl_map_assoc, ← Category.assoc, yonedaEquiv_comp,
    yonedaEquiv_comp, Equiv.apply_symm_apply]

variable (p) in
/-- The slice over the empty diagram is the whole simplicial set: when `K` is empty, the
projection `C_{/p} ⟶ C` is an isomorphism. -/
lemma isIso_π (hK : ¬ K.Nonempty) : IsIso (π p) := by
  refine isIso_of_yoneda_map_bijective _ fun X ↦ ⟨fun F G h ↦ hom_ext ?_, fun g ↦ ?_⟩
  · have := join.isIso_inl (K := X) hK
    simpa only [comp_π, cancel_epi] using h
  · have := join.isIso_inl (K := X) hK
    refine ⟨homEquiv.symm ⟨inv (join.inl X K) ≫ g, (isInitialOfNotNonempty hK).hom_ext _ _⟩, ?_⟩
    simp

section map

variable {L D : SSet.{u}} {q : L ⟶ D}

/-- The map of slices `C_{/p} ⟶ D_{/q}` induced by maps `i : L ⟶ K` and `g : C ⟶ D` with
`i ≫ p ≫ g = q`: it sends a simplex `σ : Δ[n] ⋆ K ⟶ C` of `C_{/p}` to `(Δ[n] ⋆ i) ≫ σ ≫ g`
(`SSet.slice.objEquiv_map_app_coe`). Restricting a cone along `i` and pushing it forward
along `g` are the special cases `g = 𝟙 C` and `i = 𝟙 K`. -/
noncomputable def map (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) : slice p ⟶ slice q :=
  homEquiv.symm ⟨join.map (𝟙 _) i ≫ (homEquiv (𝟙 (slice p))).1 ≫ g, by
    rw [join.inr_map_assoc, reassoc_of% (homEquiv (𝟙 (slice p))).2, h]⟩

/-- Under the universal property of the slice, composing with `SSet.slice.map i g h`
corresponds to precomposing with `X ⋆ i` and postcomposing with `g`. -/
@[simp high]
lemma homEquiv_comp_map_coe (F : X ⟶ slice p) (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) :
    (homEquiv (F ≫ map i g h)).1 = join.map (𝟙 X) i ≫ (homEquiv F).1 ≫ g := by
  have hF : (homEquiv F).1 = join.map F (𝟙 K) ≫ (homEquiv (𝟙 (slice p))).1 := by
    rw [← homEquiv_comp_coe, Category.comp_id]
  rw [homEquiv_comp_coe, map, Equiv.apply_symm_apply, hF]
  simp only [Category.assoc, ← join.map_comp_assoc, Category.id_comp, Category.comp_id]

/-- Under the universal property of the slice, `SSet.slice.map i g h` corresponds to the
universal map `C_{/p} ⋆ K ⟶ C` precomposed with `C_{/p} ⋆ i` and postcomposed with `g`. -/
@[simp]
lemma homEquiv_map_coe (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) :
    (homEquiv (map i g h)).1 = join.map (𝟙 _) i ≫ (homEquiv (𝟙 (slice p))).1 ≫ g := by
  rw [map, Equiv.apply_symm_apply]

/-- The map of slices sends a simplex `σ : Δ[n] ⋆ K ⟶ C` to `(Δ[n] ⋆ i) ≫ σ ≫ g`. -/
@[simp]
lemma objEquiv_map_app_coe {n : SimplexCategory} (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q)
    (σ : (slice p).obj (op n)) :
    (objEquiv ((map i g h).app _ σ)).1 = join.map (𝟙 _) i ≫ (objEquiv σ).1 ≫ g := by
  have hσ : (homEquiv (yonedaEquiv.symm σ)).1 = (objEquiv σ).1 := by
    have := objEquiv_app_coe (yonedaEquiv.symm σ) (yonedaEquiv (𝟙 _))
    rw [← yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
      join.map_id, Category.id_comp] at this
    exact this.symm
  rw [objEquiv_app_coe, ← homEquiv_comp_coe, homEquiv_comp_map_coe, hσ]

/-- The map of slices is compatible with the projections to `C` and `D`. -/
@[reassoc]
lemma map_π (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q) : map i g h ≫ π q = π p ≫ g := by
  rw [← Category.id_comp (map i g h), comp_π, homEquiv_comp_map_coe, join.inl_map_assoc,
    Category.id_comp, ← Category.assoc, ← comp_π, Category.id_comp]

/-- Restricting along `𝟙 K` and pushing forward along `𝟙 C` is the identity of `C_{/p}`. -/
@[simp]
lemma map_id (h : 𝟙 K ≫ p ≫ 𝟙 C = p) : map (𝟙 K) (𝟙 C) h = 𝟙 (slice p) :=
  hom_ext (by rw [← Category.id_comp (map _ _ h), homEquiv_comp_map_coe]; simp)

/-- Maps of slices compose: restrictions compose contravariantly and pushforwards covariantly. -/
@[reassoc (attr := simp)]
lemma map_comp {L' D' : SSet.{u}} {q' : L' ⟶ D'} (i : L ⟶ K) (g : C ⟶ D) (h : i ≫ p ≫ g = q)
    (i' : L' ⟶ L) (g' : D ⟶ D') (h' : i' ≫ q ≫ g' = q') :
    map i g h ≫ map i' g' h' = map (i' ≫ i) (g ≫ g') (by rw [← h', ← h]; simp) := by
  refine hom_ext ?_
  rw [← Category.id_comp (map i g h ≫ _), ← Category.assoc, homEquiv_comp_map_coe,
    ← Category.id_comp (map (i' ≫ i) _ _), homEquiv_comp_map_coe, homEquiv_comp_map_coe]
  simp only [Category.assoc, ← join.map_comp_assoc, Category.id_comp]

/-- Pushing cones forward along an isomorphism is an isomorphism of slices. -/
instance isIso_map (g : C ⟶ D) [IsIso g] {r : K ⟶ D} (h : 𝟙 K ≫ p ≫ g = r) :
    IsIso (map (𝟙 K) g h) :=
  ⟨map (𝟙 K) (inv g) (by simp [← h]), hom_ext (by simp), hom_ext (by simp)⟩

/-- Slices preserve pullbacks: for a pullback square of simplicial sets with top-left corner `C'`,
the slices over a diagram `p' : K ⟶ C'` and over its images in the other corners form a pullback
square. -/
lemma isPullback_map {C' D' : SSet.{u}} {t : C' ⟶ C} {l : C' ⟶ D'} {r : C ⟶ D} {b : D' ⟶ D}
    (sq : IsPullback t l r b) {p' : K ⟶ C'} {pD' : K ⟶ D'} {pD : K ⟶ D}
    (ht : 𝟙 K ≫ p' ≫ t = p) (hl : 𝟙 K ≫ p' ≫ l = pD') (hr : 𝟙 K ≫ p ≫ r = pD)
    (hb : 𝟙 K ≫ pD' ≫ b = pD) :
    IsPullback (map (𝟙 K) t ht) (map (𝟙 K) l hl) (map (𝟙 K) r hr) (map (𝟙 K) b hb) := by
  have hw : map (𝟙 K) t ht ≫ map (𝟙 K) r hr = map (𝟙 K) l hl ≫ map (𝟙 K) b hb :=
    hom_ext (by simp [sq.w])
  -- A cone over the cospan consists of maps `T ⋆ K ⟶ C` and `T ⋆ K ⟶ D'` agreeing in `D`, which
  -- lift uniquely to `T ⋆ K ⟶ C'`.
  have hcond (s : Limits.PullbackCone (map (𝟙 K) r hr) (map (𝟙 K) b hb)) :
      (homEquiv s.fst).1 ≫ r = (homEquiv s.snd).1 ≫ b := by
    simpa using congrArg (fun F ↦ (homEquiv F).1) s.condition
  refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk hw
    (fun s ↦ homEquiv.symm ⟨sq.lift _ _ (hcond s), sq.hom_ext
      (by rw [Category.assoc, sq.lift_fst, (homEquiv s.fst).2, ← ht, Category.id_comp])
      (by rw [Category.assoc, sq.lift_snd, (homEquiv s.snd).2, ← hl, Category.id_comp])⟩)
    (fun s ↦ hom_ext (by simp)) (fun s ↦ hom_ext (by simp)) (fun s m hm₁ hm₂ ↦ hom_ext ?_))
  have h₁ := congrArg (fun F ↦ (homEquiv F).1) hm₁
  have h₂ := congrArg (fun F ↦ (homEquiv F).1) hm₂
  simp only [homEquiv_comp_map_coe, join.map_id, Category.id_comp] at h₁ h₂
  rw [Equiv.apply_symm_apply]
  exact sq.hom_ext (by simp [h₁]) (by simp [h₂])

end map

section restrictionMap

variable {L X S : SSet.{u}}

/-- For maps `i : L ⟶ K`, `p : X ⟶ S` and a diagram `σ : K ⟶ X`, the map
`X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` which restricts a cone over `σ` along `i`
and pushes it forward along `p`. For `i` the inclusion of the target vertex of an edge `σ`, this
is the map whose being a trivial fibration makes `σ` a `p`-Cartesian edge. -/
noncomputable def restrictionMap (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    slice σ ⟶ Limits.pullback (map (𝟙 L) p (by simp) : slice (i ≫ σ) ⟶ slice (i ≫ σ ≫ p))
      (map i (𝟙 S) (by simp) : slice (σ ≫ p) ⟶ slice (i ≫ σ ≫ p)) :=
  Limits.pullback.lift (map i (𝟙 X) (by simp)) (map (𝟙 K) p (by simp)) (hom_ext (by simp))

@[reassoc (attr := simp)]
lemma restrictionMap_fst (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ Limits.pullback.fst _ _ = map i (𝟙 X) (by simp) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrictionMap_snd (i : L ⟶ K) (p : X ⟶ S) (σ : K ⟶ X) :
    restrictionMap i p σ ≫ Limits.pullback.snd _ _ = map (𝟙 K) p (by simp) :=
  Limits.pullback.lift_snd _ _ _

/-- For an isomorphism `p`, the map `SSet.slice.restrictionMap i p σ` is an isomorphism. -/
instance isIso_restrictionMap (i : L ⟶ K) (p : X ⟶ S) [IsIso p] (σ : K ⟶ X) :
    IsIso (restrictionMap i p σ) := by
  have : IsIso (restrictionMap i p σ ≫ Limits.pullback.snd _ _) := by
    rw [restrictionMap_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Limits.pullback.snd _ _)

/-- Restriction maps are stable under base change: for a pullback square of simplicial sets
with sides `t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, and a diagram
`σ : K ⟶ X'`, the restriction map for `p'` and `σ` is the base change of the restriction map for
`p` and `σ ≫ t`. -/
lemma isPullback_restrictionMap {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
    {b : S' ⟶ S} (sq : IsPullback t p' p b) (i : L ⟶ K) (σ : K ⟶ X') :
    IsPullback (map (𝟙 K) t (by simp) : slice σ ⟶ slice (σ ≫ t)) (restrictionMap i p' σ)
      (restrictionMap i p (σ ≫ t))
      (Limits.pullback.map _ _ _ _ (map (𝟙 L) t (by simp)) (map (𝟙 K) b (by simp [sq.w]))
        (map (𝟙 L) b (by simp [sq.w])) (hom_ext (by simp [sq.w])) (hom_ext (by simp))) := by
  have hK := isPullback_map sq (p' := σ) (p := σ ≫ t) (pD' := σ ≫ p') (pD := (σ ≫ t) ≫ p)
    (by simp) (by simp) (by simp) (by simp [sq.w])
  -- A cone consists of a cone `F` over `σ ≫ t` and a point `G` of the pullback for `p'`, and the
  -- lift is the cone over `σ` given by `F` and the second component of `G`.
  refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk
    (fst := map (𝟙 K) t (by simp)) (snd := restrictionMap i p' σ)
    (Limits.pullback.hom_ext (hom_ext (by simp)) (hom_ext (by simp [sq.w])))
    (fun s ↦ hK.lift s.fst (s.snd ≫ Limits.pullback.snd _ _)
      (by simpa using s.condition =≫ Limits.pullback.snd _ _))
    (fun s ↦ hK.lift_fst _ _ _) (fun s ↦ Limits.pullback.hom_ext ?_ ?_) (fun s m hm₁ hm₂ ↦ ?_))
  · -- Both maps `T ⋆ L ⟶ X'` agree after composing with `t` and with `p'`.
    have h₁ := congrArg (fun F ↦ (homEquiv F).1) (hK.lift_fst s.fst
      (s.snd ≫ Limits.pullback.snd _ _) (by simpa using s.condition =≫ Limits.pullback.snd _ _))
    have h₂ := congrArg (fun F ↦ (homEquiv F).1) (hK.lift_snd s.fst
      (s.snd ≫ Limits.pullback.snd _ _) (by simpa using s.condition =≫ Limits.pullback.snd _ _))
    have h₃ := congrArg (fun F ↦ (homEquiv F).1) (s.condition =≫ Limits.pullback.fst _ _)
    have h₄ := congrArg (fun F ↦ (homEquiv F).1) (s.snd ≫=
      Limits.pullback.condition (f := map (𝟙 L) p' (by simp)) (g := map i (𝟙 S') (by simp)))
    rw [← Category.assoc s.snd, ← Category.assoc s.snd] at h₄
    rw [homEquiv_comp_map_coe, join.map_id, Category.id_comp] at h₁ h₂
    simp only [Category.assoc, restrictionMap_fst, Limits.pullback.lift_fst] at h₃
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
      (by simpa using hm₂ =≫ Limits.pullback.snd _ _)

section comp

variable {Z : SSet.{u}} (i : L ⟶ K) (p : X ⟶ S) (r : S ⟶ Z) (σ : K ⟶ X)

/-- For maps `p : X ⟶ S` and `r : S ⟶ Z`, the map
`X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p} ⟶ X_{/i ≫ σ} ×_{Z_{/i ≫ σ ≫ p ≫ r}} Z_{/σ ≫ p ≫ r}`
pushing the second component forward along `r`. Composed with the restriction map for `p`, it is
the restriction map for `p ≫ r` (`SSet.slice.restrictionMap_comp`), and it is a base change of
the restriction map for `r` and `σ ≫ p` (`SSet.slice.isPullback_restrictionMapComp`). -/
noncomputable def restrictionMapComp :
    Limits.pullback (map (𝟙 L) p (by simp) : slice (i ≫ σ) ⟶ slice (i ≫ σ ≫ p))
        (map i (𝟙 S) (by simp) : slice (σ ≫ p) ⟶ slice (i ≫ σ ≫ p)) ⟶
      Limits.pullback (map (𝟙 L) (p ≫ r) (by simp) : slice (i ≫ σ) ⟶ slice (i ≫ σ ≫ p ≫ r))
        (map i (𝟙 Z) (by simp) : slice (σ ≫ p ≫ r) ⟶ slice (i ≫ σ ≫ p ≫ r)) :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (map (𝟙 K) r (by simp)) (map (𝟙 L) r (by simp)) (by simp)
    (by simp)

@[reassoc (attr := simp)]
lemma restrictionMapComp_fst :
    restrictionMapComp i p r σ ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ := by
  simp [restrictionMapComp]

@[reassoc (attr := simp)]
lemma restrictionMapComp_snd :
    restrictionMapComp i p r σ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ map (𝟙 K) r (by simp) :=
  Limits.pullback.lift_snd _ _ _

/-- The restriction map for a composite `p ≫ r` factors through the restriction map for `p`. -/
lemma restrictionMap_comp :
    restrictionMap i (p ≫ r) σ = restrictionMap i p σ ≫ restrictionMapComp i p r σ :=
  Limits.pullback.hom_ext (by simp) (by simp)

/-- The map `SSet.slice.restrictionMapComp i p r σ` is the base change of the restriction map for
`r` and `σ ≫ p` along the map pushing the first component forward along `p`. -/
lemma isPullback_restrictionMapComp :
    IsPullback (Limits.pullback.snd _ _) (restrictionMapComp i p r σ) (restrictionMap i r (σ ≫ p))
      (Limits.pullback.map _ _ _ _ (map (𝟙 L) p (by simp)) (map (𝟙 K) (𝟙 Z) (by simp))
        (map (𝟙 L) (𝟙 Z) (by simp)) (by simp) (by simp)) := by
  refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk
    (fst := Limits.pullback.snd _ _) (snd := restrictionMapComp i p r σ)
    (Limits.pullback.hom_ext (by simpa using Limits.pullback.condition.symm) (by simp))
    (fun s ↦ Limits.pullback.lift (s.snd ≫ Limits.pullback.fst _ _) s.fst ?_)
    (fun s ↦ Limits.pullback.lift_snd _ _ _) (fun s ↦ Limits.pullback.hom_ext ?_ ?_)
    (fun s m hm₁ hm₂ ↦ Limits.pullback.hom_ext ?_ (by simpa using hm₁)))
  · simpa using (s.condition =≫ Limits.pullback.fst _ _).symm
  · simp
  · simpa using s.condition =≫ Limits.pullback.snd _ _
  · simpa using hm₂ =≫ Limits.pullback.fst _ _

end comp

end restrictionMap

end slice

end SSet
