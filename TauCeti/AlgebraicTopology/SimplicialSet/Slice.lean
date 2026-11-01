/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join

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

## Main results

* `SSet.slice.homEquiv`: **the universal property of the slice**, maps `X ⟶ C_{/p}` correspond
  to maps `X ⋆ K ⟶ C` extending `p`, naturally in `X` (`SSet.slice.homEquiv_comp_coe`).
* `SSet.slice.objEquiv_app_coe`: the simplices of the image of a map `F : X ⟶ C_{/p}` are the
  restrictions of the corresponding map `X ⋆ K ⟶ C`.
* `SSet.slice.comp_π`: under the universal property, the projection to `C` is the restriction to
  `X`.

## Implementation notes

Given `F : X ⟶ C_{/p}`, the map `X ⋆ K ⟶ C` is defined simplexwise. A simplex of `X ⋆ K` either
lies in `K`, where it is sent through `p`, or meets `X`; in the second case it is the image of a
simplex of `Δ[m] ⋆ K` under `g ⋆ K` for a simplex `g : Δ[m] ⟶ X` extending its part in `X`
(`SSet.join.exists_eq_comp_inr_or_exists_eq_comp_map`), and it is sent to the value of `F g` on
that simplex. The extension `g` is chosen along the retraction `SSet.joinFiberZeroRetraction` of
`Δ[m]` onto its part over the vertex `0` of `Δ[1]`, and the value is independent of the choice of
factorization because `F` is compatible with the faces and degeneracies of `X`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.9.
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

end slice

end SSet
