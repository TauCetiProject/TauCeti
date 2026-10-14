/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

/-!
# Gluing morphisms out of a presheafed space with a sheaf structure presheaf

Let `X` be a presheafed space whose structure presheaf is a sheaf, and let `U i` be a family of
opens covering `X`. A family of morphisms of presheafed spaces `f i : X|_{U i} ⟶ Y` which agree on
the overlaps glues to a unique morphism `X ⟶ Y` restricting to each `f i`.

The continuous maps glue because the `U i` are open and cover `X`
(`ContinuousMap.liftCover`). For an open `W` of `Y`, the components
`(f i).c.app W : 𝒪_Y(W) ⟶ 𝒪_X(U i ∩ f_i⁻¹ W)` form a compatible family over the cover of the
preimage of `W` by the opens `U i ∩ f_i⁻¹ W`, so they amalgamate in the sheaf `𝒪_X`
(`CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows`). No assumption is made on the category of
coefficients: the sheaf condition is used in the form that maps into it from a fixed object glue.

Mathlib glues morphisms of schemes (`AlgebraicGeometry.Scheme.Cover.glueMorphisms`) by
identifying a scheme with the scheme glued from an open cover, a comparison checked on stalks.
That check is not available for coefficients, such as topological rings, in which a bijective
morphism need not be an isomorphism, so the argument here works directly with the sections.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.glueMorphisms`: the morphism glued from a family of
  morphisms out of the restrictions of `X` to an open cover, agreeing on the overlaps.

## Main results

* `AlgebraicGeometry.PresheafedSpace.ofRestrict_glueMorphisms`: the glued morphism restricts to
  the given morphism on each open of the cover.
* `AlgebraicGeometry.PresheafedSpace.hom_ext_of_ofRestrict`: two morphisms out of `X` agreeing on
  every open of a cover are equal.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.PresheafedSpace

universe w v u

variable {C : Type u} [Category.{v} C] {X Y : PresheafedSpace C}

variable (hX : X.presheaf.IsSheaf) {ι : Type w} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
    (X.ofRestrict (U j).isOpenEmbedding) ≫ f i = pullback.snd _ _ ≫ f j)

include hf in
/-- The morphisms `f i` agree on every open contained in two members of the cover. -/
private theorem restrictHomOfLE_comp_eq {V : Opens X} {i j : ι} (hi : V ≤ U i) (hj : V ≤ U j) :
    restrictHomOfLE X hi ≫ f i = restrictHomOfLE X hj ≫ f j := by
  have w : restrictHomOfLE X hi ≫ X.ofRestrict (U i).isOpenEmbedding =
      restrictHomOfLE X hj ≫ X.ofRestrict (U j).isOpenEmbedding := by
    rw [restrictHomOfLE_ofRestrict, restrictHomOfLE_ofRestrict]
  rw [← pullback.lift_fst _ _ w, Category.assoc, hf, pullback.lift_snd_assoc]

include hf in
/-- The continuous maps underlying the `f i` agree on the overlaps. -/
private theorem base_eq_base {i j : ι} (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    (f i).base ⟨x, hi⟩ = (f j).base ⟨x, hj⟩ :=
  congrArg (fun g ↦ g.base (⟨x, hi, hj⟩ : (U i ⊓ U j : Opens X)))
    (restrictHomOfLE_comp_eq U f hf (V := U i ⊓ U j) inf_le_left inf_le_right)

include hU in
private theorem exists_mem (x : X) : ∃ i, x ∈ U i :=
  Opens.mem_iSup.mp (hU.symm ▸ trivial)

/-- The continuous map glued from the `f i`. -/
private noncomputable def glueBase : X.carrier ⟶ Y.carrier :=
  TopCat.ofHom (ContinuousMap.liftCover (fun i ↦ (U i : Set X)) (fun i ↦ (f i).base.hom)
    (fun _ _ x hi hj ↦ base_eq_base U f hf x hi hj)
    (fun x ↦ (exists_mem U hU x).imp fun i hi ↦ (U i).isOpen.mem_nhds hi))

private theorem glueBase_apply {i : ι} (x : X.restrict (U i).isOpenEmbedding) :
    glueBase U hU f hf ((X.ofRestrict (U i).isOpenEmbedding).base x) = (f i).base x := by
  exact ContinuousMap.liftCover_coe (S := fun i ↦ (U i : Set X)) (φ := fun i ↦ (f i).base.hom)
    (hφ := fun i j x hi hj ↦ base_eq_base U f hf x hi hj)
    (hS := fun x ↦ (exists_mem U hU x).imp fun i hi ↦ (U i).isOpen.mem_nhds hi) x

private theorem ofRestrict_base_glueBase (i : ι) :
    (X.ofRestrict (U i).isOpenEmbedding).base ≫ glueBase U hU f hf = (f i).base := by
  ext x
  exact glueBase_apply U hU f hf x

/-- The open `U i ∩ f_i⁻¹ W` of `X`, on which `f i` provides sections. -/
private abbrev piece (W : Opens Y) (i : ι) : Opens X :=
  (U i).isOpenEmbedding.functor.obj ((Opens.map (f i).base).obj W)

private theorem piece_le (W : Opens Y) (i : ι) :
    piece U f W i ≤ (Opens.map (glueBase U hU f hf)).obj W := by
  rintro _ ⟨x, hx, rfl⟩
  have h := glueBase_apply U hU f hf x
  rw [ofRestrict_base] at h
  exact (congrArg (· ∈ W) h).mpr hx

private theorem piece_le_cover (W : Opens Y) (i : ι) : piece U f W i ≤ U i := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

private theorem ofArrows_piece_mem (W : Opens Y) :
    Sieve.ofArrows _ (fun i ↦ homOfLE (piece_le U hU f hf W i)) ∈
      Opens.grothendieckTopology X ((Opens.map (glueBase U hU f hf)).obj W) := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_mem U hU x
  refine ⟨_, _, Sieve.ofArrows_mk _ _ i, ⟨x, hi⟩, ?_, rfl⟩
  have h := glueBase_apply U hU f hf ⟨x, hi⟩
  rw [ofRestrict_base] at h
  exact (congrArg (· ∈ W) h).mp hx

/- The presheaf of the restriction `X.restrict h` is `h.functor.op ⋙ X.presheaf` only after
unfolding Mathlib's `AlgebraicGeometry.PresheafedSpace.restrict`, which `rw` does not do. In the
proofs below, restriction maps of `X.restrict h` are therefore merged with those of `X` by
`erw [← X.presheaf.map_comp]`, after which the remaining equalities of morphisms of `Opens X` hold
by `rfl`, `Opens X` being a preorder. For the same reason some rewrites by associativity are
replaced by `Category.assoc` used as a term. -/

include hf in
/-- The components of the `f i` at `W` agree on every open contained in two of the pieces. -/
private theorem c_app_map_eq (W : Opens Y) ⦃V : Opens X⦄ ⦃i j : ι⦄ (a : V ⟶ piece U f W i)
    (b : V ⟶ piece U f W j) :
    (f i).c.app (op W) ≫ X.presheaf.map a.op = (f j).c.app (op W) ≫ X.presheaf.map b.op := by
  have hi : V ≤ U i := a.le.trans (piece_le_cover U f W i)
  have hj : V ≤ U j := b.le.trans (piece_le_cover U f W j)
  have key := congr_app (restrictHomOfLE_comp_eq U f hf hi hj) (op W)
  rw [comp_c_app, comp_c_app, restrictHomOfLE_c_app, restrictHomOfLE_c_app] at key
  -- `V` lies in the preimage of `W` under the restriction of `f i` to `V`
  have hV : V ≤ V.isOpenEmbedding.functor.obj ((Opens.map ((Opens.toTopCat X).map
      (homOfLE hi))).obj ((Opens.map (f i).base).obj W)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := a.le hx
    exact ⟨⟨y.1, hx⟩, hy, rfl⟩
  have e : X.presheaf.map a.op =
      X.presheaf.map (homOfLE (Opens.functor_obj_map_homOfLE_obj_le hi _)).op ≫
        X.presheaf.map (homOfLE hV).op := by
    rw [← X.presheaf.map_comp]
    rfl
  have key' := congrArg (· ≫ X.presheaf.map (homOfLE hV).op) key
  convert key' using 1
  · rw [e]
    exact (Category.assoc _ _ _).symm
  · refine (congrArg ((f j).c.app (op W) ≫ ·) ?_).trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl

/-- The component at `W` of the glued morphism, amalgamated from those of the `f i`. -/
private noncomputable def glueApp (W : Opens Y) :
    Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op ((Opens.map (glueBase U hU f hf)).obj W)) :=
  Presheaf.IsSheaf.amalgamateOfArrows hX _ (ofArrows_piece_mem U hU f hf W)
    (fun i ↦ (f i).c.app (op W)) fun _ _ _ a b _ ↦ c_app_map_eq U f hf W a b

private theorem glueApp_map (W : Opens Y) (i : ι) :
    glueApp hX U hU f hf W ≫ X.presheaf.map (homOfLE (piece_le U hU f hf W i)).op =
      (f i).c.app (op W) :=
  Presheaf.IsSheaf.amalgamateOfArrows_map _ _ _ _ _ i

/-- **Gluing morphisms out of a presheafed space with a sheaf structure presheaf.** If the
structure presheaf of `X` is a sheaf, the opens `U i` cover `X`, and the morphisms
`f i : X|_{U i} ⟶ Y` agree on the overlaps, then they glue to a morphism `X ⟶ Y`
(`ofRestrict_glueMorphisms`), which is unique (`hom_ext_of_ofRestrict`). -/
noncomputable def glueMorphisms : X ⟶ Y where
  base := glueBase U hU f hf
  c :=
    { app W := glueApp hX U hU f hf W.unop
      naturality W W' e := by
        refine Presheaf.IsSheaf.hom_ext_ofArrows hX _ (ofArrows_piece_mem U hU f hf W'.unop)
          fun i ↦ ?_
        -- the piece of `W'` lies in the piece of `W`
        have hle : piece U f W'.unop i ≤ piece U f W.unop i := by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨x, e.unop.le hx, rfl⟩
        have h : (TopCat.Presheaf.pushforward C (glueBase U hU f hf) |>.obj X.presheaf).map e ≫
            X.presheaf.map (homOfLE (piece_le U hU f hf W'.unop i)).op =
            X.presheaf.map (homOfLE (piece_le U hU f hf W.unop i)).op ≫
              X.presheaf.map (homOfLE hle).op := by
          erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
          rfl
        rw [Category.assoc, Category.assoc, glueApp_map, h, reassoc_of% glueApp_map]
        exact (f i).c.naturality e }

/-- The glued morphism restricts to `f i` on `U i`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms hX U hU f hf = f i := by
  refine PresheafedSpace.ext _ _ (ofRestrict_base_glueBase U hU f hf i) ?_
  ext W
  rw [NatTrans.comp_app, comp_c_app, Functor.whiskerRight_app, eqToHom_app, ofRestrict_c_app,
    ← glueApp_map hX U hU f hf W i]
  refine (Category.assoc _ _ _).trans (congrArg (glueApp hX U hU f hf W ≫ ·) ?_)
  erw [← X.presheaf.map_comp]
  rfl

include hU hX in
/-- **Morphisms out of a presheafed space with a sheaf structure presheaf are determined
locally.** Two morphisms `X ⟶ Y` agreeing on every member of an open cover of `X` are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' := by
  have hbase : g.base = g'.base := by
    ext x
    obtain ⟨i, hi⟩ := exists_mem U hU x
    exact congrArg (fun k ↦ k.base ⟨x, hi⟩) (h i)
  refine PresheafedSpace.ext _ _ hbase ?_
  ext W
  refine Presheaf.IsSheaf.hom_ext_ofArrows hX
    (fun i ↦ homOfLE (inf_le_right : U i ⊓ (Opens.map g'.base).obj W ≤ _)) ?_ fun i ↦ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := exists_mem U hU x
    exact ⟨_, _, Sieve.ofArrows_mk _ _ i, ⟨hi, hx⟩⟩
  have key := congr_app (h i) (op W)
  rw [comp_c_app, comp_c_app, ofRestrict_c_app, ofRestrict_c_app] at key
  -- on `U i`, the preimages of `W` under `g` and `g'` agree
  have hk : U i ⊓ (Opens.map g'.base).obj W ≤ (U i).isOpenEmbedding.functor.obj
      ((Opens.map (X.ofRestrict (U i).isOpenEmbedding ≫ g).base).obj W) := by
    rintro x ⟨hi, hx⟩
    refine ⟨⟨x, hi⟩, ?_, rfl⟩
    have hx' : g.base x ∈ W := by rwa [hbase]
    have e : (X.ofRestrict (U i).isOpenEmbedding ≫ g).base ⟨x, hi⟩ = g.base x := by
      rw [comp_base, ofRestrict_base]
      rfl
    exact (congrArg (· ∈ W) e).mpr hx'
  have key' := congrArg (· ≫ X.presheaf.map (homOfLE hk).op) key
  convert key' using 1
  · rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app]
    refine (Category.assoc _ _ _).trans ((congrArg (g.c.app (op W) ≫ ·) ?_).trans
      (Category.assoc _ _ _).symm)
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  · refine (congrArg (g'.c.app (op W) ≫ ·) ?_).trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl

end AlgebraicGeometry.PresheafedSpace
