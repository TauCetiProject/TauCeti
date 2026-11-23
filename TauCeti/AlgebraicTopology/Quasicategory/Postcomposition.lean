/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.CompStruct
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration

/-!
# Postcomposition on right mapping spaces

For vertices `x` and `y` of a simplicial set `X`, the right mapping space `Hom^R_X(x, y)` is the
fibre over `x` of the projection `X_{/y} ⟶ X` of the slice over `y`
(`SSet.rightMappingSpace.sliceFiberIso`): through `Δ[n] ⋆ Δ[0] ≅ Δ[n + 1]`, an `n`-simplex of
the slice is an `(n + 1)`-simplex of `X` with last vertex `y`, and it lies over `x` when its face
opposite to the last vertex is constant at `x`.

An edge `g : y ⟶ z` acts on right mapping spaces by postcomposition, but only up to a contractible
space of choices. Its slice `X_{/g}` maps to `X_{/y}` and to `X_{/z}` by restricting cones to the
two vertices of `g`, over `X`. Taking fibres over `x` gives the span
`Hom^R_X(x, y) ⟵ Hom^R_X(x, g) ⟶ Hom^R_X(x, z)`,
whose middle term `SSet.rightMappingSpace.postcompSpace x g` has as vertices the `2`-simplices
of `X` with vertices `x`, `y`, `z` and last edge `g`, that is, the composition triangles
`SSet.Edge.CompStruct f g h` (`SSet.rightMappingSpace.postcompSpace.obj₀Equiv`). Its legs send
such a triangle to `f` and to `h`.

When `X` is a quasicategory, the left leg is a trivial fibration
(`SSet.rightMappingSpace.postcompSpace.rlp_src`): restricting cones over `g` to cones over its
source is one (`SSet.slice.hasLiftingProperty_map_δ_one`), and trivial fibrations are stable
under base change. Choosing a section of it gives a postcomposition map
`g_* : Hom^R_X(x, y) ⟶ Hom^R_X(x, z)` (`SSet.rightMappingSpace.postcomp`), which sends an edge
`f` to a composite of `f` and `g` (`SSet.rightMappingSpace.postcomp_compStruct`), and which is
independent of the choice of section up to homotopy
(`SSet.rightMappingSpace.exists_homotopy_postcomp`). This is the composition of mapping spaces
of a quasicategory with a fixed morphism.

## Main definitions

* `SSet.rightMappingSpace.postcompSpace x g`: the simplicial set `Hom^R_X(x, g)` of composites
  with `g`, the fibre over `x` of `X_{/g} ⟶ X` (`SSet.rightMappingSpace.postcompSpace_eq_fiber`).
* `SSet.rightMappingSpace.postcompSpace.src`, `SSet.rightMappingSpace.postcompSpace.tgt`: its
  maps to `Hom^R_X(x, y)` and `Hom^R_X(x, z)`.
* `SSet.rightMappingSpace.postcomp x g`: for a quasicategory, a postcomposition map
  `Hom^R_X(x, y) ⟶ Hom^R_X(x, z)`.

## Main results

* `SSet.rightMappingSpace.postcompSpace.obj₀Equiv`: the vertices of `Hom^R_X(x, g)` are the
  composition triangles with last edge `g`, whose `2`-simplex is the cone itself
  (`SSet.rightMappingSpace.postcompSpace.obj₀Equiv_apply_simplex`,
  `SSet.rightMappingSpace.postcompSpace.objEquiv_obj₀Equiv_symm_coe`), and `src` and `tgt` send
  them to their first and long edges (`SSet.rightMappingSpace.postcompSpace.obj₀Equiv_src_app`,
  `SSet.rightMappingSpace.postcompSpace.obj₀Equiv_tgt_app`).
* `SSet.rightMappingSpace.postcompSpace.rlp_src`: for a quasicategory, `src` is a trivial
  fibration.
* `SSet.rightMappingSpace.postcomp_compStruct`: `postcomp x g` sends an edge `f` to a composite
  of `f` and `g`.
* `SSet.rightMappingSpace.exists_homotopy_postcomp`: every map obtained from a section of `src` is
  homotopic to `postcomp x g`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 and Proposition 1.2.9.3.
* J. Lurie, *Kerodon*, §4.6.5 (right-pinched morphism spaces) and §4.6.9 (composition of
  morphisms).
-/

public section

open CategoryTheory Limits MorphismProperty Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}}

namespace rightMappingSpace

/-! ### Composites with an edge -/

variable {x y z : X _⦋0⦌}

variable (x) in
/-- The simplicial set `Hom^R_X(x, g)` of composites with an edge `g : y ⟶ z`: the cones
`Δ[n] ⋆ Δ[1] ⟶ X` over `g` whose restriction to the source of `g` lies in the fibre
`Hom^R_X(x, y)` of `X_{/y} ⟶ X` over `x`. These are the simplices of the fibre over `x` of
`X_{/g} ⟶ X` (`SSet.rightMappingSpace.postcompSpace_eq_fiber`); written as a preimage, the map
`SSet.rightMappingSpace.postcompSpace.src` to `Hom^R_X(x, y)` is a base change of the restriction
`X_{/g} ⟶ X_{/y}`. -/
noncomputable def postcompSpace (g : Edge y z) : (slice (yonedaEquiv.symm g.edge)).Subcomplex :=
  (fiber (slice.π (yonedaEquiv.symm y)) x).preimage
    (slice.map (stdSimplex.δ 1) (𝟙 X) (by simp))

variable (x) in
/-- `Hom^R_X(x, g)` is the fibre over `x` of the projection `X_{/g} ⟶ X`. -/
theorem postcompSpace_eq_fiber (g : Edge y z) :
    postcompSpace x g = fiber (slice.π (yonedaEquiv.symm g.edge)) x := by
  ext n s
  -- Restricting a cone over `g` to its source does not change its restriction to `Δ[n]`.
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (slice.map_π
    (q := yonedaEquiv.symm y) (stdSimplex.δ 1) (𝟙 X) (by simp)) n) s
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.id_app,
    ConcreteCategory.id_apply] at h
  simp only [postcompSpace, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff, h]

/-- A simplex of `X_{/g}` lies in `Hom^R_X(x, g)` exactly when its restriction to `Δ[n]` is
constant at `x`. -/
@[simp]
theorem mem_postcompSpace_iff (g : Edge y z) {n : SimplexCategoryᵒᵖ}
    (s : (slice (yonedaEquiv.symm g.edge)).obj n) :
    s ∈ (postcompSpace x g).obj n ↔
      (slice.π (yonedaEquiv.symm g.edge)).app n s = X.map (n.unop.const _ 0).op x := by
  rw [postcompSpace_eq_fiber, mem_fiber_iff]

namespace postcompSpace

variable (x) in
/-- The map `Hom^R_X(x, g) ⟶ Hom^R_X(x, y)` restricting a composite with `g : y ⟶ z` to the
source `y` of `g`. On vertices it sends a composition triangle with last edge `g` to its first
edge (`SSet.rightMappingSpace.postcompSpace.obj₀Equiv_src_app`). -/
noncomputable def src (g : Edge y z) :
    (postcompSpace x g : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}) :=
  Subcomplex.fromPreimage _ _ ≫ (sliceFiberIso x y).hom

variable (x) in
/-- The map `Hom^R_X(x, g) ⟶ Hom^R_X(x, z)` restricting a composite with `g : y ⟶ z` to the
target `z` of `g`. On vertices it sends a composition triangle with last edge `g` to its long
edge (`SSet.rightMappingSpace.postcompSpace.obj₀Equiv_tgt_app`). -/
noncomputable def tgt (g : Edge y z) :
    (postcompSpace x g : SSet.{u}) ⟶ (X.rightMappingSpace x z : SSet.{u}) :=
  Subcomplex.lift ((postcompSpace x g).ι ≫ slice.map (stdSimplex.δ 0) (𝟙 X) (by simp)) (by
    rw [range_le_fiber_iff, Category.assoc, slice.map_π, Category.comp_id,
      ← range_le_fiber_iff, ← postcompSpace_eq_fiber]
    simp) ≫
    (sliceFiberIso x z).hom

/-- The simplex of `Hom^R_X(x, y)` underlying the image under `src` of a cone
`Δ[n] ⋆ Δ[1] ⟶ X` over `g` is its restriction to `Δ[n] ⋆ Δ[0]` along the source of `Δ[1]`, through
`Δ[n + 1] ≅ Δ[n] ⋆ Δ[0]`. -/
theorem src_app_coe (g : Edge y z) {m : SimplexCategory}
    (s : (postcompSpace x g : SSet.{u}).obj (op m)) :
    ((src x g).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫ join.map (𝟙 _) (stdSimplex.δ 1) ≫
        (slice.objEquiv s.val).val) : X.obj (op (joinVertex.obj m))) := by
  -- By definition, `src` restricts a cone along `slice.map` and then applies `sliceFiberIso`.
  have h : ((src x g).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫
        (slice.objEquiv ((slice.map (q := yonedaEquiv.symm y) (stdSimplex.δ 1) (𝟙 X)
          (by simp)).app _ s.val)).val) :
          X.obj (op (joinVertex.obj m))) :=
    sliceFiberIso_hom_app_coe x y ((Subcomplex.fromPreimage _ _).app _ s)
  rw [h, slice.objEquiv_map_app_coe, Category.comp_id]

/-- The simplex of `Hom^R_X(x, z)` underlying the image under `tgt` of a cone
`Δ[n] ⋆ Δ[1] ⟶ X` over `g` is its restriction to `Δ[n] ⋆ Δ[0]` along the target of `Δ[1]`, through
`Δ[n + 1] ≅ Δ[n] ⋆ Δ[0]`. -/
theorem tgt_app_coe (g : Edge y z) {m : SimplexCategory}
    (s : (postcompSpace x g : SSet.{u}).obj (op m)) :
    ((tgt x g).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫ join.map (𝟙 _) (stdSimplex.δ 0) ≫
        (slice.objEquiv s.val).val) : X.obj (op (joinVertex.obj m))) := by
  -- By definition, `tgt` restricts a cone along `slice.map` and then applies `sliceFiberIso`.
  have h : ((tgt x g).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫
        (slice.objEquiv ((slice.map (q := yonedaEquiv.symm z) (stdSimplex.δ 0) (𝟙 X)
          (by simp)).app _ s.val)).val) :
          X.obj (op (joinVertex.obj m))) :=
    sliceFiberIso_hom_app_coe x z (Subcomplex.lift _ _ |>.app _ s)
  rw [h, slice.objEquiv_map_app_coe, Category.comp_id]

variable (x) in
/-- For a quasicategory `X`, **the restriction `Hom^R_X(x, g) ⟶ Hom^R_X(x, y)` to the source of
`g` is a trivial fibration**: it has the right lifting property with respect to every
monomorphism. It is a base change of the restriction of cones `X_{/g} ⟶ X_{/y}`, which is a
trivial fibration by `SSet.slice.hasLiftingProperty_map_δ_one`. -/
theorem rlp_src [X.Quasicategory] (g : Edge y z) :
    (monomorphisms SSet.{u}).rlp (src x g) := by
  intro _ _ i hi
  have : Mono i := hi
  have := slice.hasLiftingProperty_map_δ_one (yonedaEquiv.symm g.edge)
    (p := yonedaEquiv.symm y) (by simp) i
  exact inferInstanceAs (HasLiftingProperty i (Subcomplex.fromPreimage _ _ ≫ _))

/-! ### Vertices of `Hom^R_X(x, g)` -/

variable {g : Edge y z}

/-- The `2`-simplex of `X` underlying a vertex of `Hom^R_X(x, g)`, a cone `Δ[0] ⋆ Δ[1] ⟶ X` over
`g`, through `Δ[0] ⋆ Δ[1] ≅ Δ[2]`. -/
private noncomputable def simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) : X _⦋2⦌ :=
  yonedaEquiv ((join.coneIso 1).inv ≫ (slice.objEquiv v.val).val)

private lemma δ_zero_simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    X.δ 0 (simplex v) = g.edge := by
  rw [simplex, ← stdSimplex.yonedaEquiv_δ_comp, join.δ_zero_comp_coneIso_inv_assoc,
    (slice.objEquiv v.val).property, Equiv.apply_symm_apply]

private lemma δ_two_simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    X.δ 2 (simplex v) = ((src x g).app _ v).val := by
  rw [simplex, ← stdSimplex.yonedaEquiv_δ_comp, show (2 : Fin 3) = Fin.succ 1 from rfl,
    join.δ_succ_comp_coneIso_inv_assoc, src_app_coe, join.joinVertexIso_zero]
  -- The two sides differ only in the types `X _⦋1⦌` and `X.obj (op (joinVertex.obj ⦋0⦌))`.
  rfl

private lemma δ_one_simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    X.δ 1 (simplex v) = ((tgt x g).app _ v).val := by
  rw [simplex, ← stdSimplex.yonedaEquiv_δ_comp, show (1 : Fin 3) = Fin.succ 0 from rfl,
    join.δ_succ_comp_coneIso_inv_assoc, tgt_app_coe, join.joinVertexIso_zero]
  -- The two sides differ only in the types `X _⦋1⦌` and `X.obj (op (joinVertex.obj ⦋0⦌))`.
  rfl

/-- The composition triangle of a vertex of `Hom^R_X(x, g)`, with edges its images under `src`
and `tgt`. -/
private noncomputable def compStruct (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    Edge.CompStruct (rightMappingSpace.obj₀Equiv ((src x g).app _ v)) g
      (rightMappingSpace.obj₀Equiv ((tgt x g).app _ v)) :=
  Edge.CompStruct.mk (simplex v)
    ((δ_two_simplex v).trans (rightMappingSpace.obj₀Equiv_apply_edge _).symm) (δ_zero_simplex v)
    ((δ_one_simplex v).trans (rightMappingSpace.obj₀Equiv_apply_edge _).symm)

private lemma compStruct_simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    (compStruct v).simplex = simplex v :=
  rfl

variable (x g) in
/-- **The vertices of `Hom^R_X(x, g)` are the composition triangles with last edge `g`**: through
`Δ[0] ⋆ Δ[1] ≅ Δ[2]`, a cone over `g : y ⟶ z` with cone point `x` is a `2`-simplex of `X` whose
faces are edges `f : x ⟶ y`, `g` and `h : x ⟶ z`. -/
noncomputable def obj₀Equiv :
    (postcompSpace x g : SSet.{u}) _⦋0⦌ ≃
      Σ (f : Edge x y) (h : Edge x z), Edge.CompStruct f g h where
  toFun v := ⟨_, _, compStruct v⟩
  invFun c := ⟨slice.objEquiv.symm ⟨(join.coneIso 1).hom ≫ yonedaEquiv.symm c.2.2.simplex, by
      rw [join.inr_comp_coneIso_hom_assoc, Edge.CompStruct.δ_zero_yonedaEquiv_symm]⟩, by
    rw [mem_postcompSpace_iff, slice.π_app, Equiv.apply_symm_apply, join.inl_comp_coneIso_hom_assoc,
      yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
    exact (Edge.CompStruct.map_const_zero_simplex c.2.2).trans (by simp)⟩
  -- `dsimp only` reduces the applications of `toFun` and `invFun` and the projections of
  -- anonymous constructors, so that the equivalences and isomorphisms cancel by `rw`.
  left_inv v := Subtype.ext (slice.objEquiv.injective (Subtype.ext (by
    dsimp only
    rw [Equiv.apply_symm_apply]
    dsimp only
    rw [compStruct_simplex, simplex, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc])))
  right_inv c := Edge.CompStruct.sigma_ext (by
    dsimp only
    rw [compStruct_simplex, simplex, Equiv.apply_symm_apply, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply])

/-- The `2`-simplex of the composition triangle of a vertex of `Hom^R_X(x, g)` is its cone
`Δ[0] ⋆ Δ[1] ⟶ X` over `g`, through `Δ[0] ⋆ Δ[1] ≅ Δ[2]`. -/
theorem obj₀Equiv_apply_simplex (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    (obj₀Equiv x g v).2.2.simplex =
      yonedaEquiv ((join.coneIso 1).inv ≫ (slice.objEquiv v.val).val) :=
  (rfl)

/-- The cone `Δ[0] ⋆ Δ[1] ⟶ X` over `g` of the vertex of `Hom^R_X(x, g)` given by a composition
triangle is its `2`-simplex, through `Δ[0] ⋆ Δ[1] ≅ Δ[2]`. -/
theorem objEquiv_obj₀Equiv_symm_coe (c : Σ (f : Edge x y) (h : Edge x z), Edge.CompStruct f g h) :
    (slice.objEquiv ((obj₀Equiv x g).symm c).val).val =
      (join.coneIso 1).hom ≫ yonedaEquiv.symm c.2.2.simplex :=
  congrArg Subtype.val (slice.objEquiv.apply_symm_apply _)

/-- The image under `src` of a vertex of `Hom^R_X(x, g)` is the first edge of its composition
triangle. -/
theorem obj₀Equiv_src_app (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    rightMappingSpace.obj₀Equiv ((src x g).app _ v) = (obj₀Equiv x g v).1 :=
  (rfl)

/-- The image under `tgt` of a vertex of `Hom^R_X(x, g)` is the long edge of its composition
triangle. -/
theorem obj₀Equiv_tgt_app (v : (postcompSpace x g : SSet.{u}) _⦋0⦌) :
    rightMappingSpace.obj₀Equiv ((tgt x g).app _ v) = (obj₀Equiv x g v).2.1 :=
  (rfl)

end postcompSpace

/-! ### Postcomposition -/

variable (x) in
/-- For a quasicategory `X`, **postcomposition with an edge `g : y ⟶ z`** on right mapping spaces,
a map `Hom^R_X(x, y) ⟶ Hom^R_X(x, z)`: a chosen section of the trivial fibration
`SSet.rightMappingSpace.postcompSpace.src`, followed by
`SSet.rightMappingSpace.postcompSpace.tgt`. It sends an edge `f` to a composite of `f` and `g`
(`SSet.rightMappingSpace.postcomp_compStruct`), and any other choice of section gives a homotopic
map (`SSet.rightMappingSpace.exists_homotopy_postcomp`). -/
noncomputable def postcomp [X.Quasicategory] (g : Edge y z) :
    (X.rightMappingSpace x y : SSet.{u}) ⟶ (X.rightMappingSpace x z : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src x g)
  section_ (postcompSpace.src x g) ≫ postcompSpace.tgt x g

/-- **Postcomposition with `g` sends an edge `f` to a composite of `f` and `g`**: there is a
`2`-simplex with edges `f`, `g` and the image of `f` under `SSet.rightMappingSpace.postcomp x g`. -/
theorem postcomp_compStruct [X.Quasicategory] (g : Edge y z) (f : Edge x y) :
    Nonempty (Edge.CompStruct f g
      (obj₀Equiv ((postcomp x g).app _ (obj₀Equiv.symm f)))) := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src x g)
  -- The image of `f` under the chosen section is a composition triangle with first edge `f`, and
  -- `postcomp x g` sends `f` to its long edge.
  let v := (section_ (postcompSpace.src x g)).app _ (obj₀Equiv.symm f)
  have hf : (postcompSpace.obj₀Equiv x g v).1 = f := by
    rw [← postcompSpace.obj₀Equiv_src_app, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      IsSplitEpi.id, NatTrans.id_app, ConcreteCategory.id_apply, Equiv.apply_symm_apply]
  have hh : obj₀Equiv ((postcomp x g).app _ (obj₀Equiv.symm f)) =
      (postcompSpace.obj₀Equiv x g v).2.1 := by
    rw [← postcompSpace.obj₀Equiv_tgt_app, postcomp, NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact ⟨(postcompSpace.obj₀Equiv x g v).2.2.ofEq (by rw [hf]) rfl (by rw [hh])⟩

/-- **Postcomposition is well-defined up to homotopy**: for every section `s` of the trivial
fibration `SSet.rightMappingSpace.postcompSpace.src`, the map `s ≫ tgt` is homotopic to
`SSet.rightMappingSpace.postcomp x g`. -/
theorem exists_homotopy_postcomp [X.Quasicategory] (g : Edge y z)
    (s : (X.rightMappingSpace x y : SSet.{u}) ⟶ (postcompSpace x g : SSet.{u}))
    (hs : s ≫ postcompSpace.src x g = 𝟙 _) :
    Nonempty (Homotopy (s ≫ postcompSpace.tgt x g) (postcomp x g)) := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src x g)
  obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms (postcompSpace.rlp_src x g) s
    (section_ (postcompSpace.src x g)) (by rw [hs, IsSplitEpi.id])
  exact ⟨H.postcomp _⟩

end rightMappingSpace

end SSet
