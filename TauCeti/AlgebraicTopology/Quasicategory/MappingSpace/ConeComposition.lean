/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.LeftMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex

/-!
# Composition with cones and cocones

Composition with a cone or cocone is obtained by choosing a section of a trivial fibration.
The map returns a cone or cocone; a comparison edge over the input edge exists.
This is analogous to edge postcomposition for a one-vertex diagram, with independent choices
of sections. The maps are characterized by a section factorization and are independent of
that section up to homotopy.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 4.2.4.3.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Simplicial SimplexCategory

namespace SSet

open modelCategoryQuillen

variable {K C : SSet.{u}} {p : K ⟶ C}

namespace slice

/-! ### Composites with a cone -/

variable (y : C _⦋0⦌) (c : (slice p) _⦋0⦌)

/-- The simplicial set `Hom^R_C(y, c)` of composites with a cone `c`: the simplices of the slice
`C_{/p}_{/c}`, the morphisms of cones with target `c`, whose source lies in the fibre over `y` of
`C_{/p} ⟶ C`. It is the preimage of the fibre over `y` of `C_{/x} ⟶ C`,
canonically isomorphic to `Hom^R_C(y, x)`, for `x` the cone point of `c`, under the projection
`C_{/p}_{/c} ⟶ C_{/x}`
(`SSet.slice.postcompSpace_eq_preimage`). -/
noncomputable def postcompSpace : (slice (yonedaEquiv.symm c)).Subcomplex :=
  (fiber (π p) y).preimage (π (yonedaEquiv.symm c))

/-- A simplex of `C_{/p}_{/c}` lies in `Hom^R_C(y, c)` exactly when its source lies over the
degeneracy of `y`. -/
@[simp]
theorem mem_postcompSpace_iff {n : SimplexCategoryᵒᵖ} (s : (slice (yonedaEquiv.symm c)).obj n) :
    s ∈ (postcompSpace y c).obj n ↔
      (π p).app n ((π (yonedaEquiv.symm c)).app n s) = C.map (n.unop.const _ 0).op y := by
  rw [postcompSpace, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff]

/-- `Hom^R_C(y, c)` is the preimage of the fibre over `y`
of `C_{/x} ⟶ C`, canonically isomorphic to the right mapping space `Hom^R_C(y, x)`, under the
projection `C_{/p}_{/c} ⟶ C_{/x}`. -/
theorem postcompSpace_eq_preimage :
    postcompSpace y c = (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).preimage
      (map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  rw [postcompSpace, fiber_eq_preimage, fiber_eq_preimage, ← Subcomplex.preimage_comp,
    ← Subcomplex.preimage_comp, map_π]

namespace postcompSpace

/-- The map `Hom^R_C(y, c) ⟶ (C_{/p})_y` sending a morphism of cones with target `c` to its source,
a cone with cone point `y`. -/
noncomputable def tgt : (postcompSpace y c : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  Subcomplex.fromPreimage _ _

/-- The projection `tgt` is the restriction of `C_{/p}_{/c} ⟶ C_{/p}`. -/
@[reassoc (attr := simp)]
theorem tgt_ι :
    tgt y c ≫ (fiber (π p) y).ι = (postcompSpace y c).ι ≫ π (yonedaEquiv.symm c) :=
  Subcomplex.fromPreimage_ι _ _

/-- The map `Hom^R_C(y, c) ⟶ Hom^R_C(y, x)` projecting a morphism of cones with target `c` to `C`,
for `x` the cone point of `c`. -/
noncomputable def src :
    (postcompSpace y c : SSet.{u}) ⟶ (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) :=
  (Subcomplex.eqToIso (postcompSpace_eq_preimage y c)).hom ≫
  Subcomplex.fromPreimage _ _ ≫ (rightMappingSpace.sliceFiberIso y _).hom

/-- The source projection commutes with the inclusions into the slice or coslice. -/
@[reassoc (attr := simp)]
theorem src_inv_ι :
    src y c ≫ (rightMappingSpace.sliceFiberIso y ((π p).app _ c)).inv ≫
        (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).ι =
      (postcompSpace y c).ι ≫
        map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp]) := by
  simp [src, Subcomplex.eqToIso]

/-- The underlying simplex of the image under `src` of a morphism of cones `Δ[n] ⋆ Δ[0] ⟶ C_{/p}`
is its composite with the projection `C_{/p} ⟶ C`, through `Δ[n + 1] ≅ Δ[n] ⋆ Δ[0]`. -/
theorem src_app_coe {m : SimplexCategory} (s : (postcompSpace y c : SSet.{u}).obj (op m)) :
    ((src y c).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫ (slice.objEquiv s.val).val ≫ π p) :
        C.obj (op (joinVertex.obj m))) := by
  rw [src, NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, rightMappingSpace.sliceFiberIso_hom_app_coe,
    Subcomplex.fromPreimage, Subcomplex.lift_app_coe, NatTrans.comp_app,
    ConcreteCategory.comp_apply, objEquiv_map_app_coe, join.map_id, Category.id_comp]
  simp only [Subcomplex.eqToIso, Subcomplex.homOfLE, Subfunctor.homOfLe_app,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]

/-- If the diagram projection is a right fibration, the source projection is a trivial
fibration: it is a base change of the map of slices or coslices of that projection over `c`
(`SSet.slice.rlp_map_of_rightFibration`). -/
theorem rlp_src [RightFibration (π p)] : (monomorphisms SSet.{u}).rlp (src y c) := by
  unfold src
  apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
  apply MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  intro A B i hi
  have := rlp_map_of_rightFibration (π p) (yonedaEquiv.symm c)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
  infer_instance

/-- The target map inherits the right fibration property of the projection from `C_{/p}_{/c}`
by base change over the vertex fibre. -/
instance rightFibration_tgt [RightFibration (π (yonedaEquiv.symm c))] : RightFibration (tgt y c) :=
  inferInstanceAs (RightFibration (Subcomplex.fromPreimage _ _))

/-- The target map is a Kan fibration when the projection from `C_{/p}_{/c}` is a right
fibration and the vertex fibre of the diagram projection is a Kan complex. -/
instance fibration_tgt [RightFibration (π (yonedaEquiv.symm c))]
    [KanComplex (fiber (π p) y : SSet.{u})] : Fibration (tgt y c) :=
  RightFibration.fibration_of_kanComplex _

/-- The fibre of the target projection over `d` is weakly contractible exactly when the
corresponding fibre of the unrestricted projection over `c` is weakly contractible. -/
lemma isWeaklyContractible_fiber_tgt_iff (d : (fiber (π p) y : SSet.{u}) _⦋0⦌) :
    IsWeaklyContractible (fiber (tgt y c) d : SSet.{u}) ↔
      IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
  rw [tgt]
  exact isWeaklyContractible_fiber_fromPreimage_iff _ _ d

end postcompSpace

/-! ### Postcomposition with a cone -/

variable [RightFibration (π p)]

/-- For a diagram with right-fibration projection, **postcomposition with a cone `c`** over `p`
with cone point `x`, a map
from `Hom^R_C(y, x)` to the fibre over `y` of `C_{/p} ⟶ C`: a chosen section of the trivial
fibration `SSet.slice.postcompSpace.src`, followed by `SSet.slice.postcompSpace.tgt`. It sends an
edge `f : y ⟶ x` to a cone for which a morphism of cones to `c` over `f` exists
(`SSet.slice.exists_edge_postcomp`), and any other choice of section gives a homotopic map
(`SSet.slice.exists_homotopy_postcomp`). -/
noncomputable def postcomp :
    (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  section_ (postcompSpace.src y c) ≫ postcompSpace.tgt y c

/-- The composition map factors through a section of the source projection. -/
theorem exists_section_postcomp :
    ∃ s : (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) ⟶ (postcompSpace y c : SSet.{u}),
      s ≫ postcompSpace.src y c = 𝟙 _ ∧ s ≫ postcompSpace.tgt y c = postcomp y c := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  exact ⟨section_ (postcompSpace.src y c), IsSplitEpi.id _, rfl⟩

/-- **Postcomposition with `c` sends an edge `f : y ⟶ x` to a cone `d` with cone point `y`,
and there exists a morphism of cones from `d` to `c` lying over `f`.** -/
theorem exists_edge_postcomp (f : C.Edge y ((π p).app _ c)) :
    ∃ e : (slice p).Edge
        ((fiber (π p) y).ι.app _ ((postcomp y c).app _ (rightMappingSpace.obj₀Equiv.symm f))) c,
      (e.map (π p)).edge = f.edge := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  -- The image `v` of `f` under the chosen section is a morphism of cones with target `c` over `f`,
  -- whose source `d` is the image of `f` under `postcomp y c`.
  let v := (section_ (postcompSpace.src y c)).app _ (rightMappingSpace.obj₀Equiv.symm f)
  have hv : (postcompSpace.src y c).app _ v = rightMappingSpace.obj₀Equiv.symm f := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, IsSplitEpi.id, NatTrans.id_app,
      ConcreteCategory.id_apply]
  let d := (π (yonedaEquiv.symm c)).app _ v.val
  have hd : (fiber (π p) y).ι.app _ ((postcomp y c).app _ (rightMappingSpace.obj₀Equiv.symm f)) =
      d := by
    rw [postcomp, NatTrans.comp_app, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← NatTrans.comp_app, postcompSpace.tgt_ι]
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, d, v]
  rw [hd]
  have hf : f.edge = (π p).app _ (yonedaEquiv ((join.joinVertexIso ⦋0⦌).inv ≫
      (slice.objEquiv v.val).val) : (slice p).obj (op (joinVertex.obj ⦋0⦌))) := by
    rw [← rightMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, postcompSpace.src_app_coe]
    rw [← Category.assoc, yonedaEquiv_comp]
  -- `v` is a vertex of the fibre of `C_{/p}_{/c} ⟶ C_{/p}` over `d`, an edge from `d` to `c`.
  let w : (fiber (π (yonedaEquiv.symm c)) d : SSet.{u}) _⦋0⦌ :=
    fiber.basePoint (π (yonedaEquiv.symm c)) (x := v.val) rfl
  refine ⟨rightMappingSpace.obj₀Equiv ((rightMappingSpace.sliceFiberIso d c).hom.app _ w), ?_⟩
  rw [Edge.map_edge, rightMappingSpace.obj₀Equiv_apply_edge,
    rightMappingSpace.sliceFiberIso_hom_app_coe, hf, fiber.coe_basePoint]
  rw [join.joinVertexIso_zero]
  dsimp only [SimplexCategory.joinVertex]
  -- The remaining indices are `⦋1⦌` and `⦋0 + 1⦌`.
  rfl

/-- **Postcomposition with a cone is well-defined up to homotopy**: for every section `s` of the
trivial fibration `SSet.slice.postcompSpace.src`, the map `s ≫ tgt` is homotopic to
`SSet.slice.postcomp y c`. -/
theorem exists_homotopy_postcomp
    (s : (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) ⟶ (postcompSpace y c : SSet.{u}))
    (hs : s ≫ postcompSpace.src y c = 𝟙 _) :
    Nonempty (Homotopy (s ≫ postcompSpace.tgt y c) (postcomp y c)) := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  rw [postcomp]
  exact nonempty_homotopy_comp_section_comp (postcompSpace.rlp_src y c) _ s hs

end slice

namespace coslice

/-! ### Composites with a cocone -/

variable (c : (coslice p) _⦋0⦌) (y : C _⦋0⦌)

/-- The simplicial set `Hom^L_C(c, y)` of composites with a cocone `c`: the simplices of the coslice
`C_{p/}_{c/}`, the morphisms of cocones with source `c`, whose target lies in the fibre over `y` of
`C_{p/} ⟶ C`. It is the preimage of the fibre over `y` of `C_{x/} ⟶ C`,
canonically isomorphic to `Hom^L_C(x, y)`, for `x` the cocone point of `c`, under the projection
`C_{p/}_{c/} ⟶ C_{x/}`
(`SSet.coslice.precompSpace_eq_preimage`). -/
noncomputable def precompSpace : (coslice (yonedaEquiv.symm c)).Subcomplex :=
  (fiber (π p) y).preimage (π (yonedaEquiv.symm c))

/-- A simplex of `C_{p/}_{c/}` lies in `Hom^L_C(c, y)` exactly when its target lies over the
degeneracy of `y`. -/
@[simp]
theorem mem_precompSpace_iff {n : SimplexCategoryᵒᵖ} (s : (coslice (yonedaEquiv.symm c)).obj n) :
    s ∈ (precompSpace c y).obj n ↔
      (π p).app n ((π (yonedaEquiv.symm c)).app n s) = C.map (n.unop.const _ 0).op y := by
  rw [precompSpace, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff]

/-- `Hom^L_C(c, y)` is the preimage of the fibre over `y`
of `C_{x/} ⟶ C`, canonically isomorphic to the left mapping space `Hom^L_C(x, y)`, under the
projection `C_{p/}_{c/} ⟶ C_{x/}`. -/
theorem precompSpace_eq_preimage :
    precompSpace c y = (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).preimage
      (map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  rw [precompSpace, fiber_eq_preimage, fiber_eq_preimage, ← Subcomplex.preimage_comp,
    ← Subcomplex.preimage_comp, map_π]

namespace precompSpace

/-- The map `Hom^L_C(c, y) ⟶ (C_{p/})_y` sending a morphism of cocones with source `c` to its
target, a cocone with cocone point `y`. -/
noncomputable def tgt : (precompSpace c y : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  Subcomplex.fromPreimage _ _

/-- The projection `tgt` is the restriction of `C_{p/}_{c/} ⟶ C_{p/}`. -/
@[reassoc (attr := simp)]
theorem tgt_ι :
    tgt c y ≫ (fiber (π p) y).ι = (precompSpace c y).ι ≫ π (yonedaEquiv.symm c) :=
  Subcomplex.fromPreimage_ι _ _

/-- The map `Hom^L_C(c, y) ⟶ Hom^L_C(x, y)` projecting a morphism of cocones with source `c` to
`C`, for `x` the cocone point of `c`. -/
noncomputable def src :
    (precompSpace c y : SSet.{u}) ⟶ (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) :=
  (Subcomplex.eqToIso (precompSpace_eq_preimage c y)).hom ≫
  Subcomplex.fromPreimage _ _ ≫ (leftMappingSpace.cosliceFiberIso _ y).hom

/-- The source projection commutes with the inclusions into the slice or coslice. -/
@[reassoc (attr := simp)]
theorem src_inv_ι :
    src c y ≫ (leftMappingSpace.cosliceFiberIso ((π p).app _ c) y).inv ≫
        (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).ι =
      (precompSpace c y).ι ≫
        map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp]) := by
  simp [src, Subcomplex.eqToIso]

/-- The underlying simplex of the image under `src` of a morphism of cocones
`Δ[0] ⋆ Δ[n] ⟶ C_{p/}` is its composite with the projection `C_{p/} ⟶ C`, through
`Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
theorem src_app_coe {n : ℕ} (s : (precompSpace c y : SSet.{u}) _⦋n⦌) :
    ((src c y).app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val ≫ π p) : C _⦋n + 1⦌) := by
  rw [src, NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, leftMappingSpace.cosliceFiberIso_hom_app_coe,
    Subcomplex.fromPreimage, Subcomplex.lift_app_coe, NatTrans.comp_app,
    ConcreteCategory.comp_apply, objEquiv_map_app_coe, join.map_id, Category.id_comp]
  simp only [Subcomplex.eqToIso, Subcomplex.homOfLE, Subfunctor.homOfLe_app,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  rfl

/-- If the diagram projection is a left fibration, the source projection is a trivial
fibration: it is a base change of the map of slices or coslices of that projection over `c`
(`SSet.coslice.rlp_map_of_leftFibration`). -/
theorem rlp_src [LeftFibration (π p)] : (monomorphisms SSet.{u}).rlp (src c y) := by
  unfold src
  apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
  apply MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  intro A B i hi
  have := rlp_map_of_leftFibration (π p) (yonedaEquiv.symm c)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
  infer_instance

/-- The target map inherits the left fibration property of the projection from `C_{p/}_{c/}`
by base change over the vertex fibre. -/
instance leftFibration_tgt [LeftFibration (π (yonedaEquiv.symm c))] : LeftFibration (tgt c y) :=
  inferInstanceAs (LeftFibration (Subcomplex.fromPreimage _ _))

/-- The target map is a Kan fibration when the projection from `C_{p/}_{c/}` is a left
fibration and the vertex fibre of the diagram projection is a Kan complex. -/
instance fibration_tgt [LeftFibration (π (yonedaEquiv.symm c))]
    [KanComplex (fiber (π p) y : SSet.{u})] : Fibration (tgt c y) :=
  LeftFibration.fibration_of_kanComplex _

/-- The fibre of the target projection over `d` is weakly contractible exactly when the
corresponding fibre of the unrestricted projection over `c` is weakly contractible. -/
lemma isWeaklyContractible_fiber_tgt_iff (d : (fiber (π p) y : SSet.{u}) _⦋0⦌) :
    IsWeaklyContractible (fiber (tgt c y) d : SSet.{u}) ↔
      IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
  rw [tgt]
  exact isWeaklyContractible_fiber_fromPreimage_iff _ _ d

end precompSpace

/-! ### Precomposition with a cocone -/

variable [LeftFibration (π p)]

/-- For a diagram with left-fibration projection, **precomposition with a cocone `c`** under `p`
with cocone point `x`,
a map from `Hom^L_C(x, y)` to the fibre over `y` of `C_{p/} ⟶ C`: a chosen section of the trivial
fibration `SSet.coslice.precompSpace.src`, followed by `SSet.coslice.precompSpace.tgt`. It sends an
edge `f : x ⟶ y` to a cocone for which a morphism of cocones from `c` over `f` exists
(`SSet.coslice.exists_edge_precomp`), and any other choice of section gives a homotopic map
(`SSet.coslice.exists_homotopy_precomp`). -/
noncomputable def precomp :
    (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src c y)
  section_ (precompSpace.src c y) ≫ precompSpace.tgt c y

/-- The composition map factors through a section of the source projection. -/
theorem exists_section_precomp :
    ∃ s : (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) ⟶ (precompSpace c y : SSet.{u}),
      s ≫ precompSpace.src c y = 𝟙 _ ∧ s ≫ precompSpace.tgt c y = precomp c y := by
  have := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src c y)
  exact ⟨section_ (precompSpace.src c y), IsSplitEpi.id _, rfl⟩

/-- **Precomposition with `c` sends an edge `f : x ⟶ y` to a cocone `d` with cocone point `y`,
and there exists a morphism of cocones from `c` to `d` lying over `f`.** -/
theorem exists_edge_precomp (f : C.Edge ((π p).app _ c) y) :
    ∃ e : (coslice p).Edge c
        ((fiber (π p) y).ι.app _ ((precomp c y).app _ (leftMappingSpace.obj₀Equiv.symm f))),
      (e.map (π p)).edge = f.edge := by
  have := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src c y)
  -- The image `v` of `f` under the chosen section is a morphism of cocones with source `c` over
  -- `f`, whose target `d` is the image of `f` under `precomp c y`.
  let v := (section_ (precompSpace.src c y)).app _ (leftMappingSpace.obj₀Equiv.symm f)
  have hv : (precompSpace.src c y).app _ v = leftMappingSpace.obj₀Equiv.symm f := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, IsSplitEpi.id, NatTrans.id_app,
      ConcreteCategory.id_apply]
  let d := (π (yonedaEquiv.symm c)).app _ v.val
  have hd : (fiber (π p) y).ι.app _ ((precomp c y).app _ (leftMappingSpace.obj₀Equiv.symm f)) =
      d := by
    rw [precomp, NatTrans.comp_app, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← NatTrans.comp_app, precompSpace.tgt_ι]
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, d, v]
  rw [hd]
  have hf : f.edge = (π p).app _ (yonedaEquiv ((join.coneIso 0).inv ≫
      (coslice.objEquiv v.val).val) : (coslice p) _⦋0 + 1⦌) := by
    rw [← leftMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, precompSpace.src_app_coe]
    rw [← Category.assoc, yonedaEquiv_comp]
  -- `v` is a vertex of the fibre of `C_{p/}_{c/} ⟶ C_{p/}` over `d`, an edge from `c` to `d`.
  let w : (fiber (π (yonedaEquiv.symm c)) d : SSet.{u}) _⦋0⦌ :=
    fiber.basePoint (π (yonedaEquiv.symm c)) (x := v.val) rfl
  refine ⟨leftMappingSpace.obj₀Equiv ((leftMappingSpace.cosliceFiberIso c d).hom.app _ w), ?_⟩
  rw [Edge.map_edge, leftMappingSpace.obj₀Equiv_apply_edge,
    leftMappingSpace.cosliceFiberIso_hom_app_coe, hf, fiber.coe_basePoint]

/-- **Precomposition with a cocone is well-defined up to homotopy**: for every section `s` of the
trivial fibration `SSet.coslice.precompSpace.src`, the map `s ≫ tgt` is homotopic to
`SSet.coslice.precomp c y`. -/
theorem exists_homotopy_precomp
    (s : (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) ⟶ (precompSpace c y : SSet.{u}))
    (hs : s ≫ precompSpace.src c y = 𝟙 _) :
    Nonempty (Homotopy (s ≫ precompSpace.tgt c y) (precomp c y)) := by
  have := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src c y)
  rw [precomp]
  exact nonempty_homotopy_comp_section_comp (precompSpace.rlp_src c y) _ s hs

end coslice

end SSet
