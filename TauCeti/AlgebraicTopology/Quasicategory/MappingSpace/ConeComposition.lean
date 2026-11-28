/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex
public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.Quasicategory.LeftMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# Composition along right and left fibrations

For a right fibration `q : E ⟶ C` and a vertex `c` of `E`, lifting an edge into `q(c)`
produces a vertex in the source fibre. Dually, a left fibration lifts edges out of `q(c)`.
The composition maps choose sections of trivial fibrations, following
`SSet.rightMappingSpace.postcomp` for the right-fibration construction and its left-fibration
dual. These sections are chosen independently; any other section gives a homotopic map.

For a quasicategory base, these maps detect terminal and initial vertices of `E`.
Taking `q` to be a diagram's slice or coslice projection gives composition with cones and
cocones and the mapping-space criteria for limits and colimits.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 4.2.4.3.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Simplicial SimplexCategory

namespace SSet

open modelCategoryQuillen

variable {E C : SSet.{u}} (q : E ⟶ C)

namespace slice

/-! ### Right-fibration composites -/

variable (y : C _⦋0⦌) (c : E _⦋0⦌)

/-- The simplices of the slice `E_{/c}` over the vertex `c` whose
source lies in the fibre of `q : E ⟶ C` over `y`. For a diagram projection these are
morphisms of cones into `c` with other cone point `y`.
The source projection maps this space to the right mapping space in `C`. -/
noncomputable def postcompSpace : (slice (yonedaEquiv.symm c)).Subcomplex :=
  (fiber q y).preimage (π (yonedaEquiv.symm c))

/-- A slice simplex belongs to the composition space exactly when its source lies over the
degeneracy of `y`. -/
@[simp]
theorem mem_postcompSpace_iff {n : SimplexCategoryᵒᵖ} (s : (slice (yonedaEquiv.symm c)).obj n) :
    s ∈ (postcompSpace q y c).obj n ↔
      q.app n ((π (yonedaEquiv.symm c)).app n s) = C.map (n.unop.const _ 0).op y := by
  rw [postcompSpace, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff]

/-- The composition space is the preimage of the fibre over `y`
of `C_{/x} ⟶ C`, canonically isomorphic to the right mapping space `Hom^R_C(y, x)`, under the
projection `E_{/c} ⟶ C_{/x}`, where `x = q(c)`. -/
theorem postcompSpace_eq_preimage :
    postcompSpace q y c = (fiber (π (yonedaEquiv.symm (q.app _ c))) y).preimage
      (map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  rw [postcompSpace, fiber_eq_preimage, fiber_eq_preimage, ← Subcomplex.preimage_comp,
    ← Subcomplex.preimage_comp, map_π]

namespace postcompSpace

/-- The projection to the fibre of `q` over `y`, sending a slice simplex
with target `c` to its source in `E`. -/
noncomputable def tgt : (postcompSpace q y c : SSet.{u}) ⟶ (fiber q y : SSet.{u}) :=
  Subcomplex.fromPreimage _ _

/-- The projection `tgt` is the restriction of `E_{/c} ⟶ E`. -/
@[reassoc (attr := simp)]
theorem tgt_ι :
    tgt q y c ≫ (fiber q y).ι = (postcompSpace q y c).ι ≫ π (yonedaEquiv.symm c) :=
  Subcomplex.fromPreimage_ι _ _

/-- The target projection acts on underlying simplices by the vertex-slice projection. -/
@[simp]
theorem tgt_app_coe {n : SimplexCategoryᵒᵖ} (s : (postcompSpace q y c : SSet.{u}).obj n) :
    dsimp% ((tgt q y c).app n s).val = (π (yonedaEquiv.symm c)).app n s.val := by
  exact congrArg (fun k ↦ k.app n s) (tgt_ι q y c)

/-- The target projection is the pullback of the vertex-slice projection along the fibre
inclusion. -/
theorem isPullback_tgt :
    IsPullback (postcompSpace q y c).ι (tgt q y c)
      (π (yonedaEquiv.symm c)) (fiber q y).ι :=
  Subcomplex.isPullback_fromPreimage _ _

/-- The projection to the right mapping space between `y` and `q(c)`, induced by
the map of slices associated to `q`. -/
noncomputable def src :
    (postcompSpace q y c : SSet.{u}) ⟶ (C.rightMappingSpace y (q.app _ c) : SSet.{u}) :=
  (Subcomplex.eqToIso (postcompSpace_eq_preimage q y c)).hom ≫
  Subcomplex.fromPreimage _ _ ≫ (rightMappingSpace.sliceFiberIso y _).hom

/-- The source projection followed by the inverse right mapping-space identification
and the inclusion of the fibre of `C_{/q(c)} ⟶ C` agrees with the map of
slices induced by `q`, after the inclusion in `E_{/c}`. -/
@[reassoc (attr := simp)]
theorem src_inv_ι :
    src q y c ≫ (rightMappingSpace.sliceFiberIso y (q.app _ c)).inv ≫
        (fiber (π (yonedaEquiv.symm (q.app _ c))) y).ι =
      (postcompSpace q y c).ι ≫
        map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp]) := by
  simp [src, Subcomplex.eqToIso]

/-- The source projection is the pullback of the map of vertex slices induced by `q`,
using the mapping-space identification of its fibre. -/
theorem isPullback_src :
    IsPullback (postcompSpace q y c).ι (src q y c)
      (map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp]))
      ((rightMappingSpace.sliceFiberIso y _).inv ≫
        (fiber (π (yonedaEquiv.symm (q.app _ c))) y).ι) := by
  refine (Subcomplex.isPullback_fromPreimage _ _).of_iso
    (Subcomplex.eqToIso (postcompSpace_eq_preimage q y c)).symm
    (Iso.refl _) (rightMappingSpace.sliceFiberIso y _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp [src, Subcomplex.eqToIso, ← Category.assoc, Subcomplex.homOfLE_comp]

/-- On underlying simplices the source projection composes the slice simplex with
`q`, through the standard-simplex join isomorphism. -/
theorem src_app_coe {m : SimplexCategory} (s : (postcompSpace q y c : SSet.{u}).obj (op m)) :
    ((src q y c).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫ (slice.objEquiv s.val).val ≫ q) :
        C.obj (op (joinVertex.obj m))) := by
  rw [src, NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, rightMappingSpace.sliceFiberIso_hom_app_coe,
    Subcomplex.fromPreimage, Subcomplex.lift_app_coe, NatTrans.comp_app,
    ConcreteCategory.comp_apply, objEquiv_map_app_coe, join.map_id, Category.id_comp]
  simp only [Subcomplex.eqToIso_hom, Subfunctor.ι_app, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk]
  rw [Subcomplex.homOfLE_app_val]

/-- For a right fibration `q`, the source projection is a trivial fibration:
it is a base change of the map of slices `E_{/c} ⟶ C_{/q(c)}` induced by `q`
(`SSet.slice.rlp_map_of_rightFibration`). -/
theorem rlp_src [RightFibration q] : (monomorphisms SSet.{u}).rlp (src q y c) := by
  unfold src
  apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
  apply MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  intro A B i hi
  have := rlp_map_of_rightFibration q (yonedaEquiv.symm c)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
  infer_instance

/-- The target map inherits the right fibration property of the projection from `E_{/c}`
by base change over the vertex fibre. -/
instance rightFibration_tgt [RightFibration (π (yonedaEquiv.symm c))] :
    RightFibration (tgt q y c) :=
  inferInstanceAs (RightFibration (Subcomplex.fromPreimage _ _))

/-- The target map is a Kan fibration when the projection from `E_{/c}` is a right
fibration and the vertex fibre of `q` is a Kan complex. -/
instance fibration_tgt [RightFibration (π (yonedaEquiv.symm c))]
    [KanComplex (fiber q y : SSet.{u})] : Fibration (tgt q y c) :=
  RightFibration.fibration_of_kanComplex _

end postcompSpace

/-! ### Composition along a right fibration -/

variable [RightFibration q]

/-- Composition along a right fibration `q` with a vertex `c` above `x`:
a map from `Hom^R_C(y, x)` to the fibre of `q` over `y`. It is a chosen section of
`SSet.slice.postcompSpace.src` followed by `SSet.slice.postcompSpace.tgt`.
An edge into `x` gives a vertex in that fibre and an edge to `c` above the input edge
(`SSet.slice.exists_edge_postcomp`), independently of the section up to homotopy
(`SSet.slice.exists_homotopy_postcomp`). -/
noncomputable def postcomp :
    (C.rightMappingSpace y (q.app _ c) : SSet.{u}) ⟶ (fiber q y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src q y c)
  section_ (postcompSpace.src q y c) ≫ postcompSpace.tgt q y c

/-- The composition map factors through a section of the source projection. -/
theorem exists_section_postcomp :
    ∃ s : (C.rightMappingSpace y (q.app _ c) : SSet.{u}) ⟶ (postcompSpace q y c : SSet.{u}),
      s ≫ postcompSpace.src q y c = 𝟙 _ ∧ s ≫ postcompSpace.tgt q y c = postcomp q y c := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src q y c)
  exact ⟨section_ (postcompSpace.src q y c), IsSplitEpi.id _, rfl⟩

/-- Composition with `c` lifts an edge into `q(c)` to an edge ending at `c`
whose other endpoint is the vertex chosen by `SSet.slice.postcomp`. -/
theorem exists_edge_postcomp (f : C.Edge y (q.app _ c)) :
    ∃ e : E.Edge
        ((fiber q y).ι.app _ ((postcomp q y c).app _ (rightMappingSpace.obj₀Equiv.symm f))) c,
      (e.map q).edge = f.edge := by
  obtain ⟨s, hs, he⟩ := exists_section_postcomp q y c
  -- The image `v` of `f` under the section is a slice vertex over `f`, with target `c`,
  -- whose source `d` is the image of `f` under `postcomp q y c`.
  let v := s.app _ (rightMappingSpace.obj₀Equiv.symm f)
  have hv : (postcompSpace.src q y c).app _ v = rightMappingSpace.obj₀Equiv.symm f := by
    exact congrArg (fun k ↦ k.app _ (rightMappingSpace.obj₀Equiv.symm f)) hs
  let d := (π (yonedaEquiv.symm c)).app _ v.val
  have hd : (fiber q y).ι.app _ ((postcomp q y c).app _ (rightMappingSpace.obj₀Equiv.symm f)) =
      d := by
    rw [← he, NatTrans.comp_app_apply]
    exact postcompSpace.tgt_app_coe q y c _
  rw [hd]
  have hf : f.edge = q.app _ (yonedaEquiv ((join.joinVertexIso ⦋0⦌).inv ≫
      (slice.objEquiv v.val).val) : E.obj (op (joinVertex.obj ⦋0⦌))) := by
    rw [← rightMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, postcompSpace.src_app_coe]
    rw [← Category.assoc, yonedaEquiv_comp]
  -- `v` is a vertex of the fibre of `E_{/c} ⟶ E` over `d`, an edge from `d` to `c`.
  let w : (fiber (π (yonedaEquiv.symm c)) d : SSet.{u}) _⦋0⦌ :=
    fiber.basePoint (π (yonedaEquiv.symm c)) (x := v.val) rfl
  refine ⟨rightMappingSpace.obj₀Equiv ((rightMappingSpace.sliceFiberIso d c).hom.app _ w), ?_⟩
  rw [Edge.map_edge, rightMappingSpace.obj₀Equiv_apply_edge,
    rightMappingSpace.sliceFiberIso_hom_app_coe, hf, fiber.coe_basePoint]
  rw [join.joinVertexIso_zero]
  dsimp only [SimplexCategory.joinVertex]
  -- The remaining indices are `⦋1⦌` and `⦋0 + 1⦌`.
  rfl

/-- Composition along `q` is independent of the section up to homotopy: any section
of `SSet.slice.postcompSpace.src`, followed by `tgt`, is homotopic to
`SSet.slice.postcomp`. -/
theorem exists_homotopy_postcomp
    (s : (C.rightMappingSpace y (q.app _ c) : SSet.{u}) ⟶ (postcompSpace q y c : SSet.{u}))
    (hs : s ≫ postcompSpace.src q y c = 𝟙 _) :
    Nonempty (Homotopy (s ≫ postcompSpace.tgt q y c) (postcomp q y c)) := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src q y c)
  rw [postcomp]
  exact nonempty_homotopy_comp_section_comp (postcompSpace.rlp_src q y c)
    _ s (section_ _) hs (IsSplitEpi.id _)

/-- For a right fibration over a quasicategory, composition with a vertex detects
whether that vertex is terminal: all the induced maps to the base fibres must be
weak homotopy equivalences. -/
theorem isTerminalVertex_iff_forall_isWeakHomotopyEquivalence_postcomp [Quasicategory C] :
    E.IsTerminalVertex c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (postcomp q y c) := by
  have : Quasicategory E := quasicategory_of_innerFibration q
  have h (y : C _⦋0⦌) : IsWeakHomotopyEquivalence (postcomp q y c) ↔
      ∀ d : (fiber q y : SSet.{u}) _⦋0⦌,
        IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
    obtain ⟨s, hs, he⟩ := exists_section_postcomp q y c
    have := isWeakHomotopyEquivalence_of_rlp_monomorphisms (postcompSpace.rlp_src q y c)
    rw [← he, isWeakHomotopyEquivalence_section_comp_iff _ s hs,
      ← rlp_monomorphisms_iff_isWeakHomotopyEquivalence,
      RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
    simp only [postcompSpace.tgt, postcompSpace, isWeaklyContractible_fiber_fromPreimage_iff]
  simp only [h]
  rw [isTerminalVertex_iff_rlp_monomorphisms_π,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint q (x := d) rfl)⟩

end slice

namespace coslice

/-! ### Left-fibration composites -/

variable (c : E _⦋0⦌) (y : C _⦋0⦌)

/-- The simplices of the coslice `E_{c/}` over the vertex `c` whose
target lies in the fibre of `q : E ⟶ C` over `y`. For a diagram projection these are
morphisms of cocones out of `c` with other cone point `y`.
The source projection maps this space to the left mapping space in `C`. -/
noncomputable def precompSpace : (coslice (yonedaEquiv.symm c)).Subcomplex :=
  (fiber q y).preimage (π (yonedaEquiv.symm c))

/-- A coslice simplex belongs to the composition space exactly when its target lies over the
degeneracy of `y`. -/
@[simp]
theorem mem_precompSpace_iff {n : SimplexCategoryᵒᵖ} (s : (coslice (yonedaEquiv.symm c)).obj n) :
    s ∈ (precompSpace q c y).obj n ↔
      q.app n ((π (yonedaEquiv.symm c)).app n s) = C.map (n.unop.const _ 0).op y := by
  rw [precompSpace, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff]

/-- The composition space is the preimage of the fibre over `y`
of `C_{x/} ⟶ C`, canonically isomorphic to the left mapping space `Hom^L_C(x, y)`, under the
projection `E_{c/} ⟶ C_{x/}`, where `x = q(c)`. -/
theorem precompSpace_eq_preimage :
    precompSpace q c y = (fiber (π (yonedaEquiv.symm (q.app _ c))) y).preimage
      (map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  rw [precompSpace, fiber_eq_preimage, fiber_eq_preimage, ← Subcomplex.preimage_comp,
    ← Subcomplex.preimage_comp, map_π]

namespace precompSpace

/-- The projection to the fibre of `q` over `y`, sending a coslice simplex
with source `c` to its target in `E`. -/
noncomputable def tgt : (precompSpace q c y : SSet.{u}) ⟶ (fiber q y : SSet.{u}) :=
  Subcomplex.fromPreimage _ _

/-- The projection `tgt` is the restriction of `E_{c/} ⟶ E`. -/
@[reassoc (attr := simp)]
theorem tgt_ι :
    tgt q c y ≫ (fiber q y).ι = (precompSpace q c y).ι ≫ π (yonedaEquiv.symm c) :=
  Subcomplex.fromPreimage_ι _ _

/-- The target projection acts on underlying simplices by the vertex-coslice projection. -/
@[simp]
theorem tgt_app_coe {n : SimplexCategoryᵒᵖ} (s : (precompSpace q c y : SSet.{u}).obj n) :
    dsimp% ((tgt q c y).app n s).val = (π (yonedaEquiv.symm c)).app n s.val := by
  exact congrArg (fun k ↦ k.app n s) (tgt_ι q c y)

/-- The target projection is the pullback of the vertex-coslice projection along the fibre
inclusion. -/
theorem isPullback_tgt :
    IsPullback (precompSpace q c y).ι (tgt q c y)
      (π (yonedaEquiv.symm c)) (fiber q y).ι :=
  Subcomplex.isPullback_fromPreimage _ _

/-- The projection to the left mapping space between `y` and `q(c)`, induced by
the map of coslices associated to `q`. -/
noncomputable def src :
    (precompSpace q c y : SSet.{u}) ⟶ (C.leftMappingSpace (q.app _ c) y : SSet.{u}) :=
  (Subcomplex.eqToIso (precompSpace_eq_preimage q c y)).hom ≫
  Subcomplex.fromPreimage _ _ ≫ (leftMappingSpace.cosliceFiberIso _ y).hom

/-- The source projection followed by the inverse left mapping-space identification
and the inclusion of the fibre of `C_{q(c)/} ⟶ C` agrees with the map of
coslices induced by `q`, after the inclusion in `E_{c/}`. -/
@[reassoc (attr := simp)]
theorem src_inv_ι :
    src q c y ≫ (leftMappingSpace.cosliceFiberIso (q.app _ c) y).inv ≫
        (fiber (π (yonedaEquiv.symm (q.app _ c))) y).ι =
      (precompSpace q c y).ι ≫
        map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp]) := by
  simp [src, Subcomplex.eqToIso]

/-- The source projection is the pullback of the map of vertex coslices induced by `q`,
using the mapping-space identification of its fibre. -/
theorem isPullback_src :
    IsPullback (precompSpace q c y).ι (src q c y)
      (map (𝟙 Δ[0]) q (by rw [Category.id_comp, yonedaEquiv_symm_comp]))
      ((leftMappingSpace.cosliceFiberIso _ y).inv ≫
        (fiber (π (yonedaEquiv.symm (q.app _ c))) y).ι) := by
  refine (Subcomplex.isPullback_fromPreimage _ _).of_iso
    (Subcomplex.eqToIso (precompSpace_eq_preimage q c y)).symm
    (Iso.refl _) (leftMappingSpace.cosliceFiberIso _ y) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp [src, Subcomplex.eqToIso, ← Category.assoc, Subcomplex.homOfLE_comp]

/-- On underlying simplices the source projection composes the coslice simplex with
`q`, through the standard-simplex join isomorphism. -/
theorem src_app_coe {n : ℕ} (s : (precompSpace q c y : SSet.{u}) _⦋n⦌) :
    ((src q c y).app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val ≫ q) : C _⦋n + 1⦌) := by
  rw [src, NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, leftMappingSpace.cosliceFiberIso_hom_app_coe,
    Subcomplex.fromPreimage, Subcomplex.lift_app_coe, NatTrans.comp_app,
    ConcreteCategory.comp_apply, objEquiv_map_app_coe, join.map_id, Category.id_comp]
  simp only [Subcomplex.eqToIso_hom, Subfunctor.ι_app, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk]
  rw [Subcomplex.homOfLE_app_val]

/-- For a left fibration `q`, the source projection is a trivial fibration:
it is a base change of the map of coslices `E_{c/} ⟶ C_{q(c)/}` induced by `q`
(`SSet.coslice.rlp_map_of_leftFibration`). -/
theorem rlp_src [LeftFibration q] : (monomorphisms SSet.{u}).rlp (src q c y) := by
  unfold src
  apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
  apply MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  intro A B i hi
  have := rlp_map_of_leftFibration q (yonedaEquiv.symm c)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
  infer_instance

/-- The target map inherits the left fibration property of the projection from `E_{c/}`
by base change over the vertex fibre. -/
instance leftFibration_tgt [LeftFibration (π (yonedaEquiv.symm c))] : LeftFibration (tgt q c y) :=
  inferInstanceAs (LeftFibration (Subcomplex.fromPreimage _ _))

/-- The target map is a Kan fibration when the projection from `E_{c/}` is a left
fibration and the vertex fibre of `q` is a Kan complex. -/
instance fibration_tgt [LeftFibration (π (yonedaEquiv.symm c))]
    [KanComplex (fiber q y : SSet.{u})] : Fibration (tgt q c y) :=
  LeftFibration.fibration_of_kanComplex _

end precompSpace

/-! ### Composition along a left fibration -/

variable [LeftFibration q]

/-- Composition along a left fibration `q` with a vertex `c` above `x`:
a map from `Hom^L_C(x, y)` to the fibre of `q` over `y`. It is a chosen section of
`SSet.coslice.precompSpace.src` followed by `SSet.coslice.precompSpace.tgt`.
An edge out of `x` gives a vertex in that fibre and an edge from `c` above the input edge
(`SSet.coslice.exists_edge_precomp`), independently of the section up to homotopy
(`SSet.coslice.exists_homotopy_precomp`). -/
noncomputable def precomp :
    (C.leftMappingSpace (q.app _ c) y : SSet.{u}) ⟶ (fiber q y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src q c y)
  section_ (precompSpace.src q c y) ≫ precompSpace.tgt q c y

/-- The composition map factors through a section of the source projection. -/
theorem exists_section_precomp :
    ∃ s : (C.leftMappingSpace (q.app _ c) y : SSet.{u}) ⟶ (precompSpace q c y : SSet.{u}),
      s ≫ precompSpace.src q c y = 𝟙 _ ∧ s ≫ precompSpace.tgt q c y = precomp q c y := by
  have := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src q c y)
  exact ⟨section_ (precompSpace.src q c y), IsSplitEpi.id _, rfl⟩

/-- Composition with `c` lifts an edge out of `q(c)` to an edge starting at `c`
whose other endpoint is the vertex chosen by `SSet.coslice.precomp`. -/
theorem exists_edge_precomp (f : C.Edge (q.app _ c) y) :
    ∃ e : E.Edge c
        ((fiber q y).ι.app _ ((precomp q c y).app _ (leftMappingSpace.obj₀Equiv.symm f))),
      (e.map q).edge = f.edge := by
  obtain ⟨s, hs, he⟩ := exists_section_precomp q c y
  -- The image `v` of `f` under the section is a coslice vertex with source `c` over
  -- `f`, whose target `d` is the image of `f` under `precomp q c y`.
  let v := s.app _ (leftMappingSpace.obj₀Equiv.symm f)
  have hv : (precompSpace.src q c y).app _ v = leftMappingSpace.obj₀Equiv.symm f := by
    exact congrArg (fun k ↦ k.app _ (leftMappingSpace.obj₀Equiv.symm f)) hs
  let d := (π (yonedaEquiv.symm c)).app _ v.val
  have hd : (fiber q y).ι.app _ ((precomp q c y).app _ (leftMappingSpace.obj₀Equiv.symm f)) =
      d := by
    rw [← he, NatTrans.comp_app_apply]
    exact precompSpace.tgt_app_coe q c y _
  rw [hd]
  have hf : f.edge = q.app _ (yonedaEquiv ((join.coneIso 0).inv ≫
      (coslice.objEquiv v.val).val) : E _⦋0 + 1⦌) := by
    rw [← leftMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, precompSpace.src_app_coe]
    rw [← Category.assoc, yonedaEquiv_comp]
  -- `v` is a vertex of the fibre of `E_{c/} ⟶ E` over `d`, an edge from `c` to `d`.
  let w : (fiber (π (yonedaEquiv.symm c)) d : SSet.{u}) _⦋0⦌ :=
    fiber.basePoint (π (yonedaEquiv.symm c)) (x := v.val) rfl
  refine ⟨leftMappingSpace.obj₀Equiv ((leftMappingSpace.cosliceFiberIso c d).hom.app _ w), ?_⟩
  rw [Edge.map_edge, leftMappingSpace.obj₀Equiv_apply_edge,
    leftMappingSpace.cosliceFiberIso_hom_app_coe, hf, fiber.coe_basePoint]

/-- Composition along `q` is independent of the section up to homotopy: any section
of `SSet.coslice.precompSpace.src`, followed by `tgt`, is homotopic to
`SSet.coslice.precomp`. -/
theorem exists_homotopy_precomp
    (s : (C.leftMappingSpace (q.app _ c) y : SSet.{u}) ⟶ (precompSpace q c y : SSet.{u}))
    (hs : s ≫ precompSpace.src q c y = 𝟙 _) :
    Nonempty (Homotopy (s ≫ precompSpace.tgt q c y) (precomp q c y)) := by
  have := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src q c y)
  rw [precomp]
  exact nonempty_homotopy_comp_section_comp (precompSpace.rlp_src q c y)
    _ s (section_ _) hs (IsSplitEpi.id _)

/-- For a left fibration over a quasicategory, composition with a vertex detects
whether that vertex is initial: all the induced maps to the base fibres must be
weak homotopy equivalences. -/
theorem isInitialVertex_iff_forall_isWeakHomotopyEquivalence_precomp [Quasicategory C] :
    E.IsInitialVertex c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (precomp q c y) := by
  have : Quasicategory E := quasicategory_of_innerFibration q
  have h (y : C _⦋0⦌) : IsWeakHomotopyEquivalence (precomp q c y) ↔
      ∀ d : (fiber q y : SSet.{u}) _⦋0⦌,
        IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
    obtain ⟨s, hs, he⟩ := exists_section_precomp q c y
    have := isWeakHomotopyEquivalence_of_rlp_monomorphisms (precompSpace.rlp_src q c y)
    rw [← he, isWeakHomotopyEquivalence_section_comp_iff _ s hs,
      ← rlp_monomorphisms_iff_isWeakHomotopyEquivalence,
      LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
    simp only [precompSpace.tgt, precompSpace, isWeaklyContractible_fiber_fromPreimage_iff]
  simp only [h]
  rw [isInitialVertex_iff_rlp_monomorphisms_π,
    LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint q (x := d) rfl)⟩

end coslice

end SSet
