/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.LeftMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.Limit.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex
public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# The mapping-space criterion for limits and colimits

Let `C` be a quasicategory, `p : K ⟶ C` a diagram and `c` a cone over `p`, that is a vertex of the
slice `C_{/p}`, with cone point `x`. For a vertex `y` of `C`, the fibre over `y` of the projection
`C_{/p} ⟶ C` is the Kan complex of cones over `p` with cone point `y`. Composing with `c` sends a
morphism `y ⟶ x` to such a cone, but only up to a contractible space of choices, as for the
postcomposition `SSet.rightMappingSpace.postcomp` with an edge, which is the case `K = Δ[0]`.

Write `S = C_{/p}`. The slice `S_{/c}` of `S` over its vertex `c` has as vertices the morphisms of
cones with target `c`. It maps to `S` by its projection, restricting to the source of the morphism,
and to `C_{/x}` by projecting the morphism to `C`, over `C`. Taking fibres over `y` gives the span
`Hom^R_C(y, x) ⟵ Hom^R_C(y, c) ⟶ S_y`, whose middle term is
`SSet.slice.postcompSpace y c`. Its left leg `SSet.slice.postcompSpace.src` is a trivial
fibration (`SSet.slice.postcompSpace.rlp_src`): it is a base change of `S_{/c} ⟶ C_{/x}`, which
is one because `S ⟶ C` is a right fibration and `∂Δ[n] ⋆ Δ[0] ⟶ Δ[n] ⋆ Δ[0]` is the horn
`Λ[n + 1, n + 1]` (`SSet.slice.rlp_map_of_rightFibration`). Choosing a section of it gives the
postcomposition `SSet.slice.postcomp y c : Hom^R_C(y, x) ⟶ S_y`, which sends an edge `f : y ⟶ x`
to a cone with cone point `y` together with a morphism of cones to `c` over `f`
(`SSet.slice.exists_edge_postcomp`), and which does not depend on the section up to homotopy
(`SSet.slice.exists_homotopy_postcomp`).

**The mapping-space criterion** (`SSet.slice.isLimit_iff_forall_isWeakHomotopyEquivalence_postcomp`,
HTT Lemma 4.2.4.3): `c` is a limit cone exactly when `SSet.slice.postcomp y c` is a weak homotopy
equivalence for every vertex `y` of `C`. Indeed `c` is a terminal vertex of `S` exactly when the
projection `S_{/c} ⟶ S` is a trivial fibration (`SSet.isTerminalVertex_iff_rlp_monomorphisms_π`).
This projection is a right fibration, so it is a trivial fibration exactly when its fibres are
weakly contractible (`SSet.RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber`), and
these are the fibres of the right leg `SSet.slice.postcompSpace.tgt` of the spans. That leg is a
Kan fibration between Kan complexes, so it is a trivial fibration exactly when it is a weak
homotopy equivalence (`SSet.rlp_monomorphisms_iff_isWeakHomotopyEquivalence`), which by two out of
three happens exactly when `SSet.slice.postcomp y c` is one.

Dually, for a cocone `c` under `p` with cocone point `x`, precomposition with `c` is a map
`SSet.coslice.precomp c y` from the left mapping space `Hom^L_C(x, y)` to the fibre over `y` of the
projection `C_{p/} ⟶ C`, and `c` is a colimit cocone exactly when it is a weak homotopy equivalence
for every vertex `y` (`SSet.coslice.isColimit_iff_forall_isWeakHomotopyEquivalence_precomp`). The
proof is the dual one: `C_{p/} ⟶ C` is a left fibration, `Δ[0] ⋆ ∂Δ[n] ⟶ Δ[0] ⋆ Δ[n]` is the horn
`Λ[n + 1, 0]`, and an initial vertex is one under which the coslice projection is a trivial
fibration (`SSet.isInitialVertex_iff_rlp_monomorphisms_π`).

## Main definitions

* `SSet.slice.postcompSpace y c`: the simplicial set `Hom^R_C(y, c)` of composites with a cone `c`,
  the fibre over `y` of `C_{/p}_{/c} ⟶ C`.
* `SSet.slice.postcompSpace.src`, `SSet.slice.postcompSpace.tgt`: its maps to the right mapping
  space `Hom^R_C(y, x)` and to the fibre of `C_{/p} ⟶ C` over `y`.
* `SSet.slice.postcomp y c`: for a quasicategory `C`, the postcomposition with `c`, a map from
  `Hom^R_C(y, x)` to the fibre of `C_{/p} ⟶ C` over `y`.
* `SSet.coslice.precompSpace c y`, `SSet.coslice.precompSpace.src`,
  `SSet.coslice.precompSpace.tgt`, `SSet.coslice.precomp c y`: the duals for a cocone `c`, with the
  left mapping space `Hom^L_C(x, y)`.

## Main results

* `SSet.slice.postcompSpace.rlp_src`: for a quasicategory, `src` is a trivial fibration.
* `SSet.slice.exists_edge_postcomp`: `postcomp y c` sends an edge `f` to a cone with a morphism of
  cones to `c` over `f`.
* `SSet.slice.exists_homotopy_postcomp`: every map obtained from a section of `src` is homotopic to
  `postcomp y c`.
* `SSet.slice.isLimit_iff_forall_isWeakHomotopyEquivalence_postcomp`: the mapping-space criterion
  for limit cones.
* `SSet.coslice.precompSpace.rlp_src`, `SSet.coslice.exists_edge_precomp`,
  `SSet.coslice.exists_homotopy_precomp` and
  `SSet.coslice.isColimit_iff_forall_isWeakHomotopyEquivalence_precomp`: the duals for cocones, and
  the mapping-space criterion for colimit cocones.

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
`C_{/p} ⟶ C`. It is the preimage of the right mapping space `Hom^R_C(y, x) ⊆ C_{/x}`, for `x` the
cone point of `c`, under the projection `C_{/p}_{/c} ⟶ C_{/x}`
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

/-- `Hom^R_C(y, c)` is the preimage of the right mapping space `Hom^R_C(y, x)`, the fibre over `y`
of `C_{/x} ⟶ C`, under the projection `C_{/p}_{/c} ⟶ C_{/x}`. -/
theorem postcompSpace_eq_preimage :
    postcompSpace y c = (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).preimage
      (map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  ext n s
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (map_π (𝟙 Δ[0]) (π p)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp])) n) s
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  rw [mem_postcompSpace_iff, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff, h]

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

/-- `Hom^R_C(y, c)` lands, under the projection `C_{/p}_{/c} ⟶ C_{/x}`, in the right mapping space
`Hom^R_C(y, x)`, the fibre over `y` of `C_{/x} ⟶ C`. -/
private lemma range_ι_comp_map_le :
    Subcomplex.range ((postcompSpace y c).ι ≫
      map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) ≤
        fiber (π (yonedaEquiv.symm ((π p).app _ c))) y := by
  rw [range_le_fiber_iff, Category.assoc, map_π, ← tgt_ι_assoc, fiber.ι_comp, comp_const]

/-- The map `Hom^R_C(y, c) ⟶ Hom^R_C(y, x)` projecting a morphism of cones with target `c` to `C`,
for `x` the cone point of `c`. -/
noncomputable def src :
    (postcompSpace y c : SSet.{u}) ⟶ (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) :=
  Subcomplex.lift _ (range_ι_comp_map_le y c) ≫ (rightMappingSpace.sliceFiberIso y _).hom

/-- The underlying simplex of the image under `src` of a morphism of cones `Δ[n] ⋆ Δ[0] ⟶ C_{/p}`
is its composite with the projection `C_{/p} ⟶ C`, through `Δ[n + 1] ≅ Δ[n] ⋆ Δ[0]`. -/
theorem src_app_coe {m : SimplexCategory} (s : (postcompSpace y c : SSet.{u}).obj (op m)) :
    ((src y c).app (op m) s).val =
      (yonedaEquiv ((join.joinVertexIso m).inv ≫ (slice.objEquiv s.val).val ≫ π p) :
        C.obj (op (joinVertex.obj m))) := by
  have h := rightMappingSpace.sliceFiberIso_hom_app_coe y ((π p).app _ c)
    ((Subcomplex.lift _ (range_ι_comp_map_le y c)).app _ s)
  refine h.trans ?_
  rw [Subcomplex.lift_app_coe, NatTrans.comp_app, ConcreteCategory.comp_apply,
    objEquiv_map_app_coe, join.map_id, Category.id_comp]
  -- The inclusion of `postcompSpace y c` sends `s` to `s.val`.
  rfl

variable [Quasicategory C]

/-- For a quasicategory `C`, **the projection `Hom^R_C(y, c) ⟶ Hom^R_C(y, x)` is a trivial
fibration**: it has the right lifting property with respect to every monomorphism. It is a base
change of the map of slices `C_{/p}_{/c} ⟶ C_{/x}`, which is a trivial fibration since the
projection `C_{/p} ⟶ C` is a right fibration (`SSet.slice.rlp_map_of_rightFibration`). -/
theorem rlp_src : (monomorphisms SSet.{u}).rlp (src y c) :=
  MorphismProperty.comp_mem _ _ _ (fun _ _ i hi ↦
    have := rlp_map_of_rightFibration (π p) (yonedaEquiv.symm c)
      (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
    Subcomplex.hasLiftingProperty_lift_of_eq_preimage i _ (postcompSpace_eq_preimage y c)
      (range_ι_comp_map_le y c))
    (MorphismProperty.of_isIso _ _)

/-- For a quasicategory `C`, the map `Hom^R_C(y, c) ⟶ (C_{/p})_y` is a right fibration: it is a
base change of the projection of the slice `C_{/p}_{/c}` of the quasicategory `C_{/p}`. -/
instance rightFibration_tgt : RightFibration (tgt y c) :=
  inferInstanceAs (RightFibration (Subcomplex.fromPreimage _ _))

/-- For a quasicategory `C`, the map `Hom^R_C(y, c) ⟶ (C_{/p})_y` is a Kan fibration, as a right
fibration over a Kan complex. -/
instance fibration_tgt : Fibration (tgt y c) :=
  RightFibration.fibration_of_kanComplex _

end postcompSpace

/-! ### Postcomposition with a cone -/

variable [Quasicategory C]

/-- For a quasicategory `C`, **postcomposition with a cone `c`** over `p` with cone point `x`, a map
from `Hom^R_C(y, x)` to the fibre over `y` of `C_{/p} ⟶ C`: a chosen section of the trivial
fibration `SSet.slice.postcompSpace.src`, followed by `SSet.slice.postcompSpace.tgt`. It sends an
edge `f : y ⟶ x` to a cone with a morphism of cones to `c` over `f`
(`SSet.slice.exists_edge_postcomp`), and any other choice of section gives a homotopic map
(`SSet.slice.exists_homotopy_postcomp`). -/
noncomputable def postcomp :
    (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  section_ (postcompSpace.src y c) ≫ postcompSpace.tgt y c

/-- **Postcomposition with `c` sends an edge `f : y ⟶ x` to a cone `d` with cone point `y`,
together with a morphism of cones from `d` to `c` lying over `f`.** -/
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
    -- The inclusion of `postcompSpace y c` sends `v` to `v.val`.
    rfl
  rw [hd]
  have hf : f.edge = (π p).app _ (yonedaEquiv ((join.joinVertexIso ⦋0⦌).inv ≫
      (slice.objEquiv v.val).val) : (slice p).obj (op (joinVertex.obj ⦋0⦌))) := by
    rw [← rightMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, postcompSpace.src_app_coe]
    -- `yonedaEquiv (g ≫ π p)` is `(π p).app _ (yonedaEquiv g)` (`SSet.yonedaEquiv_comp`).
    rfl
  -- `v` is a vertex of the fibre of `C_{/p}_{/c} ⟶ C_{/p}` over `d`, an edge from `d` to `c`.
  let w : (fiber (π (yonedaEquiv.symm c)) d : SSet.{u}) _⦋0⦌ :=
    fiber.basePoint (π (yonedaEquiv.symm c)) (x := v.val) rfl
  refine ⟨rightMappingSpace.obj₀Equiv ((rightMappingSpace.sliceFiberIso d c).hom.app _ w), ?_⟩
  rw [Edge.map_edge, rightMappingSpace.obj₀Equiv_apply_edge,
    rightMappingSpace.sliceFiberIso_hom_app_coe, hf, fiber.coe_basePoint]
  -- The two sides differ only in the types `(slice p) _⦋1⦌` and `(slice p).obj (op ⦋0 + 1⦌)`.
  rfl

/-- **Postcomposition with a cone is well-defined up to homotopy**: for every section `s` of the
trivial fibration `SSet.slice.postcompSpace.src`, the map `s ≫ tgt` is homotopic to
`SSet.slice.postcomp y c`. -/
theorem exists_homotopy_postcomp
    (s : (C.rightMappingSpace y ((π p).app _ c) : SSet.{u}) ⟶ (postcompSpace y c : SSet.{u}))
    (hs : s ≫ postcompSpace.src y c = 𝟙 _) :
    Nonempty (Homotopy (s ≫ postcompSpace.tgt y c) (postcomp y c)) := by
  have := isSplitEpi_of_rlp_monomorphisms (postcompSpace.rlp_src y c)
  obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms (postcompSpace.rlp_src y c) s
    (section_ (postcompSpace.src y c)) (by rw [hs, IsSplitEpi.id])
  exact ⟨H.postcomp _⟩

/-- `SSet.slice.postcomp y c` is a weak homotopy equivalence exactly when the projection
`Hom^R_C(y, c) ⟶ (C_{/p})_y` is a trivial fibration, since the section of `src` it is built from is
a weak homotopy equivalence. -/
private lemma isWeakHomotopyEquivalence_postcomp_iff :
    IsWeakHomotopyEquivalence (postcomp y c) ↔
      (monomorphisms SSet.{u}).rlp (postcompSpace.tgt y c) := by
  have h := postcompSpace.rlp_src y c
  have := isSplitEpi_of_rlp_monomorphisms h
  have : Fibration (postcompSpace.src y c) := (rlp_monomorphisms_iff.1 h).1
  have := (rlp_monomorphisms_iff_isWeakHomotopyEquivalence (postcompSpace.src y c)).1 h
  have : IsWeakHomotopyEquivalence (section_ (postcompSpace.src y c) ≫ postcompSpace.src y c) := by
    rw [IsSplitEpi.id]
    infer_instance
  have := IsWeakHomotopyEquivalence.of_postcomp (section_ (postcompSpace.src y c))
    (postcompSpace.src y c)
  rw [rlp_monomorphisms_iff_isWeakHomotopyEquivalence]
  refine ⟨fun h' ↦ ?_, fun _ ↦ ?_⟩
  · -- `postcomp y c` is by definition the composite of the section with `tgt`.
    have : IsWeakHomotopyEquivalence
        (section_ (postcompSpace.src y c) ≫ postcompSpace.tgt y c) := h'
    exact IsWeakHomotopyEquivalence.of_precomp (section_ (postcompSpace.src y c)) _
  · exact inferInstanceAs
      (IsWeakHomotopyEquivalence (section_ (postcompSpace.src y c) ≫ postcompSpace.tgt y c))

variable {y c}

omit [Quasicategory C] in
/-- The fibre of `Hom^R_C(y, c) ⟶ (C_{/p})_y` over a cone `d` is the fibre of
`C_{/p}_{/c} ⟶ C_{/p}` over `d`, the right mapping space from `d` to `c` in `C_{/p}`. -/
private lemma isWeaklyContractible_fiber_tgt_iff (d : (fiber (π p) y : SSet.{u}) _⦋0⦌) :
    IsWeaklyContractible (fiber (postcompSpace.tgt y c) d : SSet.{u}) ↔
      IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
  -- `postcompSpace.tgt y c` is the restriction of `C_{/p}_{/c} ⟶ C_{/p}` over `(C_{/p})_y`.
  change IsWeaklyContractible
      (fiber ((fiber (π p) y).fromPreimage (π (yonedaEquiv.symm c))) d : SSet.{u}) ↔ _
  exact ⟨fun _ ↦ .of_iso (fiber.fromPreimageIso _ (fiber (π p) y) d),
    fun _ ↦ .of_iso (fiber.fromPreimageIso _ (fiber (π p) y) d).symm⟩

variable (c) in
/-- **The mapping-space criterion for limits** (HTT Lemma 4.2.4.3). For a quasicategory `C`, a cone
`c` over a diagram `p : K ⟶ C` is a limit cone exactly when, for every vertex `y` of `C`,
postcomposition with `c` is a weak homotopy equivalence from the right mapping space
`Hom^R_C(y, x)` into the cone point `x` of `c` to the fibre over `y` of the projection
`C_{/p} ⟶ C`. -/
theorem isLimit_iff_forall_isWeakHomotopyEquivalence_postcomp :
    IsLimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (postcomp y c) := by
  simp only [isWeakHomotopyEquivalence_postcomp_iff,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber,
    isWeaklyContractible_fiber_tgt_iff]
  rw [isLimit_iff, isTerminalVertex_iff_rlp_monomorphisms_π,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint (π p) (x := d) rfl)⟩

end slice

namespace coslice

/-! ### Composites with a cocone -/

variable (c : (coslice p) _⦋0⦌) (y : C _⦋0⦌)

/-- The simplicial set `Hom^L_C(c, y)` of composites with a cocone `c`: the simplices of the coslice
`C_{p/}_{c/}`, the morphisms of cocones with source `c`, whose target lies in the fibre over `y` of
`C_{p/} ⟶ C`. It is the preimage of the left mapping space `Hom^L_C(x, y) ⊆ C_{x/}`, for `x` the
cocone point of `c`, under the projection `C_{p/}_{c/} ⟶ C_{x/}`
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

/-- `Hom^L_C(c, y)` is the preimage of the left mapping space `Hom^L_C(x, y)`, the fibre over `y`
of `C_{x/} ⟶ C`, under the projection `C_{p/}_{c/} ⟶ C_{x/}`. -/
theorem precompSpace_eq_preimage :
    precompSpace c y = (fiber (π (yonedaEquiv.symm ((π p).app _ c))) y).preimage
      (map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) := by
  ext n s
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (map_π (𝟙 Δ[0]) (π p)
    (by rw [Category.id_comp, yonedaEquiv_symm_comp])) n) s
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  rw [mem_precompSpace_iff, Subcomplex.preimage_obj, Set.mem_preimage, mem_fiber_iff, h]

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

/-- `Hom^L_C(c, y)` lands, under the projection `C_{p/}_{c/} ⟶ C_{x/}`, in the left mapping space
`Hom^L_C(x, y)`, the fibre over `y` of `C_{x/} ⟶ C`. -/
private lemma range_ι_comp_map_le :
    Subcomplex.range ((precompSpace c y).ι ≫
      map (𝟙 Δ[0]) (π p) (by rw [Category.id_comp, yonedaEquiv_symm_comp])) ≤
        fiber (π (yonedaEquiv.symm ((π p).app _ c))) y := by
  rw [range_le_fiber_iff, Category.assoc, map_π, ← tgt_ι_assoc, fiber.ι_comp, comp_const]

/-- The map `Hom^L_C(c, y) ⟶ Hom^L_C(x, y)` projecting a morphism of cocones with source `c` to
`C`, for `x` the cocone point of `c`. -/
noncomputable def src :
    (precompSpace c y : SSet.{u}) ⟶ (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) :=
  Subcomplex.lift _ (range_ι_comp_map_le c y) ≫ (leftMappingSpace.cosliceFiberIso _ y).hom

/-- The underlying simplex of the image under `src` of a morphism of cocones
`Δ[0] ⋆ Δ[n] ⟶ C_{p/}` is its composite with the projection `C_{p/} ⟶ C`, through
`Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
theorem src_app_coe {n : ℕ} (s : (precompSpace c y : SSet.{u}) _⦋n⦌) :
    ((src c y).app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val ≫ π p) : C _⦋n + 1⦌) := by
  have h := leftMappingSpace.cosliceFiberIso_hom_app_coe ((π p).app _ c) y
    ((Subcomplex.lift _ (range_ι_comp_map_le c y)).app _ s)
  refine h.trans ?_
  rw [Subcomplex.lift_app_coe, NatTrans.comp_app, ConcreteCategory.comp_apply,
    objEquiv_map_app_coe, join.map_id, Category.id_comp]
  -- The inclusion of `precompSpace c y` sends `s` to `s.val`.
  rfl

variable [Quasicategory C]

/-- For a quasicategory `C`, **the projection `Hom^L_C(c, y) ⟶ Hom^L_C(x, y)` is a trivial
fibration**: it has the right lifting property with respect to every monomorphism. It is a base
change of the map of coslices `C_{p/}_{c/} ⟶ C_{x/}`, which is a trivial fibration since the
projection `C_{p/} ⟶ C` is a left fibration (`SSet.coslice.rlp_map_of_leftFibration`). -/
theorem rlp_src : (monomorphisms SSet.{u}).rlp (src c y) :=
  MorphismProperty.comp_mem _ _ _ (fun _ _ i hi ↦
    have := rlp_map_of_leftFibration (π p) (yonedaEquiv.symm c)
      (by rw [Category.id_comp, yonedaEquiv_symm_comp]) i hi
    Subcomplex.hasLiftingProperty_lift_of_eq_preimage i _ (precompSpace_eq_preimage c y)
      (range_ι_comp_map_le c y))
    (MorphismProperty.of_isIso _ _)

/-- For a quasicategory `C`, the map `Hom^L_C(c, y) ⟶ (C_{p/})_y` is a left fibration: it is a
base change of the projection of the coslice `C_{p/}_{c/}` of the quasicategory `C_{p/}`. -/
instance leftFibration_tgt : LeftFibration (tgt c y) :=
  inferInstanceAs (LeftFibration (Subcomplex.fromPreimage _ _))

/-- For a quasicategory `C`, the map `Hom^L_C(c, y) ⟶ (C_{p/})_y` is a Kan fibration, as a left
fibration over a Kan complex. -/
instance fibration_tgt : Fibration (tgt c y) :=
  LeftFibration.fibration_of_kanComplex _

end precompSpace

/-! ### Precomposition with a cocone -/

variable [Quasicategory C]

/-- For a quasicategory `C`, **precomposition with a cocone `c`** under `p` with cocone point `x`,
a map from `Hom^L_C(x, y)` to the fibre over `y` of `C_{p/} ⟶ C`: a chosen section of the trivial
fibration `SSet.coslice.precompSpace.src`, followed by `SSet.coslice.precompSpace.tgt`. It sends an
edge `f : x ⟶ y` to a cocone with a morphism of cocones from `c` over `f`
(`SSet.coslice.exists_edge_precomp`), and any other choice of section gives a homotopic map
(`SSet.coslice.exists_homotopy_precomp`). -/
noncomputable def precomp :
    (C.leftMappingSpace ((π p).app _ c) y : SSet.{u}) ⟶ (fiber (π p) y : SSet.{u}) :=
  haveI := isSplitEpi_of_rlp_monomorphisms (precompSpace.rlp_src c y)
  section_ (precompSpace.src c y) ≫ precompSpace.tgt c y

/-- **Precomposition with `c` sends an edge `f : x ⟶ y` to a cocone `d` with cocone point `y`,
together with a morphism of cocones from `c` to `d` lying over `f`.** -/
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
    -- The inclusion of `precompSpace c y` sends `v` to `v.val`.
    rfl
  rw [hd]
  have hf : f.edge = (π p).app _ (yonedaEquiv ((join.coneIso 0).inv ≫
      (coslice.objEquiv v.val).val) : (coslice p) _⦋0 + 1⦌) := by
    rw [← leftMappingSpace.obj₀Equiv_symm_apply_coe, ← hv, precompSpace.src_app_coe]
    -- `yonedaEquiv (g ≫ π p)` is `(π p).app _ (yonedaEquiv g)` (`SSet.yonedaEquiv_comp`).
    rfl
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
  obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms (precompSpace.rlp_src c y) s
    (section_ (precompSpace.src c y)) (by rw [hs, IsSplitEpi.id])
  exact ⟨H.postcomp _⟩

/-- `SSet.coslice.precomp c y` is a weak homotopy equivalence exactly when the projection
`Hom^L_C(c, y) ⟶ (C_{p/})_y` is a trivial fibration, since the section of `src` it is built from
is a weak homotopy equivalence. -/
private lemma isWeakHomotopyEquivalence_precomp_iff :
    IsWeakHomotopyEquivalence (precomp c y) ↔
      (monomorphisms SSet.{u}).rlp (precompSpace.tgt c y) := by
  have h := precompSpace.rlp_src c y
  have := isSplitEpi_of_rlp_monomorphisms h
  have : Fibration (precompSpace.src c y) := (rlp_monomorphisms_iff.1 h).1
  have := (rlp_monomorphisms_iff_isWeakHomotopyEquivalence (precompSpace.src c y)).1 h
  have : IsWeakHomotopyEquivalence (section_ (precompSpace.src c y) ≫ precompSpace.src c y) := by
    rw [IsSplitEpi.id]
    infer_instance
  have := IsWeakHomotopyEquivalence.of_postcomp (section_ (precompSpace.src c y))
    (precompSpace.src c y)
  rw [rlp_monomorphisms_iff_isWeakHomotopyEquivalence]
  refine ⟨fun h' ↦ ?_, fun _ ↦ ?_⟩
  · -- `precomp c y` is by definition the composite of the section with `tgt`.
    have : IsWeakHomotopyEquivalence
        (section_ (precompSpace.src c y) ≫ precompSpace.tgt c y) := h'
    exact IsWeakHomotopyEquivalence.of_precomp (section_ (precompSpace.src c y)) _
  · exact inferInstanceAs
      (IsWeakHomotopyEquivalence (section_ (precompSpace.src c y) ≫ precompSpace.tgt c y))

variable {c y}

omit [Quasicategory C] in
/-- The fibre of `Hom^L_C(c, y) ⟶ (C_{p/})_y` over a cocone `d` is the fibre of
`C_{p/}_{c/} ⟶ C_{p/}` over `d`, the left mapping space from `c` to `d` in `C_{p/}`. -/
private lemma isWeaklyContractible_fiber_tgt_iff (d : (fiber (π p) y : SSet.{u}) _⦋0⦌) :
    IsWeaklyContractible (fiber (precompSpace.tgt c y) d : SSet.{u}) ↔
      IsWeaklyContractible (fiber (π (yonedaEquiv.symm c)) d.val : SSet.{u}) := by
  -- `precompSpace.tgt c y` is the restriction of `C_{p/}_{c/} ⟶ C_{p/}` over `(C_{p/})_y`.
  change IsWeaklyContractible
      (fiber ((fiber (π p) y).fromPreimage (π (yonedaEquiv.symm c))) d : SSet.{u}) ↔ _
  exact ⟨fun _ ↦ .of_iso (fiber.fromPreimageIso _ (fiber (π p) y) d),
    fun _ ↦ .of_iso (fiber.fromPreimageIso _ (fiber (π p) y) d).symm⟩

variable (c) in
/-- **The mapping-space criterion for colimits**, dually to HTT Lemma 4.2.4.3. For a quasicategory
`C`, a cocone `c` under a diagram `p : K ⟶ C` is a colimit cocone exactly when, for every vertex
`y` of `C`, precomposition with `c` is a weak homotopy equivalence from the left mapping space
`Hom^L_C(x, y)` out of the cocone point `x` of `c` to the fibre over `y` of the projection
`C_{p/} ⟶ C`. -/
theorem isColimit_iff_forall_isWeakHomotopyEquivalence_precomp :
    IsColimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (precomp c y) := by
  simp only [isWeakHomotopyEquivalence_precomp_iff,
    LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber,
    isWeaklyContractible_fiber_tgt_iff]
  rw [isColimit_iff, isInitialVertex_iff_rlp_monomorphisms_π,
    LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint (π p) (x := d) rfl)⟩

end coslice

end SSet
