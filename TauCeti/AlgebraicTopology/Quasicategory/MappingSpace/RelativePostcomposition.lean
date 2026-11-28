/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Postcomposition
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex

/-!
# Relative postcomposition and the fibres of the relative slice map

For a simplicial map `p : X ⟶ S` and an edge `g : y ⟶ z` of `X`, a composition triangle
with apex `x` determines its long edge and its image triangle in `S`. These form a point of
the pullback of `Hom^R_X(x,z) ⟶ Hom^R_S(p x,p z)` and the target restriction
`Hom^R_S(p x,p g) ⟶ Hom^R_S(p x,p z)`.

This file identifies this comparison with the fibre over `x` of the relative slice map
restricting cones along the target vertex of `g`. The target restriction on the base is a
Kan fibration when `S` is a quasicategory. Consequently the displayed pullback is a Kan
model for the target fibre when `X` is also a quasicategory. This is the concrete fibre
model used in the mapping-space characterization of Cartesian edges.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 2.1.2.1 and §2.4.4.
-/

public section

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra

universe u

namespace SSet.rightMappingSpace.postcompSpace

open SSet.modelCategoryQuillen

variable {X S : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : Edge y z)

/-- Target restriction on composition spaces in a quasicategory is a Kan fibration. -/
instance fibration_tgt [Quasicategory X] : Fibration (tgt x g) :=
  RightFibration.fibration_of_kanComplex _

/-- The pullback of long edges in `X` and composition triangles in the base, with a common
long edge in the base. -/
noncomputable abbrev relativeTarget (p : X ⟶ S) : SSet.{u} :=
  pullback (rightMappingSpace.map x z p) (tgt (p.app _ x) (g.map p))

/-- The relative comparison sends a cone to its long edge and its image cone in the base. -/
noncomputable def relativeComparison (p : X ⟶ S) :
    (postcompSpace x g : SSet.{u}) ⟶ relativeTarget x g p :=
  pullback.lift (tgt x g) (map x g p) (map_tgt x g p).symm

@[reassoc (attr := simp)]
lemma relativeComparison_fst (p : X ⟶ S) :
    relativeComparison x g p ≫ pullback.fst _ _ = tgt x g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeComparison_snd (p : X ⟶ S) :
    relativeComparison x g p ≫ pullback.snd _ _ = map x g p :=
  pullback.lift_snd _ _ _

/-- The relative target is a Kan complex for a map of quasicategories. -/
instance kanComplex_relativeTarget [Quasicategory X] [Quasicategory S] (p : X ⟶ S) :
    KanComplex (relativeTarget x g p) := by
  have : Fibration (pullback.fst (rightMappingSpace.map x z p)
      (tgt (p.app _ x) (g.map p))) := by
    rw [fibration_iff]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
      ((fibration_iff _).1 inferInstance)
  exact isFibrant_of_fibration (pullback.fst _ _)

/-! ### The target fibre of the relative slice map -/

variable (p : X ⟶ S)

/-- The target of the relative slice map restricting cones along the target vertex of `g`. -/
noncomputable abbrev sliceTarget : SSet.{u} :=
  pullback (slice.map (𝟙 _) p (by simp) :
      slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge) ⟶
        slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p))
    (slice.map (stdSimplex.δ 0) (𝟙 S) (by simp) :
      slice (yonedaEquiv.symm g.edge ≫ p) ⟶
        slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p))

/-- The cone-point projection of the target of the relative slice map. -/
noncomputable abbrev sliceTargetπ : sliceTarget g p ⟶ X :=
  pullback.fst _ _ ≫ slice.π _

-- These two maps express the projections using the actual target vertex and image edge,
-- rather than their equal presentations as composites with face maps.
-- The controlled simplifications below keep slice projections opaque: `slice.comp_π`
-- would instead expand them to the underlying join maps.
private noncomputable def sliceFst : sliceTarget g p ⟶ slice (yonedaEquiv.symm z) :=
  pullback.fst _ _ ≫ slice.map (𝟙 _) (𝟙 X) (by simp)

private noncomputable def sliceSnd :
    sliceTarget g p ⟶ slice (yonedaEquiv.symm (g.map p).edge) :=
  pullback.snd _ _ ≫ slice.map (𝟙 _) (𝟙 S)
    (by rw [Category.id_comp, Category.comp_id, Edge.map_edge, ← yonedaEquiv_symm_comp])

@[reassoc]
private lemma sliceFst_π : sliceFst g p ≫ slice.π _ = sliceTargetπ g p := by
  simp only [sliceFst, Category.assoc, slice.map_π, Category.comp_id, sliceTargetπ]

@[reassoc]
private lemma sliceSnd_π : sliceSnd g p ≫ slice.π _ = sliceTargetπ g p ≫ p := by
  have h := congrArg (fun f ↦ f ≫ slice.π _) (pullback.condition
    (f := (slice.map (𝟙 _) p (by simp) :
      slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge) ⟶
        slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p)))
    (g := (slice.map (stdSimplex.δ 0) (𝟙 S) (by simp) :
      slice (yonedaEquiv.symm g.edge ≫ p) ⟶
        slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p))))
  simpa only [sliceSnd, sliceTargetπ, Category.assoc, slice.map_π, Category.comp_id]
    using h.symm

@[reassoc]
private lemma sliceFst_map :
    sliceFst g p ≫ slice.map (𝟙 _) p (by rw [Category.id_comp, yonedaEquiv_symm_comp]) =
      sliceSnd g p ≫ slice.map (stdSimplex.δ 0) (𝟙 S)
        (by rw [Category.comp_id, Edge.δ_zero_yonedaEquiv_symm]) := by
  have h := congrArg (fun (f : sliceTarget g p ⟶
      slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p)) ↦
    f ≫ slice.map (𝟙 _) (𝟙 S)
      (q := yonedaEquiv.symm (p.app _ z)) (by simp [← Category.assoc]))
    (pullback.condition
      (f := (slice.map (𝟙 _) p (by simp) :
        slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge) ⟶
          slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p)))
      (g := (slice.map (stdSimplex.δ 0) (𝟙 S) (by simp) :
        slice (yonedaEquiv.symm g.edge ≫ p) ⟶
          slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p))))
  simpa only [sliceFst, sliceSnd, Category.assoc, slice.map_comp, Category.comp_id,
    Category.id_comp] using h

private noncomputable def fiberFst :
    (fiber (sliceTargetπ g p) x : SSet.{u}) ⟶ (X.rightMappingSpace x z : SSet.{u}) :=
  fiber.lift ((fiber (sliceTargetπ g p) x).ι ≫ sliceFst g p) _ x
      (by simp only [Category.assoc, sliceFst_π, fiber.ι_comp]) ≫
    (sliceFiberIso x z).hom

private noncomputable def fiberSnd :
    (fiber (sliceTargetπ g p) x : SSet.{u}) ⟶
      (postcompSpace (p.app _ x) (g.map p) : SSet.{u}) :=
  Subcomplex.lift ((fiber (sliceTargetπ g p) x).ι ≫ sliceSnd g p) (by
    rw [postcompSpace_eq_fiber, range_le_fiber_iff]
    rw [Category.assoc, sliceSnd_π, ← Category.assoc, fiber.ι_comp, const_comp])

@[reassoc (attr := simp)]
private lemma fiberFst_toSlice :
    fiberFst x g p ≫ (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι =
      (fiber (sliceTargetπ g p) x).ι ≫ sliceFst g p := by
  simp [fiberFst]

@[reassoc (attr := simp)]
private lemma fiberSnd_ι :
    fiberSnd x g p ≫ (postcompSpace (p.app _ x) (g.map p)).ι =
      (fiber (sliceTargetπ g p) x).ι ≫ sliceSnd g p :=
  Subcomplex.lift_ι _ _

private lemma fiberFst_map :
    fiberFst x g p ≫ rightMappingSpace.map x z p =
      fiberSnd x g p ≫ tgt (p.app _ x) (g.map p) := by
  rw [← cancel_mono ((sliceFiberIso (p.app _ x) (p.app _ z)).inv ≫
    (fiber (slice.π _) (p.app _ x)).ι)]
  simp only [Category.assoc, ← sliceFiberIso_inv_comp_map, fiberFst_toSlice_assoc,
    tgt_comp_sliceFiberIso_inv_ι, fiberSnd_ι_assoc, sliceFst_map]

private noncomputable def coneLift {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    Z ⟶ sliceTarget g p := by
  have hc : a ≫ (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι ≫
        slice.map (𝟙 _) p (by rw [Category.id_comp, yonedaEquiv_symm_comp]) =
      b ≫ (postcompSpace (p.app _ x) (g.map p)).ι ≫
        slice.map (stdSimplex.δ 0) (𝟙 S)
          (by rw [Category.comp_id, Edge.δ_zero_yonedaEquiv_symm]) := by
    simpa only [Category.assoc, ← sliceFiberIso_inv_comp_map,
      tgt_comp_sliceFiberIso_inv_ι] using
      congrArg (fun (f : Z ⟶ (S.rightMappingSpace (p.app _ x) (p.app _ z) : SSet.{u})) ↦
        f ≫ (sliceFiberIso (p.app _ x) (p.app _ z)).inv ≫ (fiber (slice.π _) (p.app _ x)).ι) h
  refine pullback.lift
    (a ≫ (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι ≫
      slice.map (𝟙 _) (𝟙 X) (by simp))
    (b ≫ (postcompSpace (p.app _ x) (g.map p)).ι ≫
      slice.map (𝟙 _) (𝟙 S)
        (by rw [Category.id_comp, Category.comp_id, Edge.map_edge, ← yonedaEquiv_symm_comp])) ?_
  have hc' := congrArg (fun (f : Z ⟶ slice (yonedaEquiv.symm (p.app _ z))) ↦
    f ≫ slice.map (𝟙 _) (𝟙 S)
      (q := stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge ≫ p) (by simp [← Category.assoc])) hc
  simpa only [Category.assoc, slice.map_comp, Category.id_comp, Category.comp_id] using hc'

@[reassoc (attr := simp)]
private lemma coneLift_fst {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    coneLift x g p a b h ≫ sliceFst g p =
      a ≫ (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι := by
  simp only [coneLift, sliceFst, pullback.lift_fst_assoc, Category.assoc,
    slice.map_comp, Category.comp_id, slice.map_id]

@[reassoc (attr := simp)]
private lemma coneLift_snd {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    coneLift x g p a b h ≫ sliceSnd g p =
      b ≫ (postcompSpace (p.app _ x) (g.map p)).ι := by
  simp only [coneLift, sliceSnd, pullback.lift_snd_assoc, Category.assoc,
    slice.map_comp, Category.comp_id, slice.map_id]

private noncomputable def fiberLift {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    Z ⟶ (fiber (sliceTargetπ g p) x : SSet.{u}) :=
  fiber.lift (coneLift x g p a b h) _ x (by
    rw [← sliceFst_π, coneLift_fst_assoc, fiber.ι_comp, comp_const, comp_const])

@[reassoc (attr := simp)]
private lemma fiberLift_fst {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    fiberLift x g p a b h ≫ fiberFst x g p = a := by
  rw [← cancel_mono ((sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι)]
  simp only [Category.assoc, fiberFst_toSlice, fiberLift, fiber.lift_ι_assoc,
    coneLift_fst]

@[reassoc (attr := simp)]
private lemma fiberLift_snd {Z : SSet.{u}}
    (a : Z ⟶ (X.rightMappingSpace x z : SSet.{u}))
    (b : Z ⟶ (postcompSpace (p.app _ x) (g.map p) : SSet.{u}))
    (h : a ≫ rightMappingSpace.map x z p = b ≫ tgt (p.app _ x) (g.map p)) :
    fiberLift x g p a b h ≫ fiberSnd x g p = b := by
  rw [← cancel_mono (postcompSpace (p.app _ x) (g.map p)).ι]
  simp only [Category.assoc, fiberSnd_ι, fiberLift, fiber.lift_ι_assoc, coneLift_snd]

private lemma fiber_hom_ext {Z : SSet.{u}}
    {a b : Z ⟶ (fiber (sliceTargetπ g p) x : SSet.{u})}
    (h₁ : a ≫ fiberFst x g p = b ≫ fiberFst x g p)
    (h₂ : a ≫ fiberSnd x g p = b ≫ fiberSnd x g p) : a = b := by
  rw [← cancel_mono (fiber (sliceTargetπ g p) x).ι]
  apply pullback.hom_ext
  · rw [← cancel_mono (slice.map (𝟙 _) (𝟙 X) (by simp) :
      slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm g.edge) ⟶ slice (yonedaEquiv.symm z))]
    simpa only [Category.assoc, fiberFst_toSlice, sliceFst] using
      congrArg (fun f ↦ f ≫ (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι) h₁
  · rw [← cancel_mono (slice.map (𝟙 _) (𝟙 S)
      (by rw [Category.id_comp, Category.comp_id, Edge.map_edge, ← yonedaEquiv_symm_comp]) :
        slice (yonedaEquiv.symm g.edge ≫ p) ⟶ slice (yonedaEquiv.symm (g.map p).edge))]
    simpa only [Category.assoc, fiberSnd_ι, sliceSnd] using
      congrArg (fun f ↦ f ≫ (postcompSpace (p.app _ x) (g.map p)).ι) h₂

private lemma isPullback_fiber :
    IsPullback (fiberFst x g p) (fiberSnd x g p)
      (rightMappingSpace.map x z p) (tgt (p.app _ x) (g.map p)) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (fiberFst_map x g p)
    (fun s ↦ fiberLift x g p s.fst s.snd s.condition)
    (fun s ↦ fiberLift_fst x g p s.fst s.snd s.condition)
    (fun s ↦ fiberLift_snd x g p s.fst s.snd s.condition)
    (fun _ _ h₁ h₂ ↦ fiber_hom_ext x g p
      (by rw [fiberLift_fst]; exact h₁) (by rw [fiberLift_snd]; exact h₂)))

/-- The fibre at `x` of the target of the relative slice map is the pullback of right
mapping spaces and composition triangles in the base. The projection to `X` is
`pullback.fst ≫ slice.π`. No fibrancy assumption is needed for this identification. -/
noncomputable def sliceTargetFiberIso :
    (fiber (sliceTargetπ g p) x : SSet.{u}) ≅ relativeTarget x g p :=
  (isPullback_fiber x g p).isoPullback

/-- The first projection of the target fibre is the long edge, viewed in the slice over `z`. -/
@[reassoc (attr := simp)]
lemma sliceTargetFiberIso_hom_fst_toSlice :
    (sliceTargetFiberIso x g p).hom ≫ pullback.fst _ _ ≫
        (sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι =
      (fiber (sliceTargetπ g p) x).ι ≫ pullback.fst _ _ ≫
        slice.map (𝟙 _) (𝟙 X) (by simp) := by
  simp only [sliceTargetFiberIso, IsPullback.isoPullback_hom_fst_assoc,
    fiberFst_toSlice, sliceFst]

/-- The second projection of the target fibre is its cone in the base. -/
@[reassoc (attr := simp)]
lemma sliceTargetFiberIso_hom_snd_ι :
    (sliceTargetFiberIso x g p).hom ≫ pullback.snd _ _ ≫
        (postcompSpace (p.app _ x) (g.map p)).ι =
      (fiber (sliceTargetπ g p) x).ι ≫ pullback.snd _ _ ≫
        slice.map (𝟙 _) (𝟙 S)
          (by rw [Category.id_comp, Category.comp_id, Edge.map_edge, ← yonedaEquiv_symm_comp]) := by
  simp only [sliceTargetFiberIso, IsPullback.isoPullback_hom_snd_assoc,
    fiberSnd_ι, sliceSnd]

/-- The relative slice map preserves its cone point in `X`. -/
@[reassoc]
lemma restrictionMap_sliceTargetπ :
    slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm g.edge) ≫ sliceTargetπ g p =
      slice.π (yonedaEquiv.symm g.edge) := by
  simp only [sliceTargetπ, slice.restrictionMap_fst_assoc, slice.map_π, Category.comp_id]

/-- Under the source identification `postcompSpace_eq_fiber` and the target identification
`sliceTargetFiberIso`, the map on fibres of the relative slice map is the relative comparison.
Its projections take the long edge and apply `p` to the composition triangle. -/
theorem fiber_map_restrictionMap :
    (Subcomplex.eqToIso (postcompSpace_eq_fiber x g)).hom ≫
        fiber.map (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm g.edge))
          (restrictionMap_sliceTargetπ g p) x ≫ (sliceTargetFiberIso x g p).hom =
      relativeComparison x g p := by
  apply pullback.hom_ext
  · rw [← cancel_mono ((sliceFiberIso x z).inv ≫ (fiber (slice.π _) x).ι)]
    simp only [Category.assoc, sliceTargetFiberIso_hom_fst_toSlice,
      relativeComparison_fst_assoc, tgt_comp_sliceFiberIso_inv_ι,
      fiber.map_ι_assoc, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc,
      slice.restrictionMap_fst_assoc, slice.map_comp, Category.id_comp, Category.comp_id]
  · rw [← cancel_mono (postcompSpace (p.app _ x) (g.map p)).ι]
    simp only [Category.assoc, sliceTargetFiberIso_hom_snd_ι, relativeComparison_snd_assoc,
      map_ι, fiber.map_ι_assoc, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc,
      slice.restrictionMap_snd_assoc, slice.map_comp, Category.comp_id]

/-! ### Vertices and the terminal base -/

/-- The first projection of the comparison sends a composition triangle to its long edge. -/
lemma relativeComparison_fst_obj₀
    (c : Σ (f : Edge x y) (h : Edge x z), Edge.CompStruct f g h) :
    rightMappingSpace.obj₀Equiv
      ((relativeComparison x g p ≫ pullback.fst _ _).app _ ((obj₀Equiv x g).symm c)) =
        c.2.1 := by
  rw [relativeComparison_fst, obj₀Equiv_tgt_app, Equiv.apply_symm_apply]

/-- The second projection of the comparison sends a composition triangle to its image under
`p`, including both its first and its long edge. -/
lemma relativeComparison_snd_obj₀
    (c : Σ (f : Edge x y) (h : Edge x z), Edge.CompStruct f g h) :
    obj₀Equiv (p.app _ x) (g.map p)
      ((relativeComparison x g p ≫ pullback.snd _ _).app _ ((obj₀Equiv x g).symm c)) =
        ⟨c.1.map p, c.2.1.map p, c.2.2.map p⟩ := by
  rw [relativeComparison_snd, obj₀Equiv_map, Equiv.apply_symm_apply]

/-- Over a terminal base, the target of the relative comparison is the right mapping space
to the target of `g`. This applies in particular to the base `Δ[0]`. -/
noncomputable def relativeTargetIsoOfIsTerminal (hS : IsTerminal S) :
    relativeTarget x g p ≅ (X.rightMappingSpace x z : SSet.{u}) := by
  have hπ (σ : Δ[0] ⟶ S) : IsIso (slice.π σ) :=
    isIso_of_isTerminal (slice.isTerminal _ hS) hS _
  have hR := (fiber.isTerminalOfIsIso (slice.π (yonedaEquiv.symm (p.app _ z)))
    (p.app _ x)).ofIso (sliceFiberIso (p.app _ x) (p.app _ z))
  have : IsIso (slice.π (yonedaEquiv.symm (g.map p).edge)) :=
    isIso_of_isTerminal (slice.isTerminal _ hS) hS _
  have hP := (fiber.isTerminalOfIsIso (slice.π (yonedaEquiv.symm (g.map p).edge))
    (p.app _ x)).ofIso
      (Subcomplex.eqToIso (postcompSpace_eq_fiber (p.app _ x) (g.map p))).symm
  have : IsIso (tgt (p.app _ x) (g.map p)) := isIso_of_isTerminal hP hR _
  exact asIso (pullback.fst _ _)

@[simp]
lemma relativeTargetIsoOfIsTerminal_hom (hS : IsTerminal S) :
    (relativeTargetIsoOfIsTerminal x g p hS).hom = pullback.fst _ _ :=
  (rfl)

/-- Over a terminal base, the relative comparison is target restriction on composition spaces. -/
@[reassoc]
lemma relativeComparison_comp_relativeTargetIsoOfIsTerminal_hom (hS : IsTerminal S) :
    relativeComparison x g p ≫ (relativeTargetIsoOfIsTerminal x g p hS).hom = tgt x g := by
  rw [relativeTargetIsoOfIsTerminal_hom, relativeComparison_fst]

example (p₀ : X ⟶ Δ[0]) :
    relativeComparison x g p₀ ≫
        (relativeTargetIsoOfIsTerminal x g p₀ stdSimplex.isTerminalObj₀).hom = tgt x g := by
  exact relativeComparison_comp_relativeTargetIsoOfIsTerminal_hom x g p₀
    stdSimplex.isTerminalObj₀

end SSet.rightMappingSpace.postcompSpace
