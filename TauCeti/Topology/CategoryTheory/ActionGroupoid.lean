/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.ActionCategory
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# The topology of an action groupoid

For a continuous action of a topological group `G` on `X`, equip the objects and total arrows of
Mathlib's native `CategoryTheory.ActionCategory G X` with the topologies transported from `X`
and `G × X`. The arrow coordinates record the label and source, including labels acting
trivially. Source, target, unit, inversion and composition are continuous with these topologies.

The source-target map is proper precisely when the action is proper. For a discrete group,
each fixed-label slice is an open bisection: source and target are local homeomorphisms. Thus
these topologies give the topological action presentations used for finite quotient charts,
without imposing faithfulness or discarding ineffective isotropy. The basic topology, units,
composition and source charts are also available for monoid actions.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.

The algebraic identifications are `CategoryTheory.ActionCategory.objEquiv` and
`CategoryTheory.ActionCategory.totalEquiv`; properness uses Mathlib's `ProperSMul`.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory

namespace TauCeti.ActionGroupoid

variable (G X : Type*)

section Monoid

variable [Monoid G] [MulAction G X] [TopologicalSpace X]

/-- The object topology of the native action category, transported from `X`. -/
instance instTopologicalSpaceObjects : TopologicalSpace (ActionCategory G X) :=
  TopologicalSpace.induced (objEquiv G X).symm inferInstance

/-- Objects of the native action category are homeomorphic to the acted-on space. -/
def objectHomeomorph : ActionCategory G X ≃ₜ X :=
  (objEquiv G X).symm.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The object homeomorphism reads the point underlying a native action-category object. -/
@[simp]
theorem objectHomeomorph_apply (x : ActionCategory G X) :
    objectHomeomorph G X x = x.back := (rfl)

/-- The inverse object homeomorphism is the native object equivalence. -/
@[simp]
theorem objectHomeomorph_symm_apply (x : X) :
    (objectHomeomorph G X).symm x = objEquiv G X x := (rfl)

variable [TopologicalSpace G]

/-- The total-arrow topology of the native action category, transported from label-source pairs. -/
instance instTopologicalSpaceArrows : TopologicalSpace (Quiver.Total (ActionCategory G X)) :=
  TopologicalSpace.induced (totalEquiv G X) inferInstance

/-- Total arrows of the native action category are homeomorphic to label-source pairs. -/
def arrowHomeomorph : Quiver.Total (ActionCategory G X) ≃ₜ G × X :=
  (totalEquiv G X).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The arrow homeomorphism records the label and the point underlying the source. -/
@[simp]
theorem arrowHomeomorph_apply (f : Quiver.Total (ActionCategory G X)) :
    arrowHomeomorph G X f = (f.hom.hom, f.left.back) :=
  totalEquiv_apply f

/-- The inverse arrow homeomorphism uses the native algebraic total-arrow equivalence. -/
@[simp]
theorem arrowHomeomorph_symm_apply (p : G × X) :
    (arrowHomeomorph G X).symm p = (totalEquiv G X).symm p := (rfl)

/-- The source of the action groupoid is continuous. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  apply (objectHomeomorph G X).isInducing.continuous_iff.mpr
  simpa [Function.comp_def] using
    continuous_snd.comp (arrowHomeomorph G X).continuous

/-- The label of a total arrow is continuous. -/
@[fun_prop]
theorem continuous_label :
    Continuous (fun f : Quiver.Total (ActionCategory G X) => f.hom.hom) := by
  simpa [Function.comp_def] using
    continuous_fst.comp (arrowHomeomorph G X).continuous

/-- The unit map of the action groupoid is continuous. -/
@[fun_prop]
theorem continuous_unit :
    Continuous (fun x : ActionCategory G X =>
      (⟨x, x, 𝟙 x⟩ : Quiver.Total (ActionCategory G X))) := by
  apply (arrowHomeomorph G X).isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, arrowHomeomorph_apply, ActionCategory.id_hom,
    objectHomeomorph_apply] using
    (continuous_const (y := (1 : G))).prodMk (objectHomeomorph G X).continuous

variable [ContinuousSMul G X]

/-- The target of the action groupoid is continuous. -/
@[fun_prop]
theorem continuous_target :
    Continuous (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  apply (objectHomeomorph G X).isInducing.continuous_iff.mpr
  convert continuous_smul.comp ((continuous_label G X).prodMk
    ((objectHomeomorph G X).continuous.comp (continuous_source G X))) using 1
  funext f
  exact f.hom.map_val.symm

omit [ContinuousSMul G X] in
/-- Multiplication is continuous on the subspace of composable pairs of total arrows. The
first arrow is followed by the second, so the second label multiplies on the left. -/
@[fun_prop]
theorem continuous_comp [ContinuousMul G] :
    Continuous (fun p : {p : Quiver.Total (ActionCategory G X) ×
        Quiver.Total (ActionCategory G X) // p.1.right = p.2.left} =>
      (⟨p.1.1.left, p.1.2.right,
        p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total (ActionCategory G X))) := by
  have hlabel : ∀ (a b : ActionCategory G X) (h : a = b), (eqToHom h).hom = (1 : G) := by
    rintro a _ rfl
    rfl
  apply (arrowHomeomorph G X).isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, arrowHomeomorph_apply, ActionCategory.comp_hom, hlabel,
    one_mul, mul_one, Pi.mul_apply, objectHomeomorph_apply] using
    (((continuous_label G X).comp (continuous_snd.comp continuous_subtype_val)).mul
      ((continuous_label G X).comp (continuous_fst.comp continuous_subtype_val))).prodMk
        ((objectHomeomorph G X).continuous.comp
          ((continuous_source G X).comp (continuous_fst.comp continuous_subtype_val)))

section Discrete

omit [ContinuousSMul G X]

variable [DiscreteTopology G]

/-- The open source chart of arrows with one fixed label. It keeps distinct labels even when
they induce the same action on objects. -/
def sourceChart (g : G) :
    OpenPartialHomeomorph (Quiver.Total (ActionCategory G X)) (ActionCategory G X) where
  toFun := Quiver.Total.left
  invFun x := (arrowHomeomorph G X).symm (g, x.back)
  source := {f | f.hom.hom = g}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := by simp
  left_inv' f hf := by
    apply (arrowHomeomorph G X).injective
    simp only [Homeomorph.apply_symm_apply, arrowHomeomorph_apply]
    exact Prod.ext hf.symm rfl
  right_inv' x _ := by
    simp only [arrowHomeomorph_symm_apply, totalEquiv_symm_apply_left]
    exact (objEquiv G X).apply_symm_apply x
  open_source := (isOpen_discrete {g}).preimage (continuous_label G X)
  open_target := isOpen_univ
  continuousOn_toFun := (continuous_source G X).continuousOn
  continuousOn_invFun := ((arrowHomeomorph G X).symm.continuous.comp
    (continuous_const.prodMk (objectHomeomorph G X).continuous)).continuousOn

/-- The fixed-label source chart sends an arrow to its source object. -/
@[simp]
theorem sourceChart_apply (g : G) (f : Quiver.Total (ActionCategory G X)) :
    sourceChart G X g f = f.left := (rfl)

/-- The domain of a fixed-label source chart is exactly that label slice. -/
@[simp]
theorem sourceChart_source (g : G) :
    (sourceChart G X g).source = {f | f.hom.hom = g} := (rfl)

/-- Every object occurs as the source of an arrow with the prescribed label. -/
@[simp]
theorem sourceChart_target (g : G) : (sourceChart G X g).target = Set.univ := (rfl)

/-- The inverse source chart constructs the arrow with the prescribed label and source. -/
@[simp]
theorem sourceChart_symm_apply (g : G) (x : ActionCategory G X) :
    (sourceChart G X g).symm x = (arrowHomeomorph G X).symm (g, x.back) := (rfl)

/-- The source of the action category of a discrete monoid is a local homeomorphism. -/
theorem isLocalHomeomorph_source :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total (ActionCategory G X) →
      ActionCategory G X) :=
  IsLocalHomeomorph.mk _ fun f => ⟨sourceChart G X f.hom.hom, rfl, fun _ _ => rfl⟩

end Discrete

end Monoid

section Group

variable [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]

/-- Inversion of arrows is continuous for a continuous action with continuous inversion. -/
@[fun_prop]
theorem continuous_inverse [ContinuousInv G] [ContinuousSMul G X] :
    Continuous (fun f : Quiver.Total (ActionCategory G X) =>
      (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total (ActionCategory G X))) := by
  apply (arrowHomeomorph G X).isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, arrowHomeomorph_apply, inv_hom, Pi.inv_apply,
    objectHomeomorph_apply] using
    (continuous_label G X).inv.prodMk
      ((objectHomeomorph G X).continuous.comp (continuous_target G X))

/-- Properness of the source-target map of the native action groupoid is exactly properness
of the action, with the full group of labels retained. -/
theorem isProperMap_source_target_iff :
    IsProperMap (fun f : Quiver.Total (ActionCategory G X) => (f.left, f.right)) ↔
      ProperSMul G X := by
  let e := (objectHomeomorph G X).prodCongr (objectHomeomorph G X)
  constructor
  · intro h
    constructor
    simpa only [e, Function.comp_def, Homeomorph.coe_prodCongr, Homeomorph.coe_prodComm,
      Prod.map_apply, Prod.swap_prod_mk, arrowHomeomorph_symm_apply,
      totalEquiv_symm_apply_left, totalEquiv_symm_apply_right,
      ← objectHomeomorph_symm_apply, Homeomorph.apply_symm_apply] using
      (Homeomorph.prodComm X X).isProperMap.comp
        (e.isProperMap.comp (h.comp (arrowHomeomorph G X).symm.isProperMap))
  · intro h
    have hp := h.isProperMap_smul_pair.comp (arrowHomeomorph G X).isProperMap
    convert e.symm.isProperMap.comp ((Homeomorph.prodComm X X).isProperMap.comp hp) using 1
    funext f
    simp only [Function.comp_def, arrowHomeomorph_apply]
    apply Prod.ext
    · exact ((objectHomeomorph G X).symm_apply_apply f.left).symm
    · exact ((congrArg (objectHomeomorph G X).symm f.hom.map_val).trans
        ((objectHomeomorph G X).symm_apply_apply f.right)).symm

variable [DiscreteTopology G] [ContinuousConstSMul G X]

/-- The target of the action groupoid of a discrete group is a local homeomorphism. -/
theorem isLocalHomeomorph_target :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total (ActionCategory G X) →
      ActionCategory G X) := by
  apply IsLocalHomeomorph.mk
  intro f
  let h := ((objectHomeomorph G X).trans (Homeomorph.smul (f.hom.hom : G))).trans
    (objectHomeomorph G X).symm
  refine ⟨(sourceChart G X f.hom.hom).trans h.toOpenPartialHomeomorph, ?_, ?_⟩
  · simp
  · intro a ha
    have hl : a.hom.hom = f.hom.hom := ha.1
    apply (objectHomeomorph G X).injective
    simp only [OpenPartialHomeomorph.trans_apply, sourceChart_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, h, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply, objectHomeomorph_apply]
    exact a.hom.map_val.symm.trans (congrArg (· • a.left.back) hl)

end Group

end TauCeti.ActionGroupoid
