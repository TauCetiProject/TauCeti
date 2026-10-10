/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measured metric spaces and support reduction

`MetricMeasureSpace` bundles a complete separable metric space and a Borel reference measure
finite on bounded sets. The reference measure need not be a probability measure, and no
curvature, geodesicity or properness is assumed.

`MetricMeasureSpace.supportSpace` discards points outside the reference measure's support.
Its inclusion is isometric and measure-preserving, and its reference measure has full support.
`MetricMeasureSpace.Equiv` records measure-preserving isometric equivalence of presentations.
These are the common carrier and change-of-presentation data for measured metric geometry.

The conventions follow Sturm, *On the geometry of metric measure spaces. I* (2006), §2,
allowing reference measures finite on bounded sets rather than only probability measures.
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace TauCeti

namespace TauCeti

universe u v w

/-- A complete separable metric space with a Borel reference measure finite on bounded sets.
The carrier may contain points outside the measure's support. -/
structure MetricMeasureSpace where
  /-- The underlying metric carrier. -/
  carrier : Type u
  [metricSpace : MetricSpace carrier]
  [completeSpace : CompleteSpace carrier]
  [separableSpace : SeparableSpace carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  /-- The reference measure, finite on bounded sets and not necessarily normalized. -/
  referenceMeasure : Measure carrier
  /-- Bounded sets have finite reference measure, even when the carrier is not proper. -/
  measure_lt_top_of_isBounded : ∀ ⦃s : Set carrier⦄, Bornology.IsBounded s →
    referenceMeasure s < ⊤

attribute [instance] MetricMeasureSpace.metricSpace MetricMeasureSpace.completeSpace
  MetricMeasureSpace.separableSpace MetricMeasureSpace.measurableSpace MetricMeasureSpace.borelSpace

namespace MetricMeasureSpace

instance : CoeSort MetricMeasureSpace (Type u) := ⟨carrier⟩

/-- Finiteness on bounded sets supplies local finiteness without a properness assumption. -/
instance (X : MetricMeasureSpace) : IsLocallyFiniteMeasure X.referenceMeasure where
  finiteAtNhds x := ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num),
    X.measure_lt_top_of_isBounded Metric.isBounded_ball⟩

/-- The canonical unbundled constructor uses the existing Borel structure on the carrier.
Its body is exposed so the constructed carrier and its instances reduce to those of `X`. -/
@[expose]
def ofMeasure (X : Type u) [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    (hμ : ∀ ⦃s : Set X⦄, Bornology.IsBounded s → μ s < ⊤) : MetricMeasureSpace where
  carrier := X
  referenceMeasure := μ
  measure_lt_top_of_isBounded := hμ

/-- The canonical constructor for finite reference measures, including probability measures. -/
@[expose]
def ofFiniteMeasure (X : Type u) [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    MetricMeasureSpace :=
  ofMeasure X μ (fun {_} _ ↦ measure_lt_top μ _)

@[simp]
theorem referenceMeasure_ofMeasure (X : Type u) [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    (hμ : ∀ ⦃s : Set X⦄, Bornology.IsBounded s → μ s < ⊤) :
    (ofMeasure X μ hμ).referenceMeasure = μ := (rfl)

@[simp]
theorem referenceMeasure_ofFiniteMeasure (X : Type u) [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] : (ofFiniteMeasure X μ).referenceMeasure = μ := (rfl)

/-- The support, with the induced metric and pullback reference measure. Its body is exposed
so elements of the support representative can be used as elements of the support subtype. -/
@[expose]
def supportSpace (X : MetricMeasureSpace) : MetricMeasureSpace where
  carrier := X.referenceMeasure.support
  completeSpace := X.referenceMeasure.isClosed_support.isComplete.completeSpace_coe
  referenceMeasure := X.referenceMeasure.comap ((↑) : X.referenceMeasure.support → X)
  measure_lt_top_of_isBounded {s} hs := by
    rw [comap_subtype_coe_apply X.referenceMeasure.isClosed_support.measurableSet]
    exact X.measure_lt_top_of_isBounded (isometry_subtype_coe.lipschitzWith.isBounded_image hs)

/-- The reduced reference measure is the pullback along the support subtype inclusion. -/
@[simp]
theorem referenceMeasure_supportSpace (X : MetricMeasureSpace) :
    X.supportSpace.referenceMeasure =
      X.referenceMeasure.comap ((↑) : X.referenceMeasure.support → X) := (rfl)

/-- Support reduction preserves all the reference measure, including infinite total mass. -/
theorem measurePreserving_subtype_coe (X : MetricMeasureSpace) :
    MeasurePreserving ((↑) : X.referenceMeasure.support → X)
      X.supportSpace.referenceMeasure X.referenceMeasure :=
  measurePreserving_subtype_coe_of_ae_mem X.referenceMeasure
    X.referenceMeasure.isClosed_support.measurableSet X.referenceMeasure.support_mem_ae

/-- The support representative has positive reference measure on every nonempty open set. -/
instance (X : MetricMeasureSpace) : X.supportSpace.referenceMeasure.IsOpenPosMeasure :=
  isOpenPosMeasure_comap_subtype_support X.referenceMeasure
    X.referenceMeasure.isClosed_support.measurableSet X.referenceMeasure.support_mem_ae

/-- The reduced reference measure has support equal to the entire reduced carrier. -/
-- Rewrite the support before simp expands the reference-measure projection.
@[simp↓]
theorem support_referenceMeasure_supportSpace (X : MetricMeasureSpace) :
    X.supportSpace.referenceMeasure.support = univ :=
  Measure.support_eq_univ

/-- An isomorphism of measured metric spaces is an isometric equivalence preserving the
reference measure. There is no additional choice of normalization or representative. -/
structure Equiv (X : MetricMeasureSpace.{u}) (Y : MetricMeasureSpace.{v}) extends X ≃ᵢ Y where
  measurePreserving' : MeasurePreserving toIsometryEquiv X.referenceMeasure Y.referenceMeasure

namespace Equiv

variable {X : MetricMeasureSpace.{u}} {Y : MetricMeasureSpace.{v}}
  {Z : MetricMeasureSpace.{w}}

instance : EquivLike (Equiv X Y) X Y where
  coe e := e.toIsometryEquiv
  inv e := e.toIsometryEquiv.symm
  left_inv e := e.toIsometryEquiv.left_inv
  right_inv e := e.toIsometryEquiv.right_inv
  coe_injective' e f h _ := by
    have hef : e.toIsometryEquiv = f.toIsometryEquiv := DFunLike.ext' h
    cases e
    cases f
    cases hef
    rfl

instance : IsometryClass (Equiv X Y) X Y where
  isometry e := e.toIsometryEquiv.isometry

@[simp]
theorem toIsometryEquiv_eq_coe (e : Equiv X Y) : e.toIsometryEquiv = (e : X ≃ᵢ Y) := by
  ext
  rfl

/-- The underlying map preserves the reference measure. -/
theorem measurePreserving (e : Equiv X Y) :
    MeasurePreserving (e : X → Y) X.referenceMeasure Y.referenceMeasure :=
  e.measurePreserving'

@[ext]
theorem ext {e f : Equiv X Y} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

@[simp]
theorem map_referenceMeasure (e : Equiv X Y) :
    X.referenceMeasure.map e = Y.referenceMeasure :=
  e.measurePreserving.map_eq

/-- The identity change of presentation. -/
protected def refl (X : MetricMeasureSpace) : Equiv X X where
  toIsometryEquiv := IsometryEquiv.refl X
  measurePreserving' := MeasurePreserving.id _

/-- Coercion to an isometric equivalence preserves the identity. -/
@[simp]
theorem coe_refl (X : MetricMeasureSpace) :
    (Equiv.refl X : X ≃ᵢ X) = IsometryEquiv.refl X := by
  ext
  rfl

/-- The inverse change of presentation. -/
protected def symm (e : Equiv X Y) : Equiv Y X where
  toIsometryEquiv := e.toIsometryEquiv.symm
  measurePreserving' := e.measurePreserving.symm e.toIsometryEquiv.toHomeomorph.toMeasurableEquiv

/-- Coercion to an isometric equivalence commutes with inversion. -/
@[simp]
theorem coe_symm (e : Equiv X Y) :
    (e.symm : Y ≃ᵢ X) = (e : X ≃ᵢ Y).symm := by
  ext
  rfl

/-- Composition of changes of presentation. -/
protected def trans (e : Equiv X Y) (f : Equiv Y Z) : Equiv X Z where
  toIsometryEquiv := e.toIsometryEquiv.trans f.toIsometryEquiv
  measurePreserving' := f.measurePreserving.comp e.measurePreserving

/-- Coercion to an isometric equivalence preserves composition. -/
@[simp]
theorem coe_trans (e : Equiv X Y) (f : Equiv Y Z) :
    (e.trans f : X ≃ᵢ Z) = (e : X ≃ᵢ Y).trans (f : Y ≃ᵢ Z) := by
  ext
  rfl

@[simp]
theorem refl_apply (x : X) : Equiv.refl X x = x := (rfl)

@[simp]
theorem symm_apply_apply (e : Equiv X Y) (x : X) : e.symm (e x) = x :=
  e.toIsometryEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : Equiv X Y) (y : Y) : e (e.symm y) = y :=
  e.toIsometryEquiv.apply_symm_apply y

@[simp]
theorem trans_apply (e : Equiv X Y) (f : Equiv Y Z) (x : X) : e.trans f x = f (e x) := (rfl)

@[simp]
theorem symm_symm (e : Equiv X Y) : e.symm.symm = e := by ext; rfl

@[simp]
theorem trans_refl (e : Equiv X Y) : e.trans (Equiv.refl Y) = e := by ext; rfl

@[simp]
theorem refl_trans (e : Equiv X Y) : (Equiv.refl X).trans e = e := by ext; rfl

theorem trans_assoc {W : MetricMeasureSpace} (e : Equiv X Y) (f : Equiv Y Z) (g : Equiv Z W) :
    (e.trans f).trans g = e.trans (f.trans g) := by ext; rfl

@[simp]
theorem self_trans_symm (e : Equiv X Y) : e.trans e.symm = Equiv.refl X := by ext; simp

@[simp]
theorem symm_trans_self (e : Equiv X Y) : e.symm.trans e = Equiv.refl Y := by ext; simp

/-- A change of presentation carries precisely the support of the reference measure. -/
@[simp]
theorem image_support (e : Equiv X Y) : e '' X.referenceMeasure.support =
    Y.referenceMeasure.support := by
  rw [← e.measurePreserving.map_eq]
  exact (support_map_homeomorph X.referenceMeasure e.toIsometryEquiv.toHomeomorph
    e.measurePreserving.measurable).symm

@[simp]
theorem apply_mem_support_iff (e : Equiv X Y) (x : X) :
    e x ∈ Y.referenceMeasure.support ↔ x ∈ X.referenceMeasure.support := by
  rw [← e.image_support]
  exact e.toIsometryEquiv.injective.mem_set_image

/-- The isometric equivalence induced on the supports of the reference measures. -/
private def supportIsometryEquiv (e : Equiv X Y) : X.supportSpace ≃ᵢ Y.supportSpace where
  toEquiv := e.toIsometryEquiv.toEquiv.subtypeEquiv (fun x ↦ (e.apply_mem_support_iff x).symm)
  isometry_toFun := by
    -- Expose the support subtypes and their induced metrics for the distance rewrites.
    change Isometry (e.toIsometryEquiv.toEquiv.subtypeEquiv
      (fun x ↦ (e.apply_mem_support_iff x).symm))
    intro x y
    rw [Subtype.edist_eq, Subtype.edist_eq]
    simp only [_root_.Equiv.subtypeEquiv_apply]
    exact e.toIsometryEquiv.edist_eq x.val y.val

-- Rewrite before simp reduces the coercions through the bundled support carriers.
@[simp↓]
private theorem coe_supportIsometryEquiv_apply (e : Equiv X Y) (x : X.supportSpace) :
    ((↑) : Y.referenceMeasure.support → Y) (e.supportIsometryEquiv x) =
      e (((↑) : X.referenceMeasure.support → X) x) := (rfl)

/-- Restrict a change of presentation to the supports of its two reference measures. -/
def supportEquiv (e : Equiv X Y) : Equiv X.supportSpace Y.supportSpace where
  toIsometryEquiv := e.supportIsometryEquiv
  measurePreserving' := by
    let f : X.referenceMeasure.support → Y.referenceMeasure.support := e.supportIsometryEquiv
    let μ : Measure X.referenceMeasure.support := X.supportSpace.referenceMeasure
    let ν : Measure Y.referenceMeasure.support := Y.supportSpace.referenceMeasure
    have hf : Measurable f := e.supportIsometryEquiv.continuous.measurable
    have hX : MeasurePreserving ((↑) : X.referenceMeasure.support → X) μ X.referenceMeasure :=
      X.measurePreserving_subtype_coe
    have hY : MeasurePreserving ((↑) : Y.referenceMeasure.support → Y) ν Y.referenceMeasure :=
      Y.measurePreserving_subtype_coe
    refine ⟨hf, ?_⟩
    apply (MeasurableEmbedding.subtype_coe
      Y.referenceMeasure.isClosed_support.measurableSet).map_injective
    calc
      (μ.map f).map ((↑) : Y.referenceMeasure.support → Y) =
          (μ.map ((↑) : X.referenceMeasure.support → X)).map e := by
        rw [Measure.map_map measurable_subtype_coe hf,
          Measure.map_map (g := (e : X → Y))
            e.measurePreserving.measurable measurable_subtype_coe]
        exact congrArg (fun g : X.referenceMeasure.support → Y ↦ μ.map g)
          (funext fun x ↦ e.coe_supportIsometryEquiv_apply x)
      _ = ν.map ((↑) : Y.referenceMeasure.support → Y) := by
        rw [hX.map_eq, e.map_referenceMeasure, hY.map_eq]

@[simp↓]
theorem coe_supportEquiv_apply (e : Equiv X Y) (x : X.supportSpace) :
    ((↑) : Y.referenceMeasure.support → Y) (e.supportEquiv x) =
      e (((↑) : X.referenceMeasure.support → X) x) :=
  e.coe_supportIsometryEquiv_apply x

@[simp]
theorem supportEquiv_refl (X : MetricMeasureSpace) :
    (Equiv.refl X).supportEquiv = Equiv.refl X.supportSpace := by ext; rfl

@[simp]
theorem supportEquiv_trans (e : Equiv X Y) (f : Equiv Y Z) :
    (e.trans f).supportEquiv = e.supportEquiv.trans f.supportEquiv := by ext; rfl

@[simp]
theorem supportEquiv_symm (e : Equiv X Y) : e.symm.supportEquiv = e.supportEquiv.symm := by
  ext
  rfl

end Equiv

/-- For a full-support reference measure, support reduction is isomorphic to the original
presentation, with the support inclusion as its forward map. -/
def supportSpaceEquivOfFullSupport (X : MetricMeasureSpace) [X.referenceMeasure.IsOpenPosMeasure] :
    Equiv X.supportSpace X where
  toIsometryEquiv :=
    { toEquiv := _root_.Equiv.subtypeUnivEquiv (fun x ↦ by simp [Measure.support_eq_univ])
      isometry_toFun := by
        -- Expose the support subtype so the equivalence application lemma can rewrite.
        change Isometry (_root_.Equiv.subtypeUnivEquiv
          (fun x : X ↦ by simp [Measure.support_eq_univ]))
        intro x y
        simp only [_root_.Equiv.subtypeUnivEquiv_apply]
        exact isometry_subtype_coe x y }
  measurePreserving' := X.measurePreserving_subtype_coe

@[simp↓]
theorem supportSpaceEquivOfFullSupport_apply (X : MetricMeasureSpace)
    [X.referenceMeasure.IsOpenPosMeasure] (x : X.supportSpace) :
    X.supportSpaceEquivOfFullSupport x = ((↑) : X.referenceMeasure.support → X) x := (rfl)

/-- The inverse full-support equivalence sends a point to the support point over it. -/
@[simp↓]
theorem coe_supportSpaceEquivOfFullSupport_symm_apply (X : MetricMeasureSpace)
    [X.referenceMeasure.IsOpenPosMeasure] (x : X) :
    ((↑) : X.referenceMeasure.support → X) (X.supportSpaceEquivOfFullSupport.symm x) = x := by
  rw [← X.supportSpaceEquivOfFullSupport_apply]
  exact X.supportSpaceEquivOfFullSupport.apply_symm_apply x

end MetricMeasureSpace

end TauCeti
