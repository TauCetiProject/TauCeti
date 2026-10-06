/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measured metric spaces and support reduction

`MetricMeasureSpace` bundles a complete separable metric space and a Borel reference measure
finite on bounded sets. The reference measure need not be a probability measure, and no
curvature, geodesicity or properness is assumed. Probability laws transported on the carrier
remain ordinary `ProbabilityMeasure`s, separate from the reference measure.

`MetricMeasureSpace.supportSpace` discards points outside the reference measure's support.
Its inclusion is isometric and measure-preserving, and its reference measure has full support.
`MetricMeasureSpace.Isom` records measure-preserving isometric equivalence of presentations.
These are the common carrier and change-of-presentation data for measured metric geometry.

The conventions follow Sturm, *On the geometry of metric measure spaces. I* (2006), §2,
allowing reference measures finite on bounded sets rather than only probability measures.
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace

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
  /-- The reference measure, distinct from probability laws to be transported. -/
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

theorem referenceMeasure_supportSpace (X : MetricMeasureSpace) :
    X.supportSpace.referenceMeasure =
      X.referenceMeasure.comap ((↑) : X.referenceMeasure.support → X) := (rfl)

/-- The canonical inclusion of the support representative in the original carrier. -/
def supportInclusion (X : MetricMeasureSpace) : X.supportSpace → X := Subtype.val

@[simp]
theorem supportInclusion_mem_support (X : MetricMeasureSpace) (x : X.supportSpace) :
    X.supportInclusion x ∈ X.referenceMeasure.support :=
  (x : X.referenceMeasure.support).property

theorem isometry_supportInclusion (X : MetricMeasureSpace) : Isometry X.supportInclusion :=
  isometry_subtype_coe

/-- Support reduction preserves all the reference measure, including infinite total mass. -/
theorem measurePreserving_supportInclusion (X : MetricMeasureSpace) :
    MeasurePreserving X.supportInclusion X.supportSpace.referenceMeasure X.referenceMeasure := by
  refine ⟨measurable_subtype_coe, ?_⟩
  exact (map_comap_subtype_coe X.referenceMeasure.isClosed_support.measurableSet
    X.referenceMeasure).trans (Measure.restrict_eq_self_of_ae_mem
      X.referenceMeasure.support_mem_ae)

/-- The support representative has positive reference measure on every nonempty open set. -/
instance (X : MetricMeasureSpace) : X.supportSpace.referenceMeasure.IsOpenPosMeasure :=
  isOpenPosMeasure_comap_subtype_support X.referenceMeasure X.referenceMeasure.support_mem_ae

@[simp]
theorem support_supportSpace (X : MetricMeasureSpace) :
    X.supportSpace.referenceMeasure.support = univ :=
  Measure.support_eq_univ

@[simp]
theorem range_supportInclusion (X : MetricMeasureSpace) :
    range X.supportInclusion = X.referenceMeasure.support :=
  Subtype.range_coe

/-- An isomorphism of measured metric spaces is an isometric equivalence preserving the
reference measure. There is no additional choice of normalization or representative. -/
structure Isom (X : MetricMeasureSpace.{u}) (Y : MetricMeasureSpace.{v}) extends X ≃ᵢ Y where
  measurePreserving : MeasurePreserving toIsometryEquiv X.referenceMeasure Y.referenceMeasure

namespace Isom

variable {X : MetricMeasureSpace.{u}} {Y : MetricMeasureSpace.{v}}
  {Z : MetricMeasureSpace.{w}}

instance : EquivLike (Isom X Y) X Y where
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

instance : IsometryClass (Isom X Y) X Y where
  isometry e := e.toIsometryEquiv.isometry

@[ext]
theorem ext {e f : Isom X Y} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

@[simp]
theorem map_referenceMeasure (e : Isom X Y) :
    X.referenceMeasure.map e = Y.referenceMeasure :=
  e.measurePreserving.map_eq

/-- The identity change of presentation. -/
protected def refl (X : MetricMeasureSpace) : Isom X X where
  toIsometryEquiv := IsometryEquiv.refl X
  measurePreserving := MeasurePreserving.id _

/-- The inverse change of presentation. -/
protected def symm (e : Isom X Y) : Isom Y X where
  toIsometryEquiv := e.toIsometryEquiv.symm
  measurePreserving := e.measurePreserving.symm e.toIsometryEquiv.toHomeomorph.toMeasurableEquiv

/-- Composition of changes of presentation. -/
protected def trans (e : Isom X Y) (f : Isom Y Z) : Isom X Z where
  toIsometryEquiv := e.toIsometryEquiv.trans f.toIsometryEquiv
  measurePreserving := f.measurePreserving.comp e.measurePreserving

@[simp]
theorem refl_apply (x : X) : Isom.refl X x = x := (rfl)

@[simp]
theorem symm_apply_apply (e : Isom X Y) (x : X) : e.symm (e x) = x :=
  e.toIsometryEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : Isom X Y) (y : Y) : e (e.symm y) = y :=
  e.toIsometryEquiv.apply_symm_apply y

@[simp]
theorem trans_apply (e : Isom X Y) (f : Isom Y Z) (x : X) : e.trans f x = f (e x) := (rfl)

@[simp]
theorem symm_symm (e : Isom X Y) : e.symm.symm = e := by ext; rfl

@[simp]
theorem trans_refl (e : Isom X Y) : e.trans (Isom.refl Y) = e := by ext; rfl

@[simp]
theorem refl_trans (e : Isom X Y) : (Isom.refl X).trans e = e := by ext; rfl

theorem trans_assoc {W : MetricMeasureSpace} (e : Isom X Y) (f : Isom Y Z) (g : Isom Z W) :
    (e.trans f).trans g = e.trans (f.trans g) := by ext; rfl

@[simp]
theorem self_trans_symm (e : Isom X Y) : e.trans e.symm = Isom.refl X := by ext; simp

@[simp]
theorem symm_trans_self (e : Isom X Y) : e.symm.trans e = Isom.refl Y := by ext; simp

/-- A change of presentation carries precisely the support of the reference measure. -/
theorem image_support (e : Isom X Y) : e '' X.referenceMeasure.support =
    Y.referenceMeasure.support := by
  rw [← e.measurePreserving.map_eq]
  exact (support_map_homeomorph X.referenceMeasure e.toIsometryEquiv.toHomeomorph).symm

@[simp]
theorem mem_support_iff (e : Isom X Y) (x : X) :
    e x ∈ Y.referenceMeasure.support ↔ x ∈ X.referenceMeasure.support := by
  rw [← e.image_support]
  exact e.toIsometryEquiv.injective.mem_set_image

/-- Restrict a change of presentation to the supports of its two reference measures. -/
def supportIsom (e : Isom X Y) : Isom X.supportSpace Y.supportSpace where
  toIsometryEquiv :=
    { toEquiv := e.toIsometryEquiv.toEquiv.subtypeEquiv (fun x ↦ (e.mem_support_iff x).symm)
      isometry_toFun := fun x y ↦ e.toIsometryEquiv.edist_eq
        (x : X.referenceMeasure.support).val (y : X.referenceMeasure.support).val }
  measurePreserving := by
    let f : X.supportSpace → Y.supportSpace :=
      e.toIsometryEquiv.toEquiv.subtypeEquiv (fun x ↦ (e.mem_support_iff x).symm)
    have hf : Measurable f :=
      (e.toIsometryEquiv.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable
    refine ⟨hf, ?_⟩
    apply (MeasurableEmbedding.subtype_coe
      Y.referenceMeasure.isClosed_support.measurableSet).map_injective
    calc
      (X.supportSpace.referenceMeasure.map f).map Y.supportInclusion =
          (X.supportSpace.referenceMeasure.map X.supportInclusion).map e := by
        rw [Measure.map_map Y.isometry_supportInclusion.continuous.measurable hf,
          Measure.map_map (g := (e : X → Y))
            e.toIsometryEquiv.continuous.measurable
            X.isometry_supportInclusion.continuous.measurable]
        rfl
      _ = Y.supportSpace.referenceMeasure.map Y.supportInclusion := by
        rw [X.measurePreserving_supportInclusion.map_eq, e.map_referenceMeasure,
          Y.measurePreserving_supportInclusion.map_eq]

@[simp]
theorem supportInclusion_supportIsom (e : Isom X Y) (x : X.supportSpace) :
    Y.supportInclusion (e.supportIsom x) = e (X.supportInclusion x) := (rfl)

@[simp]
theorem supportIsom_refl (X : MetricMeasureSpace) :
    (Isom.refl X).supportIsom = Isom.refl X.supportSpace := by ext; rfl

@[simp]
theorem supportIsom_trans (e : Isom X Y) (f : Isom Y Z) :
    (e.trans f).supportIsom = e.supportIsom.trans f.supportIsom := by ext; rfl

@[simp]
theorem supportIsom_symm (e : Isom X Y) : e.symm.supportIsom = e.supportIsom.symm := by
  ext
  rfl

end Isom

/-- For a full-support reference measure, support reduction is isomorphic to the original
presentation, with the support inclusion as its forward map. -/
def supportIsomOfFullSupport (X : MetricMeasureSpace) [X.referenceMeasure.IsOpenPosMeasure] :
    Isom X.supportSpace X where
  toIsometryEquiv :=
    { toEquiv := Equiv.subtypeUnivEquiv (fun x ↦ by simp [Measure.support_eq_univ])
      isometry_toFun := X.isometry_supportInclusion }
  measurePreserving := X.measurePreserving_supportInclusion

@[simp]
theorem supportIsomOfFullSupport_apply (X : MetricMeasureSpace)
    [X.referenceMeasure.IsOpenPosMeasure] (x : X.supportSpace) :
    X.supportIsomOfFullSupport x = X.supportInclusion x := (rfl)

end MetricMeasureSpace

end TauCeti
