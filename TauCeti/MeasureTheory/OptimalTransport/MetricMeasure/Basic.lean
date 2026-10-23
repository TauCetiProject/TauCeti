/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Metric spaces with a boundedly finite reference measure

A metric-measure space here has a complete separable metric carrier and a Borel reference
measure finite on bounded sets. The reference need not be a probability: transported
probability laws are separate objects. This is the carrier used in synthetic curvature and
the metric-measure specialization of measured kernels.

The reference measure can be restricted to its closed support. The resulting metric space is
again complete and separable, and its measure has full support. In particular, points outside
the support play no role in integration against the reference measure.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- A Borel reference measure finite on every bounded set of a complete separable metric
space. The metric and measurable structures are Mathlib's existing structures on `X`. -/
structure MetricMeasureSpace (X : Type*) [MetricSpace X] [MeasurableSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X] where
  /-- The reference measure, distinct from any transported probability law. -/
  reference : Measure X
  /-- Every bounded set has finite reference mass. -/
  finite_bounded : ∀ s : Set X, Bornology.IsBounded s → reference s < ∞

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X]

/-- A finite Borel measure gives a metric-measure space on any complete separable metric
carrier. -/
def ofFinite (μ : Measure X) [IsFiniteMeasure μ] : MetricMeasureSpace X where
  reference := μ
  finite_bounded := fun _ _ ↦ measure_lt_top μ _

@[simp]
theorem reference_ofFinite (μ : Measure X) [IsFiniteMeasure μ] :
    (ofFinite μ).reference = μ := (rfl)

/-- A reference measure finite on bounded sets is locally finite: balls are bounded. -/
instance instIsLocallyFiniteMeasureReference (M : MetricMeasureSpace X) :
    IsLocallyFiniteMeasure M.reference :=
  ⟨fun x ↦ ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
    M.finite_bounded _ Metric.isBounded_ball⟩⟩

/-- The topological support of the reference measure. -/
def support (M : MetricMeasureSpace X) : Set X := M.reference.support

/-- The support of a metric-measure space is the support of its reference measure. -/
theorem support_def (M : MetricMeasureSpace X) : M.support = M.reference.support := by
  unfold support
  rfl

/-- A point belongs to the support exactly when every neighborhood has positive reference mass. -/
theorem mem_support_iff (M : MetricMeasureSpace X) (x : X) :
    x ∈ M.support ↔ ∀ U ∈ nhds x, 0 < M.reference U := by
  rw [support_def]
  exact Measure.mem_support_iff_forall x

theorem isClosed_support (M : MetricMeasureSpace X) : IsClosed M.support :=
  Measure.isClosed_support

/-- A closed support inherits completeness from the ambient complete metric space. -/
instance instCompleteSpaceSupport (M : MetricMeasureSpace X) : CompleteSpace M.support := by
  let : IsClosed M.support := M.isClosed_support
  infer_instance

/-- The reference measure is concentrated on its support. -/
theorem measure_compl_support (M : MetricMeasureSpace X) :
    M.reference M.supportᶜ = 0 :=
  Measure.measure_compl_support

/-- The reference measure regarded as a measure on its support. -/
noncomputable def supportMeasure (M : MetricMeasureSpace X) : Measure M.support :=
  M.reference.comap Subtype.val

/-- The measure on the support is the comap of the reference measure along inclusion. -/
theorem supportMeasure_def (M : MetricMeasureSpace X) :
    M.supportMeasure = M.reference.comap Subtype.val := by
  unfold supportMeasure
  rfl

/-- The mass of a set in the support is the reference mass of its image in the carrier. -/
theorem supportMeasure_apply (M : MetricMeasureSpace X) (s : Set M.support) :
    M.supportMeasure s = M.reference (Subtype.val '' s) := by
  rw [supportMeasure_def, comap_subtype_coe_apply M.isClosed_support.measurableSet]

/-- Inclusion of the support pushes its restricted measure back to the original measure. -/
theorem map_supportMeasure (M : MetricMeasureSpace X) :
    (M.supportMeasure).map (Subtype.val : M.support → X) = M.reference := by
  rw [supportMeasure, map_comap_subtype_coe M.isClosed_support.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem M.reference.support_mem_ae

/-- Restrict the reference measure to its support, with the inherited metric and Borel
structures. This removes points that the reference measure does not see. -/
noncomputable def supportSpace (M : MetricMeasureSpace X) : MetricMeasureSpace M.support where
  reference := M.supportMeasure
  finite_bounded := by
    intro s hs
    rw [supportMeasure, comap_subtype_coe_apply M.isClosed_support.measurableSet]
    exact M.finite_bounded _ (isometry_subtype_coe.lipschitzWith.isBounded_image hs)

@[simp]
theorem reference_supportSpace (M : MetricMeasureSpace X) :
    M.supportSpace.reference = M.supportMeasure := (rfl)

/-- The restricted reference measure gives positive mass to every neighborhood of every
point in the support. -/
theorem support_supportMeasure (M : MetricMeasureSpace X) :
    (M.supportMeasure).support = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨O, hO, hVO⟩ := isOpen_induced_iff.mp hV
  have hxO : (x : X) ∈ O := by
    have : x ∈ Subtype.val ⁻¹' O := hVO.symm ▸ hxV
    exact this
  have hμO : 0 < M.reference O :=
    (Measure.mem_support_iff_forall (x : X)).mp x.property O (hO.mem_nhds hxO)
  have hμinter : M.reference (O ∩ M.support) = M.reference O := by
    simpa only [Set.sdiff_compl] using
      (measure_sdiff_null (s := O) M.measure_compl_support)
  have hVpos : 0 < M.supportMeasure V := by
    rw [supportMeasure, comap_subtype_coe_apply M.isClosed_support.measurableSet, ← hVO,
      Subtype.image_preimage_coe, Set.inter_comm, hμinter]
    exact hμO
  exact hVpos.trans_le (measure_mono hVU)

/-- The reduced measure is positive on every nonempty open subset of its carrier. -/
instance instIsOpenPosMeasureSupportMeasure (M : MetricMeasureSpace X) :
    M.supportMeasure.IsOpenPosMeasure where
  open_pos := by
    intro U hU ⟨x, hx⟩
    have hx' : x ∈ M.supportMeasure.support := by
      rw [M.support_supportMeasure]
      trivial
    exact ((Measure.mem_support_iff_forall x).mp hx' U (hU.mem_nhds hx)).ne'

/-- The support reduction has full topological support. -/
theorem support_supportSpace (M : MetricMeasureSpace X) :
    M.supportSpace.reference.support = (Set.univ : Set M.support) :=
  M.support_supportMeasure

end MetricMeasureSpace

/-- An isometric map that pushes one reference measure to another. Surjectivity is not
required: the inclusion of a measure's support is an example. -/
structure MeasurePreservingIsometry {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [BorelSpace Y] (M : MetricMeasureSpace X) (N : MetricMeasureSpace Y) where
  /-- The underlying isometry. -/
  toFun : X → Y
  /-- The map preserves distance. -/
  isometry : Isometry toFun
  /-- The map sends the first reference measure to the second. -/
  measurePreserving : MeasurePreserving toFun M.reference N.reference

namespace MeasurePreservingIsometry

variable {X Y Z : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y]
  [CompleteSpace Y] [SecondCountableTopology Y] [BorelSpace Y] [MetricSpace Z]
  [MeasurableSpace Z] [CompleteSpace Z] [SecondCountableTopology Z] [BorelSpace Z]
  {M : MetricMeasureSpace X} {N : MetricMeasureSpace Y} {P : MetricMeasureSpace Z}

instance : FunLike (MeasurePreservingIsometry M N) X Y where
  coe := toFun
  coe_injective := by
    intro f g h
    cases f
    cases g
    congr

@[ext]
theorem ext {f g : MeasurePreservingIsometry M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Identity is a measure-preserving isometry. -/
def refl (M : MetricMeasureSpace X) : MeasurePreservingIsometry M M where
  toFun := id
  isometry := isometry_id
  measurePreserving := MeasurePreserving.id M.reference

@[simp]
theorem refl_apply (M : MetricMeasureSpace X) (x : X) : refl M x = x := (rfl)

/-- Composition of measure-preserving isometries. -/
def comp (g : MeasurePreservingIsometry N P) (f : MeasurePreservingIsometry M N) :
    MeasurePreservingIsometry M P where
  toFun := g ∘ f
  isometry := g.isometry.comp f.isometry
  measurePreserving := g.measurePreserving.comp f.measurePreserving

@[simp]
theorem comp_apply (g : MeasurePreservingIsometry N P) (f : MeasurePreservingIsometry M N)
    (x : X) : comp g f x = g (f x) := (rfl)

end MeasurePreservingIsometry

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X]

/-- The inclusion of the support preserves distances and pushes the reduced reference
measure back to the original one. -/
noncomputable def supportInclusion (M : MetricMeasureSpace X) :
    MeasurePreservingIsometry M.supportSpace M where
  toFun := Subtype.val
  isometry := isometry_subtype_coe
  measurePreserving := ⟨measurable_subtype_coe, M.map_supportMeasure⟩

@[simp]
theorem supportInclusion_apply (M : MetricMeasureSpace X) (x : M.support) :
    M.supportInclusion x = (x : X) := (rfl)

end MetricMeasureSpace

end TauCeti
