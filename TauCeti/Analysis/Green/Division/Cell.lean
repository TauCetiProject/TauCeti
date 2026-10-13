/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Cell
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Graph cells for finite directional divisions

A cell carries continuous graphs on its actual closed base interval. Their extension to the
real line is the canonical constant endpoint extension. Regularity means `C¹` off a finite
exceptional set, with no regularity up to the exceptional points and no absolute-continuity
assumption. The same cell data give either a type-I or a type-II planar cell.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- A graph-cell presentation with `C¹` graphs away from finitely many exceptions.
Only values on the base interval are stored. -/
@[ext]
structure GraphCell where
  a : ℝ
  b : ℝ
  a_lt_b : a < b
  lower : C(Icc a b, ℝ)
  upper : C(Icc a b, ℝ)
  ordered : ∀ x, lower x ≤ upper x
  lower_regular : ∃ s : Set ℝ, s.Finite ∧
    ContDiffOn ℝ 1 (IccExtend a_lt_b.le lower) (Icc a b \ s)
  upper_regular : ∃ s : Set ℝ, s.Finite ∧
    ContDiffOn ℝ 1 (IccExtend a_lt_b.le upper) (Icc a b \ s)

namespace GraphCell

/-- The canonical constant extension of the lower graph. -/
def lowerFun (K : GraphCell) : ℝ → ℝ := IccExtend K.a_lt_b.le K.lower

/-- The canonical constant extension of the upper graph. -/
def upperFun (K : GraphCell) : ℝ → ℝ := IccExtend K.a_lt_b.le K.upper

@[simp]
theorem lowerFun_apply (K : GraphCell) {x : ℝ} (hx : x ∈ Icc K.a K.b) :
    K.lowerFun x = K.lower ⟨x, hx⟩ := IccExtend_of_mem _ _ hx

@[simp]
theorem upperFun_apply (K : GraphCell) {x : ℝ} (hx : x ∈ Icc K.a K.b) :
    K.upperFun x = K.upper ⟨x, hx⟩ := IccExtend_of_mem _ _ hx

/-- The constant extension of a continuous lower graph is globally continuous. -/
@[continuity, fun_prop]
theorem continuous_lowerFun (K : GraphCell) : Continuous K.lowerFun :=
  K.lower.continuous.Icc_extend'

/-- The constant extension of a continuous upper graph is globally continuous. -/
@[continuity, fun_prop]
theorem continuous_upperFun (K : GraphCell) : Continuous K.upperFun :=
  K.upper.continuous.Icc_extend'

/-- The graphs retain their pointwise order on the base interval. -/
theorem lowerFun_le_upperFun (K : GraphCell) {x : ℝ} (hx : x ∈ Icc K.a K.b) :
    K.lowerFun x ≤ K.upperFun x := by
  simpa only [lowerFun_apply K hx, upperFun_apply K hx] using K.ordered ⟨x, hx⟩

private theorem differentiableAt_off_finite {a b : ℝ} {f : ℝ → ℝ}
    (h : ∃ s : Set ℝ, s.Finite ∧ ContDiffOn ℝ 1 f (Icc a b \ s)) :
    ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo a b \ s, DifferentiableAt ℝ f t := by
  obtain ⟨s, hs, hf⟩ := h
  refine ⟨s, hs.countable, ?_⟩
  intro t ht
  exact (hf.contDiffAt (Filter.inter_mem (Icc_mem_nhds ht.1.1 ht.1.2)
    (hs.isClosed.isOpen_compl.mem_nhds ht.2))).differentiableAt (by norm_num)

/-- Finite-exception `C¹` regularity supplies the graph-arc hypothesis for the lower edge. -/
theorem exists_countable_differentiableAt_lowerFun (K : GraphCell) :
    ∃ s : Set ℝ, s.Countable ∧
      ∀ t ∈ Ioo K.a K.b \ s, DifferentiableAt ℝ K.lowerFun t :=
  differentiableAt_off_finite K.lower_regular

/-- Finite-exception `C¹` regularity supplies the graph-arc hypothesis for the upper edge. -/
theorem exists_countable_differentiableAt_upperFun (K : GraphCell) :
    ∃ s : Set ℝ, s.Countable ∧
      ∀ t ∈ Ioo K.a K.b \ s, DifferentiableAt ℝ K.upperFun t :=
  differentiableAt_off_finite K.upper_regular

/-- The planar cell, in either base-coordinate direction. -/
def region (K : GraphCell) : Coordinate → Set ℂ
  | .re => verticalRegion K.a K.b K.lowerFun K.upperFun
  | .im => horizontalRegion K.a K.b K.lowerFun K.upperFun

@[simp]
theorem region_re (K : GraphCell) : K.region .re =
    verticalRegion K.a K.b K.lowerFun K.upperFun := (rfl)

@[simp]
theorem region_im (K : GraphCell) : K.region .im =
    horizontalRegion K.a K.b K.lowerFun K.upperFun := (rfl)

/-- Every graph cell is compact. -/
theorem isCompact_region (K : GraphCell) (d : Coordinate) : IsCompact (K.region d) := by
  cases d
  · exact isCompact_verticalRegion K.continuous_lowerFun.continuousOn
      K.continuous_upperFun.continuousOn
  · exact isCompact_horizontalRegion K.continuous_lowerFun.continuousOn
      K.continuous_upperFun.continuousOn

/-- Every graph cell is measurable. -/
theorem measurableSet_region (K : GraphCell) (d : Coordinate) : MeasurableSet (K.region d) :=
  (K.isCompact_region d).measurableSet

/-- The actual four-path oriented boundary of a graph cell. -/
def boundary (K : GraphCell) (d : Coordinate) : BoundaryChain :=
  BoundaryChain.cellBoundary d K.a K.b K.lowerFun K.upperFun
    K.continuous_lowerFun.continuousOn K.continuous_upperFun.continuousOn

/-- The boundary uses the canonical graph extensions and the actual four-edge cell chain. -/
theorem boundary_def (K : GraphCell) (d : Coordinate) :
    K.boundary d = BoundaryChain.cellBoundary d K.a K.b K.lowerFun K.upperFun
      K.continuous_lowerFun.continuousOn K.continuous_upperFun.continuousOn := (rfl)

/-- The graph-cell boundary is an endpoint cycle. -/
@[simp]
theorem boundary_boundary (K : GraphCell) (d : Coordinate) :
    BoundaryChain.boundary (K.boundary d) = 0 := by
  simp [boundary]

/-- Directional Green for a finite-exception cell, including gauge boundary integrability.
Only differentiation in the fiber direction is assumed of the field. -/
theorem integral_boundary (K : GraphCell) (d : Coordinate) {P R : ℂ → ℝ}
    (hP : ContinuousOn P (K.region d))
    (hdP : ∀ x ∈ Icc K.a K.b, ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
      HasDerivAt (fun y ↦ P (d.graph (fun _ ↦ y) x)) (R (d.graph (fun _ ↦ y) x)) y)
    (hR : IntegrableOn R (K.region d)) :
    BoundaryChain.Integrable d.proj P (K.boundary d) ∧
      BoundaryChain.integral d.proj P (K.boundary d) =
        -(d.orientation : ℝ) * ∫ z in K.region d, R z := by
  cases d with
  | re =>
    simp only [Coordinate.graph_re_apply] at hdP
    simpa only [boundary, region, Coordinate.proj_re, Coordinate.orientation_re, Int.cast_one,
      neg_one_mul] using
      BoundaryChain.integral_cellBoundary_re K.a_lt_b.le
      K.continuous_lowerFun.continuousOn K.continuous_upperFun.continuousOn
      K.exists_countable_differentiableAt_lowerFun K.exists_countable_differentiableAt_upperFun
      (fun _ hx ↦ K.lowerFun_le_upperFun hx) hP hdP hR
  | im =>
    simp only [Coordinate.graph_im_apply] at hdP
    simpa only [boundary, region, Coordinate.proj_im, Coordinate.orientation_im, Int.cast_neg,
      Int.cast_one, neg_neg, one_mul] using
      BoundaryChain.integral_cellBoundary_im K.a_lt_b.le
      K.continuous_lowerFun.continuousOn K.continuous_upperFun.continuousOn
      K.exists_countable_differentiableAt_lowerFun K.exists_countable_differentiableAt_upperFun
      (fun _ hx ↦ K.lowerFun_le_upperFun hx) hP hdP hR

/-- Build a cell from raw graph functions by storing only their restrictions to the base
interval. Changing either function outside that interval changes no stored graph value. -/
def ofFunctions (a b : ℝ) (hab : a < b) (lower upper : ℝ → ℝ)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hlu : ∀ x ∈ Icc a b, lower x ≤ upper x)
    (hdl : ∃ s : Set ℝ, s.Finite ∧ ContDiffOn ℝ 1 lower (Icc a b \ s))
    (hdu : ∃ s : Set ℝ, s.Finite ∧ ContDiffOn ℝ 1 upper (Icc a b \ s)) : GraphCell where
  a := a
  b := b
  a_lt_b := hab
  lower := ⟨fun x ↦ lower x, hl.domRestrict⟩
  upper := ⟨fun x ↦ upper x, hu.domRestrict⟩
  ordered x := hlu x x.prop
  lower_regular := by
    obtain ⟨s, hs, h⟩ := hdl
    refine ⟨s, hs, h.congr ?_⟩
    intro x hx
    exact IccExtend_of_mem hab.le _ hx.1
  upper_regular := by
    obtain ⟨s, hs, h⟩ := hdu
    refine ⟨s, hs, h.congr ?_⟩
    intro x hx
    exact IccExtend_of_mem hab.le _ hx.1

section ofFunctions

variable (a b : ℝ) (hab : a < b) (lower upper : ℝ → ℝ)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hlu : ∀ x ∈ Icc a b, lower x ≤ upper x)
    (hdl : ∃ s : Set ℝ, s.Finite ∧ ContDiffOn ℝ 1 lower (Icc a b \ s))
    (hdu : ∃ s : Set ℝ, s.Finite ∧ ContDiffOn ℝ 1 upper (Icc a b \ s))

@[simp]
theorem ofFunctions_a : (ofFunctions a b hab lower upper hl hu hlu hdl hdu).a = a := (rfl)

@[simp]
theorem ofFunctions_b : (ofFunctions a b hab lower upper hl hu hlu hdl hdu).b = b := (rfl)

@[simp]
theorem ofFunctions_lowerFun {x : ℝ} (hx : x ∈ Icc a b) :
    (ofFunctions a b hab lower upper hl hu hlu hdl hdu).lowerFun x = lower x :=
  IccExtend_of_mem hab.le _ hx

@[simp]
theorem ofFunctions_upperFun {x : ℝ} (hx : x ∈ Icc a b) :
    (ofFunctions a b hab lower upper hl hu hlu hdl hdu).upperFun x = upper x :=
  IccExtend_of_mem hab.le _ hx

end ofFunctions

/-- Constant graphs give all nondegenerate-base rectangles, including collapsed fibers. -/
def rectangle (a b c e : ℝ) (hab : a < b) (hce : c ≤ e) : GraphCell where
  a := a
  b := b
  a_lt_b := hab
  lower := ContinuousMap.const _ c
  upper := ContinuousMap.const _ e
  ordered _ := hce
  lower_regular := ⟨∅, finite_empty, by
    simp only [IccExtend, ContinuousMap.coe_const, Function.const_comp]
    exact contDiffOn_const⟩
  upper_regular := ⟨∅, finite_empty, by
    simp only [IccExtend, ContinuousMap.coe_const, Function.const_comp]
    exact contDiffOn_const⟩

@[simp]
theorem rectangle_a (a b c e : ℝ) (hab : a < b) (hce : c ≤ e) :
    (rectangle a b c e hab hce).a = a := (rfl)

@[simp]
theorem rectangle_b (a b c e : ℝ) (hab : a < b) (hce : c ≤ e) :
    (rectangle a b c e hab hce).b = b := (rfl)

@[simp]
theorem rectangle_lowerFun (a b c e : ℝ) (hab : a < b) (hce : c ≤ e) :
    (rectangle a b c e hab hce).lowerFun = fun _ ↦ c := by
  rfl

@[simp]
theorem rectangle_upperFun (a b c e : ℝ) (hab : a < b) (hce : c ≤ e) :
    (rectangle a b c e hab hce).upperFun = fun _ ↦ e := by
  rfl

end GraphCell
end TauCeti.Green
