/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Topology.VectorBundle.Coordinates
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Source-indexed orientation lifts

An orientation lift consists of an orientation of the model vector space and locally constant
signs defined only on the source of each preferred chart. The signs compensate for the sign of
the transition derivative within the model range, including boundary and corner points.
Simultaneously reversing the model orientation and every chart sign leaves the induced tangent
orientations unchanged.

## References

* Michael Lee's [Mathlib PR #35376](https://github.com/leanprover-community/mathlib4/pull/35376):
  the chart-sign lift and diagonal-quotient design, adapted here to source-indexed signs and
  actual tangent-bundle trivializations.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15.
* [TauCeti PR #15107](https://github.com/TauCetiProject/TauCeti/pull/15107): the earlier
  formalization of the chart-sign lift and diagonal-flip quotient.
-/

public section

noncomputable section


open Set Filter Bundle
open scoped Topology Manifold

namespace TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*}

/-- A model orientation with source-indexed chart signs. Compatibility is expressed through
actual transition Jacobians within `range I`, including boundary and corner points. -/
@[ext]
structure OrientationLift (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (ι : Type*) [Fintype ι] [FiniteDimensional ℝ E] where
  /-- Orientation of the model vector space. -/
  modelOrientation : _root_.Orientation ℝ E ι
  /-- The index type has the dimension of the model space. -/
  card_eq : Fintype.card ι = Module.finrank ℝ E
  /-- A sign only at points lying in the chosen preferred chart's source. -/
  sign : (α : M) → (chartAt H α).source → ℤˣ
  /-- Chart signs are locally constant on their actual domains. -/
  locallyConstant_sign : ∀ α, IsLocallyConstant (sign α)
  /-- The two chart signs compensate for the sign of the within-range transition Jacobian. -/
  compatible : ∀ α β (x : M) (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source),
    0 < ((sign α ⟨x, hα⟩ : ℤ) : ℝ) * ((sign β ⟨x, hβ⟩ : ℤ) : ℝ) *
      (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm)
        (range I) (extChartAt I α x)).det

namespace OrientationLift

variable [Fintype ι] [FiniteDimensional ℝ E]

variable {I}

omit [ChartedSpace H M] in
/-- Changing the atlas without changing its preferred charts leaves the lift data unchanged. -/
def congrChartAt {c c' : ChartedSpace H M} (h : c.chartAt = c'.chartAt)
    (o : @OrientationLift E H _ _ _ I M _ c ι _ _) :
    @OrientationLift E H _ _ _ I M _ c' ι _ _ := by
  letI : ChartedSpace H M := c
  let castSource (α : M) (x : (c'.chartAt α).source) : (c.chartAt α).source :=
    ⟨x.val, by rw [h]; exact x.property⟩
  refine @OrientationLift.mk E H _ _ _ I M _ c' ι _ _
    o.modelOrientation o.card_eq (fun α x ↦ o.sign α (castSource α x)) ?_ ?_
  · intro α
    exact (o.locallyConstant_sign α).comp_continuous
      (continuous_subtype_val.subtype_mk _)
  · intro α β x hα hβ
    have hα' : x ∈ (c.chartAt α).source := by rw [h]; exact hα
    have hβ' : x ∈ (c.chartAt β).source := by rw [h]; exact hβ
    simpa only [castSource, extChartAt, chartAt, h] using o.compatible α β x hα' hβ'

omit [ChartedSpace H M] in
/-- Changing only the atlas preserves the model orientation. -/
@[simp]
theorem congrChartAt_modelOrientation {c c' : ChartedSpace H M} (h : c.chartAt = c'.chartAt)
    (o : @OrientationLift E H _ _ _ I M _ c ι _ _) :
    (letI := c'; (o.congrChartAt h).modelOrientation) =
      (letI := c; o.modelOrientation) := (rfl)

omit [ChartedSpace H M] in
/-- Changing only the atlas transports each source sign along equality of preferred charts. -/
@[simp]
theorem congrChartAt_sign {c c' : ChartedSpace H M} (h : c.chartAt = c'.chartAt)
    (o : @OrientationLift E H _ _ _ I M _ c ι _ _) (α : M)
    (x : (c'.chartAt α).source) :
    (letI := c'; (o.congrChartAt h).sign α x) =
      (letI := c; o.sign α ⟨x.val, by
        -- The local instance is c; expose its chart source before transporting along h.
        change x.val ∈ (c.chartAt α).source
        rw [h]
        exact x.property⟩) := (rfl)

/-- The product of the source signs is exactly the sign of the within-range transition
Jacobian. -/
theorem sign_mul_sign (o : OrientationLift I M ι) (α β x : M)
    (hα : x ∈ (chartAt H α).source) (hβ : x ∈ (chartAt H β).source) :
    ((o.sign α ⟨x, hα⟩ * o.sign β ⟨x, hβ⟩ : ℤˣ) : ℤ) =
      (SignType.sign (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm)
        (range I) (extChartAt I α x)).det : ℤ) := by
  let u := o.sign α ⟨x, hα⟩ * o.sign β ⟨x, hβ⟩
  have hd : 0 < (u : ℝ) * (fderivWithin ℝ
      (extChartAt I β ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)).det := by
    simpa only [u, Units.val_mul, Int.cast_mul] using o.compatible α β x hα hβ
  -- Treat the product of the two source signs as one integer unit.
  change (u : ℤ) = _
  rcases Int.units_eq_one_or u with h | h
  · rw [h] at hd ⊢
    norm_num only [Units.val_one, Int.cast_one, one_mul] at hd
    simp only [sign_pos hd, SignType.coe_one, Units.val_one]
  · rw [h] at hd ⊢
    norm_num only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
      neg_pos] at hd
    simp only [sign_neg hd, SignType.coe_neg, SignType.coe_one, Units.val_neg, Units.val_one]

/-- Signed transition determinants agree with the absolute Jacobian factor appearing in the
change-of-variables theorem for top forms. -/
theorem sign_mul_det (o : OrientationLift I M ι) (α β x : M)
    (hα : x ∈ (chartAt H α).source) (hβ : x ∈ (chartAt H β).source) :
    ((o.sign α ⟨x, hα⟩ : ℤ) : ℝ) * (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm)
        (range I) (extChartAt I α x)).det =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm)
        (range I) (extChartAt I α x)).det| * ((o.sign β ⟨x, hβ⟩ : ℤ) : ℝ) := by
  let u := o.sign α ⟨x, hα⟩
  let v := o.sign β ⟨x, hβ⟩
  let D := (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm)
    (range I) (extChartAt I α x)).det
  have hs : (u : ℝ) * (v : ℝ) = (SignType.sign D : ℝ) := by
    exact_mod_cast o.sign_mul_sign α β x hα hβ
  have hv : (v : ℝ) * (v : ℝ) = 1 := by
    exact_mod_cast Int.isUnit_mul_self v.isUnit
  calc
    (u : ℝ) * D = ((u : ℝ) * (v : ℝ)) * D * (v : ℝ) := by
      calc
        (u : ℝ) * D = (u : ℝ) * D * ((v : ℝ) * (v : ℝ)) := by rw [hv, mul_one]
        _ = _ := by ring
    _ = |D| * (v : ℝ) := by rw [hs, sign_mul_self]

/-- Simultaneously reverse the model orientation and all source signs. This changes only the
representative lift, not any induced tangent orientation. -/
def flip (o : OrientationLift I M ι) : OrientationLift I M ι where
  modelOrientation := -o.modelOrientation
  card_eq := o.card_eq
  sign α x := -o.sign α x
  locallyConstant_sign α := (o.locallyConstant_sign α).comp Neg.neg
  compatible α β x hα hβ := by
    simpa only [Units.val_neg, Int.cast_neg, neg_mul_neg] using o.compatible α β x hα hβ

@[simp]
theorem flip_modelOrientation (o : OrientationLift I M ι) :
    o.flip.modelOrientation = -o.modelOrientation := (rfl)

@[simp]
theorem flip_sign (o : OrientationLift I M ι) (α) (x) :
    o.flip.sign α x = -o.sign α x := (rfl)

@[simp]
theorem flip_flip (o : OrientationLift I M ι) : o.flip.flip = o := by
  ext α x
  · exact _root_.neg_neg o.modelOrientation
  · simp [flip]

/-- Reverse the induced orientation while holding the chart signs fixed. -/
instance : Neg (OrientationLift I M ι) where
  neg o := { o with modelOrientation := -o.modelOrientation }

@[simp]
theorem neg_modelOrientation (o : OrientationLift I M ι) :
    (-o).modelOrientation = -o.modelOrientation := (rfl)

@[simp]
theorem neg_sign (o : OrientationLift I M ι) (α) (x) : (-o).sign α x = o.sign α x := (rfl)

open Classical in
/-- A total chart sign with the fixed value `1` off the chart source. Only the source-indexed
signs are part of the lift. -/
def signAt (o : OrientationLift I M ι) (α x : M) : ℤˣ :=
  if hx : x ∈ (chartAt H α).source then o.sign α ⟨x, hx⟩ else 1

@[simp]
theorem signAt_of_mem (o : OrientationLift I M ι) {α x : M}
    (hx : x ∈ (chartAt H α).source) : o.signAt α x = o.sign α ⟨x, hx⟩ := by
  simp only [signAt, dite_eq_left hx]

@[simp]
theorem signAt_of_notMem (o : OrientationLift I M ι) {α x : M}
    (hx : x ∉ (chartAt H α).source) : o.signAt α x = 1 := by
  simp only [signAt, dite_eq_right hx]

/-- The total sign is continuous when restricted to the actual preferred chart source. -/
theorem continuousOn_signAt (o : OrientationLift I M ι) (α : M) :
    ContinuousOn (o.signAt α) (chartAt H α).source := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (o.locallyConstant_sign α).continuous using 1
  funext x
  exact o.signAt_of_mem x.property

@[simp]
theorem neg_signAt (o : OrientationLift I M ι) (α x : M) :
    (-o).signAt α x = o.signAt α x := by
  classical
  by_cases hx : x ∈ (chartAt H α).source <;> simp [hx]

/-- Diagonal reversal negates the total sign on the chart source. -/
theorem flip_signAt_of_mem (o : OrientationLift I M ι) {α x : M}
    (hx : x ∈ (chartAt H α).source) : o.flip.signAt α x = -o.signAt α x := by
  rw [signAt_of_mem _ hx, signAt_of_mem _ hx, flip_sign]

section Tangent

variable [IsManifold I 1 M]

private theorem map_signedOrientation (o : OrientationLift I M ι) {α β x : M}
    (hα : x ∈ (chartAt H α).source) (hβ : x ∈ (chartAt H β).source) :
    _root_.Orientation.map ι
      ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) x).toLinearEquiv
      (((Units.map (Int.castRingHom ℝ).toMonoidHom (o.sign α ⟨x, hα⟩)) • o.modelOrientation)) =
        ((Units.map (Int.castRingHom ℝ).toMonoidHom (o.sign β ⟨x, hβ⟩)) • o.modelOrientation) := by
  rw [_root_.Orientation.map_units_smul_eq_iff_det_mul_pos _ _ _ _ o.card_eq]
  have hd := o.compatible α β x hα hβ
  have hdet : LinearMap.det ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x).toLinearEquiv.toLinearMap =
      (tangentCoordChange I α β x).det := by
    change LinearMap.det (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x : E →L[ℝ] E).toLinearMap) = _
    exact congrArg (fun f : E →L[ℝ] E ↦ LinearMap.det f.toLinearMap)
      ((tangentBundleCore I M).trivializationAt_coordChangeL
        (α := α) (β := β) (x := x) ⟨hα, hβ⟩)
  rwa [hdet]

/-- The signed model orientation read in a preferred chart at a point of its source. -/
def chartOrientation (o : OrientationLift I M ι) (α : M)
    (x : (chartAt H α).source) : _root_.Orientation ℝ E ι :=
  ((Units.map (Int.castRingHom ℝ).toMonoidHom (o.sign α x)) • o.modelOrientation)

omit [IsManifold I 1 M] in
/-- The chart orientation is the model orientation or its negative according to the chart sign. -/
theorem chartOrientation_eq_ite (o : OrientationLift I M ι) (α : M)
    (x : (chartAt H α).source) : o.chartOrientation α x =
      if o.sign α x = 1 then o.modelOrientation else -o.modelOrientation :=
  _root_.Orientation.intCast_units_smul_eq_ite _ _

/-- The tangent orientation induced by a lift, using the actual inverse tangent trivialization
of the preferred chart at the point. -/
def orientationAt (o : OrientationLift I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι :=
  ((trivializationAt E (TangentSpace I) x).mapOrientation ι
    (FiberBundle.mem_baseSet_trivializationAt' x)).symm
      ((Units.map (Int.castRingHom ℝ).toMonoidHom
        (o.sign x ⟨x, mem_chart_source H x⟩)) • o.modelOrientation)

/-- Reading the tangent orientation in any preferred chart gives precisely its signed model
orientation. Thus the construction is independent of the chosen chart. -/
@[simp] theorem mapOrientation_orientationAt (o : OrientationLift I M ι) {α x : M}
    (hα : x ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).mapOrientation ι
      (by rwa [TangentBundle.trivializationAt_baseSet (I := I)]) (o.orientationAt x) =
        o.chartOrientation α ⟨x, hα⟩ := by
  rw [Bundle.Trivialization.mapOrientation_eq_map_coordChangeL
    (trivializationAt E (TangentSpace I) x) _ (FiberBundle.mem_baseSet_trivializationAt' x)]
  simp only [orientationAt, Equiv.apply_symm_apply]
  exact o.map_signedOrientation (mem_chart_source H x) hα

/-- Diagonally flipping a lift preserves every actual tangent orientation. -/
@[simp]
theorem orientationAt_flip (o : OrientationLift I M ι) (x : M) :
    o.flip.orientationAt x = o.orientationAt x := by
  simp only [orientationAt, flip]
  congr 1
  rw [_root_.Orientation.intCast_units_smul_eq_ite,
    _root_.Orientation.intCast_units_smul_eq_ite]
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or (o.sign x ⟨x, mem_chart_source H x⟩) with h | h
  · simp only [h, hn, ite_true, ite_false]
    exact _root_.neg_neg o.modelOrientation
  · simp only [h, _root_.neg_neg, hn, ite_true, ite_false]

/-- The tangent orientation at a point is its signed model orientation in that point's
preferred chart. -/
theorem orientationAt_eq (o : OrientationLift I M ι) (x : M) :
    o.orientationAt x = o.chartOrientation x ⟨x, mem_chart_source H x⟩ := by
  have he : (trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x) = LinearEquiv.refl ℝ E := by
    ext v
    rw [Bundle.Trivialization.linearEquivAt_apply]
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _
      (FiberBundle.mem_baseSet_trivializationAt' x)]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
    exact tangentCoordChange_self (mem_extChartAt_source x)
  have h := o.mapOrientation_orientationAt (mem_chart_source H x)
  rw [Bundle.Trivialization.mapOrientation_apply, he] at h
  -- TangentSpace at the base point is the model space; the identity trivialization
  -- therefore gives the identity orientation map, with the displayed model-space type.
  change _root_.Orientation.map ι (LinearEquiv.refl ℝ E) _ = _ at h
  rwa [_root_.Orientation.map_refl] at h

/-- The tangent orientations of a lift vary locally constantly in bundle trivializations. -/
def toVectorBundleOrientation (o : OrientationLift I M ι) :
    TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι where
  toFun := o.orientationAt
  eventually_mapOrientation_eq' α := by
    have h := (o.locallyConstant_sign α).eventually_eq
      ⟨α, mem_chart_source H α⟩
    rcases (mem_nhds_subtype _ _ _).mp h with ⟨u, hu, hus⟩
    filter_upwards [hu] with x hx hxs
    have hxs' : x ∈ (chartAt H α).source := by
      rwa [← TangentBundle.trivializationAt_baseSet (I := I)]
    rw [o.mapOrientation_orientationAt hxs',
      o.mapOrientation_orientationAt (mem_chart_source H α)]
    simp only [chartOrientation]
    have hx' : (⟨x, hxs'⟩ : (chartAt H α).source) ∈ Subtype.val ⁻¹' u := hx
    rw [hus hx']

@[simp]
theorem toVectorBundleOrientation_apply (o : OrientationLift I M ι) (x : M) :
    o.toVectorBundleOrientation x = o.orientationAt x := (rfl)

/-- Negating the model orientation reverses every induced tangent orientation. -/
@[simp]
theorem orientationAt_neg (o : OrientationLift I M ι) (x : M) :
    (-o).orientationAt x = -o.orientationAt x := by
  apply ((trivializationAt E (TangentSpace I) x).mapOrientation ι
    (FiberBundle.mem_baseSet_trivializationAt' x)).injective
  rw [Bundle.Trivialization.mapOrientation_neg,
    mapOrientation_orientationAt _ (mem_chart_source H x),
    mapOrientation_orientationAt _ (mem_chart_source H x)]
  simp only [chartOrientation, _root_.Orientation.intCast_units_smul_eq_ite,
    neg_sign, neg_modelOrientation]
  split_ifs <;> rfl

open Classical in
/-- Every orientation of the tangent bundle gives a source-indexed lift, after choosing a
model orientation. The model choice disappears in the diagonal quotient. -/
def ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) :
    OrientationLift I M ι where
  modelOrientation := model
  card_eq := hι
  sign α x := if ((trivializationAt E (TangentSpace I) α).mapOrientation ι
    (by rw [TangentBundle.trivializationAt_baseSet (I := I)]; exact x.property) (o x)) = model
      then 1 else -1
  locallyConstant_sign α := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : x.val ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (I := I)]; exact x.property
    have he := o.eventually_mapOrientation_eq hι (trivializationAt E (TangentSpace I) α) hx
    have hp := (continuous_subtype_val.tendsto x).eventually he
    filter_upwards [hp] with y hy
    rw [hy (by
      rw [TangentBundle.trivializationAt_baseSet (I := I)]
      exact y.property)]
  compatible α β x hα hβ := by
    let A := (trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x
    have hdet : LinearMap.det A.toLinearEquiv.toLinearMap =
        (tangentCoordChange I α β x).det := by
      change LinearMap.det (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) x : E →L[ℝ] E).toLinearMap) = _
      exact congrArg (fun f : E →L[ℝ] E ↦ LinearMap.det f.toLinearMap)
        ((tangentBundleCore I M).trivializationAt_coordChangeL
          (α := α) (β := β) (x := x) ⟨hα, hβ⟩)
    rw [tangentCoordChange_def] at hdet
    let a := (trivializationAt E (TangentSpace I) α).mapOrientation ι
      (by rwa [TangentBundle.trivializationAt_baseSet (I := I)]) (o x)
    let b := (trivializationAt E (TangentSpace I) β).mapOrientation ι
      (by rwa [TangentBundle.trivializationAt_baseSet (I := I)]) (o x)
    let u : ℤˣ := if a = model then 1 else -1
    let v : ℤˣ := if b = model then 1 else -1
    have hmap : _root_.Orientation.map ι A.toLinearEquiv
        ((Units.map (Int.castRingHom ℝ).toMonoidHom u) • model) =
          (Units.map (Int.castRingHom ℝ).toMonoidHom v) • model := by
      dsimp only [u, v]
      rw [_root_.Orientation.intCast_units_smul_ite_eq _ _ hι,
        _root_.Orientation.intCast_units_smul_ite_eq _ _ hι]
      exact (Bundle.Trivialization.mapOrientation_eq_map_coordChangeL _ _
        (by rwa [TangentBundle.trivializationAt_baseSet (I := I)])
        (by rwa [TangentBundle.trivializationAt_baseSet (I := I)]) (o x)).symm
    rw [← hdet]
    exact (_root_.Orientation.map_units_smul_eq_iff_det_mul_pos model A.toLinearEquiv
      (Units.map (Int.castRingHom ℝ).toMonoidHom u)
      (Units.map (Int.castRingHom ℝ).toMonoidHom v) hι).mp hmap

/-- The lift reconstructed from a tangent bundle orientation recovers that orientation pointwise. -/
@[simp]
theorem orientationAt_ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) (x : M) :
    (ofVectorBundleOrientation model hι o).orientationAt x = o x := by
  apply ((trivializationAt E (TangentSpace I) x).mapOrientation ι
    (FiberBundle.mem_baseSet_trivializationAt' x)).injective
  rw [mapOrientation_orientationAt _ (mem_chart_source H x)]
  exact _root_.Orientation.intCast_units_smul_ite_eq _ _ hι

/-- A model with corners carries every constant model orientation, with all chart signs `1`. -/
def model (o : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E) :
    OrientationLift I H ι where
  modelOrientation := o
  card_eq := hι
  sign _ _ := 1
  locallyConstant_sign _ := IsLocallyConstant.const _
  compatible α β x _ _ := by
    have ht : tangentCoordChange I α β x = ContinuousLinearMap.id ℝ E := by
      ext v
      -- The preferred charts of a model are all the identity, so this is its self transition.
      change tangentCoordChange I x x x v = v
      exact tangentCoordChange_self (mem_extChartAt_source x)
    rw [tangentCoordChange_def] at ht
    rw [ht]
    simp [ContinuousLinearMap.det]

@[simp]
theorem model_modelOrientation (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    (model (I := I) o hι).modelOrientation = o := (rfl)

@[simp]
theorem model_sign (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (α : H) (x) :
    (model (I := I) o hι).sign α x = 1 := (rfl)

@[simp]
theorem orientationAt_model (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (x : H) :
    (model (I := I) o hι).orientationAt x = o := by
  rw [orientationAt_eq, chartOrientation_eq_ite]
  simp only [model_sign, ite_true, model_modelOrientation]
  -- The model's tangent space carries its model-space scalar structure.
  rfl

/-- Two lifts with the same model orientation and tangent orientations have the same signs. -/
theorem ext_of_orientationAt {o o' : OrientationLift I M ι}
    (hm : o.modelOrientation = o'.modelOrientation)
    (h : ∀ x, o.orientationAt x = o'.orientationAt x) : o = o' := by
  apply OrientationLift.ext hm
  funext α x
  apply _root_.Orientation.intCast_units_smul_injective o'.modelOrientation
  have hx := congrArg ((trivializationAt E (TangentSpace I) α).mapOrientation ι
    (by rw [TangentBundle.trivializationAt_baseSet (I := I)]; exact x.property)) (h x)
  rw [mapOrientation_orientationAt _ x.property,
    mapOrientation_orientationAt _ x.property] at hx
  simpa only [chartOrientation, hm] using hx

/-- Equality of the induced tangent orientations identifies precisely the diagonal flip. -/
theorem eq_or_eq_flip_of_orientationAt {o o' : OrientationLift I M ι}
    (h : ∀ x, o.orientationAt x = o'.orientationAt x) : o = o' ∨ o = o'.flip := by
  rcases _root_.Orientation.eq_or_eq_neg o.modelOrientation o'.modelOrientation o.card_eq
    with hm | hm
  · exact .inl (ext_of_orientationAt hm h)
  · exact .inr (ext_of_orientationAt hm (by simpa using h))

end Tangent

@[simp]
protected theorem neg_neg (o : OrientationLift I M ι) : - -o = o := by
  apply OrientationLift.ext (_root_.neg_neg o.modelOrientation)
  funext α x
  simp only [neg_sign]

@[simp]
theorem flip_neg (o : OrientationLift I M ι) : (-o).flip = -o.flip := by
  apply OrientationLift.ext (by simp only [flip_modelOrientation, neg_modelOrientation])
  funext α x
  simp only [flip_sign, neg_sign]

/-- The equivalence relation that forgets the simultaneous reversal of the model orientation
and all chart signs. -/
def setoid : Setoid (OrientationLift I M ι) where
  r o o' := o' = o ∨ o' = o.flip
  iseqv := ⟨fun _ ↦ .inl rfl, fun {o o'} h ↦ by
    rcases h with rfl | rfl
    · exact .inl rfl
    · exact .inr o.flip_flip.symm,
    fun {o o' o''} h h' ↦ by
      rcases h with rfl | rfl <;> rcases h' with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
      · exact .inr rfl
      · exact .inl o.flip_flip⟩

/-- The diagonal equivalence relation is equality or simultaneous sign reversal. -/
theorem setoid_rel (o o' : OrientationLift I M ι) :
    setoid.r o o' ↔ o' = o ∨ o' = o.flip := Iff.rfl

end OrientationLift
end TauCeti.Manifold
