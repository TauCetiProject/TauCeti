/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.VectorBundle.Orientation
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Source-indexed orientation lifts

An orientation lift consists of an orientation of the model vector space and locally constant
signs defined only on the source of each preferred chart. The signs compensate for the sign of
the transition derivative within the model range, including boundary and corner points.
Simultaneously reversing the model orientation and every chart sign leaves the induced tangent
orientations unchanged.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold

namespace Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {ι : Type*}

private def signedOrientation (u : ℤˣ) (o : _root_.Orientation ℝ E ι) :
    _root_.Orientation ℝ E ι := if u = 1 then o else -o

private theorem signedOrientation_neg (u : ℤˣ)
    (o : _root_.Orientation ℝ E ι) :
    signedOrientation (-u) (-o) = signedOrientation u o := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [signedOrientation,
      ite_eq_right (show (-1 : ℤˣ) ≠ 1 by decide)]
    exact _root_.neg_neg o
  · simp [signedOrientation]

private theorem signedOrientation_injective
    (o : _root_.Orientation ℝ E ι) :
    Function.Injective (fun u : ℤˣ ↦ signedOrientation u o) := by
  intro u v huv
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all [signedOrientation, Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self o).symm]

private theorem map_signedOrientation_iff [Fintype ι] [FiniteDimensional ℝ E]
    (o : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (A : E ≃ₗ[ℝ] E) (u v : ℤˣ) :
    _root_.Orientation.map ι A (signedOrientation u o) = signedOrientation v o ↔
      0 < ((u : ℤ) : ℝ) * ((v : ℤ) : ℝ) * LinearMap.det A.toLinearMap := by
  have hmap : _root_.Orientation.map ι A (-o) = -(_root_.Orientation.map ι A o) :=
    Module.Ray.map_neg _ _
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · simpa only [signedOrientation, ite_true, Units.val_one, Int.cast_one, one_mul] using
      _root_.Orientation.map_eq_iff_det_pos o A hι
  · simpa only [signedOrientation, ite_true, ite_false, show (-1 : ℤˣ) ≠ 1 by decide,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul,
      neg_pos] using _root_.Orientation.map_eq_neg_iff_det_neg o A hι
  · simp only [signedOrientation, ite_true, ite_false, show (-1 : ℤˣ) ≠ 1 by decide,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, mul_one, neg_one_mul,
      neg_pos, hmap]
    exact (show -(_root_.Orientation.map ι A o) = o ↔
      _root_.Orientation.map ι A o = -o from
        neg_eq_iff_eq_neg (a := _root_.Orientation.map ι A o) (b := o)).trans
        (_root_.Orientation.map_eq_neg_iff_det_neg o A hι)
  · simp only [signedOrientation, ite_false, show (-1 : ℤˣ) ≠ 1 by decide,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, neg_mul_neg, one_mul, hmap]
    exact (show -(_root_.Orientation.map ι A o) = -o ↔
      _root_.Orientation.map ι A o = o from
        neg_inj (a := _root_.Orientation.map ι A o) (b := o)).trans
        (_root_.Orientation.map_eq_iff_det_pos o A hι)

open Classical in
private def orientationSign (model o : _root_.Orientation ℝ E ι) : ℤˣ :=
  if o = model then 1 else -1

private theorem signed_orientationSign [Fintype ι] [FiniteDimensional ℝ E]
    (model o : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E) :
    signedOrientation (orientationSign model o) model = o := by
  classical
  rcases _root_.Orientation.eq_or_eq_neg o model hι with h | h
  · simp only [orientationSign, h, ite_true, signedOrientation]
  · rw [h]
    simp only [orientationSign, (Module.Ray.ne_neg_self model).symm, ite_false,
      signedOrientation, show (-1 : ℤˣ) ≠ 1 by decide]

/-- A model orientation with source-indexed chart signs. Compatibility is expressed through
actual transition Jacobians within `range I`, including boundary and corner points. -/
@[ext]
structure OrientationLift (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (ι : Type*) [Fintype ι] [FiniteDimensional ℝ E] where
  /-- Orientation of the model vector space. -/
  modelOrientation : _root_.Orientation ℝ E ι
  /-- The index type has the dimension of the model space. -/
  card_eq : Fintype.card ι = Module.finrank ℝ E
  /-- A sign only at points lying in the chosen preferred chart's source. -/
  sign : (α : M) → (extChartAt I α).source → ℤˣ
  /-- Chart signs are locally constant on their actual domains. -/
  locallyConstant_sign : ∀ α, IsLocallyConstant (sign α)
  /-- The two chart signs compensate for the sign of the within-range transition Jacobian. -/
  compatible : ∀ α β (x : M) (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source),
    0 < ((sign α ⟨x, hα⟩ : ℤ) : ℝ) * ((sign β ⟨x, hβ⟩ : ℤ) : ℝ) *
      (tangentCoordChange I α β x).det

namespace OrientationLift

variable [Fintype ι] [FiniteDimensional ℝ E]

variable {I}

/-- The product of the source signs is exactly the sign of the within-range transition
Jacobian. -/
theorem sign_mul_sign (o : OrientationLift I M ι) (α β x : M)
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source) :
    ((o.sign α ⟨x, hα⟩ * o.sign β ⟨x, hβ⟩ : ℤˣ) : ℤ) =
      (SignType.sign (tangentCoordChange I α β x).det : ℤ) := by
  have hd := o.compatible α β x hα hβ
  rcases Int.units_eq_one_or (o.sign α ⟨x, hα⟩) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (o.sign β ⟨x, hβ⟩) with h₂ | h₂
  all_goals rw [h₁, h₂] at hd ⊢
  all_goals norm_num at hd ⊢
  · rw [sign_pos hd]; rfl
  · rw [sign_neg hd]; rfl
  · rw [sign_neg hd]; rfl
  · rw [sign_pos hd]; rfl

/-- Signed transition determinants agree with the absolute Jacobian factor appearing in the
change-of-variables theorem for top forms. -/
theorem sign_mul_det (o : OrientationLift I M ι) (α β x : M)
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source) :
    ((o.sign α ⟨x, hα⟩ : ℤ) : ℝ) * (tangentCoordChange I α β x).det =
      |(tangentCoordChange I α β x).det| * ((o.sign β ⟨x, hβ⟩ : ℤ) : ℝ) := by
  have hd := o.compatible α β x hα hβ
  rcases Int.units_eq_one_or (o.sign α ⟨x, hα⟩) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (o.sign β ⟨x, hβ⟩) with h₂ | h₂
  all_goals rw [h₁, h₂] at hd ⊢
  all_goals norm_num at hd ⊢
  · exact (abs_of_pos hd).symm
  · rw [abs_of_neg hd, neg_neg]
  · exact (abs_of_neg hd).symm
  · rw [abs_of_pos hd]

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

omit [FiniteDimensional ℝ E] in
private theorem baseSet_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (extChartAt I α).source := by
  rw [TangentBundle.trivializationAt_baseSet, extChartAt_source]

omit [FiniteDimensional ℝ E] in
private theorem coordChange_eq {α β x : M} (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source) :
    ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x : E →L[ℝ] E) =
      tangentCoordChange I α β x := by
  ext v
  exact (tangentBundleCore I M).trivializationAt_coordChange_eq
    ⟨by change x ∈ (chartAt H α).source; rwa [← extChartAt_source I],
      by change x ∈ (chartAt H β).source; rwa [← extChartAt_source I]⟩ v

private theorem map_signedOrientation (o : OrientationLift I M ι) {α β x : M}
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source) :
    _root_.Orientation.map ι
      ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) x).toLinearEquiv
      (signedOrientation (o.sign α ⟨x, hα⟩) o.modelOrientation) =
        signedOrientation (o.sign β ⟨x, hβ⟩) o.modelOrientation := by
  rw [map_signedOrientation_iff o.modelOrientation o.card_eq]
  have hd := o.compatible α β x hα hβ
  have hdet : LinearMap.det ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x).toLinearEquiv.toLinearMap =
      (tangentCoordChange I α β x).det := by
    change (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x) : E →L[ℝ] E).det = _
    rw [coordChange_eq hα hβ]
  rwa [hdet]

/-- The signed model orientation read in a preferred chart at a point of its source. -/
def chartOrientation (o : OrientationLift I M ι) (α : M)
    (x : (extChartAt I α).source) : _root_.Orientation ℝ E ι :=
  signedOrientation (o.sign α x) o.modelOrientation

/-- The chart orientation is the model orientation or its negative according to the chart sign. -/
theorem chartOrientation_def (o : OrientationLift I M ι) (α : M)
    (x : (extChartAt I α).source) : o.chartOrientation α x =
      if o.sign α x = 1 then o.modelOrientation else -o.modelOrientation := (rfl)

/-- The tangent orientation induced by a lift, using the actual inverse tangent trivialization
of the preferred chart at the point. -/
def orientationAt (o : OrientationLift I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι :=
  ((trivializationAt E (TangentSpace I) x).mapOrientation ι
    (FiberBundle.mem_baseSet_trivializationAt' x)).symm
      (signedOrientation (o.sign x ⟨x, mem_extChartAt_source x⟩) o.modelOrientation)

/-- Reading the tangent orientation in any preferred chart gives precisely its signed model
orientation. Thus the construction is independent of the chosen chart. -/
theorem mapOrientation_orientationAt (o : OrientationLift I M ι) {α x : M}
    (hα : x ∈ (extChartAt I α).source) :
    (trivializationAt E (TangentSpace I) α).mapOrientation ι
      (by rwa [baseSet_eq]) (o.orientationAt x) =
        o.chartOrientation α ⟨x, hα⟩ := by
  rw [Bundle.Trivialization.mapOrientation_eq_map_coordChangeL
    (trivializationAt E (TangentSpace I) x) _ (FiberBundle.mem_baseSet_trivializationAt' x)]
  simp only [orientationAt, Equiv.apply_symm_apply]
  exact o.map_signedOrientation (mem_extChartAt_source x) hα

/-- Diagonally flipping a lift preserves every actual tangent orientation. -/
@[simp]
theorem orientationAt_flip (o : OrientationLift I M ι) (x : M) :
    o.flip.orientationAt x = o.orientationAt x := by
  simp only [orientationAt, flip, signedOrientation_neg]

/-- At the base point of its own preferred chart, the tangent coordinates are the identity. -/
theorem orientationAt_eq (o : OrientationLift I M ι) (x : M) :
    o.orientationAt x = o.chartOrientation x ⟨x, mem_extChartAt_source x⟩ := by
  have he : (trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x) = LinearEquiv.refl ℝ E := by
    ext v
    rw [Bundle.Trivialization.linearEquivAt_apply]
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _
      (FiberBundle.mem_baseSet_trivializationAt' x)]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
    exact tangentCoordChange_self (mem_extChartAt_source x)
  have h := o.mapOrientation_orientationAt (mem_extChartAt_source x)
  rw [Bundle.Trivialization.mapOrientation_apply, he] at h
  change _root_.Orientation.map ι (LinearEquiv.refl ℝ E) _ = _ at h
  rwa [_root_.Orientation.map_refl] at h

open Classical in
/-- A total chart sign with the fixed value `1` off the chart source. Only the source-indexed
signs are part of the lift. -/
def signAt (o : OrientationLift I M ι) (α x : M) : ℤˣ :=
  if hx : x ∈ (extChartAt I α).source then o.sign α ⟨x, hx⟩ else 1

@[simp]
theorem signAt_of_mem (o : OrientationLift I M ι) {α x : M}
    (hx : x ∈ (extChartAt I α).source) : o.signAt α x = o.sign α ⟨x, hx⟩ := by
  simp only [signAt, dite_eq_left hx]

@[simp]
theorem signAt_of_not_mem (o : OrientationLift I M ι) {α x : M}
    (hx : x ∉ (extChartAt I α).source) : o.signAt α x = 1 := by
  simp only [signAt, dite_eq_right hx]

/-- The tangent orientations of a lift vary locally constantly in bundle trivializations. -/
def toVectorBundleOrientation (o : OrientationLift I M ι) :
    TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι where
  toFun := o.orientationAt
  eventually_mapOrientation_eq' α := by
    have h := (o.locallyConstant_sign α).eventually_eq
      ⟨α, mem_extChartAt_source α⟩
    rcases (mem_nhds_subtype _ _ _).mp h with ⟨u, hu, hus⟩
    filter_upwards [hu] with x hx hxs
    have hxs' : x ∈ (extChartAt I α).source := by rwa [← baseSet_eq]
    rw [o.mapOrientation_orientationAt hxs',
      o.mapOrientation_orientationAt (mem_extChartAt_source α)]
    change signedOrientation _ _ = signedOrientation _ _
    rw [hus (show (⟨x, hxs'⟩ : (extChartAt I α).source) ∈ Subtype.val ⁻¹' u from hx)]

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
    mapOrientation_orientationAt _ (mem_extChartAt_source x),
    mapOrientation_orientationAt _ (mem_extChartAt_source x)]
  simp only [chartOrientation, signedOrientation, neg_sign, neg_modelOrientation]
  split_ifs <;> rfl

/-- Every orientation of the tangent bundle gives a source-indexed lift, after choosing a
model orientation. The model choice disappears in the diagonal quotient. -/
def ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) :
    OrientationLift I M ι where
  modelOrientation := model
  card_eq := hι
  sign α x := orientationSign model ((trivializationAt E (TangentSpace I) α).mapOrientation ι
    (by rw [baseSet_eq]; exact x.property) (o x))
  locallyConstant_sign α := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : x.val ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [baseSet_eq]; exact x.property
    have he := o.eventually_mapOrientation_eq hι (trivializationAt E (TangentSpace I) α) hx
    have hp := (continuous_subtype_val.tendsto x).eventually he
    filter_upwards [hp] with y hy
    rw [hy (by rw [baseSet_eq]; exact y.property)]
  compatible α β x hα hβ := by
    let A := (trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) x
    have hdet : LinearMap.det A.toLinearEquiv.toLinearMap =
        (tangentCoordChange I α β x).det := by
      change (A : E →L[ℝ] E).det = _
      rw [coordChange_eq hα hβ]
    rw [← hdet, ← map_signedOrientation_iff model hι]
    rw [signed_orientationSign _ _ hι, signed_orientationSign _ _ hι]
    exact (Bundle.Trivialization.mapOrientation_eq_map_coordChangeL _ _
      (by rwa [baseSet_eq]) (by rwa [baseSet_eq]) (o x)).symm

/-- The lift reconstructed from a tangent bundle orientation recovers that orientation pointwise. -/
@[simp]
theorem orientationAt_ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) (x : M) :
    (ofVectorBundleOrientation model hι o).orientationAt x = o x := by
  apply ((trivializationAt E (TangentSpace I) x).mapOrientation ι
    (FiberBundle.mem_baseSet_trivializationAt' x)).injective
  rw [mapOrientation_orientationAt _ (mem_extChartAt_source x)]
  exact signed_orientationSign _ _ hι

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
      change tangentCoordChange I x x x v = v
      exact tangentCoordChange_self (mem_extChartAt_source x)
    rw [ht]
    simp [ContinuousLinearMap.det]

@[simp]
theorem orientationAt_model (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (x : H) :
    (model (I := I) o hι).orientationAt x = o := by
  rw [orientationAt_eq]
  rfl

/-- Two lifts with the same model orientation and tangent orientations have the same signs. -/
theorem ext_of_orientationAt {o o' : OrientationLift I M ι}
    (hm : o.modelOrientation = o'.modelOrientation)
    (h : ∀ x, o.orientationAt x = o'.orientationAt x) : o = o' := by
  apply OrientationLift.ext hm
  funext α x
  apply signedOrientation_injective o'.modelOrientation
  have hx := congrArg ((trivializationAt E (TangentSpace I) α).mapOrientation ι
    (by rw [baseSet_eq]; exact x.property)) (h x)
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

@[simp]
theorem neg_neg (o : OrientationLift I M ι) : - -o = o := by
  apply OrientationLift.ext (_root_.neg_neg o.modelOrientation)
  rfl

@[simp]
theorem flip_neg (o : OrientationLift I M ι) : (-o).flip = -o.flip := by
  apply OrientationLift.ext rfl
  rfl

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
end Manifold
