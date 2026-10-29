/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# The positive orientation of the circle `AddCircle p`

For a positive real `p`, the charts of the circle `AddCircle p = ℝ ⧸ pℤ` are local real lifts,
and two local lifts differ near each point by a fixed integer multiple of `p`. The coordinate
changes of the atlas are therefore translations of `ℝ`, with derivative `1`, so the atlas of
`AddCircle p` is an oriented atlas (`AddCircle.instHasGroupoidOrientationPreservingGroupoid`,
together with `TauCeti.isOrientedAtlas_atlas`), in which the real time direction is positive.

The time form `dt_p` vanishes nowhere, so it determines an orientation `AddCircle.orientation p`:
a tangent basis is positive exactly when `dt_p` is positive on it. Read through the local real
lifts, this is the orientation of `ℝ` in which `1` is positive, so it is the orientation of the
oriented atlas (`AddCircle.orientation_eq_isOrientedAtlas_orientation`).

The maps of the circle that the rest of the circle API constructs behave as expected for this
orientation. The quotient map `ℝ → AddCircle p`, the charts, the translations and the rescalings
`AddCircle p ≃ AddCircle q` preserve orientation; multiplication by an integer `k` preserves it
when `k > 0` and reverses it when `k < 0`, and negation reverses it. All of these follow from
`AddCircle.isOrientationPreservingAt_of_mfderiv_eq_smul` and its reversing counterpart: a map of
circles whose derivative is multiplication by a positive (negative) real number preserves
(reverses) orientation.

## Main declarations

* `AddCircle.instHasGroupoidOrientationPreservingGroupoid`: the coordinate changes of
  `AddCircle p` preserve orientation.
* `AddCircle.orientation p`: the orientation of `AddCircle p` on which `dt_p` is positive.
* `AddCircle.orientation_eq_orientationAt_orientation_iff`, `AddCircle.orientationAt_orientation`:
  its tangent orientations.
* `AddCircle.orientation_eq_isOrientedAtlas_orientation`: it is the orientation of the atlas.
* `AddCircle.isOrientationPreservingAt_coe`, `AddCircle.isOrientationPreservingAt_of_mem_atlas`:
  the quotient map and the charts are orientation preserving for the standard orientation of `ℝ`.
* `AddCircle.isOrientationPreservingAt_add_right`, `AddCircle.isOrientationPreservingAt_zsmul`,
  `AddCircle.isOrientationReversingAt_zsmul`, `AddCircle.isOrientationReversingAt_neg`,
  `AddCircle.isOrientationPreservingAt_diffeomorphAddCircle`: translations, integer
  multiplications, negation and rescalings.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (orientations, oriented atlases and orientations
  from nonvanishing top forms).
-/

public section

noncomputable section

open Set Filter TauCeti TauCeti.Manifold.Orientation
open scoped Manifold Topology ContDiff

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-! ### The oriented atlas -/

variable {p} in
/-- The coordinate change between two local real lifts of `AddCircle p` preserves orientation:
near each point of its domain it is a translation of `ℝ`. -/
private theorem orientationPreservingOn_symm_trans {c c' : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : ∀ x ∈ c.source, (c x : AddCircle p) = x)
    (hc' : ∀ x ∈ c'.source, (c' x : AddCircle p) = x) :
    OrientationPreservingOn 𝓘(ℝ) (c.symm ≫ₕ c') (c.symm ≫ₕ c').source := by
  rw [orientationPreservingOn_iff]
  intro u hu
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.symm_source] at hu
  obtain ⟨k, hk⟩ := exists_eventuallyEq_add_zsmul hc hc' (c.map_target hu.1) hu.2
  have heq : ⇑(c.symm ≫ₕ c') =ᶠ[𝓝 u] fun v ↦ v + k • p := by
    filter_upwards [hk.comp_tendsto (c.continuousAt_symm hu.1), c.open_target.mem_nhds hu.1]
      with v hv hv'
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at hv ⊢
    rw [hv, c.right_inv hv']
  have hd : HasFDerivAt (c.symm ≫ₕ c') (ContinuousLinearMap.id ℝ ℝ) u :=
    ((hasFDerivAt_id u).add_const (k • p)).congr_of_eventuallyEq heq
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, range_id, id_eq, fderivWithin_univ, differentiableWithinAt_univ, hd.fderiv,
    ContinuousLinearMap.coe_id, LinearMap.det_id]
  exact ⟨hd.differentiableAt, one_pos⟩

/-- The coordinate changes of `AddCircle p` preserve orientation: its charts are local real lifts,
which differ from each other near each point by a translation. -/
instance instHasGroupoidOrientationPreservingGroupoid :
    HasGroupoid (AddCircle p) (orientationPreservingGroupoid 𝓘(ℝ)) where
  compatible {c c'} hc hc' := by
    have hl := fun x (hx : x ∈ c.source) ↦ coe_apply_of_mem_atlas hc hx
    have hl' := fun x (hx : x ∈ c'.source) ↦ coe_apply_of_mem_atlas hc' hx
    refine mem_orientationPreservingGroupoid_iff.mpr ⟨orientationPreservingOn_symm_trans hl hl', ?_⟩
    -- The inverse coordinate change is the coordinate change in the other direction.
    rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact orientationPreservingOn_symm_trans hl' hl

/-- The circle `AddCircle p` is orientable. -/
instance instOrientable : Orientable 𝓘(ℝ) (AddCircle p) :=
  Orientable.of_hasGroupoid

/-! ### The orientation of the time form -/

/-- The **positive orientation** of `AddCircle p`: the orientation on which the nowhere-vanishing
time form `dt_p` is positive. -/
protected def orientation : Manifold.Orientation 𝓘(ℝ) (AddCircle p) (Fin 1) :=
  Manifold.Orientation.ofTopForm (Module.finrank_self ℝ) (timeForm p).1
    ((timeForm p).isSmoothForm.of_le zero_le) (timeForm_apply_ne_zero p)

/-- A tangent basis of `AddCircle p` is positive for `AddCircle.orientation p` exactly when the
time form is positive on it. -/
theorem orientation_eq_orientationAt_orientation_iff {x : AddCircle p}
    (b : Module.Basis (Fin 1) ℝ (TangentSpace 𝓘(ℝ) x)) :
    b.orientation = (AddCircle.orientation p).orientationAt x ↔ 0 < (timeForm p).1 x b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

/-- At every point of `AddCircle p`, whose tangent spaces are read as `ℝ` through the local real
lifts, the positive orientation is the orientation of `ℝ` in which `1` is positive. -/
@[simp]
theorem orientationAt_orientation (x : AddCircle p) :
    (AddCircle.orientation p).orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation := by
  refine ((orientation_eq_orientationAt_orientation_iff p _).mpr ?_).symm
  -- The time form sends the tangent vector `1` to `1`.
  rw [timeForm_apply]
  exact one_pos.trans_eq (Module.Basis.singleton_apply (Fin 1) ℝ 0).symm

/-- The positive orientation of `AddCircle p` is the orientation of its oriented atlas, in which
every chart carries the tangent orientation to the orientation of `ℝ` in which `1` is
positive. -/
theorem orientation_eq_isOrientedAtlas_orientation {n : ℕ∞ω} [NeZero n] :
    AddCircle.orientation p =
      (isOrientedAtlas_atlas 𝓘(ℝ) n (AddCircle p)).orientation
        (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp) := by
  ext x
  obtain ⟨L, hL, hmap⟩ := (isOrientedAtlas_atlas 𝓘(ℝ) n (AddCircle p)).orientation_spec
    (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp) (chart_mem_atlas ℝ x)
    (mem_chart_source ℝ x)
  -- The chart at `x` is a local real lift, so its derivative `L` is the identity.
  have hL' (v : TangentSpace 𝓘(ℝ) x) : L v = v := DFunLike.congr_fun (hL.trans
    (mfderiv_of_coe_apply (fun y hy ↦ coe_apply_of_mem_atlas (chart_mem_atlas ℝ x) hy)
      (mem_chart_source ℝ x))) v
  -- Read back through `L`, the atlas orientation at `x` is that of the basis `L⁻¹ 1`.
  rw [← Equiv.eq_symm_apply, Orientation.map_symm, ← Module.Basis.orientation_map] at hmap
  rw [hmap]
  refine ((orientation_eq_orientationAt_orientation_iff p _).mpr ?_).symm
  rw [timeForm_apply, Module.Basis.map_apply]
  -- Tangent vectors at `x` are real numbers, and `L⁻¹ 1 = 1`.
  exact one_pos.trans_eq ((L.toLinearEquiv.symm_apply_eq.mpr (hL' _).symm).trans
    (Module.Basis.singleton_apply (Fin 1) ℝ 0)).symm

/-! ### Orientation behaviour of maps -/

section Maps

/-- Multiplication by a nonzero real number on `ℝ` has determinant that number. -/
private theorem det_smulOfNeZero {c : ℝ} (hc : c ≠ 0) :
    LinearMap.det (LinearEquiv.smulOfNeZero ℝ ℝ c hc : ℝ →ₗ[ℝ] ℝ) = c := by
  have h : (LinearEquiv.smulOfNeZero ℝ ℝ c hc : ℝ →ₗ[ℝ] ℝ) = c • LinearMap.id :=
    LinearMap.ext fun _ ↦ rfl
  rw [h, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold 𝓘(ℝ) 1 M]
  [TopologicalSpace M'] [ChartedSpace ℝ M'] [IsManifold 𝓘(ℝ) 1 M']

omit [Fact (0 < p)] in
/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
positive real number preserves orientation at `x`. -/
private theorem isOrientationPreservingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) M (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) M' (Fin 1)}
    {f : M → M'} {x : M} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : 0 < c) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationPreservingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationPreservingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne').toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (Orientation.map_eq_iff_det_pos _ _ (by simp)).mpr ?_
  -- The tangent spaces are `ℝ`, on which the derivative is `smulOfNeZero`, of determinant `c`.
  exact hc.trans_eq (det_smulOfNeZero _).symm

omit [Fact (0 < p)] in
/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
negative real number reverses orientation at `x`. -/
private theorem isOrientationReversingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) M (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) M' (Fin 1)}
    {f : M → M'} {x : M} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : c < 0) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationReversingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationReversingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne).toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr ?_
  -- The tangent spaces are `ℝ`, on which the derivative is `smulOfNeZero`, of determinant `c`.
  exact (det_smulOfNeZero _).trans_lt hc

end Maps

variable {p} {q : ℝ} [Fact (0 < q)]

/-- A map of circles whose derivative at `x` is multiplication by a positive real number preserves
the positive orientations at `x`. -/
theorem isOrientationPreservingAt_of_mfderiv_eq_smul {f : AddCircle p → AddCircle q}
    {x : AddCircle p} {c : ℝ} (hc : 0 < c)
    (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationPreservingAt (AddCircle.orientation p) (AddCircle.orientation q) f x :=
  isOrientationPreservingAt_of_orientationAt_eq (orientationAt_orientation p x)
    (orientationAt_orientation q (f x)) hc hf

/-- A map of circles whose derivative at `x` is multiplication by a negative real number reverses
the positive orientations at `x`. -/
theorem isOrientationReversingAt_of_mfderiv_eq_smul {f : AddCircle p → AddCircle q}
    {x : AddCircle p} {c : ℝ} (hc : c < 0)
    (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationReversingAt (AddCircle.orientation p) (AddCircle.orientation q) f x :=
  isOrientationReversingAt_of_orientationAt_eq (orientationAt_orientation p x)
    (orientationAt_orientation q (f x)) hc hf

variable (p)

/-- The quotient map `ℝ → AddCircle p` preserves orientation, for the standard orientation of `ℝ`
in which `1` is positive. -/
theorem isOrientationPreservingAt_coe (t : ℝ) :
    IsOrientationPreservingAt
      (Manifold.Orientation.model (I := 𝓘(ℝ)) (Module.Basis.singleton (Fin 1) ℝ).orientation
        (by simp))
      (AddCircle.orientation p) ((↑) : ℝ → AddCircle p) t :=
  isOrientationPreservingAt_of_orientationAt_eq (Manifold.Orientation.orientationAt_model _ _ t)
    (orientationAt_orientation p t) one_pos ((mfderiv_coe p t).trans (one_smul ℝ _).symm)

variable {p} in
/-- Every chart of `AddCircle p` preserves orientation, from the positive orientation of
`AddCircle p` to the standard orientation of `ℝ` in which `1` is positive. -/
theorem isOrientationPreservingAt_of_mem_atlas {c : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : c ∈ atlas ℝ (AddCircle p)) {x : AddCircle p} (hx : x ∈ c.source) :
    IsOrientationPreservingAt (AddCircle.orientation p)
      (Manifold.Orientation.model (I := 𝓘(ℝ)) (Module.Basis.singleton (Fin 1) ℝ).orientation
        (by simp)) c x :=
  isOrientationPreservingAt_of_orientationAt_eq (orientationAt_orientation p x)
    (Manifold.Orientation.orientationAt_model _ _ (c x)) one_pos
    ((mfderiv_of_coe_apply (fun _ hy ↦ coe_apply_of_mem_atlas hc hy) hx).trans
      (one_smul ℝ _).symm)

/-- Every translation of `AddCircle p` preserves orientation. -/
theorem isOrientationPreservingAt_add_right (a x : AddCircle p) :
    IsOrientationPreservingAt (AddCircle.orientation p) (AddCircle.orientation p) (· + a) x :=
  isOrientationPreservingAt_of_mfderiv_eq_smul one_pos
    ((mfderiv_add_right p a x).trans (one_smul ℝ _).symm)

/-- Multiplication by a positive integer preserves the orientation of `AddCircle p`. -/
theorem isOrientationPreservingAt_zsmul {k : ℤ} (hk : 0 < k) (x : AddCircle p) :
    IsOrientationPreservingAt (AddCircle.orientation p) (AddCircle.orientation p)
      (fun y ↦ k • y) x :=
  isOrientationPreservingAt_of_mfderiv_eq_smul (Int.cast_pos.mpr hk)
    ((mfderiv_zsmul p k x).trans (Int.cast_smul_eq_zsmul ℝ k _).symm)

/-- Multiplication by a negative integer reverses the orientation of `AddCircle p`. -/
theorem isOrientationReversingAt_zsmul {k : ℤ} (hk : k < 0) (x : AddCircle p) :
    IsOrientationReversingAt (AddCircle.orientation p) (AddCircle.orientation p)
      (fun y ↦ k • y) x :=
  isOrientationReversingAt_of_mfderiv_eq_smul (Int.cast_lt_zero.mpr hk)
    ((mfderiv_zsmul p k x).trans (Int.cast_smul_eq_zsmul ℝ k _).symm)

/-- Negation reverses the orientation of `AddCircle p`. -/
theorem isOrientationReversingAt_neg (x : AddCircle p) :
    IsOrientationReversingAt (AddCircle.orientation p) (AddCircle.orientation p)
      (fun y ↦ -y) x := by
  simpa only [neg_one_zsmul] using isOrientationReversingAt_zsmul p (k := -1) (by norm_num) x

variable (q) in
/-- The rescaling `AddCircle p ≃ AddCircle q` preserves the positive orientations. -/
theorem isOrientationPreservingAt_diffeomorphAddCircle (n : ℕ∞ω) (x : AddCircle p) :
    IsOrientationPreservingAt (AddCircle.orientation p) (AddCircle.orientation q)
      (diffeomorphAddCircle p q n) x :=
  isOrientationPreservingAt_of_mfderiv_eq_smul
    (mul_pos (inv_pos.mpr (Fact.out : 0 < p)) (Fact.out : 0 < q))
    (mfderiv_diffeomorphAddCircle p q n x)

end AddCircle
