/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# Normal coordinates

Let `U` be a normal domain at a point `p` of a Riemannian manifold `M`.  The Riemannian logarithm
`log_p` identifies the normal neighbourhood `exp_p '' U` with the open subset `U` of the vector
space `T_p M`: these are *normal coordinates* centred at `p`, read without choosing a basis of
`T_p M`.  For `w ∈ T_p M`, the *normal coordinate field* `X_w` is the pullback by `log_p` of the
constant vector field `w`, so that at `exp_p v` it is `d(exp_p)_v w`.  Choosing a basis
`(e_i)` of `T_p M`, the fields `X_{e_i}` are the coordinate vector fields `∂_i` of the associated
normal coordinate chart.

The fields `X_w` depend linearly on `w`, are smooth on the normal neighbourhood, and take the
value `w` at the centre `p`.  Their characteristic property is that they are parallel at `p`:
`∇ X_w = 0` at `p` for the Levi-Civita connection.  In a basis, this is the classical statement
that **the Christoffel symbols of normal coordinates vanish at the centre**.  Two facts combine:

* the radial geodesic `t ↦ exp_p (t • w)` has velocity `X_w`, so `∇_w X_w = 0` at `p`;
* the parameter curves of the surface `(s, t) ↦ exp_p (s • w₁ + t • w₂)` have velocities `X_{w₁}`
  and `X_{w₂}`, so the symmetry lemma for the torsion-free Levi-Civita connection gives
  `∇_{w₁} X_{w₂} = ∇_{w₂} X_{w₁}` at `p`.

A symmetric bilinear form vanishing on the diagonal is zero.  By metric compatibility, the first
derivatives of the metric coefficients `⟪X_{w₁}, X_{w₂}⟫` vanish at `p` as well.

## Main definitions and results

* `TauCeti.Manifold.normalCoordinateField`: the normal coordinate field `X_w`.
* `TauCeti.Manifold.normalCoordinateField_add` and
  `TauCeti.Manifold.normalCoordinateField_smul`: `X_w` is linear in `w`.
* `TauCeti.Manifold.IsNormalDomain.normalCoordinateField_riemannianExp`: at `exp_p v`, the field
  `X_w` is `d(exp_p)_v w`.
* `TauCeti.Manifold.IsNormalDomain.normalCoordinateField_self`: at the centre, `X_w` is `w`.
* `TauCeti.Manifold.IsNormalDomain.contMDiffOn_normalCoordinateField`: `X_w` is smooth on the
  normal neighbourhood.
* `TauCeti.Manifold.IsNormalDomain.curveVelocity_riemannianExp_smul_eq_normalCoordinateField`: the
  radial geodesic in the direction `v` has velocity `X_v`.
* `TauCeti.Manifold.IsNormalDomain.leviCivitaConnection_normalCoordinateField_self`: the normal
  coordinate fields are parallel at the centre.
* `TauCeti.Manifold.IsNormalDomain.mfderiv_inner_normalCoordinateField_self`: the first
  derivatives of the metric coefficients in normal coordinates vanish at the centre.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Prop. 5.24.
-/

public section

open Bundle Manifold Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The **normal coordinate field** `X_w` of a tangent vector `w ∈ T_p M`, relative to a set `U`
of tangent vectors at `p`: the pullback by the Riemannian logarithm `log_p` of the constant vector
field `TauCeti.constVectorField w` on `T_p M`.  When `U` is a normal domain, its value at
`exp_p v` for `v ∈ U` is `d(exp_p)_v w`; for a basis `(e_i)` of `T_p M`, the fields `X_{e_i}` are
the coordinate vector fields of the normal coordinates defined by that basis.  Outside the normal
neighbourhood the field carries the junk values of `VectorField.mpullback`. -/
def normalCoordinateField (p : M) (U : Set (TangentSpace I p)) (w : TangentSpace I p) :
    Π q : M, TangentSpace I q :=
  mpullback I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) (constVectorField w)

variable {p : M} {U : Set (TangentSpace I p)} {v w w₁ w₂ : TangentSpace I p}

/-- The normal coordinate field of `w` is the pullback of the constant field `w` by the
logarithm. -/
theorem normalCoordinateField_def (p : M) (U : Set (TangentSpace I p)) (w : TangentSpace I p) :
    normalCoordinateField I M p U w =
      mpullback I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) (constVectorField w) :=
  (rfl)

/-- The normal coordinate field is additive in the tangent vector. -/
theorem normalCoordinateField_add (w₁ w₂ : TangentSpace I p) :
    normalCoordinateField I M p U (w₁ + w₂) =
      normalCoordinateField I M p U w₁ + normalCoordinateField I M p U w₂ := by
  funext q
  simp [normalCoordinateField_def, mpullback_apply, constVectorField_apply]

/-- The normal coordinate field is homogeneous in the tangent vector. -/
theorem normalCoordinateField_smul (c : ℝ) (w : TangentSpace I p) :
    normalCoordinateField I M p U (c • w) = c • normalCoordinateField I M p U w := by
  funext q
  simp [normalCoordinateField_def, mpullback_apply, constVectorField_apply]

variable [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

/-- **The normal coordinate field at `exp_p v`** is the differential of the exponential map at `v`
applied to `w`. -/
@[simp] theorem normalCoordinateField_riemannianExp (h : IsNormalDomain I M p U) (hv : v ∈ U)
    (w : TangentSpace I p) :
    normalCoordinateField I M p U w (riemannianExp I M p v) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w := by
  rw [normalCoordinateField_def, mpullback_apply, constVectorField_apply]
  -- `fromTangentSpace` is the identity of `T_p M`, so the inverse of `d(log_p)` evaluated at the
  -- constant field is `d(exp_p)_v w`
  exact DFunLike.congr_fun (ContinuousLinearMap.inverse_eq
    (h.mfderiv_riemannianLog_comp_mfderiv_riemannianExp hv)
    (h.mfderiv_riemannianExp_comp_mfderiv_riemannianLog hv)) _

/-- **The normal coordinate field at the centre** `p` is the tangent vector it is defined by. -/
@[simp] theorem normalCoordinateField_self (h : IsNormalDomain I M p U) (w : TangentSpace I p) :
    normalCoordinateField I M p U w p = w := by
  have h0 := h.normalCoordinateField_riemannianExp h.zero_mem w
  rwa [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at h0

/-- **The normal coordinate fields are smooth** on the normal neighbourhood. -/
theorem contMDiffOn_normalCoordinateField (h : IsNormalDomain I M p U) (w : TangentSpace I p) :
    CMDiff[riemannianExp I M p '' U] ∞ (T% (normalCoordinateField I M p U w)) := by
  intro q hq
  exact (ContMDiffAt.mpullback_vectorField_preimage (contMDiff_constVectorField w _)
    (h.contMDiffOn_riemannianLog.contMDiffAt (h.isOpen_image.mem_nhds hq))
    (h.isInvertible_mfderiv_riemannianLog hq) (by simp)).contMDiffWithinAt

/-- The normal coordinate fields are differentiable at every point of the normal
neighbourhood. -/
theorem mdifferentiableAt_normalCoordinateField (h : IsNormalDomain I M p U)
    (w : TangentSpace I p) {q : M} (hq : q ∈ riemannianExp I M p '' U) :
    MDiffAt (T% (normalCoordinateField I M p U w)) q :=
  ((h.contMDiffOn_normalCoordinateField w).contMDiffAt
    (h.isOpen_image.mem_nhds hq)).mdifferentiableAt (by simp)

/-- **The coordinate lines of normal coordinates.**  The curve `s ↦ exp_p (v + s • w)` has the
normal coordinate field `X_w` as its velocity, as long as it stays in the normal domain. -/
theorem curveVelocity_riemannianExp_add_smul_eq_normalCoordinateField
    (h : IsNormalDomain I M p U) {u : ℝ} (hu : v + u • w ∈ U) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (v + s • w)) u =
      normalCoordinateField I M p U w (riemannianExp I M p (v + u • w)) := by
  rw [curveVelocity_riemannianExp_add_smul (h.subset_expDomain hu),
    h.normalCoordinateField_riemannianExp hu]

/-- **Radial geodesics in normal coordinates.**  The radial geodesic `s ↦ exp_p (s • v)` has the
normal coordinate field `X_v` as its velocity, as long as it stays in the normal domain. -/
theorem curveVelocity_riemannianExp_smul_eq_normalCoordinateField
    (h : IsNormalDomain I M p U) {t : ℝ} (ht : t • v ∈ U) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t =
      normalCoordinateField I M p U v (riemannianExp I M p (t • v)) := by
  rw [curveVelocity_riemannianExp_smul (h.subset_expDomain ht),
    h.normalCoordinateField_riemannianExp ht]

omit [I.Boundaryless] [T2Space M] in
/-- A path in `T_p M` through the origin stays in the normal domain near the origin. -/
private theorem eventually_mem (h : IsNormalDomain I M p U) {c : ℝ → TangentSpace I p}
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ U :=
  hc.preimage_mem_nhds (by rw [hc0]; exact h.isOpen.mem_nhds h.zero_mem)

open CovariantDerivative

/-- The covariant derivative at `p` of a vector field in the direction `a` is its derivative along
the exponential image of a path in `T_p M` leaving the origin with velocity `a`. -/
private theorem leviCivitaConnection_apply_eq_alongCurve {X : Π q : M, TangentSpace I q}
    (hX : MDiffAt (T% X) p) {c : ℝ → TangentSpace I p} {a : TangentSpace I p} (hc0 : c 0 = 0)
    (hc : HasDerivAt c a 0) :
    leviCivitaConnection I M X p a =
      alongCurve (leviCivitaConnection I M) (fun s ↦ riemannianExp I M p (c s))
        (fun s ↦ X (riemannianExp I M p (c s))) 0 := by
  have hdom : c 0 ∈ expDomain I M p := by rw [hc0]; exact zero_mem_expDomain p
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ riemannianExp I M p (c s)) 0 :=
    ((contMDiffAt_riemannianExp hdom).mdifferentiableAt (by simp)).comp (0 : ℝ)
      (mdifferentiableAt_iff_differentiableAt.2 hc.differentiableAt)
  have hvel : curveVelocity I (fun s ↦ riemannianExp I M p (c s)) 0 = a := by
    rw [← Function.comp_def, curveVelocity_riemannianExp_comp hc hdom]
    -- `mfderiv_congr_point` moves the base point of the differential from `c 0` to `0`
    exact (DFunLike.congr_fun (mfderiv_congr_point (I := 𝓘(ℝ, TangentSpace I p)) (I' := I)
      (f := riemannianExp I M p) hc0) a).trans (mfderiv_riemannianExp_apply_zero p a)
  have hγ0 : riemannianExp I M p (c 0) = p := by rw [hc0, riemannianExp_zero]
  have hX' : MDiffAt (T% X) (riemannianExp I M p (c 0)) := by rwa [hγ0]
  rw [alongCurve_pullback (leviCivitaConnection I M) _ X (hasMFDerivAt_curveVelocity hγ) hX',
    hvel]
  -- the two sides differ only by the base point `exp_p (c 0) = p` of the covariant derivative
  exact congrArg (β := E) (fun x ↦ leviCivitaConnection I M X x a) hγ0.symm

/-- The normal coordinate field `X_w` has vanishing covariant derivative at `p` in the direction
`w`: along the radial geodesic in the direction `w` it is the velocity, whose covariant
acceleration vanishes. -/
private theorem leviCivitaConnection_normalCoordinateField_apply_self
    (h : IsNormalDomain I M p U) (w : TangentSpace I p) :
    leviCivitaConnection I M (normalCoordinateField I M p U w) p w = 0 := by
  have hc : HasDerivAt (fun s : ℝ ↦ s • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  rw [leviCivitaConnection_apply_eq_alongCurve (h.mdifferentiableAt_normalCoordinateField w
    h.self_mem_image) (zero_smul ℝ w) hc]
  have hfield : ∀ᶠ s in 𝓝 (0 : ℝ),
      normalCoordinateField I M p U w (riemannianExp I M p (s • w)) =
        curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • w)) s := by
    filter_upwards [h.eventually_mem hc.continuousAt (zero_smul ℝ w)] with s hs
    exact (h.curveVelocity_riemannianExp_smul_eq_normalCoordinateField hs).symm
  rw [alongCurve_congr _ _ _ hfield, ← acceleration_def,
    show (fun s : ℝ ↦ riemannianExp I M p (s • w)) = maximalGeodesic I M p w from
      funext (riemannianExp_smul p w)]
  exact ((isGeodesicCurveOn_iff_of_isOpen isOpen_geodesicInterval).1
    (isGeodesicCurveOnFrom_maximalGeodesic p w).isGeodesicCurveOn).2 0 zero_mem_geodesicInterval

/-- The covariant derivatives at `p` of the normal coordinate fields are symmetric:
`∇_{w₁} X_{w₂} = ∇_{w₂} X_{w₁}`.  This is the symmetry lemma for the surface
`(s, t) ↦ exp_p (s • w₁ + t • w₂)`, whose parameter curves have the normal coordinate fields as
velocities. -/
private theorem leviCivitaConnection_normalCoordinateField_apply_comm
    (h : IsNormalDomain I M p U) (w₁ w₂ : TangentSpace I p) :
    leviCivitaConnection I M (normalCoordinateField I M p U w₂) p w₁ =
      leviCivitaConnection I M (normalCoordinateField I M p U w₁) p w₂ := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      ((0 : ℝ × ℝ).1 • w₁ + (0 : ℝ × ℝ).2 • w₂) := by
    simpa using contMDiffAt_riemannianExp (I := I) (zero_mem_expDomain p)
  have hlin : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, TangentSpace I p) ∞
      (fun z : ℝ × ℝ ↦ z.1 • w₁ + z.2 • w₂) 0 :=
    (contMDiff_iff_contDiff.2
      ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const))).contMDiffAt
  have hswap := alongCurve_curveVelocity_comm (leviCivitaConnection I M)
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (f := fun s t ↦ riemannianExp I M p (s • w₁ + t • w₂)) (u := 0) (v := 0)
    ((hexp.comp 0 hlin).of_le (by simp))
  have hc₁ : HasDerivAt (fun s : ℝ ↦ s • w₁ + (0 : ℝ) • w₂) w₁ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w₁
  have hc₂ : HasDerivAt (fun t : ℝ ↦ (0 : ℝ) • w₁ + t • w₂) w₂ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w₂
  rw [leviCivitaConnection_apply_eq_alongCurve (h.mdifferentiableAt_normalCoordinateField w₂
      h.self_mem_image) (by simp) hc₁,
    leviCivitaConnection_apply_eq_alongCurve (h.mdifferentiableAt_normalCoordinateField w₁
      h.self_mem_image) (by simp) hc₂]
  have hfield₁ : ∀ᶠ s in 𝓝 (0 : ℝ),
      normalCoordinateField I M p U w₂ (riemannianExp I M p (s • w₁ + (0 : ℝ) • w₂)) =
        curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (s • w₁ + t • w₂)) 0 := by
    filter_upwards [h.eventually_mem hc₁.continuousAt (by simp)] with s hs
    exact (h.curveVelocity_riemannianExp_add_smul_eq_normalCoordinateField hs).symm
  have hfield₂ : ∀ᶠ t in 𝓝 (0 : ℝ),
      normalCoordinateField I M p U w₁ (riemannianExp I M p ((0 : ℝ) • w₁ + t • w₂)) =
        curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • w₁ + t • w₂)) 0 := by
    filter_upwards [h.eventually_mem hc₂.continuousAt (by simp)] with t ht
    have hd : HasDerivAt (fun s : ℝ ↦ s • w₁ + t • w₂) w₁ 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const w₁).add_const _ |>.congr_deriv (one_smul ℝ w₁)
    rw [← Function.comp_def, curveVelocity_riemannianExp_comp hd (h.subset_expDomain ht),
      h.normalCoordinateField_riemannianExp ht]
  rw [alongCurve_congr _ _ _ hfield₁, alongCurve_congr _ _ _ hfield₂]
  exact hswap.symm

/-- **The Christoffel symbols of normal coordinates vanish at the centre.**  Every normal
coordinate field is parallel at `p`: its covariant derivative there vanishes in every direction.
For a basis `(e_i)` of `T_p M` this says `∇_{∂_i} ∂_j = 0` at `p` for the coordinate vector fields
`∂_i = X_{e_i}` of the corresponding normal coordinates. -/
theorem leviCivitaConnection_normalCoordinateField_self (h : IsNormalDomain I M p U)
    (w : TangentSpace I p) :
    leviCivitaConnection I M (normalCoordinateField I M p U w) p = 0 := by
  ext a
  -- polarize the vanishing of `∇_a X_a` using the symmetry of `∇_a X_b` in `a` and `b`
  have hd := h.leviCivitaConnection_normalCoordinateField_apply_self (a + w)
  rw [normalCoordinateField_add, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      (h.mdifferentiableAt_normalCoordinateField a h.self_mem_image)
      (h.mdifferentiableAt_normalCoordinateField w h.self_mem_image),
    add_apply, map_add, map_add,
    h.leviCivitaConnection_normalCoordinateField_apply_self a,
    h.leviCivitaConnection_normalCoordinateField_apply_self w,
    h.leviCivitaConnection_normalCoordinateField_apply_comm w a] at hd
  rw [zero_apply]
  have h2 : (2 : ℝ) • leviCivitaConnection I M (normalCoordinateField I M p U w) p a = 0 := by
    rw [two_smul]
    simpa using hd
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **The metric coefficients of normal coordinates are stationary at the centre.**  The first
derivatives of `q ↦ ⟪X_{w₁} q, X_{w₂} q⟫` vanish at `p`; at `p` itself this function takes the
value `⟪w₁, w₂⟫` by `normalCoordinateField_self`. -/
theorem mfderiv_inner_normalCoordinateField_self (h : IsNormalDomain I M p U)
    (w₁ w₂ : TangentSpace I p) :
    mfderiv I 𝓘(ℝ, ℝ)
      (fun q ↦ inner ℝ (normalCoordinateField I M p U w₁ q) (normalCoordinateField I M p U w₂ q))
      p = 0 := by
  ext a
  have hcompat := (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).mvfderiv_inner_eq
    (FiberBundle.extend E a) (h.mdifferentiableAt_normalCoordinateField w₁ h.self_mem_image)
    (h.mdifferentiableAt_normalCoordinateField w₂ h.self_mem_image)
  simp only [FiberBundle.extend_apply_self, h.leviCivitaConnection_normalCoordinateField_self,
    zero_apply, inner_zero_left, inner_zero_right, add_zero] at hcompat
  exact hcompat

end IsNormalDomain

end TauCeti.Manifold

end
