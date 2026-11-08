/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Coordinates
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Jet
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import Mathlib.Tactic.Module

/-!
# The quadratic metric jet in normal coordinates

For a normal coordinate field `X_w` along the radial geodesic `γ(t) = exp_p(t v)`,
its second covariant derivative at zero is `-R(w,v)v / 3`. Consequently the second
radial derivative of the normal-coordinate metric coefficient is
`-2 ⟪R(w,v)v,z⟫ / 3`. These are exact derivatives at the centre; they require no
completeness, unit vectors, or orthogonality hypotheses.

The calculation uses the radial Jacobi field `t X_w(γ(t))` and its initial third
covariant derivative `IsJacobiFieldOn.alongCurveWithin_three_of_eq_zero`, followed by
metric compatibility. Thus the curvature coefficient is obtained from the Jacobi equation.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 5 and 10
  (normal coordinates and Jacobi fields).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {U : Set (TangentSpace I p)}

namespace IsNormalDomain

/-- Smoothness of a normal coordinate field along a radial geodesic. -/
private theorem contMDiffOn_radialField (h : IsNormalDomain I M p U)
    (v w : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ ↦ TotalSpace.mk' E (riemannianExp I M p (t • v))
        (normalCoordinateField I M p U w (riemannianExp I M p (t • v))))
      {t | t • v ∈ U} := by
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentSpace I p) ∞ (fun t : ℝ ↦ t • v) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  exact (h.contMDiffOn_normalCoordinateField w).comp
    ((contMDiffOn_riemannianExp p).comp hlin.contMDiffOn
      (fun t ht ↦ h.subset_expDomain ht)) (fun t ht ↦ mem_image_of_mem _ ht)

omit [I.Boundaryless] [T2Space M] in
/-- Covariant differentiation of a smooth radial field, with no loss at infinite regularity. -/
private theorem contMDiffOn_radial_derivative (h : IsNormalDomain I M p U)
    (v : TangentSpace I p)
    (X : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v)))
    (hX : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t ↦ TotalSpace.mk' E (riemannianExp I M p (t • v)) (X t)) {t | t • v ∈ U}) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t ↦ TotalSpace.mk' E (riemannianExp I M p (t • v))
        (alongCurveWithin (leviCivitaConnection I M)
          (fun r : ℝ ↦ riemannianExp I M p (r • v)) X {r | r • v ∈ U} t))
      {t | t • v ∈ U} := by
  have hs : IsOpen {t : ℝ | t • v ∈ U} := h.isOpen.preimage (continuous_id.smul continuous_const)
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ : IsManifold I (∞ + 1 + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let _ : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact contMDiffOn_alongCurveWithin (n := ∞) (leviCivitaConnection I M) _ X
    (fun x ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection
      (m := ∞) (k := ∞) (trivializationAt E (TangentSpace I) x).open_baseSet
      (by simp) (by simp)) hs.uniqueDiffOn (by simpa using hX)

/-- The second covariant product rule for the radial normal coordinate field. -/
private theorem alongCurveWithin_two_radialField (h : IsNormalDomain I M p U)
    (v w : TangentSpace I p) {t : ℝ} (ht : t • v ∈ U) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let X := fun t ↦ normalCoordinateField I M p U w (γ t)
    let s := {t : ℝ | t • v ∈ U}
    let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
      alongCurveWithin (leviCivitaConnection I M) γ Y s
    D (D (fun r ↦ r • X r)) t = (2 : ℝ) • D X t + t • D (D X) t := by
  let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
  let X := fun t ↦ normalCoordinateField I M p U w (γ t)
  let s := {t : ℝ | t • v ∈ U}
  let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
    alongCurveWithin (leviCivitaConnection I M) γ Y s
  have hs : IsOpen s := h.isOpen.preimage (continuous_id.smul continuous_const)
  have hX := h.contMDiffOn_radialField v w
  have hDX := h.contMDiffOn_radial_derivative v X hX
  have hcoord (Y : ∀ t, TangentSpace I (γ t))
      (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t ↦ TotalSpace.mk' E (γ t) (Y t)) s) (t : ℝ) (ht : t ∈ s) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Y (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ Y ((hY t ht).mdifferentiableWithinAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hmul (Y : ∀ t, TangentSpace I (γ t))
      (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t ↦ TotalSpace.mk' E (γ t) (Y t)) s) (t : ℝ) (ht : t ∈ s) :
      D (fun r ↦ r • Y r) t = Y t + t • D Y t := by
    simpa only [D, id_eq, derivWithin_id _ _ (hs.uniqueDiffOn t ht), one_smul] using
      alongCurveWithin_smul (leviCivitaConnection I M) γ Y id s
        differentiableWithinAt_id (hcoord Y hY t ht)
  have hm := hmul X hX
  have hsmul : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ r • D X r) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact differentiableWithinAt_id.smul (hcoord (D X) hDX t ht)
  calc
    D (D (fun r ↦ r • X r)) t = D (fun r ↦ X r + r • D X r) t :=
      alongCurveWithin_congr (leviCivitaConnection I M) γ _
        (Filter.mem_of_superset self_mem_nhdsWithin (hm ·)) (hm t ht)
    _ = D X t + D (fun r ↦ r • D X r) t :=
      alongCurveWithin_add (leviCivitaConnection I M) γ _ _ s (hcoord X hX t ht) hsmul
    _ = _ := by rw [hmul (D X) hDX t ht, two_smul]; abel

/-- The radial Jacobi field is `t` times its normal coordinate field; differentiating
this product three times at zero gives three times the second derivative of the latter. -/
private theorem alongCurveWithin_three_radialField (h : IsNormalDomain I M p U)
    (v w : TangentSpace I p) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let X := fun t ↦ normalCoordinateField I M p U w (γ t)
    let s := {t : ℝ | t • v ∈ U}
    let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
      alongCurveWithin (leviCivitaConnection I M) γ Y s
    D (D (D (fun t ↦ t • X t))) 0 = (3 : ℝ) • D (D X) 0 := by
  let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
  let X := fun t ↦ normalCoordinateField I M p U w (γ t)
  let s := {t : ℝ | t • v ∈ U}
  let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
    alongCurveWithin (leviCivitaConnection I M) γ Y s
  have hs : IsOpen s := h.isOpen.preimage (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using h.zero_mem
  have hX := h.contMDiffOn_radialField v w
  have hDX := h.contMDiffOn_radial_derivative v X hX
  have hDDX := h.contMDiffOn_radial_derivative v (D X) hDX
  have hcoord (Y : ∀ t, TangentSpace I (γ t))
      (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t ↦ TotalSpace.mk' E (γ t) (Y t)) s) (t : ℝ) (ht : t ∈ s) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Y (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ Y ((hY t ht).mdifferentiableWithinAt (by simp))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hsecond (t : ℝ) (ht : t ∈ s) := h.alongCurveWithin_two_radialField v w ht
  have hsmul : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ r • D (D X) r) (γ 0)) s 0 := by
    rw [sectionCoord_smul]
    exact differentiableWithinAt_id.smul (hcoord (D (D X)) hDDX 0 h0)
  have hmul0 : D (fun r ↦ r • D (D X) r) 0 = D (D X) 0 := by
    simpa only [D, id_eq, derivWithin_id _ _ (hs.uniqueDiffOn 0 h0), one_smul, zero_smul,
      add_zero] using alongCurveWithin_smul (leviCivitaConnection I M) γ (D (D X)) id s
        differentiableWithinAt_id (hcoord (D (D X)) hDDX 0 h0)
  calc
    D (D (D (fun r ↦ r • X r))) 0 = D (fun r ↦ (2 : ℝ) • D X r + r • D (D X) r) 0 :=
      alongCurveWithin_congr (leviCivitaConnection I M) γ _
        (Filter.mem_of_superset self_mem_nhdsWithin (hsecond ·)) (hsecond 0 h0)
    _ = D (fun r ↦ (2 : ℝ) • D X r) 0 + D (fun r ↦ r • D (D X) r) 0 :=
      alongCurveWithin_add (leviCivitaConnection I M) γ _ _ s
        (by rw [sectionCoord_smul]; exact (hcoord (D X) hDX 0 h0).const_smul 2) hsmul
    _ = (2 : ℝ) • D (D X) 0 + D (fun r ↦ r • D (D X) r) 0 :=
      congrArg (· + D (fun r ↦ r • D (D X) r) 0)
        (alongCurveWithin_const_smul (leviCivitaConnection I M) γ (D X) 2 s 0)
    _ = _ := by rw [hmul0]; module

/-- The second radial covariant derivative of a normal coordinate field at its centre.
The parameter domain is the inverse image of the normal domain under `t ↦ t v`. -/
theorem alongCurveWithin_two_normalCoordinateField_zero (h : IsNormalDomain I M p U)
    (v w : TangentSpace I p) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let X := fun t ↦ normalCoordinateField I M p U w (γ t)
    let s := {t : ℝ | t • v ∈ U}
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ X s) s 0 =
        -(1 / 3 : ℝ) • (leviCivitaConnection I M).curvatureTensor p w v v := by
  dsimp only
  let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
  let X := fun t ↦ normalCoordinateField I M p U w (γ t)
  let s := {t : ℝ | t • v ∈ U}
  let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
    alongCurveWithin (leviCivitaConnection I M) γ Y s
  have hs : IsOpen s := h.isOpen.preimage (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using h.zero_mem
  have hthird := h.alongCurveWithin_three_radialField v w
  have hsub : s ⊆ geodesicInterval I M p v :=
    fun t ht ↦ mem_geodesicInterval_iff_smul_mem_expDomain.mpr (h.subset_expDomain ht)
  have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w).mono hs.uniqueDiffOn hsub
  have hJX : IsJacobiFieldOn I γ (fun r ↦ r • X r) s := hJ.congr fun t ht ↦ by
    exact (congrArg (t • ·) (h.normalCoordinateField_riemannianExp ht w)).trans
      ((mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).map_smul t w).symm
  have hj3 := hJX.alongCurveWithin_three_of_eq_zero h0 (by simp)
  have hcoord := differentiableWithinAt_sectionCoord γ X
    ((h.contMDiffOn_radialField v w 0 h0).mdifferentiableWithinAt (by simp))
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0))
  have hfirst : D (fun r ↦ r • X r) 0 = X 0 := by
    simpa only [D, id_eq, derivWithin_id _ _ (hs.uniqueDiffOn 0 h0), one_smul, zero_smul, add_zero]
      using alongCurveWithin_smul (leviCivitaConnection I M) γ X id s
        differentiableWithinAt_id hcoord
  have hscaled : (3 : ℝ) • D (D X) 0 =
      -(leviCivitaConnection I M).curvatureTensor (γ 0) (X 0)
        (curveVelocityWithin I γ s 0) (curveVelocityWithin I γ s 0) :=
    hthird.symm.trans (hj3.trans (congrArg
      (fun u ↦ -(leviCivitaConnection I M).curvatureTensor (γ 0) u
        (curveVelocityWithin I γ s 0) (curveVelocityWithin I γ s 0)) hfirst))
  have hγ0 : γ 0 = p :=
    (congrArg (riemannianExp I M p) (zero_smul ℝ v)).trans (riemannianExp_zero p)
  have hX0 : X 0 = w :=
    (congrArg (fun q ↦ (normalCoordinateField I M p U w q : E)) hγ0).trans
      (h.normalCoordinateField_self w)
  have hvel0 : curveVelocityWithin I γ s 0 = v := by
    rw [curveVelocityWithin_of_mem_nhds (hs.mem_nhds h0)]
    exact curveVelocity_riemannianExp_smul_zero p v
  have hcurv : (leviCivitaConnection I M).curvatureTensor (γ 0) (X 0)
      (curveVelocityWithin I γ s 0) (curveVelocityWithin I γ s 0) =
      (leviCivitaConnection I M).curvatureTensor p w v v := by
    rw [hX0, hvel0]
    exact congrArg (fun q ↦ ((leviCivitaConnection I M).curvatureTensor q w v v : E)) hγ0
  have hscaled' := hscaled.trans (congrArg Neg.neg hcurv)
  have hdiv := congrArg (fun u : E ↦ (1 / 3 : ℝ) • u) hscaled'
  have hleft : (1 / 3 : ℝ) • ((3 : ℝ) • (D (D X) 0 : E)) = D (D X) 0 := by module
  have hright : (1 / 3 : ℝ) • (-(leviCivitaConnection I M).curvatureTensor p w v v : E) =
      -(1 / 3 : ℝ) • (leviCivitaConnection I M).curvatureTensor p w v v := by module
  exact hleft.symm.trans (hdiv.trans hright)

/-- The first covariant radial derivative of a normal coordinate field vanishes at zero. -/
private theorem radialField_derivative_zero (h : IsNormalDomain I M p U)
    (v w : TangentSpace I p) :
    alongCurveWithin (leviCivitaConnection I M)
      (fun t : ℝ ↦ riemannianExp I M p (t • v))
      (fun t ↦ normalCoordinateField I M p U w (riemannianExp I M p (t • v)))
      {t : ℝ | t • v ∈ U} 0 = 0 := by
  have hs : IsOpen {t : ℝ | t • v ∈ U} := h.isOpen.preimage (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ {t : ℝ | t • v ∈ U} := by simpa using h.zero_mem
  have hγ := contMDiffAt_riemannianExp_smul_zero (I := I) p v
  have hX : MDiffAt (T% (normalCoordinateField I M p U w))
      (riemannianExp I M p ((0 : ℝ) • v)) := by
    simpa only [zero_smul, riemannianExp_zero] using
      h.mdifferentiableAt_normalCoordinateField w h.self_mem_image
  rw [alongCurveWithin_pullback_curveVelocityWithin _ _ _ (hs.uniqueDiffOn 0 h0)
    (hγ.mdifferentiableAt (by simp)).mdifferentiableWithinAt hX]
  have hγ0 : riemannianExp I M p ((0 : ℝ) • v) = p :=
    (congrArg (riemannianExp I M p) (zero_smul ℝ v)).trans (riemannianExp_zero p)
  refine (congrArg (fun q ↦ (leviCivitaConnection I M
    (normalCoordinateField I M p U w) q
      (curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
        {t : ℝ | t • v ∈ U} 0) : E)) hγ0).trans ?_
  exact DFunLike.congr_fun (h.leviCivitaConnection_normalCoordinateField_self w) _

/-- Twice differentiating a normal-coordinate metric coefficient; the first radial
covariant derivatives vanish at zero, leaving only the two second-derivative terms. -/
private theorem deriv_deriv_inner_radialField (h : IsNormalDomain I M p U)
    (v w z : TangentSpace I p) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let s := {t : ℝ | t • v ∈ U}
    let X := fun (u : TangentSpace I p) (t : ℝ) ↦ normalCoordinateField I M p U u (γ t)
    let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
      alongCurveWithin (leviCivitaConnection I M) γ Y s
    deriv (deriv (fun t ↦ inner ℝ (X w t) (X z t))) 0 =
      inner ℝ (D (D (X w)) 0) (X z 0) + inner ℝ (X w 0) (D (D (X z)) 0) := by
  dsimp only
  let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
  let s := {t : ℝ | t • v ∈ U}
  let X := fun (u : TangentSpace I p) (t : ℝ) ↦ normalCoordinateField I M p U u (γ t)
  let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
    alongCurveWithin (leviCivitaConnection I M) γ Y s
  let f := fun t ↦ inner ℝ (X w t) (X z t)
  have hs : IsOpen s := h.isOpen.preimage (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using h.zero_mem
  have hX (u : TangentSpace I p) := h.contMDiffOn_radialField v u
  have hDX (u : TangentSpace I p) := h.contMDiffOn_radial_derivative v (X u) (hX u)
  have hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s :=
    ((Bundle.contMDiff_proj (TangentSpace I) (IB := I) (n := ∞)).comp_contMDiffOn
      (hX w)).mdifferentiableOn (by simp)
  have hpair (Y Z : ∀ t, TangentSpace I (γ t))
      (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (Y t)) s)
      (hZ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ (fun t ↦ TotalSpace.mk' E (γ t) (Z t)) s)
      (t : ℝ) (ht : t ∈ s) :
      HasDerivWithinAt (fun r ↦ inner ℝ (Y r) (Z r))
        (inner ℝ (D Y t) (Z t) + inner ℝ (Y t) (D Z t)) s t :=
    (isMetricCompatible_leviCivitaConnection I).hasDerivWithinAt_inner_alongCurveWithin
      (hs.uniqueDiffOn t ht) (hγ t ht)
      (differentiableWithinAt_sectionCoord γ Y ((hY t ht).mdifferentiableWithinAt (by simp))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
      (differentiableWithinAt_sectionCoord γ Z ((hZ t ht).mdifferentiableWithinAt (by simp))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  have hfirst (t : ℝ) (ht : t ∈ s) : deriv f t =
      inner ℝ (D (X w) t) (X z t) + inner ℝ (X w t) (D (X z) t) := by
    rw [← derivWithin_of_isOpen hs ht]
    exact (hpair (X w) (X z) (hX w) (hX z) t ht).derivWithin (hs.uniqueDiffOn t ht)
  have hnear : deriv f =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦ inner ℝ (D (X w) t) (X z t) + inner ℝ (X w t) (D (X z) t) :=
    eventually_of_mem (hs.mem_nhds h0) hfirst
  have hsecond := ((hpair (D (X w)) (X z) (hDX w) (hX z) 0 h0).fun_add
    (hpair (X w) (D (X z)) (hX w) (hDX z) 0 h0)).hasDerivAt (hs.mem_nhds h0)
  rw [hnear.deriv_eq]
  rw [hsecond.deriv]
  have hDX0 (u : TangentSpace I p) : D (X u) 0 = 0 := h.radialField_derivative_zero v u
  rw [hDX0, hDX0]
  simp only [inner_zero_right, add_zero, zero_add]
  rfl

/-- The second radial derivative of a metric coefficient in normal coordinates.
This pins the quadratic coefficient to `-⟪R(w,v)v,z⟫ / 3`, with the curvature sign
for which the round unit sphere has positive sectional curvature. -/
theorem deriv_deriv_inner_normalCoordinateField_zero (h : IsNormalDomain I M p U)
    (v w z : TangentSpace I p) :
    deriv (deriv (fun t : ℝ ↦
      inner ℝ (normalCoordinateField I M p U w (riemannianExp I M p (t • v)))
        (normalCoordinateField I M p U z (riemannianExp I M p (t • v))))) 0 =
      -(2 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
  let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
  let s := {t : ℝ | t • v ∈ U}
  let X := fun (u : TangentSpace I p) (t : ℝ) ↦ normalCoordinateField I M p U u (γ t)
  let D := fun (Y : ∀ t, TangentSpace I (γ t)) ↦
    alongCurveWithin (leviCivitaConnection I M) γ Y s
  let f := fun t ↦ inner ℝ (X w t) (X z t)
  have hraw : deriv (deriv f) 0 =
      inner ℝ (D (D (X w)) 0) (X z 0) + inner ℝ (X w 0) (D (D (X z)) 0) :=
    h.deriv_deriv_inner_radialField v w z
  refine hraw.trans ?_
  have hγ0 : γ 0 = p :=
    (congrArg (riemannianExp I M p) (zero_smul ℝ v)).trans (riemannianExp_zero p)
  have hX0 (u : TangentSpace I p) : X u 0 = u :=
    (congrArg (fun q ↦ (normalCoordinateField I M p U u q : E)) hγ0).trans
      (h.normalCoordinateField_self u)
  have hDDX0 (u : TangentSpace I p) : D (D (X u)) 0 =
      -(1 / 3 : ℝ) • (leviCivitaConnection I M).curvatureTensor p u v v :=
    h.alongCurveWithin_two_normalCoordinateField_zero v u
  rw [hDDX0, hDDX0, hX0, hX0]
  have hinner (a b : E) :
      @inner ℝ (TangentSpace I (γ 0)) _ a b = @inner ℝ (TangentSpace I p) _ a b :=
    congrArg (fun q : M ↦ @inner ℝ (TangentSpace I q) _ a b) hγ0
  -- The input vectors use the canonical model carrier E of their tangent fibres;
  -- the explicit equality hinner transports the metric between the two base points.
  erw [hinner, hinner]
  simp only [real_inner_smul_left, real_inner_smul_right]
  have hcurv : inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z =
      inner ℝ w ((leviCivitaConnection I M).curvatureTensor p z v v) := by
    rw [(isMetricCompatible_leviCivitaConnection I).inner_curvatureTensor_swap_pairs
      (torsion_leviCivitaConnection_eq_zero I),
      (isMetricCompatible_leviCivitaConnection I).inner_curvatureTensor_eq_neg,
      curvatureTensor_antisymm]
    simp
  rw [← hcurv]
  ring

end IsNormalDomain

/-- The quadratic radial jet of the exponential pullback metric, on arbitrary tangent
vectors. This statement is independent of any choice of normal domain. -/
theorem deriv_deriv_inner_mfderiv_riemannianExp_zero (p : M) (v w z : TangentSpace I p) :
    deriv (deriv (fun t : ℝ ↦
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) z))) 0 =
      -(2 / 3 : ℝ) * inner ℝ ((leviCivitaConnection I M).curvatureTensor p w v v) z := by
  obtain ⟨r, hr, h⟩ := exists_isNormalDomain_ball (I := I) p
  have hnear : (fun t : ℝ ↦
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) z)) =ᶠ[𝓝 0]
      fun t ↦ inner ℝ
        (normalCoordinateField I M p (Metric.ball 0 r) w (riemannianExp I M p (t • v)))
        (normalCoordinateField I M p (Metric.ball 0 r) z (riemannianExp I M p (t • v))) := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t • v ∈ Metric.ball 0 r :=
      (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using Metric.ball_mem_nhds (0 : TangentSpace I p) hr)
    filter_upwards [ht] with t ht
    rw [h.normalCoordinateField_riemannianExp ht, h.normalCoordinateField_riemannianExp ht]
  exact hnear.deriv.deriv_eq.trans (h.deriv_deriv_inner_normalCoordinateField_zero v w z)

end TauCeti.Manifold
