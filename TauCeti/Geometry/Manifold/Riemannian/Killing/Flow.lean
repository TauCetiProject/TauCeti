/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Killing.LieDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Flow

/-!
# Metric conservation in variations and local flows of Killing fields

This file proves two metric-conservation results for a Killing vector field `X` on a `C¹`
Riemannian manifold:

1. **Variations through integral curves:** the transverse velocity `V(t) = ∂q F(0, t)` of a `C²`
   family of integral curves of `X` satisfies `D_t V = ∇_V X`, so its squared norm has derivative
   `2 ⟪∇_V X, V⟫ = 0` and transverse lengths are constant on each connected time interval
   (`IsKillingField.hasDerivAt_inner_variationField_self`,
   `IsKillingField.norm_variationField_eq`).
2. **Local flows act by local isometries:** since the Lie derivative of the metric along `X`
   vanishes (`IsKillingField.mlieDerivBilin_inner_eq_zero`), the pullback variation formula for
   covariant two-tensors (`mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero`) shows that
   `flowOf X t` preserves the metric tensor wherever `(t, x) ∈ flowDomain X`
   (`IsKillingField.mpullbackBilin_flowOf_inner_eq`), immediately yielding inner-product and norm
   preservation (`IsKillingField.inner_mfderiv_flowOf`, `IsKillingField.norm_mfderiv_flowOf`).

## References

* P. Petersen, *Riemannian Geometry*, third edition, Chapter 8
  (Killing fields and local isometries).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {X : Π x : M, TangentSpace I x} {F : ℝ → ℝ → M} {t : ℝ}

/-- In a family of integral curves of a Killing field, the squared length of the transverse
variation field has zero time derivative. -/
theorem IsKillingField.hasDerivAt_inner_variationField_self (h : IsKillingField I X)
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hcurve : ∀ᶠ q in 𝓝 0, curveVelocity I (F q) t = X (F q t)) :
    HasDerivAt (fun r ↦ inner ℝ (variationField I F r) (variationField I F r)) 0 t := by
  have hskew := h.inner_covariantDerivative_eq_neg (isMetricCompatible_leviCivitaConnection I)
    (torsion_leviCivitaConnection_eq_zero I) (F 0 t) (variationField I F t)
      (variationField I F t)
  have hz : 2 * inner ℝ (leviCivitaConnection I M X (F 0 t) (variationField I F t))
      (variationField I F t) = 0 := by
    linarith [real_inner_comm (variationField I F t)
      (leviCivitaConnection I M X (F 0 t) (variationField I F t))]
  have hcompat := isMetricCompatible_leviCivitaConnection (M := M) I
  have hp := hcompat.hasDerivAt_inner_curveVelocity_self_of_integralCurve
      ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)) hF
        (h.contMDiff.mdifferentiableAt (by simp)) hcurve
  simpa only [← variationField_apply, hz] using hp

/-- Transverse lengths in a family of integral curves of a Killing field are constant on
every open connected time domain on which the family is `C²` near its central trajectory. -/
theorem IsKillingField.norm_variationField_eq (h : IsKillingField I X)
    {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hF : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hcurve : ∀ t ∈ s, ∀ᶠ q in 𝓝 0, curveVelocity I (F q) t = X (F q t))
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖variationField I F a‖ = ‖variationField I F b‖ := by
  have hd (t : ℝ) (ht : t ∈ s) := h.hasDerivAt_inner_variationField_self (hF t ht) (hcurve t ht)
  have heq := hs.is_const_of_deriv_eq_zero hconn
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) ha hb
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    congrArg Real.sqrt heq

section Flow

variable [I.Boundaryless]

/-- **Local flows of Killing fields act by local isometries:** the maximal flow of a Killing field
pulls back the Riemannian metric to itself wherever `(t, x) ∈ flowDomain X`. -/
theorem IsKillingField.mpullbackBilin_flowOf_inner_eq (h : IsKillingField I X) {x : M}
    (hx : (t, x) ∈ flowDomain X) :
    mpullbackBilin I I (flowOf X t) RiemannianBundle.g.inner x = RiemannianBundle.g.inner x := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  exact mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero
    (h.contMDiff.of_le (by simp))
    (Bundle.mdifferentiable_riemannianBundle_inner (IB := I) (F := E) (V := TangentSpace I))
    h.mlieDerivBilin_inner_eq_zero hx

/-- The maximal flow of a Killing field preserves the Riemannian inner product on tangent
vectors at every point of its domain of existence. -/
@[simp] theorem IsKillingField.inner_mfderiv_flowOf (h : IsKillingField I X) {p : M}
    (ht : (t, p) ∈ flowDomain X) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I I (flowOf X t) p v) (mfderiv I I (flowOf X t) p w) = inner ℝ v w := by
  have heq := congr($(h.mpullbackBilin_flowOf_inner_eq ht) v w)
  rw [mpullbackBilin_apply] at heq
  -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
  exact heq

/-- The differential of the maximal flow of a Killing field preserves tangent norms wherever
that flow exists. No completeness of the vector field or the Riemannian metric is assumed. -/
@[simp] theorem IsKillingField.norm_mfderiv_flowOf (h : IsKillingField I X) {p : M}
    (ht : (t, p) ∈ flowDomain X) (v : TangentSpace I p) :
    ‖mfderiv I I (flowOf X t) p v‖ = ‖v‖ := by
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    congrArg Real.sqrt (h.inner_mfderiv_flowOf ht v v)

end Flow

end TauCeti.Manifold
