/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Norm comparison for Jacobi fields in nonpositive curvature

The norm, rather than just the squared norm, of a Jacobi field is convex when sectional
curvature is nonpositive. At a zero of the field the norm need not be differentiable.
Regularizing it by `sqrt (|J|² + ε)` gives convex functions even across such zeros.
Their limit gives `IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos`.
Applied to the radial Jacobi field `J(t) = d(exp_p)_(tv)(tw)`, convexity and `J(0) = 0`
show that `|J(t)| / t` cannot decrease for positive time. Continuity of `d(exp_p)` at the
origin then gives `norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`:
`|d(exp_p)_v(w)| ≥ |w|` on the natural exponential domain.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–12 (Jacobi comparison and the Cartan–Hadamard theorem).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold InnerProductSpace Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ}

private theorem IsJacobiFieldOn.hasDerivWithinAt_regularized_norm
    (h : IsJacobiFieldOn I γ V s) {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ Real.sqrt (‖V r‖ ^ 2 + ε))
      (⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ /
        Real.sqrt (‖V t‖ ^ 2 + ε)) s t := by
  convert ((h.hasDerivWithinAt_norm_sq ht).add_const ε).sqrt
    (ne_of_gt (by positivity)) using 1
  ring

private theorem IsJacobiFieldOn.convexOn_regularized_norm
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ s (fun r ↦ Real.sqrt (‖V r‖ ^ 2 + ε)) := by
  let A (r : ℝ) := ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ
  let B (r : ℝ) := ‖alongCurveWithin (leviCivitaConnection I M) γ V s r‖ ^ 2 -
    ⟪(leviCivitaConnection I M).curvatureTensor (γ r) (V r)
      (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r), V r⟫_ℝ
  let N (r : ℝ) := Real.sqrt (‖V r‖ ^ 2 + ε)
  have hN (r : ℝ) : 0 < N r := Real.sqrt_pos.2 (by positivity)
  have hd (r : ℝ) (hr : r ∈ s) : HasDerivWithinAt N (A r / N r) s r :=
    h.hasDerivWithinAt_regularized_norm hε hr
  refine convexOn_of_hasDerivWithinAt2_nonneg (Real.convex_iff_isPreconnected.2 hs)
    (fun r hr ↦ (hd r hr).continuousWithinAt)
    (fun r hr ↦ (hd r (interior_subset hr)).mono interior_subset)
    (f'' := fun r ↦ (B r * N r - A r * (A r / N r)) / (N r) ^ 2)
    (fun r hr ↦ ((h.hasDerivWithinAt_inner_alongCurveWithin_self
      (interior_subset hr)).div (hd r (interior_subset hr)) (ne_of_gt (hN r))).mono
      interior_subset) ?_
  intro r hr
  have hc := ((leviCivitaConnection I M).forall_sectionalCurvature_le_iff
    (isMetricCompatible_leviCivitaConnection I) (γ r) 0).1
      (hK r (interior_subset hr)) (V r) (curveVelocityWithin I γ s r)
  simp only [zero_mul] at hc
  have hcs := real_inner_mul_inner_self_le
    (alongCurveWithin (leviCivitaConnection I M) γ V s r) (V r)
  have hNsq : N r ^ 2 = ‖V r‖ ^ 2 + ε := Real.sq_sqrt (by positivity)
  have hnum : 0 ≤ B r * (N r) ^ 2 - A r ^ 2 := by
    dsimp only [A, B]
    rw [hNsq]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
    nlinarith [sq_nonneg ‖alongCurveWithin (leviCivitaConnection I M) γ V s r‖]
  apply div_nonneg _ (sq_nonneg _)
  have heq : B r * N r - A r * (A r / N r) =
      (B r * (N r) ^ 2 - A r ^ 2) / N r := by
    field_simp
  rw [heq]
  exact div_nonneg hnum (le_of_lt (hN r))

/-- The norm of a Jacobi field is convex on a preconnected parameter set under nonpositive
sectional curvature. This includes zeros of the field, constant geodesics and tangential fields;
no completeness or unit-speed assumption is needed. -/
theorem IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) :
    ConvexOn ℝ s (fun r ↦ ‖V r‖) := by
  refine ⟨Real.convex_iff_isPreconnected.2 hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hlim (r : ℝ) : Tendsto (fun ε : ℝ ↦ Real.sqrt (‖V r‖ ^ 2 + ε))
      (𝓝[>] 0) (𝓝 ‖V r‖) := by
    have ht : Tendsto (fun ε : ℝ ↦ ‖V r‖ ^ 2 + ε) (𝓝[>] 0)
        (𝓝 (‖V r‖ ^ 2 + 0)) :=
      tendsto_const_nhds.add nhdsWithin_le_nhds
    simpa only [add_zero, Real.sqrt_sq_eq_abs, abs_norm] using ht.sqrt
  exact le_of_tendsto_of_tendsto (hlim (a • x + b • y))
    ((hlim x).const_mul a |>.add ((hlim y).const_mul b))
    (eventually_nhdsWithin_of_forall fun ε hε ↦
      (h.convexOn_regularized_norm hs hK hε).2 hx hy ha hb hab)

/-- In nonpositive sectional curvature along the radial segment from `0` to `v`, the
exponential differential does not decrease any tangent norm. The segment lies in the natural
exponential domain; completeness, unit speed and orthogonality to the radial vector are not
required. -/
theorem norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos [I.Boundaryless]
    {p : M} {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u z : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, z] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (riemannianExp I M p (t • v)) u z ≤ 0)
    (w : TangentSpace I p) :
    ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w).mono
    (uniqueDiffOn_Icc zero_lt_one) hsub
  have hc := hJ.convexOn_norm_of_sectionalCurvature_nonpos isPreconnected_Icc hK
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) w‖ ≤
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
    intro t ht
    have h := hc.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    -- The source tangent space is canonically the original vector space. Apply linearity
    -- before rewriting the parameters, since the target fibre norms depend on those parameters.
    have hnorm (r : ℝ) :
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w)‖ =
          |r| * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ := by
      calc
        _ = ‖r • mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ :=
          congrArg norm ((mfderiv 𝓘(ℝ, TangentSpace I p) I
            (riemannianExp I M p) (r • v)).map_smul r w)
        _ = _ := norm_smul r _
    simp_rw [hnorm] at h
    have htcoord : (1 - t) • (0 : ℝ) + t • (1 : ℝ) = t := by simp
    rw [htcoord] at h
    simp only [abs_zero, abs_one, zero_mul, one_mul, smul_eq_mul, abs_of_pos ht.1] at h
    rw [mul_zero, zero_add, one_smul] at h
    exact (mul_le_mul_iff_right₀ ht.1).1 h
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hcont := ((contMDiffOn_riemannianExp p).continuousOn_norm_mfderiv
    (by simp) (isOpen_expDomain p) w).continuousAt
      ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p))
  have hsmul : Tendsto (fun t : ℝ ↦ t • v) (𝓝[>] 0) (𝓝 0) :=
    ((by fun_prop : Continuous (fun t : ℝ ↦ t • v)).tendsto' 0 0
      (zero_smul ℝ v)).mono_left nhdsWithin_le_nhds
  have hlim := hcont.tendsto.comp hsmul
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono
      nhdsWithin_le_nhds] with t ht h1
    exact ⟨ht, h1⟩
  have hbound := le_of_tendsto hlim (hevent.mono fun t ht ↦ hle t ht)
  rw [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at hbound
  exact hbound

end TauCeti.Manifold
