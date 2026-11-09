/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The index form and Jacobi integration by parts

Let `γ` be a curve in a Riemannian manifold and `V`, `W` tangent fields along `γ`. The index form
of `V` and `W` on `[a, b]` is

`I(V, W) = ∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt`,

with the curvature convention `R(X, Y) Z = [∇_X, ∇_Y] Z - ∇_[X, Y] Z` of the Jacobi equation. The
velocity and the covariant derivatives are taken within a parameter set `s`, so that the index
form is defined on closed segments; where `s` is a neighbourhood of the segment, it agrees with
the index form for unrestricted derivatives. It only depends on the fields on the open segment.

If `V` is a Jacobi field, then `⟪D_t V, W⟫` differentiates to the integrand, which gives the
integration by parts `I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. If moreover
`D_t V(a) = -k V(a)` for a scalar `k`, the initial boundary term is `k ⟪V(a), W(a)⟫`. This is the
correction of the index form for an initial point moving along a submanifold whose shape operator
acts on `V(a)` as multiplication by `k`, as for a curve in a surface.

## Main definitions and results

* `TauCeti.Manifold.indexFormIntegrandWithin` and `TauCeti.Manifold.indexFormWithin`: the
  integrand of the index form and the index form.
* `TauCeti.Manifold.indexFormWithin_congr`: the index form depends only on the curve and on the
  fields on the open segment.
* `TauCeti.Manifold.indexFormWithin_of_mem_nhds`: on a neighbourhood of the segment, derivatives
  within the parameter set give the unrestricted index form.
* `TauCeti.Manifold.IsJacobiFieldOn.indexFormWithin_eq_boundary`: Jacobi integration by parts.
* `TauCeti.Manifold.IsJacobiFieldOn.indexFormWithin_sub_initial_eq_boundary`: the corrected
  index form against a Jacobi field with prescribed initial derivative is its terminal pairing,
  so that it vanishes on the Jacobi field itself when it vanishes at `b`
  (`TauCeti.Manifold.IsJacobiFieldOn.indexFormWithin_self_sub_initial_eq_zero`) and is negative
  against a field with value `-D_t V(b) ≠ 0` at `b`
  (`TauCeti.Manifold.IsJacobiFieldOn.indexFormWithin_sub_initial_neg`).

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b : ℝ}

variable (I γ V W s) in
/-- The integrand `⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫` of the index form, with the velocity and
the covariant derivatives within the parameter set `s`. -/
def indexFormIntegrandWithin (t : ℝ) : ℝ :=
  inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t)
      (alongCurveWithin (leviCivitaConnection I M) γ W s t) -
    inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t)

/-- The defining formula of the integrand of the index form. -/
theorem indexFormIntegrandWithin_def (t : ℝ) : indexFormIntegrandWithin I γ V W s t =
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t)
      (alongCurveWithin (leviCivitaConnection I M) γ W s t) -
    inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) := by rfl

variable (I γ V W s a b) in
/-- The index form `∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt` of the fields `V` and `W` along
`γ`, with the velocity and the covariant derivatives within the parameter set `s`. -/
def indexFormWithin : ℝ :=
  ∫ t in a..b, indexFormIntegrandWithin I γ V W s t

/-- The defining integral of the index form. -/
theorem indexFormWithin_def : indexFormWithin I γ V W s a b =
    ∫ t in a..b, inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t)
        (alongCurveWithin (leviCivitaConnection I M) γ W s t) -
      inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) := by rfl

/-- The index form depends only on the curve and on the fields on the open segment. The fields
may live along equal curves given by different expressions. -/
theorem indexFormWithin_congr {δ : ℝ → M}
    {P Q : ∀ t, TangentSpace I (δ t)} (hγ : γ = δ)
    (hV : ∀ t ∈ uIoo a b, HEq (V t) (P t))
    (hW : ∀ t ∈ uIoo a b, HEq (W t) (Q t)) :
    indexFormWithin I γ V W s a b = indexFormWithin I δ P Q s a b := by
  subst δ
  rw [indexFormWithin_def, indexFormWithin_def]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have hv : V t = P t := eq_of_heq (hV t ht)
  have hw : W t = Q t := eq_of_heq (hW t ht)
  have hvgerm : ∀ᶠ r in 𝓝[s] t, V r = P r := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact eq_of_heq (hV r hr)
  have hwgerm : ∀ᶠ r in 𝓝[s] t, W r = Q r := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact eq_of_heq (hW r hr)
  dsimp only
  rw [alongCurveWithin_congr _ γ V hvgerm hv, alongCurveWithin_congr _ γ W hwgerm hw,
    hv, hw]

/-- Where the parameter set is a neighbourhood of `t`, the integrand of the index form at `t`
is the one with unrestricted derivatives. -/
theorem indexFormIntegrandWithin_of_mem_nhds {t : ℝ} (hs : s ∈ 𝓝 t) :
    indexFormIntegrandWithin I γ V W s t = indexFormIntegrandWithin I γ V W univ t := by
  simp only [indexFormIntegrandWithin_def, alongCurveWithin_univ, curveVelocityWithin_univ,
    alongCurveWithin_of_mem_nhds _ γ V hs, alongCurveWithin_of_mem_nhds _ γ W hs,
    curveVelocityWithin_of_mem_nhds (I := I) (γ := γ) hs]

/-- If the parameter set is a neighbourhood of every point of the segment, the index form is the
one with unrestricted derivatives. -/
theorem indexFormWithin_of_mem_nhds (hs : ∀ t ∈ uIcc a b, s ∈ 𝓝 t) :
    indexFormWithin I γ V W s a b = indexFormWithin I γ V W univ a b := by
  simp only [indexFormWithin_def, ← indexFormIntegrandWithin_def]
  exact intervalIntegral.integral_congr fun t ht ↦ indexFormIntegrandWithin_of_mem_nhds (hs t ht)

/-- The pairing `⟪D_t V, W⟫` of the covariant derivative of a Jacobi field `V` with a `C¹`
field `W` differentiates to the integrand of the index form. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ) I.tangent 1
      (fun t ↦ (⟨γ t, W t⟩ : TangentBundle I M)) s)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ inner ℝ
        (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r))
      (inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t)
          (alongCurveWithin (leviCivitaConnection I M) γ W s t) -
        inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t)) s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hd := hm.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht)
    (h.isGeodesicCurveOn.mdifferentiableOn t ht)
    (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
    (TauCeti.Manifold.differentiableWithinAt_sectionCoord γ W
      ((hW t ht).mdifferentiableWithinAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  convert hd using 1
  rw [h.alongCurveWithin_alongCurveWithin_eq ht, inner_neg_left]
  ring

/-- **Jacobi integration by parts.** For a Jacobi field `V` and a `C¹` field `W` on a parameter
set containing `[a, b]`, `I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. -/
theorem IsJacobiFieldOn.indexFormWithin_eq_boundary (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ) I.tangent 1
      (fun t ↦ (⟨γ t, W t⟩ : TangentBundle I M)) s)
    (hsub : uIcc a b ⊆ s) :
    indexFormWithin I γ V W s a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) := by
  let A := fun r ↦ inner ℝ
    (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r)
  have hA : ContDiffOn ℝ 1 A s := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact ContMDiffOn.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := γ) h.contMDiffOn_alongCurveWithin hW
  have hint : IntervalIntegrable (derivWithin A s) MeasureTheory.volume a b :=
    ((hA.continuousOn_derivWithin h.uniqueDiffOn le_rfl).mono hsub).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ s) := h.hasDerivWithinAt_inner_alongCurveWithin hW ht
  have hFTC : ∫ t in a..b, derivWithin A s t = A b - A a := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hA.continuousOn.mono hsub) _ hint
    intro t ht
    have hs : s ∈ 𝓝 t := mem_of_superset (Icc_mem_nhds ht.1 ht.2) hsub
    exact ((hA t (hsub (mem_Icc_of_Ioo ht))).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt |>.hasDerivAt hs).hasDerivWithinAt
  rw [indexFormWithin]
  convert hFTC using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact ((hd t (hsub ht)).derivWithin (h.uniqueDiffOn t (hsub ht))).symm

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -k V(a)`, then
`I(V, W) - k ⟪V(a), W(a)⟫ = ⟪D_t V(b), W(b)⟫`. -/
theorem IsJacobiFieldOn.indexFormWithin_sub_initial_eq_boundary
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ) I.tangent 1
      (fun t ↦ (⟨γ t, W t⟩ : TangentBundle I M)) s)
    (hsub : uIcc a b ⊆ s) {k : ℝ}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -k • V a) :
    indexFormWithin I γ V W s a b - k * inner ℝ (V a) (W a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) := by
  rw [h.indexFormWithin_eq_boundary hW hsub, hinit, real_inner_smul_left]
  ring

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -k V(a)` and vanishes at `b`, then
`I(V, V) - k ‖V(a)‖² = 0`. -/
theorem IsJacobiFieldOn.indexFormWithin_self_sub_initial_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hsub : uIcc a b ⊆ s) {k : ℝ}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -k • V a)
    (hzero : V b = 0) :
    indexFormWithin I γ V V s a b - k * ‖V a‖ ^ 2 = 0 := by
  simpa only [hzero, inner_zero_right, real_inner_self_eq_norm_sq] using
    h.indexFormWithin_sub_initial_eq_boundary (h.contMDiffOn.of_le (by norm_num)) hsub hinit

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -k V(a)` and `W(b) = -D_t V(b)`
is nonzero, then `I(V, W) - k ⟪V(a), W(a)⟫ < 0`. -/
theorem IsJacobiFieldOn.indexFormWithin_sub_initial_neg
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ) I.tangent 1
      (fun t ↦ (⟨γ t, W t⟩ : TangentBundle I M)) s)
    (hsub : uIcc a b ⊆ s) {k : ℝ}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -k • V a)
    (hterminal : W b = -alongCurveWithin (leviCivitaConnection I M) γ V s b)
    (hne : alongCurveWithin (leviCivitaConnection I M) γ V s b ≠ 0) :
    indexFormWithin I γ V W s a b - k * inner ℝ (V a) (W a) < 0 := by
  rw [h.indexFormWithin_sub_initial_eq_boundary hW hsub hinit, hterminal,
    inner_neg_right, real_inner_self_eq_norm_sq]
  exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hne))

end TauCeti.Manifold
