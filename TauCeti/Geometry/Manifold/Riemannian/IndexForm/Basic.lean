/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness

/-!
# The index form and integration by parts

Let `γ` be a curve in a Riemannian manifold and `V`, `W` tangent fields along `γ`. The index form
of `V` and `W` on `[a, b]` is

`I(V, W) = ∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt`,

with the curvature convention `R(X, Y) Z = [∇_X, ∇_Y] Z - ∇_[X, Y] Z` of the Jacobi equation. The
integral uses unrestricted derivatives. On a closed segment it can equally be computed with
derivatives within any parameter set containing the open segment. Values at endpoints and
finitely many corners do not affect the integral. It only depends on the curve and the fields
on the open segment. It is symmetric, bilinear on `C¹` fields, and additive over adjacent
segments whenever the integrands are interval integrable on each piece.

For a `C²` field `V`, `⟪D_t V, W⟫` differentiates to the integrand plus `⟪D_t² V + R(V, γ') γ', W⟫`,
which gives the integration by parts
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫ - ∫_a^b ⟪D_t² V + R(V, γ') γ', W⟫ dt`.
For a Jacobi field `V` the last integral vanishes. If `D_t V(a) + u` is orthogonal to `W(a)`,
then `-⟪D_t V(a), W(a)⟫ = ⟪u, W(a)⟫`, so
`I(V, W) - ⟪u, W(a)⟫ = ⟪D_t V(b), W(b)⟫`. Taking `u` to be the ambient image of the shape
operator applied to `V(a)` gives the correction for an initial point moving along a submanifold,
without requiring the normal component of `D_t V(a) + u` to vanish.

## Main definitions and results

* `TauCeti.Manifold.indexFormIntegrand` and `TauCeti.Manifold.indexForm`: the unrestricted
  integrand and its interval integral.
* `TauCeti.Manifold.indexFormIntegrandWithin` and
  `TauCeti.Manifold.indexForm_eq_integral_indexFormIntegrandWithin`: computation using derivatives
  within a parameter set, including at closed interval endpoints.
* `TauCeti.Manifold.indexForm_congr`: invariance under curves and fields agreeing on the open
  segment.
* `TauCeti.Manifold.indexForm_comm`, `TauCeti.Manifold.indexForm_add_left`,
  `TauCeti.Manifold.indexForm_const_smul_left` and their right-slot versions: symmetry and
  bilinearity, with zero, negation, subtraction and finite-sum laws.
* `TauCeti.Manifold.intervalIntegrable_indexFormIntegrand`:
  integrability from `C¹` lifts on the closed interval.
* `TauCeti.Manifold.indexForm_add_adjacent_intervals` and
  `TauCeti.Manifold.sum_indexForm_adjacent_intervals`: additivity over pieces with separately
  integrable integrands, allowing corners at the joining parameters.
* `TauCeti.Manifold.indexForm_eq_inner_sub_inner_sub_integral` and
  `TauCeti.Manifold.indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral`: integration by
  parts with unrestricted and within-set derivatives.
* `TauCeti.Manifold.IsJacobiFieldOn.indexForm_eq_inner_sub_inner`: Jacobi integration by parts.
* `TauCeti.Manifold.IsJacobiFieldOn.indexForm_sub_inner_eq_inner`: the corrected index form is
  the terminal pairing when `D_t V(a) + u` is orthogonal to the initial test value. It vanishes
  on the Jacobi field itself when it vanishes at `b`
  (`TauCeti.Manifold.IsJacobiFieldOn.indexForm_self_sub_inner_eq_zero`) and is negative against a
  field with value `-D_t V(b) ≠ 0` at `b`
  (`TauCeti.Manifold.IsJacobiFieldOn.indexForm_sub_inner_neg`).

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
  {γ : ℝ → M} {V V' W W' : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b : ℝ}

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

variable (I γ V W) in
/-- The unrestricted integrand of the index form. Its integral also applies to fields smooth
only on each piece of a finite partition. -/
def indexFormIntegrand (t : ℝ) : ℝ := indexFormIntegrandWithin I γ V W univ t

/-- The within-set integrand on the whole parameter line is the unrestricted integrand. -/
@[simp]
theorem indexFormIntegrandWithin_univ :
    indexFormIntegrandWithin I γ V W univ = indexFormIntegrand I γ V W := (rfl)

/-- The defining formula of the unrestricted index-form integrand. -/
theorem indexFormIntegrand_def (t : ℝ) : indexFormIntegrand I γ V W t =
    inner ℝ (alongCurve (leviCivitaConnection I M) γ V t)
      (alongCurve (leviCivitaConnection I M) γ W t) -
    inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
      (curveVelocity I γ t) (curveVelocity I γ t)) (W t) := by
  rw [← indexFormIntegrandWithin_univ, indexFormIntegrandWithin_def,
    alongCurveWithin_univ, alongCurveWithin_univ, curveVelocityWithin_univ]

variable (I γ V W a b) in
/-- The index form of two tangent fields along a curve on an oriented parameter interval.
Values of the integrand at finitely many corners do not affect this integral. -/
def indexForm : ℝ := ∫ t in a..b, indexFormIntegrand I γ V W t

/-- The defining integral of the index form. -/
theorem indexForm_def : indexForm I γ V W a b =
    ∫ t in a..b, indexFormIntegrand I γ V W t := (rfl)

/-- Where the parameter set is a neighbourhood of `t`, the integrand uses unrestricted
derivatives. -/
theorem indexFormIntegrandWithin_of_mem_nhds {t : ℝ} (hs : s ∈ 𝓝 t) :
    indexFormIntegrandWithin I γ V W s t = indexFormIntegrand I γ V W t := by
  simp only [← indexFormIntegrandWithin_univ, indexFormIntegrandWithin_def, alongCurveWithin_univ,
    curveVelocityWithin_univ, alongCurveWithin_of_mem_nhds _ γ V hs,
    alongCurveWithin_of_mem_nhds _ γ W hs, curveVelocityWithin_of_mem_nhds (I := I) (γ := γ) hs]

/-- The index form can be computed with derivatives within any set containing the open
parameter interval. No regularity is needed at the endpoints. -/
theorem indexForm_eq_integral_indexFormIntegrandWithin (hs : uIoo a b ⊆ s) :
    indexForm I γ V W a b = ∫ t in a..b, indexFormIntegrandWithin I γ V W s t := by
  rw [indexForm_def]
  exact intervalIntegral.integral_congr_uIoo fun t ht ↦
    (indexFormIntegrandWithin_of_mem_nhds
      (mem_of_superset (isOpen_Ioo.mem_nhds ht) hs)).symm

/-- The within-set integrand depends only on the germs of the curve and the two fields,
together with their values at the tested parameter. -/
theorem indexFormIntegrandWithin_congr {δ : ℝ → M} {P Q : ∀ r, TangentSpace I (δ r)}
    {t : ℝ} (hγ : γ =ᶠ[𝓝[s] t] δ) (hγt : γ t = δ t)
    (hV : ∀ᶠ r in 𝓝[s] t, HEq (V r) (P r)) (hVt : HEq (V t) (P t))
    (hW : ∀ᶠ r in 𝓝[s] t, HEq (W r) (Q r)) (hWt : HEq (W t) (Q t)) :
    indexFormIntegrandWithin I γ V W s t = indexFormIntegrandWithin I δ P Q s t := by
  have hdV := alongCurveWithin_congr_heq (leviCivitaConnection I M) V hγ hγt hV hVt
  have hdW := alongCurveWithin_congr_heq (leviCivitaConnection I M) W hγ hγt hW hWt
  have hv := hγ.curveVelocityLiftWithin_eq (I := I) hγt
  rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply] at hv
  have hvel : HEq (curveVelocityWithin I γ s t) (curveVelocityWithin I δ s t) :=
    (TotalSpace.ext_iff.mp hv).2
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def]
  generalize γ t = x at *
  generalize δ t = y at *
  subst y
  rw [eq_of_heq hdV, eq_of_heq hdW, eq_of_heq hVt, eq_of_heq hWt, eq_of_heq hvel]

/-- The unrestricted integrand depends only on the germs of the curve and both fields. -/
theorem indexFormIntegrand_congr {δ : ℝ → M} {P Q : ∀ r, TangentSpace I (δ r)} {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] δ) (hV : ∀ᶠ r in 𝓝 t, HEq (V r) (P r))
    (hW : ∀ᶠ r in 𝓝 t, HEq (W r) (Q r)) :
    indexFormIntegrand I γ V W t = indexFormIntegrand I δ P Q t := by
  simp only [← indexFormIntegrandWithin_univ]
  exact indexFormIntegrandWithin_congr (by rwa [nhdsWithin_univ]) hγ.eq_of_nhds
    (by rwa [nhdsWithin_univ]) hV.self_of_nhds
    (by rwa [nhdsWithin_univ]) hW.self_of_nhds

/-- The index form depends only on the curve and the fields on the open parameter interval.
The two pairs of fields may be given along different curves agreeing on the open interval. -/
theorem indexForm_congr {δ : ℝ → M} {P Q : ∀ t, TangentSpace I (δ t)}
    (hγ : EqOn γ δ (uIoo a b))
    (hV : ∀ t ∈ uIoo a b, HEq (V t) (P t))
    (hW : ∀ t ∈ uIoo a b, HEq (W t) (Q t)) :
    indexForm I γ V W a b = indexForm I δ P Q a b := by
  rw [indexForm_def, indexForm_def]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hmem : uIoo a b ∈ 𝓝[univ] t := nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht)
  simp only [← indexFormIntegrandWithin_univ]
  exact indexFormIntegrandWithin_congr
    (eventually_of_mem hmem hγ) (hγ ht)
    (eventually_of_mem hmem hV) (hV t ht)
    (eventually_of_mem hmem hW) (hW t ht)

/-! ### Symmetry and bilinearity -/

/-- The integrand of the index form is symmetric in the two fields. -/
theorem indexFormIntegrandWithin_comm (t : ℝ) :
    indexFormIntegrandWithin I γ V W s t = indexFormIntegrandWithin I γ W V s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hcurv : inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) =
      inner ℝ (V t) ((leviCivitaConnection I M).curvatureTensor (γ t) (W t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) := by
    rw [hm.inner_curvatureTensor_swap_pairs (torsion_leviCivitaConnection_eq_zero I),
      hm.inner_curvatureTensor_eq_neg, curvatureTensor_antisymm]
    simp
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def, hcurv,
    real_inner_comm (V t), real_inner_comm (alongCurveWithin _ γ V s t)]

/-- The index form is symmetric in the two fields. -/
theorem indexForm_comm :
    indexForm I γ V W a b = indexForm I γ W V a b := by
  simp only [indexForm_def, ← indexFormIntegrandWithin_univ]
  exact intervalIntegral.integral_congr fun t _ ↦ indexFormIntegrandWithin_comm (s := univ) t

/-- The integrand of the index form is additive in the first field, at a parameter where both
fields are differentiable within the parameter set. -/
@[to_fun indexFormIntegrandWithin_fun_add_left]
theorem indexFormIntegrandWithin_add_left {t : ℝ}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hV' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V' (γ t)) s t) :
    indexFormIntegrandWithin I γ (V + V') W s t =
      indexFormIntegrandWithin I γ V W s t + indexFormIntegrandWithin I γ V' W s t := by
  simp only [Pi.add_def, indexFormIntegrandWithin_def,
    alongCurveWithin_add _ γ V V' s hV hV', map_add,
    LinearMap.add_apply, inner_add_left]
  ring

/-- The integrand of the index form is additive in the second field, at a parameter where both
fields are differentiable within the parameter set. -/
@[to_fun indexFormIntegrandWithin_fun_add_right]
theorem indexFormIntegrandWithin_add_right {t : ℝ}
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hW' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W' (γ t)) s t) :
    indexFormIntegrandWithin I γ V (W + W') s t =
      indexFormIntegrandWithin I γ V W s t + indexFormIntegrandWithin I γ V W' s t := by
  rw [indexFormIntegrandWithin_comm, indexFormIntegrandWithin_add_left hW hW',
    indexFormIntegrandWithin_comm, indexFormIntegrandWithin_comm (V := W')]

/-- The integrand of the index form is homogeneous in the first field. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_const_smul_left]
theorem indexFormIntegrandWithin_const_smul_left (c : ℝ) (t : ℝ) :
    indexFormIntegrandWithin I γ (c • V) W s t =
      c * indexFormIntegrandWithin I γ V W s t := by
  simp only [Pi.smul_def, indexFormIntegrandWithin_def, alongCurveWithin_const_smul, map_smul,
    LinearMap.smul_apply, real_inner_smul_left]
  ring

/-- The integrand of the index form is homogeneous in the second field. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_const_smul_right]
theorem indexFormIntegrandWithin_const_smul_right (c : ℝ) (t : ℝ) :
    indexFormIntegrandWithin I γ V (c • W) s t =
      c * indexFormIntegrandWithin I γ V W s t := by
  rw [indexFormIntegrandWithin_comm, indexFormIntegrandWithin_const_smul_left,
    indexFormIntegrandWithin_comm]

/-- The index form is homogeneous in the first field. -/
@[to_fun (attr := simp) indexForm_fun_const_smul_left]
theorem indexForm_const_smul_left (c : ℝ) :
    indexForm I γ (c • V) W a b = c * indexForm I γ V W a b := by
  simp only [indexForm_def, ← indexFormIntegrandWithin_univ,
    indexFormIntegrandWithin_const_smul_left,
    intervalIntegral.integral_const_mul]

/-- The index form is homogeneous in the second field. -/
@[to_fun (attr := simp) indexForm_fun_const_smul_right]
theorem indexForm_const_smul_right (c : ℝ) :
    indexForm I γ V (c • W) a b = c * indexForm I γ V W a b := by
  rw [indexForm_comm, indexForm_const_smul_left, indexForm_comm]

/-- The within-set integrand is zero when its left field is zero. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_zero_left]
theorem indexFormIntegrandWithin_zero_left (t : ℝ) :
    indexFormIntegrandWithin I γ (0) W s t = 0 := by
  simpa only [zero_smul, zero_mul] using
    (indexFormIntegrandWithin_const_smul_left (I := I) (γ := γ)
      (V := 0) (W := W) (s := s) 0 t)

/-- Negating the left field negates the within-set integrand. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_neg_left]
theorem indexFormIntegrandWithin_neg_left (t : ℝ) :
    indexFormIntegrandWithin I γ (-V) W s t = -indexFormIntegrandWithin I γ V W s t := by
  simpa only [neg_one_smul, neg_one_mul] using
    (indexFormIntegrandWithin_const_smul_left (I := I) (γ := γ) (V := V) (W := W)
      (s := s) (-1) t)

/-- The integrand is zero when its left field is zero. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_zero_left]
theorem indexFormIntegrand_zero_left (t : ℝ) :
    indexFormIntegrand I γ (0) W t = 0 := by
  simpa only [zero_smul, zero_mul, ← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_const_smul_left (I := I) (γ := γ)
      (V := 0) (W := W) (s := univ) 0 t)

/-- Negating the left field negates the integrand. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_neg_left]
theorem indexFormIntegrand_neg_left (t : ℝ) :
    indexFormIntegrand I γ (-V) W t = -indexFormIntegrand I γ V W t := by
  simpa only [neg_one_smul, neg_one_mul, ← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_const_smul_left (I := I) (γ := γ) (V := V) (W := W)
      (s := univ) (-1) t)

/-- The index form vanishes when its left field is zero. -/
@[to_fun (attr := simp) indexForm_fun_zero_left]
theorem indexForm_zero_left : indexForm I γ (0) W a b = 0 := by
  simp only [indexForm_def, indexFormIntegrand_zero_left, intervalIntegral.integral_zero]

/-- Negating the left field negates the index form. -/
@[to_fun (attr := simp) indexForm_fun_neg_left]
theorem indexForm_neg_left :
    indexForm I γ (-V) W a b = -indexForm I γ V W a b := by
  simp only [indexForm_def, indexFormIntegrand_neg_left, intervalIntegral.integral_neg]

/-- The unrestricted integrand is homogeneous in its left field. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_const_smul_left]
theorem indexFormIntegrand_const_smul_left (c : ℝ) (t : ℝ) :
    indexFormIntegrand I γ (c • V) W t = c * indexFormIntegrand I γ V W t := by
  simp only [← indexFormIntegrandWithin_univ, indexFormIntegrandWithin_const_smul_left]

/-- The within-set integrand is zero when its right field is zero. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_zero_right]
theorem indexFormIntegrandWithin_zero_right (t : ℝ) :
    indexFormIntegrandWithin I γ V (0) s t = 0 := by
  simpa only [zero_smul, zero_mul] using
    (indexFormIntegrandWithin_const_smul_right (I := I) (γ := γ)
      (V := V) (W := 0) (s := s) 0 t)

/-- Negating the right field negates the within-set integrand. -/
@[to_fun (attr := simp) indexFormIntegrandWithin_fun_neg_right]
theorem indexFormIntegrandWithin_neg_right (t : ℝ) :
    indexFormIntegrandWithin I γ V (-W) s t = -indexFormIntegrandWithin I γ V W s t := by
  simpa only [neg_one_smul, neg_one_mul] using
    (indexFormIntegrandWithin_const_smul_right (I := I) (γ := γ) (V := V) (W := W)
      (s := s) (-1) t)

/-- The integrand is zero when its right field is zero. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_zero_right]
theorem indexFormIntegrand_zero_right (t : ℝ) :
    indexFormIntegrand I γ V (0) t = 0 := by
  simpa only [zero_smul, zero_mul, ← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_const_smul_right (I := I) (γ := γ)
      (V := V) (W := 0) (s := univ) 0 t)

/-- Negating the right field negates the integrand. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_neg_right]
theorem indexFormIntegrand_neg_right (t : ℝ) :
    indexFormIntegrand I γ V (-W) t = -indexFormIntegrand I γ V W t := by
  simpa only [neg_one_smul, neg_one_mul, ← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_const_smul_right (I := I) (γ := γ) (V := V) (W := W)
      (s := univ) (-1) t)

/-- The index form vanishes when its right field is zero. -/
@[to_fun (attr := simp) indexForm_fun_zero_right]
theorem indexForm_zero_right : indexForm I γ V (0) a b = 0 := by
  simp only [indexForm_def, indexFormIntegrand_zero_right, intervalIntegral.integral_zero]

/-- Negating the right field negates the index form. -/
@[to_fun (attr := simp) indexForm_fun_neg_right]
theorem indexForm_neg_right :
    indexForm I γ V (-W) a b = -indexForm I γ V W a b := by
  simp only [indexForm_def, indexFormIntegrand_neg_right, intervalIntegral.integral_neg]

/-- The unrestricted integrand is homogeneous in its right field. -/
@[to_fun (attr := simp) indexFormIntegrand_fun_const_smul_right]
theorem indexFormIntegrand_const_smul_right (c : ℝ) (t : ℝ) :
    indexFormIntegrand I γ V (c • W) t = c * indexFormIntegrand I γ V W t := by
  simp only [← indexFormIntegrandWithin_univ, indexFormIntegrandWithin_const_smul_right]

/-- The integrand is symmetric in its two fields. -/
theorem indexFormIntegrand_comm (t : ℝ) :
    indexFormIntegrand I γ V W t = indexFormIntegrand I γ W V t := by
  simp only [← indexFormIntegrandWithin_univ, indexFormIntegrandWithin_comm]

/-- The index form vanishes on a degenerate parameter interval. -/
@[simp]
theorem indexForm_same : indexForm I γ V W a a = 0 := by
  simp only [indexForm_def, intervalIntegral.integral_same]

/-- Reversing the orientation of the interval negates the index form. -/
theorem indexForm_symm : indexForm I γ V W b a = -indexForm I γ V W a b := by
  rw [indexForm_def, indexForm_def, intervalIntegral.integral_symm]

/-- The within-set integrand respects subtraction in its first field. -/
@[to_fun indexFormIntegrandWithin_fun_sub_left]
theorem indexFormIntegrandWithin_sub_left {t : ℝ}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hV' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V' (γ t)) s t) :
    indexFormIntegrandWithin I γ (V - V') W s t =
      indexFormIntegrandWithin I γ V W s t - indexFormIntegrandWithin I γ V' W s t := by
  simp only [Pi.sub_def, indexFormIntegrandWithin_def,
    alongCurveWithin_sub _ γ V V' s hV hV', map_sub,
    LinearMap.sub_apply, inner_sub_left]
  ring

/-- The within-set integrand respects subtraction in its second field. -/
@[to_fun indexFormIntegrandWithin_fun_sub_right]
theorem indexFormIntegrandWithin_sub_right {t : ℝ}
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hW' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W' (γ t)) s t) :
    indexFormIntegrandWithin I γ V (W - W') s t =
      indexFormIntegrandWithin I γ V W s t - indexFormIntegrandWithin I γ V W' s t := by
  rw [indexFormIntegrandWithin_comm, indexFormIntegrandWithin_sub_left hW hW',
    indexFormIntegrandWithin_comm, indexFormIntegrandWithin_comm (V := W')]

/-- The within-set integrand commutes with a finite sum in its first field. -/
@[to_fun indexFormIntegrandWithin_fun_sum_left]
theorem indexFormIntegrandWithin_sum_left {ι : Type*} (A : Finset ι)
    (X : ι → ∀ r, TangentSpace I (γ r)) {t : ℝ}
    (hX : ∀ i ∈ A, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (X i) (γ t)) s t) :
    indexFormIntegrandWithin I γ (∑ i ∈ A, X i) W s t =
      ∑ i ∈ A, indexFormIntegrandWithin I γ (X i) W s t := by
  simp only [Finset.sum_fn, indexFormIntegrandWithin_def, alongCurveWithin_sum _ γ A X hX, map_sum,
    LinearMap.sum_apply, sum_inner, Finset.sum_sub_distrib]

/-- The within-set integrand commutes with a finite sum in its second field. -/
@[to_fun indexFormIntegrandWithin_fun_sum_right]
theorem indexFormIntegrandWithin_sum_right {ι : Type*} (A : Finset ι)
    (X : ι → ∀ r, TangentSpace I (γ r)) {t : ℝ}
    (hX : ∀ i ∈ A, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (X i) (γ t)) s t) :
    indexFormIntegrandWithin I γ V (∑ i ∈ A, X i) s t =
      ∑ i ∈ A, indexFormIntegrandWithin I γ V (X i) s t := by
  simp_rw [indexFormIntegrandWithin_comm (V := V)]
  exact indexFormIntegrandWithin_sum_left A X hX

/-- The integrand respects addition in its left field at differentiable parameters. -/
@[to_fun indexFormIntegrand_fun_add_left]
theorem indexFormIntegrand_add_left {t : ℝ}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hV' : DifferentiableAt ℝ (sectionCoord (F := E) γ V' (γ t)) t) :
    indexFormIntegrand I γ (V + V') W t =
      indexFormIntegrand I γ V W t + indexFormIntegrand I γ V' W t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    indexFormIntegrandWithin_add_left hV.differentiableWithinAt hV'.differentiableWithinAt

/-- The integrand respects addition in its right field at differentiable parameters. -/
@[to_fun indexFormIntegrand_fun_add_right]
theorem indexFormIntegrand_add_right {t : ℝ}
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (hW' : DifferentiableAt ℝ (sectionCoord (F := E) γ W' (γ t)) t) :
    indexFormIntegrand I γ V (W + W') t =
      indexFormIntegrand I γ V W t + indexFormIntegrand I γ V W' t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    indexFormIntegrandWithin_add_right hW.differentiableWithinAt hW'.differentiableWithinAt

/-- The integrand respects subtraction in its left field at differentiable parameters. -/
@[to_fun indexFormIntegrand_fun_sub_left]
theorem indexFormIntegrand_sub_left {t : ℝ}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hV' : DifferentiableAt ℝ (sectionCoord (F := E) γ V' (γ t)) t) :
    indexFormIntegrand I γ (V - V') W t =
      indexFormIntegrand I γ V W t - indexFormIntegrand I γ V' W t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    indexFormIntegrandWithin_sub_left hV.differentiableWithinAt hV'.differentiableWithinAt

/-- The integrand respects subtraction in its right field at differentiable parameters. -/
@[to_fun indexFormIntegrand_fun_sub_right]
theorem indexFormIntegrand_sub_right {t : ℝ}
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (hW' : DifferentiableAt ℝ (sectionCoord (F := E) γ W' (γ t)) t) :
    indexFormIntegrand I γ V (W - W') t =
      indexFormIntegrand I γ V W t - indexFormIntegrand I γ V W' t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    indexFormIntegrandWithin_sub_right hW.differentiableWithinAt hW'.differentiableWithinAt

/-- The integrand commutes with a finite sum in its left field. -/
@[to_fun indexFormIntegrand_fun_sum_left]
theorem indexFormIntegrand_sum_left {ι : Type*} (A : Finset ι)
    (X : ι → ∀ r, TangentSpace I (γ r)) {t : ℝ}
    (hX : ∀ i ∈ A, DifferentiableAt ℝ (sectionCoord (F := E) γ (X i) (γ t)) t) :
    indexFormIntegrand I γ (∑ i ∈ A, X i) W t =
      ∑ i ∈ A, indexFormIntegrand I γ (X i) W t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_sum_left A X fun i hi ↦ (hX i hi).differentiableWithinAt)

/-- The integrand commutes with a finite sum in its right field. -/
@[to_fun indexFormIntegrand_fun_sum_right]
theorem indexFormIntegrand_sum_right {ι : Type*} (A : Finset ι)
    (X : ι → ∀ r, TangentSpace I (γ r)) {t : ℝ}
    (hX : ∀ i ∈ A, DifferentiableAt ℝ (sectionCoord (F := E) γ (X i) (γ t)) t) :
    indexFormIntegrand I γ V (∑ i ∈ A, X i) t =
      ∑ i ∈ A, indexFormIntegrand I γ V (X i) t := by
  simpa only [← indexFormIntegrandWithin_univ] using
    (indexFormIntegrandWithin_sum_right A X fun i hi ↦ (hX i hi).differentiableWithinAt)

/-! ### Integrability -/

/-- The integrand of the index form of `C¹` fields is continuous on a parameter set with unique
derivatives. -/
theorem continuousOn_indexFormIntegrandWithin (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s) :
    ContinuousOn (indexFormIntegrandWithin I γ V W s) s := by
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 1)).comp_contMDiffOn hV
  have hvel : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r)) s := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ s)] using
      hγ.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp) hs.uniqueMDiffOn
  have hD :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) hs (by simpa using hV))
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) hs
        (by simpa using hW))).continuousOn
  have hR :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      ((leviCivitaConnection I M).contMDiffOn_curvatureTensor
        (F := E) (V := TangentSpace I) (by simp)
        (hV.of_le zero_le_one) hvel hvel)
      (hW.of_le zero_le_one)).continuousOn
  exact (hD.sub hR).congr fun t _ ↦ indexFormIntegrandWithin_def t

/-- The unrestricted integrand of `C¹` fields is continuous on an open parameter set. -/
theorem continuousOn_indexFormIntegrand (hs : IsOpen s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s) :
    ContinuousOn (indexFormIntegrand I γ V W) s :=
  (continuousOn_indexFormIntegrandWithin hs.uniqueDiffOn hV hW).congr fun _ ht ↦
    (indexFormIntegrandWithin_of_mem_nhds (hs.mem_nhds ht)).symm

/-- The unrestricted integrand of globally `C¹` fields is continuous. -/
theorem continuous_indexFormIntegrand
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r))) :
    Continuous (indexFormIntegrand I γ V W) :=
  continuousOn_univ.mp (continuousOn_indexFormIntegrand isOpen_univ
    hV.contMDiffOn hW.contMDiffOn)

/-- The unrestricted integrand is interval integrable when both fields have `C¹` lifts on the
closed interval, including degenerate intervals. -/
theorem intervalIntegrable_indexFormIntegrand
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact IntervalIntegrable.refl
  exact (continuousOn_indexFormIntegrandWithin (uniqueDiffOn_uIcc hab) hV hW).intervalIntegrable
    |>.congr_uIoo fun t ht ↦ indexFormIntegrandWithin_of_mem_nhds
      (mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self)

/-- The integrand computed within any set containing the open interval is integrable when
both fields have `C¹` lifts on the closed interval. -/
theorem intervalIntegrable_indexFormIntegrandWithin
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hs : uIoo a b ⊆ s) :
    IntervalIntegrable (indexFormIntegrandWithin I γ V W s) MeasureTheory.volume a b :=
  (intervalIntegrable_indexFormIntegrand hV hW).congr_uIoo fun _ ht ↦
    (indexFormIntegrandWithin_of_mem_nhds (mem_of_superset (isOpen_Ioo.mem_nhds ht) hs)).symm

/-- The index form is additive in the first field on `C¹` fields. -/
@[to_fun indexForm_fun_add_left]
theorem indexForm_add_left
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hV' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ (V + V') W a b =
      indexForm I γ V W a b + indexForm I γ V' W a b := by
  rw [indexForm_eq_integral_indexFormIntegrandWithin uIoo_subset_uIcc_self,
    indexForm_eq_integral_indexFormIntegrandWithin uIoo_subset_uIcc_self,
    indexForm_eq_integral_indexFormIntegrandWithin uIoo_subset_uIcc_self,
    ← intervalIntegral.integral_add
    (intervalIntegrable_indexFormIntegrandWithin hV hW uIoo_subset_uIcc_self)
    (intervalIntegrable_indexFormIntegrandWithin hV' hW uIoo_subset_uIcc_self)]
  exact intervalIntegral.integral_congr fun t ht ↦ indexFormIntegrandWithin_add_left
    (differentiableWithinAt_sectionCoord γ V ((hV t ht).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    (differentiableWithinAt_sectionCoord γ V' ((hV' t ht).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))

/-- The index form is additive in the second field on `C¹` fields. -/
@[to_fun indexForm_fun_add_right]
theorem indexForm_add_right
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hW' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W' r)) (uIcc a b)) :
    indexForm I γ V (W + W') a b =
      indexForm I γ V W a b + indexForm I γ V W' a b := by
  rw [indexForm_comm, indexForm_add_left hW hW' hV, indexForm_comm,
    indexForm_comm (V := W')]

/-- The index form respects subtraction in its first field on `C¹` fields. -/
@[to_fun indexForm_fun_sub_left]
theorem indexForm_sub_left
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hV' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ (V - V') W a b =
      indexForm I γ V W a b - indexForm I γ V' W a b := by
  simp_rw [indexForm_eq_integral_indexFormIntegrandWithin uIoo_subset_uIcc_self]
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_indexFormIntegrandWithin hV hW uIoo_subset_uIcc_self)
    (intervalIntegrable_indexFormIntegrandWithin hV' hW uIoo_subset_uIcc_self)]
  exact intervalIntegral.integral_congr fun t ht ↦ indexFormIntegrandWithin_sub_left
    (differentiableWithinAt_sectionCoord γ V ((hV t ht).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    (differentiableWithinAt_sectionCoord γ V' ((hV' t ht).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))

/-- The index form respects subtraction in its second field on `C¹` fields. -/
@[to_fun indexForm_fun_sub_right]
theorem indexForm_sub_right
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hW' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W' r)) (uIcc a b)) :
    indexForm I γ V (W - W') a b =
      indexForm I γ V W a b - indexForm I γ V W' a b := by
  rw [indexForm_comm, indexForm_sub_left hW hW' hV, indexForm_comm,
    indexForm_comm (V := W')]

/-- The index form commutes with finite sums of `C¹` fields in its first slot. -/
@[to_fun indexForm_fun_sum_left]
theorem indexForm_sum_left {ι : Type*} (A : Finset ι) (X : ι → ∀ r, TangentSpace I (γ r))
    (hX : ∀ i ∈ A, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (X i r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ (∑ i ∈ A, X i) W a b =
      ∑ i ∈ A, indexForm I γ (X i) W a b := by
  simp_rw [indexForm_eq_integral_indexFormIntegrandWithin uIoo_subset_uIcc_self]
  rw [← intervalIntegral.integral_finsetSum
    (fun i hi ↦ intervalIntegrable_indexFormIntegrandWithin (hX i hi) hW uIoo_subset_uIcc_self)]
  exact intervalIntegral.integral_congr fun t ht ↦ indexFormIntegrandWithin_sum_left A X
    fun i hi ↦ differentiableWithinAt_sectionCoord γ (X i)
      ((hX i hi t ht).mdifferentiableWithinAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))

/-- The index form commutes with finite sums of `C¹` fields in its second slot. -/
@[to_fun indexForm_fun_sum_right]
theorem indexForm_sum_right {ι : Type*} (A : Finset ι) (X : ι → ∀ r, TangentSpace I (γ r))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hX : ∀ i ∈ A, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (X i r)) (uIcc a b)) :
    indexForm I γ V (∑ i ∈ A, X i) a b =
      ∑ i ∈ A, indexForm I γ V (X i) a b := by
  simp_rw [indexForm_comm (V := V)]
  exact indexForm_sum_left A X hX hV

/-- The index form is additive over adjacent intervals with integrable integrands.
The fields may have corners at the joining parameter. -/
theorem indexForm_add_adjacent_intervals {c : ℝ}
    (hab : IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume b c) :
    indexForm I γ V W a b + indexForm I γ V W b c = indexForm I γ V W a c :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The index form is additive over any finite partition on which the integrand is integrable.
The partition need not be strict or increasing. -/
theorem sum_indexForm_adjacent_intervals {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hint : ∀ i : Fin n, IntervalIntegrable (indexFormIntegrand I γ V W)
      MeasureTheory.volume (τ i.castSucc) (τ i.succ)) :
    ∑ i : Fin n, indexForm I γ V W (τ i.castSucc) (τ i.succ) =
      indexForm I γ V W (τ 0) (τ (Fin.last n)) := by
  simp only [indexForm_def]
  exact TauCeti.intervalIntegral.sum_integral_adjacent_intervals_fin τ hint

/-! ### Integration by parts -/

/-- For a `C²` field `V`, the pairing `⟪D_t V, W⟫` differentiates to the integrand of the index
form plus `⟪D_t² V + R(V, γ') γ', W⟫`. -/
theorem hasDerivWithinAt_inner_alongCurveWithin (hs : UniqueDiffOn ℝ s)
    {t : ℝ} (hV : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t)
    (ht : t ∈ s)
    (hW : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s t) :
    HasDerivWithinAt (fun r ↦ inner ℝ
        (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r))
      (indexFormIntegrandWithin I γ V W s t +
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V s) s t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t)) s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t :=
    ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 2)).contMDiffAt
      |>.comp_contMDiffWithinAt t
      hV).mdifferentiableWithinAt (by norm_num)
  have hd := hm.hasDerivWithinAt_inner_alongCurveWithin hγ
    (differentiableWithinAt_sectionCoord_alongCurveWithin_leviCivitaConnection hs hV ht)
    (differentiableWithinAt_sectionCoord γ W hW
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  convert hd using 1
  rw [indexFormIntegrandWithin_def, inner_add_left]
  ring

/-- For a `C²` field `V`, the unrestricted pairing `⟪D_t V, W⟫` differentiates to the
index-form integrand plus `⟪D_t² V + R(V, γ') γ', W⟫`. -/
theorem hasDerivAt_inner_alongCurve {t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hW : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) t) :
    HasDerivAt (fun r ↦ inner ℝ (alongCurve (leviCivitaConnection I M) γ V r) (W r))
      (indexFormIntegrand I γ V W t +
        inner ℝ (alongCurve (leviCivitaConnection I M) γ
            (alongCurve (leviCivitaConnection I M) γ V) t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocity I γ t) (curveVelocity I γ t)) (W t)) t := by
  simpa only [hasDerivWithinAt_univ, alongCurveWithin_univ,
    funext (alongCurveWithin_univ (leviCivitaConnection I M) γ V), curveVelocityWithin_univ,
    indexFormIntegrandWithin_univ] using
    hasDerivWithinAt_inner_alongCurveWithin uniqueDiffOn_univ hV.contMDiffWithinAt
      (mem_univ t) hW.mdifferentiableWithinAt

/-- **Integration by parts.** For a field `V` with a `C²` lift within `s` at every point of
`[a, b] ⊆ s` and a `C¹` field `W` on the closed segment,
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫ - ∫_a^b ⟪D_t² V + R(V, γ') γ', W⟫ dt`. -/
theorem indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral
    (hV : ∀ t ∈ uIcc a b, ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hsub : uIcc a b ⊆ s) :
    indexForm I γ V W a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) -
        ∫ t in a..b, inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V s) s t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) := by
  rcases eq_or_ne a b with rfl | hab
  · simp only [indexForm_same, sub_self, intervalIntegral.integral_same]
  let u := uIcc a b
  have hu : UniqueDiffOn ℝ u := uniqueDiffOn_uIcc hab
  have hVu : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) u := fun t ht ↦ (hV t ht).mono hsub
  have hγ (t : ℝ) (ht : t ∈ u) : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t :=
    ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 2)).contMDiffAt
      |>.comp_contMDiffWithinAt t (hV t ht)).mdifferentiableWithinAt (by norm_num)
  -- Restrict the first derivative to the closed segment, where derivatives are unique.
  have hD (r : ℝ) (hr : r ∈ u) : alongCurveWithin (leviCivitaConnection I M) γ V u r =
      alongCurveWithin (leviCivitaConnection I M) γ V s r :=
    alongCurveWithin_subset _ γ V hsub (hu r hr)
      (differentiableWithinAt_sectionCoord γ V
        ((hV r hr).mdifferentiableWithinAt (by norm_num))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
      (by simpa [writtenInExtChartAt] using
        (hγ r hr).differentiableWithinAt_writtenInExtChartAt)
  have hDV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ V s r)) u :=
    (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 1) (m := ∞) (k := ∞)
      (by simp) (by simp) hu hVu).congr fun r hr ↦ by rw [hD r hr]
  let A := fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r)
  let J := fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ V s) s r +
    (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
      (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)) (W r)
  have hA : ContDiffOn ℝ 1 A u := contMDiffOn_iff_contDiffOn.mp
    (ContMDiffOn.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := γ) hDV hW)
  -- On the open segment all within-set derivatives agree with unrestricted ones.
  have hd (t : ℝ) (ht : t ∈ uIoo a b) :
      derivWithin A u t = indexFormIntegrandWithin I γ V W s t + J t := by
    have hut : uIcc a b ∈ 𝓝 t := mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self
    have hst : s ∈ 𝓝 t := mem_of_superset hut hsub
    have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
    have hd := hm.hasDerivWithinAt_inner_alongCurveWithin
        ((hγ t (uIoo_subset_uIcc_self ht)).mono hsub)
        (differentiableWithinAt_sectionCoord γ _
          ((hDV t (uIoo_subset_uIcc_self ht)).mdifferentiableWithinAt one_ne_zero)
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
        (differentiableWithinAt_sectionCoord γ W
          ((hW t (uIoo_subset_uIcc_self ht)).mdifferentiableWithinAt one_ne_zero)
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    have heq := hd.derivWithin (hu t (uIoo_subset_uIcc_self ht))
    dsimp only [A, J]
    rw [heq, indexFormIntegrandWithin_def, inner_add_left]
    simp only [alongCurveWithin_of_mem_nhds _ γ _ hut,
      alongCurveWithin_of_mem_nhds _ γ _ hst]
    ring
  have hdA : IntervalIntegrable (derivWithin A u) MeasureTheory.volume a b :=
    (hA.continuousOn_derivWithin hu le_rfl).intervalIntegrable
  have hI := intervalIntegrable_indexFormIntegrandWithin
    (hVu.of_le one_le_two) hW (uIoo_subset_uIcc_self.trans hsub)
  have hJ : IntervalIntegrable J MeasureTheory.volume a b :=
    (hdA.sub hI).congr_uIoo fun t ht ↦ by
      simp only [hd t ht, add_sub_cancel_left]
  calc indexForm I γ V W a b = ∫ t in a..b, (derivWithin A u t - J t) := by
        rw [indexForm_eq_integral_indexFormIntegrandWithin
          (uIoo_subset_uIcc_self.trans hsub)]
        exact intervalIntegral.integral_congr_uIoo fun t ht ↦ by
          rw [hd t ht, add_sub_cancel_right]
    _ = A b - A a - ∫ t in a..b, J t := by
        rw [intervalIntegral.integral_sub hdA hJ,
          intervalIntegral.integral_derivWithin_uIcc_of_contDiffOn_uIcc hA]

/-- **Integration by parts with unrestricted derivatives.** For a field `V` with a `C²` lift
at every point of `[a, b]` and a field `W` with a `C¹` lift on that closed segment,
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫ - ∫_a^b ⟪D_t² V + R(V, γ') γ', W⟫ dt`. -/
theorem indexForm_eq_inner_sub_inner_sub_integral
    (hV : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ V W a b =
      inner ℝ (alongCurve (leviCivitaConnection I M) γ V b) (W b) -
        inner ℝ (alongCurve (leviCivitaConnection I M) γ V a) (W a) -
        ∫ t in a..b, inner ℝ (alongCurve (leviCivitaConnection I M) γ
            (alongCurve (leviCivitaConnection I M) γ V) t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocity I γ t) (curveVelocity I γ t)) (W t) := by
  simpa only [alongCurveWithin_univ,
    funext (alongCurveWithin_univ (leviCivitaConnection I M) γ V), curveVelocityWithin_univ] using
    indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral
      (s := univ) (fun t ht ↦ (hV t ht).contMDiffWithinAt) hW (subset_univ _)

/-- **Jacobi integration by parts.** For a Jacobi field `V` on a set containing `[a, b]`
and a `C¹` field `W` on that closed segment, `I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. -/
theorem IsJacobiFieldOn.indexForm_eq_inner_sub_inner (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hsub : uIcc a b ⊆ s) :
    indexForm I γ V W a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) := by
  rw [indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral
    (fun t ht ↦ h.contMDiffOn t (hsub ht)) hW hsub,
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      simp only [h.equation t (hsub ht), inner_zero_left],
    intervalIntegral.integral_zero, sub_zero]

/-- If `D_t V(a) + u` is orthogonal to the initial test value, then
`I(V, W) - ⟪u, W(a)⟫ = ⟪D_t V(b), W(b)⟫`. -/
theorem IsJacobiFieldOn.indexForm_sub_inner_eq_inner
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hsub : uIcc a b ⊆ s) {u : TangentSpace I (γ a)}
    (hinit : inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a + u) (W a) = 0) :
    indexForm I γ V W a b - inner ℝ u (W a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) := by
  rw [h.indexForm_eq_inner_sub_inner hW hsub]
  rw [inner_add_left] at hinit
  linarith

/-- If `D_t V(a) + u` is orthogonal to `V(a)` and the Jacobi field vanishes at `b`, then
`I(V, V) - ⟪u, V(a)⟫ = 0`. -/
theorem IsJacobiFieldOn.indexForm_self_sub_inner_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hsub : uIcc a b ⊆ s)
    {u : TangentSpace I (γ a)}
    (hinit : inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a + u) (V a) = 0)
    (hzero : V b = 0) :
    indexForm I γ V V a b - inner ℝ u (V a) = 0 := by
  simpa only [hzero, inner_zero_right] using
    h.indexForm_sub_inner_eq_inner ((h.contMDiffOn.mono hsub).of_le (by norm_num)) hsub hinit

/-- If `D_t V(a) + u` is orthogonal to the initial test value and `W(b) = -D_t V(b)`
is nonzero, then `I(V, W) - ⟪u, W(a)⟫ < 0`. -/
theorem IsJacobiFieldOn.indexForm_sub_inner_neg
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b))
    (hsub : uIcc a b ⊆ s) {u : TangentSpace I (γ a)}
    (hinit : inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a + u) (W a) = 0)
    (hterminal : W b = -alongCurveWithin (leviCivitaConnection I M) γ V s b)
    (hne : alongCurveWithin (leviCivitaConnection I M) γ V s b ≠ 0) :
    indexForm I γ V W a b - inner ℝ u (W a) < 0 := by
  rw [h.indexForm_sub_inner_eq_inner hW hsub hinit, hterminal,
    inner_neg_right, real_inner_self_eq_norm_sq]
  exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hne))

end TauCeti.Manifold
