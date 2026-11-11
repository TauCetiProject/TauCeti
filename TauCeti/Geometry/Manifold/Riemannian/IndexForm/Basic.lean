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
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AlongCurve

/-!
# The index form and integration by parts

Let `γ` be a curve in a Riemannian manifold and `V`, `W` tangent fields along `γ`. The index form
of `V` and `W` on `[a, b]` is

`I(V, W) = ∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt`,

with the curvature convention `R(X, Y) Z = [∇_X, ∇_Y] Z - ∇_[X, Y] Z` of the Jacobi equation. The
velocity and the covariant derivatives are taken within a parameter set `s`, so that the index
form is defined on closed segments; where `s` is a neighbourhood of the open segment, it agrees
with the index form for unrestricted derivatives. It only depends on the fields on the open
segment. It is symmetric, and on `C¹` fields it is bilinear and additive over adjacent segments.

For a `C²` field `V`, `⟪D_t V, W⟫` differentiates to the integrand plus `⟪D_t² V + R(V, γ') γ', W⟫`,
which gives the integration by parts
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫ - ∫_a^b ⟪D_t² V + R(V, γ') γ', W⟫ dt`.
For a Jacobi field `V` the last integral vanishes. If moreover `D_t V(a) = -S V(a)` for an
endomorphism `S` of the initial tangent space, the initial boundary term is `⟪S V(a), W(a)⟫`.
This is the correction of the index form for an initial point moving along a submanifold with
shape operator `S`.

## Main definitions and results

* `TauCeti.Manifold.indexFormIntegrandWithin` and `TauCeti.Manifold.indexFormWithin`: the
  integrand of the index form and the index form.
* `TauCeti.Manifold.indexFormWithin_congr`: the index form depends only on the curve and on the
  fields on the open segment.
* `TauCeti.Manifold.indexFormWithin_of_mem_nhds`: on a neighbourhood of the open segment,
  derivatives within the parameter set give the unrestricted index form.
* `TauCeti.Manifold.indexFormWithin_comm`, `TauCeti.Manifold.indexFormWithin_add_left`,
  `TauCeti.Manifold.indexFormWithin_const_smul_left` and
  `TauCeti.Manifold.indexFormWithin_add_adjacent_intervals`: symmetry, bilinearity and
  additivity over segments.
* `TauCeti.Manifold.indexFormWithin_eq_boundary_sub_integral`: integration by parts.
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
  -- `uIoo a b` is the open interval `Ioo (a ⊓ b) (a ⊔ b)`.
  have hnhds (t : ℝ) (ht : t ∈ uIoo a b) : uIoo a b ∈ 𝓝 t := by
    rw [uIoo] at ht ⊢
    exact isOpen_Ioo.mem_nhds ht
  -- Fields agreeing on the open segment have the same value and covariant derivative there.
  have hcongr {X Y : ∀ t, TangentSpace I (γ t)} (hXY : ∀ t ∈ uIoo a b, HEq (X t) (Y t))
      (t : ℝ) (ht : t ∈ uIoo a b) : X t = Y t ∧
        alongCurveWithin (leviCivitaConnection I M) γ X s t =
          alongCurveWithin (leviCivitaConnection I M) γ Y s t := by
    have hpt : X t = Y t := eq_of_heq (hXY t ht)
    refine ⟨hpt, alongCurveWithin_congr _ γ X ?_ hpt⟩
    filter_upwards [nhdsWithin_le_nhds (hnhds t ht)] with r hr using eq_of_heq (hXY r hr)
  rw [indexFormWithin, indexFormWithin]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  obtain ⟨hv, hdv⟩ := hcongr hV t ht
  obtain ⟨hw, hdw⟩ := hcongr hW t ht
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def, hdv, hdw, hv, hw]

/-- Where the parameter set is a neighbourhood of `t`, the integrand of the index form at `t`
is the one with unrestricted derivatives. -/
theorem indexFormIntegrandWithin_of_mem_nhds {t : ℝ} (hs : s ∈ 𝓝 t) :
    indexFormIntegrandWithin I γ V W s t = indexFormIntegrandWithin I γ V W univ t := by
  simp only [indexFormIntegrandWithin_def, alongCurveWithin_univ, curveVelocityWithin_univ,
    alongCurveWithin_of_mem_nhds _ γ V hs, alongCurveWithin_of_mem_nhds _ γ W hs,
    curveVelocityWithin_of_mem_nhds (I := I) (γ := γ) hs]

/-- If the parameter set is a neighbourhood of every point of the open segment, the index form is
the one with unrestricted derivatives. -/
theorem indexFormWithin_of_mem_nhds (hs : ∀ t ∈ uIoo a b, s ∈ 𝓝 t) :
    indexFormWithin I γ V W s a b = indexFormWithin I γ V W univ a b :=
  intervalIntegral.integral_congr_uIoo fun t ht ↦ indexFormIntegrandWithin_of_mem_nhds (hs t ht)

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
theorem indexFormWithin_comm :
    indexFormWithin I γ V W s a b = indexFormWithin I γ W V s a b :=
  intervalIntegral.integral_congr fun t _ ↦ indexFormIntegrandWithin_comm t

/-- The integrand of the index form is additive in the first field, at a parameter where both
fields are differentiable within the parameter set. -/
theorem indexFormIntegrandWithin_add_left {t : ℝ}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hV' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V' (γ t)) s t) :
    indexFormIntegrandWithin I γ (fun r ↦ V r + V' r) W s t =
      indexFormIntegrandWithin I γ V W s t + indexFormIntegrandWithin I γ V' W s t := by
  simp only [indexFormIntegrandWithin_def, alongCurveWithin_add _ γ V V' s hV hV', map_add,
    LinearMap.add_apply, inner_add_left]
  ring

/-- The integrand of the index form is additive in the second field, at a parameter where both
fields are differentiable within the parameter set. -/
theorem indexFormIntegrandWithin_add_right {t : ℝ}
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hW' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W' (γ t)) s t) :
    indexFormIntegrandWithin I γ V (fun r ↦ W r + W' r) s t =
      indexFormIntegrandWithin I γ V W s t + indexFormIntegrandWithin I γ V W' s t := by
  rw [indexFormIntegrandWithin_comm, indexFormIntegrandWithin_add_left hW hW',
    indexFormIntegrandWithin_comm, indexFormIntegrandWithin_comm (V := W')]

/-- The integrand of the index form is homogeneous in the first field. -/
theorem indexFormIntegrandWithin_const_smul_left (c : ℝ) (t : ℝ) :
    indexFormIntegrandWithin I γ (fun r ↦ c • V r) W s t =
      c * indexFormIntegrandWithin I γ V W s t := by
  simp only [indexFormIntegrandWithin_def, alongCurveWithin_const_smul, map_smul,
    LinearMap.smul_apply, real_inner_smul_left]
  ring

/-- The integrand of the index form is homogeneous in the second field. -/
theorem indexFormIntegrandWithin_const_smul_right (c : ℝ) (t : ℝ) :
    indexFormIntegrandWithin I γ V (fun r ↦ c • W r) s t =
      c * indexFormIntegrandWithin I γ V W s t := by
  rw [indexFormIntegrandWithin_comm, indexFormIntegrandWithin_const_smul_left,
    indexFormIntegrandWithin_comm]

/-- The index form is homogeneous in the first field. -/
theorem indexFormWithin_const_smul_left (c : ℝ) :
    indexFormWithin I γ (fun r ↦ c • V r) W s a b = c * indexFormWithin I γ V W s a b := by
  simp only [indexFormWithin, indexFormIntegrandWithin_const_smul_left,
    intervalIntegral.integral_const_mul]

/-- The index form is homogeneous in the second field. -/
theorem indexFormWithin_const_smul_right (c : ℝ) :
    indexFormWithin I γ V (fun r ↦ c • W r) s a b = c * indexFormWithin I γ V W s a b := by
  rw [indexFormWithin_comm, indexFormWithin_const_smul_left, indexFormWithin_comm]

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
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) hs (by simpa using hV))
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) hs
        (by simpa using hW))).continuousOn
  have hR :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      ((leviCivitaConnection I M).contMDiffOn_curvatureTensor (by simp)
        (hV.of_le zero_le_one) hvel hvel)
      (hW.of_le zero_le_one)).continuousOn
  exact (hD.sub hR).congr fun t _ ↦ indexFormIntegrandWithin_def t

/-- The integrand of the index form of `C¹` fields is integrable on a segment inside a parameter
set with unique derivatives. -/
theorem intervalIntegrable_indexFormIntegrandWithin (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) :
    IntervalIntegrable (indexFormIntegrandWithin I γ V W s) MeasureTheory.volume a b :=
  ((continuousOn_indexFormIntegrandWithin hs hV hW).mono hsub).intervalIntegrable

/-- The index form is additive in the first field on `C¹` fields. -/
theorem indexFormWithin_add_left (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hV' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) :
    indexFormWithin I γ (fun r ↦ V r + V' r) W s a b =
      indexFormWithin I γ V W s a b + indexFormWithin I γ V' W s a b := by
  rw [indexFormWithin, indexFormWithin, indexFormWithin, ← intervalIntegral.integral_add
    (intervalIntegrable_indexFormIntegrandWithin hs hV hW hsub)
    (intervalIntegrable_indexFormIntegrandWithin hs hV' hW hsub)]
  exact intervalIntegral.integral_congr fun t ht ↦ indexFormIntegrandWithin_add_left
    (differentiableWithinAt_sectionCoord γ V ((hV t (hsub ht)).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    (differentiableWithinAt_sectionCoord γ V' ((hV' t (hsub ht)).mdifferentiableWithinAt
      one_ne_zero) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))

/-- The index form is additive in the second field on `C¹` fields. -/
theorem indexFormWithin_add_right (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hW' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W' r)) s)
    (hsub : uIcc a b ⊆ s) :
    indexFormWithin I γ V (fun r ↦ W r + W' r) s a b =
      indexFormWithin I γ V W s a b + indexFormWithin I γ V W' s a b := by
  rw [indexFormWithin_comm, indexFormWithin_add_left hs hW hW' hV hsub, indexFormWithin_comm,
    indexFormWithin_comm (V := W')]

/-- The index form of `C¹` fields is additive over adjacent segments. -/
theorem indexFormWithin_add_adjacent_intervals {c : ℝ} (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hab : uIcc a b ⊆ s) (hbc : uIcc b c ⊆ s) :
    indexFormWithin I γ V W s a b + indexFormWithin I γ V W s b c =
      indexFormWithin I γ V W s a c :=
  intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_indexFormIntegrandWithin hs hV hW hab)
    (intervalIntegrable_indexFormIntegrandWithin hs hV hW hbc)

/-! ### Integration by parts -/

/-- For a `C²` field `V`, the pairing `⟪D_t V, W⟫` differentiates to the integrand of the index
form plus `⟪D_t² V + R(V, γ') γ', W⟫`. -/
theorem hasDerivWithinAt_inner_alongCurveWithin (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    {t : ℝ} (ht : t ∈ s)
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
    ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 2)).comp_contMDiffOn
      hV t ht).mdifferentiableWithinAt (by norm_num)
  have hd := hm.hasDerivWithinAt_inner_alongCurveWithin hγ
    (differentiableWithinAt_sectionCoord_alongCurveWithin_leviCivitaConnection hs hV ht)
    (differentiableWithinAt_sectionCoord γ W hW
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  convert hd using 1
  rw [indexFormIntegrandWithin_def, inner_add_left]
  ring

/-- **Integration by parts.** For a `C²` field `V` and a `C¹` field `W` on a parameter set with
unique derivatives containing `[a, b]`,
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫ - ∫_a^b ⟪D_t² V + R(V, γ') γ', W⟫ dt`. -/
theorem indexFormWithin_eq_boundary_sub_integral (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) :
    indexFormWithin I γ V W s a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) -
        ∫ t in a..b, inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V s) s t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) := by
  let A := fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r)
  let J := fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ V s) s r +
    (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
      (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)) (W r)
  have hA : ContDiffOn ℝ 1 A s := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact ContMDiffOn.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 1) hs hV) hW
  have hd (t : ℝ) (ht : t ∈ s) :
      derivWithin A s t = indexFormIntegrandWithin I γ V W s t + J t :=
    (hasDerivWithinAt_inner_alongCurveWithin hs hV ht
      ((hW t ht).mdifferentiableWithinAt one_ne_zero)).derivWithin (hs t ht)
  have hdA : ContinuousOn (derivWithin A s) s := hA.continuousOn_derivWithin hs le_rfl
  have hJ : ContinuousOn J s :=
    (hdA.sub (continuousOn_indexFormIntegrandWithin hs (hV.of_le one_le_two) hW)).congr
      fun t ht ↦ by rw [Pi.sub_apply, hd t ht, add_sub_cancel_left]
  -- `uIcc a b` is the closed interval `Icc (min a b) (max a b)`.
  have hsub' : Icc (min a b) (max a b) ⊆ s := by rwa [Icc_min_max]
  have hFTC : ∫ t in a..b, derivWithin A s t = A b - A a := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hA.continuousOn.mono hsub) _ (hdA.mono hsub).intervalIntegrable
    intro t ht
    have hs' : s ∈ 𝓝 t := mem_of_superset (Icc_mem_nhds ht.1 ht.2) hsub'
    exact ((hA t (hsub' (Ioo_subset_Icc_self ht))).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt |>.hasDerivAt hs').hasDerivWithinAt
  calc indexFormWithin I γ V W s a b = ∫ t in a..b, (derivWithin A s t - J t) := by
        rw [indexFormWithin]
        refine intervalIntegral.integral_congr fun t ht ↦ ?_
        rw [hd t (hsub ht), add_sub_cancel_right]
    _ = A b - A a - ∫ t in a..b, J t := by
        rw [intervalIntegral.integral_sub (hdA.mono hsub).intervalIntegrable
          (hJ.mono hsub).intervalIntegrable, hFTC]

/-- The pairing `⟪D_t V, W⟫` of the covariant derivative of a Jacobi field `V` with a field `W`
differentiable at `t` differentiates to the integrand of the index form. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin
    (h : IsJacobiFieldOn I γ V s) {t : ℝ} (ht : t ∈ s)
    (hW : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s t) :
    HasDerivWithinAt (fun r ↦ inner ℝ
        (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r))
      (indexFormIntegrandWithin I γ V W s t) s t := by
  simpa only [h.equation t ht, inner_zero_left, add_zero] using
    TauCeti.Manifold.hasDerivWithinAt_inner_alongCurveWithin h.uniqueDiffOn h.contMDiffOn ht hW

/-- **Jacobi integration by parts.** For a Jacobi field `V` and a `C¹` field `W` on a parameter
set containing `[a, b]`, `I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. -/
theorem IsJacobiFieldOn.indexFormWithin_eq_boundary (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) :
    indexFormWithin I γ V W s a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) := by
  rw [indexFormWithin_eq_boundary_sub_integral h.uniqueDiffOn h.contMDiffOn hW hsub,
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      simp only [h.equation t (hsub ht), inner_zero_left],
    intervalIntegral.integral_zero, sub_zero]

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -S V(a)`, then
`I(V, W) - ⟪S V(a), W(a)⟫ = ⟪D_t V(b), W(b)⟫`. -/
theorem IsJacobiFieldOn.indexFormWithin_sub_initial_eq_boundary
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) {S : TangentSpace I (γ a) →ₗ[ℝ] TangentSpace I (γ a)}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -S (V a)) :
    indexFormWithin I γ V W s a b - inner ℝ (S (V a)) (W a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) := by
  rw [h.indexFormWithin_eq_boundary hW hsub, hinit, inner_neg_left]
  ring

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -S V(a)` and vanishes at `b`, then
`I(V, V) - ⟪S V(a), V(a)⟫ = 0`. -/
theorem IsJacobiFieldOn.indexFormWithin_self_sub_initial_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hsub : uIcc a b ⊆ s)
    {S : TangentSpace I (γ a) →ₗ[ℝ] TangentSpace I (γ a)}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -S (V a))
    (hzero : V b = 0) :
    indexFormWithin I γ V V s a b - inner ℝ (S (V a)) (V a) = 0 := by
  simpa only [hzero, inner_zero_right] using
    h.indexFormWithin_sub_initial_eq_boundary (h.contMDiffOn.of_le (by norm_num)) hsub hinit

/-- If the Jacobi field `V` has initial derivative `D_t V(a) = -S V(a)` and `W(b) = -D_t V(b)`
is nonzero, then `I(V, W) - ⟪S V(a), W(a)⟫ < 0`. -/
theorem IsJacobiFieldOn.indexFormWithin_sub_initial_neg
    (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) s)
    (hsub : uIcc a b ⊆ s) {S : TangentSpace I (γ a) →ₗ[ℝ] TangentSpace I (γ a)}
    (hinit : alongCurveWithin (leviCivitaConnection I M) γ V s a = -S (V a))
    (hterminal : W b = -alongCurveWithin (leviCivitaConnection I M) γ V s b)
    (hne : alongCurveWithin (leviCivitaConnection I M) γ V s b ≠ 0) :
    indexFormWithin I γ V W s a b - inner ℝ (S (V a)) (W a) < 0 := by
  rw [h.indexFormWithin_sub_initial_eq_boundary hW hsub hinit, hterminal,
    inner_neg_right, real_inner_self_eq_norm_sq]
  exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hne))

end TauCeti.Manifold
