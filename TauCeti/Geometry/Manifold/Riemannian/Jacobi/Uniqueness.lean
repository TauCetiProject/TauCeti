/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bound

/-!
# Uniqueness of Jacobi fields

A Jacobi field along a geodesic is determined by its value and covariant derivative at one
parameter: on a preconnected parameter set, two Jacobi fields with the same initial data at one
parameter agree everywhere. In particular, two Jacobi fields defined on overlapping parameter sets
agree on the overlap as soon as their initial data agree at one point of a preconnected overlap.

The proof is an energy estimate and needs neither parallel transport nor a chart. For a Jacobi
field `J`, the energy `f = ‖J‖² + ‖DJ‖²` has derivative `2⟨DJ, J⟩ - 2⟨R(J, γ')γ', DJ⟩`. Between
two parameters the geodesic stays in a compact set, on which the curvature tensor is bounded
(`CovariantDerivative.exists_norm_curvatureTensor_le_of_isCompact`), and its speed is constant.
This gives `|f'| ≤ K f` on the parameter interval, so `f` vanishes identically once it vanishes at
one point (`TauCeti.eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc`).

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.hasDerivWithinAt_norm_sq_add_norm_sq`: the energy identity
  `(‖J‖² + ‖DJ‖²)' = 2⟨DJ, J⟩ - 2⟨R(J, γ')γ', DJ⟩`.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_zero_of_eq_zero_of_alongCurveWithin_eq_zero`: a Jacobi
  field with vanishing initial data vanishes on a preconnected parameter set.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq`: Jacobi fields with the same
  initial data agree on a preconnected parameter set.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq_inter`: Jacobi fields on two
  parameter sets with the same initial data at a point of a preconnected overlap agree on the
  overlap.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (existence and uniqueness of Jacobi fields).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s u : Set ℝ} {t₀ t : ℝ}

/-- **The energy identity for Jacobi fields.** The energy `‖J‖² + ‖DJ‖²` of a Jacobi field has
derivative `2⟨DJ, J⟩ - 2⟨R(J, γ')γ', DJ⟩`. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_norm_sq_add_norm_sq (h : IsJacobiFieldOn I γ V s)
    (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ ‖V r‖ ^ 2 +
        ‖alongCurveWithin (leviCivitaConnection I M) γ V s r‖ ^ 2)
      (2 * inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t) (V t) -
        2 * inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t))
          (alongCurveWithin (leviCivitaConnection I M) γ V s t)) s t := by
  set D := alongCurveWithin (leviCivitaConnection I M) γ V s
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ := h.isGeodesicCurveOn.mdifferentiableOn t ht
  have hV := hm.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht) hγ
    (h.differentiableWithinAt_sectionCoord ht) (h.differentiableWithinAt_sectionCoord ht)
  have hD := hm.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht) hγ
    (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
    (h.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
  simp only [← real_inner_self_eq_norm_sq]
  refine (hV.add hD).congr_deriv ?_
  rw [h.alongCurveWithin_alongCurveWithin_eq ht, inner_neg_left, inner_neg_right,
    real_inner_comm (D t) (V t), real_inner_comm (D t)]
  ring

/-- A Jacobi field whose value and covariant derivative vanish at one parameter of a preconnected
parameter set vanishes on that set. -/
theorem IsJacobiFieldOn.eq_zero_of_eq_zero_of_alongCurveWithin_eq_zero
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) (ht₀ : t₀ ∈ s) (hV : V t₀ = 0)
    (hDV : alongCurveWithin (leviCivitaConnection I M) γ V s t₀ = 0) (ht : t ∈ s) :
    V t = 0 := by
  set D := alongCurveWithin (leviCivitaConnection I M) γ V s
  set R := fun r ↦ (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
    (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)
  -- The geodesic between `t₀` and `t` stays in a compact set, where the curvature is bounded,
  -- and it has constant speed `c`.
  have hab : Icc (min t₀ t) (max t₀ t) ⊆ s := hs.Icc_subset
    (by rcases min_choice t₀ t with h | h <;> rw [h] <;> assumption)
    (by rcases max_choice t₀ t with h | h <;> rw [h] <;> assumption)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  obtain ⟨C, hC⟩ := exists_norm_curvatureTensor_le_of_isCompact (F := E)
    (V := fun x : M ↦ TangentSpace I x) (leviCivitaConnection I M)
    (isCompact_Icc.image_of_continuousOn
      (h.isGeodesicCurveOn.contMDiffOn.continuousOn.mono hab))
  set c := ‖curveVelocityWithin I γ s t₀‖
  have hR (r : ℝ) (hr : r ∈ Icc (min t₀ t) (max t₀ t)) : ‖R r‖ ≤ max C 0 * c ^ 2 * ‖V r‖ := by
    have hspeed : ‖curveVelocityWithin I γ s r‖ = c :=
      h.isGeodesicCurveOn.norm_curveVelocityWithin_eq hs (hab hr) ht₀
    calc ‖R r‖ ≤ C * ‖V r‖ * c * c := by
          simpa only [hspeed] using hC (γ r) (mem_image_of_mem γ hr) (V r)
            (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)
      _ ≤ max C 0 * ‖V r‖ * c * c := by gcongr; exact le_max_left C 0
      _ = max C 0 * c ^ 2 * ‖V r‖ := by ring
  -- Hence the derivative of the energy `‖V‖² + ‖DV‖²` is bounded by a multiple of the energy.
  have hbound (r : ℝ) (hr : r ∈ Icc (min t₀ t) (max t₀ t)) :
      ‖2 * inner ℝ (D r) (V r) - 2 * inner ℝ (R r) (D r)‖ ≤
        (1 + max C 0 * c ^ 2) * ‖‖V r‖ ^ 2 + ‖D r‖ ^ 2‖ := by
    have hK : 0 ≤ max C 0 * c ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (a := ‖V r‖ ^ 2 + ‖D r‖ ^ 2) (by positivity)]
    calc |2 * inner ℝ (D r) (V r) - 2 * inner ℝ (R r) (D r)|
        ≤ 2 * (‖D r‖ * ‖V r‖) + 2 * (‖R r‖ * ‖D r‖) := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_two]
          gcongr
          · exact abs_real_inner_le_norm _ _
          · exact abs_real_inner_le_norm _ _
      _ ≤ 2 * (‖D r‖ * ‖V r‖) + 2 * (max C 0 * c ^ 2 * ‖V r‖ * ‖D r‖) := by
          gcongr
          exact hR r hr
      _ = (1 + max C 0 * c ^ 2) * (2 * ‖V r‖ * ‖D r‖) := by ring
      _ ≤ (1 + max C 0 * c ^ 2) * (‖V r‖ ^ 2 + ‖D r‖ ^ 2) := by
          gcongr
          exact two_mul_le_add_sq _ _
  -- Grönwall: the energy vanishes at `t₀`, hence on the whole interval.
  have hft : ‖V t‖ ^ 2 + ‖D t‖ ^ 2 = 0 :=
    TauCeti.eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc
      (fun r hr ↦ (h.hasDerivWithinAt_norm_sq_add_norm_sq (hab hr)).mono hab) hbound
      ⟨min_le_left t₀ t, le_max_left t₀ t⟩ (by simpa [hV] using hDV) t
      ⟨min_le_right t₀ t, le_max_right t₀ t⟩
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm
    (by linarith [sq_nonneg ‖D t‖]) (sq_nonneg _)))

/-- **Uniqueness of Jacobi fields.** Two Jacobi fields along the same geodesic with the same value
and covariant derivative at one parameter of a preconnected parameter set agree on that set. -/
theorem IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq (hV : IsJacobiFieldOn I γ V s)
    (hW : IsJacobiFieldOn I γ W s) (hs : IsPreconnected s) (ht₀ : t₀ ∈ s) (h₀ : V t₀ = W t₀)
    (h₁ : alongCurveWithin (leviCivitaConnection I M) γ V s t₀ =
      alongCurveWithin (leviCivitaConnection I M) γ W s t₀) (ht : t ∈ s) :
    V t = W t := by
  have hW' := hW.const_smul (-1)
  have hD : alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ V r + (-1 : ℝ) • W r) s t₀ =
      alongCurveWithin (leviCivitaConnection I M) γ V s t₀ +
        (-1 : ℝ) • alongCurveWithin (leviCivitaConnection I M) γ W s t₀ := by
    rw [alongCurveWithin_add _ γ V _ s (hV.differentiableWithinAt_sectionCoord ht₀)
      (hW'.differentiableWithinAt_sectionCoord ht₀), alongCurveWithin_const_smul]
  have h := (hV.add hW').eq_zero_of_eq_zero_of_alongCurveWithin_eq_zero hs ht₀
    (by simp [h₀]) (by rw [hD, h₁, neg_one_smul, add_neg_cancel]) ht
  simpa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using h

/-- **Uniqueness of Jacobi fields on overlapping parameter sets.** Two Jacobi fields along the
same geodesic, on parameter sets whose intersection is preconnected with unique derivatives, agree
on the intersection as soon as their values and covariant derivatives agree at one point of it. -/
theorem IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq_inter (hV : IsJacobiFieldOn I γ V s)
    (hW : IsJacobiFieldOn I γ W u) (hsu : IsPreconnected (s ∩ u))
    (hsu' : UniqueDiffOn ℝ (s ∩ u)) (ht₀ : t₀ ∈ s ∩ u) (h₀ : V t₀ = W t₀)
    (h₁ : alongCurveWithin (leviCivitaConnection I M) γ V s t₀ =
      alongCurveWithin (leviCivitaConnection I M) γ W u t₀) (ht : t ∈ s ∩ u) :
    V t = W t :=
  (hV.mono hsu' inter_subset_left).eq_of_eq_of_alongCurveWithin_eq
    (hW.mono hsu' inter_subset_right) hsu ht₀ h₀
    (by rw [hV.alongCurveWithin_subset (hsu' t₀ ht₀) inter_subset_left ht₀,
      hW.alongCurveWithin_subset (hsu' t₀ ht₀) inter_subset_right ht₀, h₁]) ht

end TauCeti.Manifold
