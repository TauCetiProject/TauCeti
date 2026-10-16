/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Quadratic
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Power

/-!
# Exterior points of Schwarz--Christoffel images

If all finite prevertices are integrable and the total turning exponent is less than `1`,
the closure of the Schwarz--Christoffel image is a proper subset of the plane. This provides
an exterior point about which to invert an unbounded polygonal image, reducing boundary
separation questions to bounded images. Boundary simplicity is not required.

For total exponent greater than `-1`, the leading power has opening strictly less than `2π`.
The uniform power asymptotic confines the image at infinity to a slightly wider cone, while
continuity up to the real axis bounds the remaining compact part. At total exponent `-1`,
the real part tends to positive infinity, so the image has a global lower bound on its real part.
For total exponent less than `-1`, the image is bounded and its closure is compact.

At total exponent `1` the leading term `z ^ 2 / 2` maps the upper half-plane onto a slit plane,
whose closure contains a full neighbourhood of infinity, and the logarithmic coefficient
`C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` decides what is left out. When `C < 0`,
for each `δ > 0` the closure of the image misses the points of height strictly between
`im c + π * C + δ` and `im c - δ` that lie sufficiently far to the right, where `c` is the
quadratic constant at infinity and how far to the right depends on `δ`. The heights
`im c + π * C` and `im c` carry the outer sides of an end of opening `2π`, so each such open
sub-band supplies exterior points. Without the sign condition there need not be an exterior
point, as for the slit plane `z ↦ z ^ 2`.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private theorem exists_norm_bound_schwarzChristoffelPrimitive_on_bounded_part
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ upperHalfPlaneSet, ‖z‖ ≤ R →
      ‖schwarzChristoffelPrimitive a e z₀ z‖ ≤ M := by
  let K := closedBall (0 : ℂ) R ∩ closure upperHalfPlaneSet
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_closure
  obtain ⟨M, hMpos, hM⟩ :=
    (hK.image_of_continuousOn
      ((continuousOn_extendFrom_schwarzChristoffelPrimitive a e z₀ hfinite).mono
        inter_subset_right)).isBounded.exists_pos_norm_le
  refine ⟨M, hMpos.le, fun z hz hzR => ?_⟩
  have hzK : z ∈ K := ⟨by simpa using hzR, subset_closure hz⟩
  have h := hM _ (mem_image_of_mem _ hzK)
  rw [extendFrom_extends
    (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hz] at h
  exact h

/-- In the power regime with opening less than `2π`, a rotation of the primitive eventually
lies in a closed cone strictly smaller than the full plane. -/
private theorem exists_eventually_cone_schwarzChristoffelPrimitive
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hlow : -1 < ∑ i, e i)
    (hhigh : ∑ i, e i < 1) :
    ∃ (u : ℂ) (k : ℝ), ‖u‖ = 1 ∧ 0 ≤ k ∧ k < 1 ∧
      ∀ᶠ z in cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet,
        0 ≤ (u * schwarzChristoffelPrimitive a e z₀ z).re +
          k * ‖schwarzChristoffelPrimitive a e z₀ z‖ := by
  let β : ℝ := (∑ i, e i) + 1
  let θ : ℝ := β * Real.pi / 2
  let c : ℝ := Real.cos θ
  -- Center the leading sector on the positive real axis. Its cosine lower bound is
  -- strictly greater than `-1`, leaving room for the asymptotic error.
  let η : ℝ := (1 + c) / 4
  let u : ℂ := exp ((-θ : ℝ) * Complex.I)
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβhigh : β < 2 := by dsimp [β]; linarith
  have hθ : 0 ≤ θ ∧ θ < Real.pi := by
    dsimp [θ]
    constructor <;> nlinarith [Real.pi_pos, hβhigh]
  have hc : -1 < c := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1 le_rfl hθ.2
    simpa [c] using h
  have hη : 0 < η := by dsimp [η]; linarith
  have hηle : η ≤ 1 / 2 := by dsimp [η, c]; linarith [Real.cos_le_one θ]
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  refine ⟨u, 1 - η, hu, by linarith, by linarith, ?_⟩
  have hlim := tendsto_schwarzChristoffelPrimitive_div_cpow_atInfinity_of_neg_one_lt_sum
    a e z₀ hlow
  have hnear := hlim.eventually (closedBall_mem_nhds _ (div_pos hη hβ))
  filter_upwards [hnear, mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz hzH
  let P : ℂ := z ^ (β : ℂ) / (β : ℂ)
  let F : ℂ := schwarzChristoffelPrimitive a e z₀ z
  have hz0 : z ≠ 0 := fun h => by simp [h] at hzH
  have hpow0 : z ^ (β : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hβnorm : ‖(β : ℂ)‖ = β := by simp [abs_of_pos hβ]
  -- Convert the uniform ratio limit into a relative error for the leading power.
  have herror : ‖F - P‖ ≤ η * ‖P‖ := by
    have hmul := mul_le_mul_of_nonneg_right hz (norm_nonneg (z ^ (β : ℂ)))
    rw [dist_eq_norm] at hmul
    have heq : (F / z ^ (β : ℂ) - (β : ℂ)⁻¹) * z ^ (β : ℂ) = F - P := by
      dsimp [P]
      field_simp
    rw [← norm_mul, heq] at hmul
    calc
      ‖F - P‖ ≤ η / β * ‖z ^ (β : ℂ)‖ := hmul
      _ = η * ‖P‖ := by
        dsimp only [P]
        rw [norm_div, hβnorm]
        ring
  have hcone : c * ‖P‖ ≤ (u * P).re := by
    have harg : |z.arg * β - θ| ≤ θ := by
      apply abs_le.mpr
      constructor <;> dsimp [θ] <;>
        nlinarith [arg_nonneg_iff.mpr hzH.le, arg_le_pi z]
    have hcos : c ≤ Real.cos (z.arg * β - θ) := by
      simpa only [Real.cos_abs] using
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hθ.2.le harg
    have hure : u.re = Real.cos θ := by
      simpa only [Real.cos_neg] using exp_ofReal_mul_I_re (-θ)
    have huim : u.im = -Real.sin θ := by
      simpa only [Real.sin_neg] using exp_ofReal_mul_I_im (-θ)
    have hre : (u * P).re = ‖P‖ * Real.cos (z.arg * β - θ) := by
      simp [P, mul_div_assoc, Complex.mul_re, cpow_ofReal_re, cpow_ofReal_im,
        hure, huim, Real.cos_sub, abs_of_pos hβ]
      ring
    rw [hre]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcos (norm_nonneg P)
  -- Widen the leading cone from cosine bound `c` to `-(1 - η)`; the same
  -- error estimate controls both the real part and the norm of the primitive.
  have hreError : |(u * (F - P)).re| ≤ η * ‖P‖ := by
    exact (abs_re_le_norm _).trans (by simpa [norm_mul, hu] using herror)
  have hre : c * ‖P‖ - η * ‖P‖ ≤ (u * F).re := by
    have h := (abs_le.mp hreError).1
    simp only [mul_sub, sub_re] at h
    linarith
  have hnorm : (1 - η) * ‖P‖ ≤ ‖F‖ := by
    have h := norm_sub_norm_le P F
    rw [norm_sub_rev] at h
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hnorm (by linarith : 0 ≤ 1 - η)
  have hpositive : 0 ≤ (c - η + (1 - η) ^ 2) * ‖P‖ := by
    apply mul_nonneg _ (norm_nonneg _)
    dsimp [η]
    nlinarith [sq_nonneg (1 + c)]
  nlinarith

/-- **A Schwarz--Christoffel image has an exterior point** if the finite prevertices
are integrable and the total exponent is less than `1`. The point lies outside the closure
of the image, not merely outside the image. No simplicity or sign assumptions are imposed on
the finite turning data. -/
theorem exists_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_lt_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hhigh : ∑ i, e i < 1) :
    ∃ q : ℂ, q ∉ closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
  by_cases hbounded : ∑ i, e i < -1
  · have hcompact :=
      (isBounded_image_schwarzChristoffelPrimitive a e z₀ hfinite hbounded).isCompact_closure
    exact (ne_univ_iff_exists_notMem _).mp hcompact.ne_univ
  have hlow : -1 ≤ ∑ i, e i := le_of_not_gt hbounded
  -- Both asymptotic regimes yield an eventual cone inequality; the logarithmic case is
  -- the half-plane `re ≥ 0` and needs no rotation.
  have hcone : ∃ (u : ℂ) (k : ℝ), ‖u‖ = 1 ∧ 0 ≤ k ∧ k < 1 ∧
      ∀ᶠ z in cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet,
        0 ≤ (u * schwarzChristoffelPrimitive a e z₀ z).re +
          k * ‖schwarzChristoffelPrimitive a e z₀ z‖ := by
    rcases hlow.eq_or_lt with hlog | hpow
    · refine ⟨1, 0, by simp, le_rfl, zero_lt_one, ?_⟩
      have h := (tendsto_re_schwarzChristoffelPrimitive_atTop_of_sum_eq_neg_one
        a e z₀ hlog.symm).eventually (eventually_ge_atTop 0)
      simpa using h
    · exact exists_eventually_cone_schwarzChristoffelPrimitive a e z₀ hpow hhigh
  obtain ⟨u, k, hu, hk, hk1, htail⟩ := hcone
  rw [eventually_inf_principal, hasBasis_cobounded_norm.eventually_iff] at htail
  obtain ⟨R, _, hR⟩ := htail
  obtain ⟨M, hM, hbound⟩ :=
    exists_norm_bound_schwarzChristoffelPrimitive_on_bounded_part a e z₀ hfinite R
  let C : Set ℂ := {w | -M ≤ (u * w).re + k * ‖w‖}
  have hC : IsClosed C := isClosed_le continuous_const (by fun_prop)
  have hsub : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ C := by
    rintro w ⟨z, hz, rfl⟩
    by_cases hzR : R ≤ ‖z‖
    · exact (neg_nonpos.mpr hM).trans (hR hzR hz)
    · have hnorm := hbound z hz (not_le.mp hzR).le
      have hre := (abs_le.mp (abs_re_le_norm (u * schwarzChristoffelPrimitive a e z₀ z))).1
      simp only [norm_mul, hu, one_mul] at hre
      have hpos := mul_nonneg hk (norm_nonneg (schwarzChristoffelPrimitive a e z₀ z))
      exact ((neg_le_neg hnorm).trans hre).trans (le_add_of_nonneg_right hpos)
  -- The compact part only translates the cone inequality. A sufficiently distant
  -- point on its negative axis is still outside this closed set and hence the image closure.
  let T : ℝ := (M + 1) / (1 - k)
  have hT : 0 < T := div_pos (by linarith) (by linarith)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  refine ⟨(-T : ℂ) / u, fun hq => ?_⟩
  have h := closure_minimal hsub hC hq
  have heq : u * ((-T : ℂ) / u) = (-T : ℂ) := mul_div_cancel₀ _ hu0
  have hnorm : ‖(-T : ℂ) / u‖ = T := by simp [hu, abs_of_pos hT]
  simp only [C, mem_ofPred_eq, heq, hnorm, neg_re, ofReal_re] at h
  have hTmul : T * (1 - k) = M + 1 := div_mul_cancel₀ _ (by linarith)
  nlinarith

/-- **The far-right band missed by an image with an end of opening `2π`.** Suppose the finite
prevertices are integrable, the total exponent is `1`, and the logarithmic coefficient
`C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is negative. Then for each `δ > 0`,
sufficiently far to the right, no point whose height lies strictly between `im c + π * C + δ`
and `im c - δ` is in the closure of the image, where `c` is the quadratic constant at infinity.
No simplicity or ordering assumption on the finite data is imposed. -/
theorem exists_forall_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = 1)
    (hC : (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ w : ℂ, R < w.re →
      (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im +
          Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) + δ < w.im →
        w.im < (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im - δ →
          w ∉ closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
  set M : ℝ := ∑ i, e i * a i
  set C : ℝ := (M ^ 2 - ∑ i, e i * a i ^ 2) / 2
  set c := schwarzChristoffelQuadraticConstantAtInfinity a e z₀
  set F := schwarzChristoffelPrimitive a e z₀
  have hCneg : C < 0 := by simp only [C]; linarith
  have hQ (z : ℂ) : z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
      ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z =
      z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z := by
    simp only [M, C]
    push_cast
    rfl
  have htail : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet,
      ‖F z - (z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z) - c‖ < δ / 2 := by
    have h := (tendsto_schwarzChristoffelPrimitive_sub_quadratic_atInfinity_of_sum_eq_one
      a e z₀ hsum).eventually (ball_mem_nhds c (half_pos hδ))
    simp only [hQ] at h
    exact h.mono fun z hz => mem_ball_iff_norm.mp hz
  rw [eventually_inf_principal, hasBasis_cobounded_norm.eventually_iff] at htail
  obtain ⟨A, _, htail⟩ := htail
  obtain ⟨R₁, hR₁⟩ := exists_forall_im_quadratic_log_notMem_Ioo (M := M) hCneg (half_pos hδ)
  obtain ⟨B, _, hB⟩ :=
    exists_norm_bound_schwarzChristoffelPrimitive_on_bounded_part a e z₀ hfinite (max A R₁)
  set R := max B (c.re + δ / 2 + 1 / 2)
  refine ⟨R, fun w hwR hwlo hwhi hw => ?_⟩
  -- The image lies in a closed set that misses the far-right band.
  let S : Set ℂ := {w | w.re ≤ R} ∪ ({w | c.im - δ ≤ w.im} ∪ {w | w.im ≤ c.im + Real.pi * C + δ})
  have hS : IsClosed S :=
    (isClosed_le Complex.continuous_re continuous_const).union
      ((isClosed_le continuous_const Complex.continuous_im).union
        (isClosed_le Complex.continuous_im continuous_const))
  have hsub : F '' upperHalfPlaneSet ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hnot
    simp only [S, mem_union, mem_ofPred_eq, not_or, not_le] at hnot
    obtain ⟨hre, hhi, hlo⟩ := hnot
    have hzR : max A R₁ < ‖z‖ := by
      by_contra h
      linarith [re_le_norm (F z), hB z hz (not_lt.mp h), le_max_left B (c.re + δ / 2 + 1 / 2)]
    have herr := htail ((le_max_left _ _).trans hzR.le) hz
    have hreErr := (abs_le.mp ((abs_re_le_norm _).trans herr.le)).2
    have himErr := abs_lt.mp ((abs_im_le_norm _).trans_lt herr)
    simp only [sub_re, sub_im] at hreErr himErr
    exact hR₁ z hz ((le_max_right _ _).trans hzR.le)
      (by linarith [le_max_right B (c.re + δ / 2 + 1 / 2)])
      ⟨by linarith [himErr.2], by linarith [himErr.1]⟩
  exact (closure_minimal hsub hS hw).elim (fun h => not_le.mpr hwR h)
    (fun h => h.elim (fun h => not_le.mpr hwhi h) (fun h => not_le.mpr hwlo h))

/-- **A Schwarz--Christoffel image with an end of opening `2π` has an exterior point** if the
finite prevertices are integrable, the total exponent is `1`, and the logarithmic coefficient
`((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is negative. The point lies outside the closure
of the image. No simplicity or ordering assumption on the finite data is imposed. -/
theorem exists_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = 1)
    (hC : (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2) :
    ∃ q : ℂ, q ∉ closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
  have hCneg : ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2 < 0 := by linarith
  obtain ⟨R, hR⟩ :=
    exists_forall_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_eq_one a e z₀
      hfinite hsum hC (δ := -(Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2)) / 4)
      (by nlinarith [Real.pi_pos])
  set C : ℝ := ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2
  -- Take a far-right point halfway between the two outer heights.
  exact ⟨⟨R + 1, (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im + Real.pi * C / 2⟩,
    hR _ (by simp) (by dsimp only; nlinarith [Real.pi_pos])
      (by dsimp only; nlinarith [Real.pi_pos])⟩

end TauCeti
