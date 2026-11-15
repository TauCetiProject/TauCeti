/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Conformal

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Conformally Euclidean asymptotically Euclidean ends

Given a smooth positive conformal factor `w : ℝⁿ → ℝ` whose deviation `w - 1` decays at order `t`
up to second derivatives outside `{x : ‖x‖ ≤ r}`, rescaling the standard Euclidean metric by `w`
on `WithMetric` produces a smooth asymptotically Euclidean end of order `t` and a one-ended
`FiniteEndedAE` manifold. Specializing to a smoothly cut-off version of
`(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))` (`3 ≤ n`) yields a smooth globally positive non-flat
model manifold of decay order `n - 2` for every real parameter `c`.

## Main definitions

* `TauCeti.AsymptoticallyEuclideanEnd.conformalEuclidean`,
  `TauCeti.FiniteEndedAE.conformalEuclidean`: smooth conformally Euclidean ends and one-ended
  manifolds on `WithMetric` from a scalar `O_2(‖x‖ ^ (-t))` conformal factor.
* `TauCeti.schwarzschildModelFactor`, `TauCeti.schwarzschildModelMetric`,
  `TauCeti.schwarzschildModelEnd`, `TauCeti.schwarzschildModelAE`: smooth globally positive
  conformal model on `ℝⁿ` (`3 ≤ n`) agreeing outside a ball with
  `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) • g_eucl`, giving a non-flat end of order `n - 2`.

## Main results

* `TauCeti.pullbackMetricCoeff_toWithMetric_rescale`: pulling back `f • g_eucl` along
  `WithMetric.toWithMetric` gives `f x * δ_ij`.
* `TauCeti.contDiff_schwarzschildModelFactor`, `TauCeti.schwarzschildModelFactor_pos`,
  `TauCeti.schwarzschildModelFactor_of_lt`: global smoothness, positivity, and exterior formula
  for `schwarzschildModelFactor`.
-/

public section

noncomputable section

open Bundle Filter Function Metric Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

/-- Pulling back the conformally rescaled Euclidean metric `f • g_eucl` along
`WithMetric.toWithMetric` yields the conformally flat coefficients `f x * δ_ij`. -/
@[simp]
theorem pullbackMetricCoeff_toWithMetric_rescale {n : ℕ} {k : ℕ∞ω}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ) k f) (hf_pos : ∀ x, 0 < f x)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff
      (WithMetric.toWithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE le_top).rescale
          f hf hf_pos))
      x i j = f x * if i = j then 1 else 0 := by
  let g₀ := (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := k) le_top
  let g := g₀.rescale f hf hf_pos
  let bi : TangentSpace (𝓡 n) x := EuclideanSpace.basisFun (Fin n) ℝ i
  let bj : TangentSpace (𝓡 n) x := EuclideanSpace.basisFun (Fin n) ℝ j
  have h1 := WithMetric.inner_rescale (I := 𝓡 n) (WithMetric.toWithMetric g x)
    (mfderiv (𝓡 n) (𝓡 n) (WithMetric.toWithMetric g) x bi)
    (mfderiv (𝓡 n) (𝓡 n) (WithMetric.toWithMetric g) x bj)
  rw [WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    ContMDiffRiemannianMetric.ofLE_inner] at h1
  rw [pullbackMetricCoeff_def]
  exact h1.trans (congrArg (f x * ·)
    (orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j))

/-! ### General conformally Euclidean ends on `WithMetric` -/

section ConformalEuclidean

variable {n : ℕ} {t r : ℝ} (hr : 0 < r) {w : EuclideanSpace ℝ (Fin n) → ℝ}
  (hw : ContDiff ℝ ∞ w) (hw_pos : ∀ x, 0 < w x)
  (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ →
    |w x - 1| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ w x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ C * ‖x‖ ^ (-t - 2))
include hr hdecay

/-- Package any smooth positive conformal factor `w : ℝⁿ → ℝ` satisfying `w - 1 = O_2(‖x‖ ^ (-t))`
on `{x | r < ‖x‖}` as an `AsymptoticallyEuclideanEnd` on
`WithMetric (((riemannianMetricVectorSpace _).ofLE le_top).rescale w hw.contMDiff hw_pos)`. -/
def AsymptoticallyEuclideanEnd.conformalEuclidean :
    AsymptoticallyEuclideanEnd n
      (WithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
          w hw.contMDiff hw_pos)) t := by
  let g := ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
    w hw.contMDiff hw_pos
  have hopen : IsOpen (WithMetric.toWithMetric g '' {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖}) := by
    rw [← WithMetric.coe_diffeomorph_symm (g := g) ∞]
    exact (WithMetric.diffeomorph g ∞).symm.toHomeomorph.isOpenMap _
      (isOpen_lt continuous_const continuous_norm)
  refine AsymptoticallyEuclideanEnd.ofFun r hr (WithMetric.toWithMetric g)
    WithMetric.contMDiff_toWithMetric.contMDiffOn
    (WithMetric.toWithMetric_injective g).injOn hopen
    (fun x _ ↦ by
      rw [WithMetric.mfderiv_toWithMetric]
      exact (ContinuousLinearEquiv.refl ℝ _).bijective) ?_
  obtain ⟨C, hC⟩ := hdecay
  refine ⟨max C 0, fun x hx i j ↦ ?_⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  obtain ⟨h0, h1, h2⟩ := hC x hx
  by_cases hij : i = j
  · subst hij
    have hcoeff : (fun y ↦ pullbackMetricCoeff (WithMetric.toWithMetric g) y i i) = w := by
      ext y; dsimp only [g]; rw [pullbackMetricCoeff_toWithMetric_rescale]; simp
    rw [congrFun hcoeff x, hcoeff]; simp only [↓reduceIte]
    exact ⟨h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0 _)),
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0 _)),
      h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0 _))⟩
  · have hcoeff : (fun y ↦ pullbackMetricCoeff (WithMetric.toWithMetric g) y i j) = 0 := by
      ext y; dsimp only [g]; rw [pullbackMetricCoeff_toWithMetric_rescale]; simp [hij]
    rw [congrFun hcoeff x, hcoeff]
    simp only [hij, ↓reduceIte, Pi.zero_apply, sub_zero, abs_zero, fderiv_zero,
      ContinuousLinearMap.opNorm_zero]
    exact ⟨mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0 _),
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0 _),
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0 _)⟩

/-- Excision radius of `AsymptoticallyEuclideanEnd.conformalEuclidean`. -/
@[simp]
theorem AsymptoticallyEuclideanEnd.conformalEuclidean_radius :
    (AsymptoticallyEuclideanEnd.conformalEuclidean hr hw hw_pos hdecay).radius = r := by
  rw [AsymptoticallyEuclideanEnd.conformalEuclidean, AsymptoticallyEuclideanEnd.ofFun_radius]

/-- On `{x | r < ‖x‖}`, `AsymptoticallyEuclideanEnd.conformalEuclidean` acts by
`WithMetric.toWithMetric`. -/
theorem AsymptoticallyEuclideanEnd.conformalEuclidean_toFun_of_lt
    {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖) :
    (AsymptoticallyEuclideanEnd.conformalEuclidean hr hw hw_pos hdecay).toFun x =
      WithMetric.toWithMetric _ x := by
  rw [AsymptoticallyEuclideanEnd.conformalEuclidean]
  exact AsymptoticallyEuclideanEnd.ofFun_toFun_of_lt hr _ _ _ _ _ _ hx

/-- End image of `AsymptoticallyEuclideanEnd.conformalEuclidean`. -/
@[simp]
theorem AsymptoticallyEuclideanEnd.conformalEuclidean_image :
    (AsymptoticallyEuclideanEnd.conformalEuclidean hr hw hw_pos hdecay).image =
      WithMetric.toWithMetric _ '' {x | r < ‖x‖} := by
  rw [AsymptoticallyEuclideanEnd.conformalEuclidean, AsymptoticallyEuclideanEnd.ofFun_image]

/-- Package a smooth positive conformal factor `w : ℝⁿ → ℝ` with `w - 1 = O_2(‖x‖ ^ (-t))` as a
one-ended `FiniteEndedAE` structure on `WithMetric`. -/
def FiniteEndedAE.conformalEuclidean :
    FiniteEndedAE n
      (WithMetric
        (((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
          w hw.contMDiff hw_pos)) t := by
  let g := ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
    w hw.contMDiff hw_pos
  refine FiniteEndedAE.ofSingleEnd
    (AsymptoticallyEuclideanEnd.conformalEuclidean hr hw hw_pos hdecay) ?_
  rw [← AsymptoticallyEuclideanEnd.image_def, AsymptoticallyEuclideanEnd.conformalEuclidean_image]
  have hcompl : (WithMetric.toWithMetric g '' {x | r < ‖x‖})ᶜ =
      WithMetric.toWithMetric g '' closedBall 0 r := by
    ext p; refine ⟨fun hp ↦ ⟨p.ofWithMetric, ?_, WithMetric.toWithMetric_ofWithMetric g p⟩, ?_⟩
    · simp only [mem_closedBall, dist_zero_right]
      exact not_lt.1 fun h ↦ hp ⟨p.ofWithMetric, h, WithMetric.toWithMetric_ofWithMetric g p⟩
    · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      obtain rfl := (WithMetric.toWithMetric_injective g) hxy
      exact (not_lt_of_ge (by simpa using hx)) hy
  rw [hcompl]
  exact (isCompact_closedBall 0 r).image (WithMetric.continuous_toWithMetric (g := g))

end ConformalEuclidean

/-! ### Smooth Schwarzschild model manifold of order `n - 2` (`3 ≤ n`) -/

private def schwarzschildBaseProfile (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if x = 0 then 1
  else 1 + c * Real.smoothTransition (‖x‖ - max 1 (2 * |c|)) * ‖x‖ ^ (2 - (n : ℝ))

/-- Smooth conformal factor on `ℝⁿ` equal on `{x | max 1 (2 |c|) + 1 < ‖x‖}` to
`(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))` and to `1` on `{x | ‖x‖ ≤ max 1 (2 |c|)}`. For `3 ≤ n` it
is globally smooth and strictly positive. -/
def schwarzschildModelFactor (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (schwarzschildBaseProfile n c x) ^ (4 / ((n : ℝ) - 2))

private theorem abs_mul_norm_rpow_le_half {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : max 1 (2 * |c|) < ‖y‖) :
    |c * ‖y‖ ^ (2 - (n : ℝ))| ≤ 1 / 2 := by
  set R₀ : ℝ := max 1 (2 * |c|)
  have h1 : 1 ≤ R₀ := le_max_left _ _
  have hR0 : 0 < R₀ := zero_lt_one.trans_le h1
  have hrp : ‖y‖ ^ (2 - (n : ℝ)) ≤ R₀⁻¹ :=
    (Real.rpow_le_rpow_of_exponent_le (h1.trans hy.le)
      (by linarith [(Nat.ofNat_le_cast.2 hn : (3 : ℝ) ≤ n)] : 2 - (n : ℝ) ≤ -1)).trans <| by
        rw [Real.rpow_neg_one]; exact inv_anti₀ hR0 hy.le
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
  calc |c| * ‖y‖ ^ (2 - (n : ℝ)) ≤ (R₀ / 2) * R₀⁻¹ :=
        mul_le_mul (by linarith [le_max_right 1 (2 * |c|)]) hrp
          (Real.rpow_nonneg (norm_nonneg y) _) (by positivity)
    _ = 1 / 2 := by field_simp [hR0.ne']

private theorem half_le_schwarzschildBaseProfile {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (1 / 2 : ℝ) ≤ schwarzschildBaseProfile n c x := by
  set R₀ : ℝ := max 1 (2 * |c|)
  by_cases hx0 : x = 0
  · simp [schwarzschildBaseProfile, hx0]; norm_num
  · simp only [schwarzschildBaseProfile, hx0, ↓reduceIte]
    by_cases hle : ‖x‖ ≤ R₀
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : ‖x‖ - R₀ ≤ 0)]; norm_num
    · have hgt : R₀ < ‖x‖ := lt_of_not_ge hle
      have hst0 := Real.smoothTransition.nonneg (‖x‖ - R₀)
      have hst1 := Real.smoothTransition.le_one (‖x‖ - R₀)
      have habs : |c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ))| ≤ 1 / 2 := by
        calc |c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ))|
            = Real.smoothTransition (‖x‖ - R₀) * |c * ‖x‖ ^ (2 - (n : ℝ))| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_mul]; ring
          _ ≤ 1 * (1 / 2) := mul_le_mul hst1 (abs_mul_norm_rpow_le_half hn c hgt)
                (abs_nonneg _) zero_le_one
          _ = 1 / 2 := one_mul _
      linarith [neg_abs_le (c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ)))]

private theorem contDiff_schwarzschildBaseProfile (n : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (schwarzschildBaseProfile n c) := by
  set R₀ : ℝ := max 1 (2 * |c|)
  have hR0 : 0 < R₀ := zero_lt_one.trans_le (le_max_left _ _)
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR0] with y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [schwarzschildBaseProfile]
    · have hle : ‖y‖ - R₀ ≤ 0 := by linarith [mem_ball_zero_iff.1 hy]
      simp [schwarzschildBaseProfile, hy0, R₀, Real.smoothTransition.zero_of_nonpos hle]
  · have hst : ContDiffAt ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin n) ↦ Real.smoothTransition (‖y‖ - R₀)) x :=
      Real.smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_norm ℝ hx).sub (contDiffAt_const (c := R₀)))
    have hrp : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ))) x :=
      (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)
    refine ((contDiffAt_const (c := (1 : ℝ))).add
      (((contDiffAt_const (c := c)).mul hst).mul hrp)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [schwarzschildBaseProfile, hy, R₀]

/-- In dimension `3 ≤ n`, `schwarzschildModelFactor n c` is globally smooth on `ℝⁿ`. -/
theorem contDiff_schwarzschildModelFactor {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ContDiff ℝ ∞ (schwarzschildModelFactor n c) :=
  contDiff_iff_contDiffAt.2 fun x ↦
    ((contDiff_schwarzschildBaseProfile n c).contDiffAt.rpow_const_of_ne
      (by linarith [half_le_schwarzschildBaseProfile hn c x]))

/-- In dimension `3 ≤ n`, `schwarzschildModelFactor n c` is everywhere strictly positive. -/
theorem schwarzschildModelFactor_pos {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < schwarzschildModelFactor n c x :=
  Real.rpow_pos_of_pos (by linarith [half_le_schwarzschildBaseProfile hn c x]) _

/-- Outside `{x | ‖x‖ ≤ max 1 (2 |c|) + 1}`, `schwarzschildModelFactor n c` agrees with the exact
conformal Schwarzschild profile `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))`. -/
theorem schwarzschildModelFactor_of_lt (n : ℕ) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : max 1 (2 * |c|) + 1 < ‖x‖) :
    schwarzschildModelFactor n c x =
      (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by linarith [le_max_left (1 : ℝ) (2 * |c|)])
  have h1 : 1 ≤ ‖x‖ - max 1 (2 * |c|) := by linarith
  simp [schwarzschildModelFactor, schwarzschildBaseProfile, hx0,
    Real.smoothTransition.one_of_one_le h1]

private theorem mul_norm_rpow_mem_Icc {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : max 1 (2 * |c|) < ‖y‖) :
    c * ‖y‖ ^ (2 - (n : ℝ)) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  have h := abs_mul_norm_rpow_le_half hn c hy
  exact ⟨by linarith [neg_abs_le (c * ‖y‖ ^ (2 - (n : ℝ)))], (le_abs_self _).trans h⟩

private theorem hasFDerivAt_conformal_rpow {n : ℕ} (hn : 3 ≤ n) (c p : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : max 1 (2 * |c|) < ‖y‖) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ (1 + c * ‖z‖ ^ (2 - (n : ℝ))) ^ p)
      ((p * (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ (p - 1) * c) •
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ (2 - (n : ℝ))) y) y := by
  have hy0 : y ≠ 0 := norm_pos_iff.1 ((zero_lt_one.trans_le (le_max_left _ _)).trans hy)
  have hvy : 0 < 1 + c * ‖y‖ ^ (2 - (n : ℝ)) := by linarith [(mul_norm_rpow_mem_Icc hn c hy).1]
  have hin : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ 1 + c * ‖z‖ ^ (2 - (n : ℝ)))
      (c • fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ (2 - (n : ℝ))) y) y :=
    (((hasFDerivAt_norm_rpow_of_ne (2 - (n : ℝ)) hy0).differentiableAt.hasFDerivAt).const_smul c
      ).const_add 1
  exact (hin.rpow_const (p := p) (Or.inl hvy.ne')).congr_fderiv <| by
    ext v; simp [smul_smul, mul_assoc]

private theorem exists_nonneg_bound_one_add_rpow_Icc (a r : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc (-1 / 2 : ℝ) (1 / 2), |a * (1 + s) ^ r| ≤ B := by
  have hpos : ∀ s ∈ Icc (-1 / 2 : ℝ) (1 / 2), 0 < 1 + s := fun s hs ↦ by linarith [hs.1]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s : ℝ ↦ a * (1 + s) ^ r) <| fun s hs ↦
      (continuousAt_const.mul
        ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (hpos s hs).ne'))
        ).continuousWithinAt
  refine ⟨max M 0, le_max_right M 0, fun s hs ↦ ?_⟩
  exact (Real.norm_eq_abs _ ▸ hM s hs).trans (le_max_left M 0)

private theorem exists_conformal_rpow_zero_first_decay {n : ℕ} (hn : 3 ≤ n) (c p : ℝ) :
    ∃ C₀ : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), max 1 (2 * |c|) < ‖x‖ →
      |(1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ p - 1| ≤ C₀ * ‖x‖ ^ (-((n : ℝ) - 2)) ∧
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ p) x‖ ≤
        C₀ * ‖x‖ ^ (-((n : ℝ) - 2) - 1) := by
  set q : ℝ := 2 - (n : ℝ)
  obtain ⟨B₁, hB₁, hM₁⟩ := exists_nonneg_bound_one_add_rpow_Icc p (p - 1)
  refine ⟨B₁ * |c| * (1 + |q|), fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := norm_pos_iff.1 ((zero_lt_one.trans_le (le_max_left _ _)).trans hx)
  have hsK : c * ‖x‖ ^ q ∈ Icc (-1 / 2 : ℝ) (1 / 2) := mul_norm_rpow_mem_Icc hn c hx
  have h0K : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by constructor <;> norm_num
  have hb1 : |p * (1 + c * ‖x‖ ^ q) ^ (p - 1)| ≤ B₁ := hM₁ _ hsK
  have hmvt := (convex_Icc (-1 / 2 : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ ↦ (1 + s) ^ p) (f' := fun s : ℝ ↦ p * (1 + s) ^ (p - 1)) (C := B₁)
    (fun s hs ↦ ((((hasDerivAt_id' s).const_add 1).rpow_const (p := p)
      (Or.inl (by linarith [hs.1]))).congr_deriv (by ring)).hasDerivWithinAt)
    (fun s hs ↦ by simpa [Real.norm_eq_abs] using hM₁ s hs) h0K hsK
  have h0 : |(1 + c * ‖x‖ ^ q) ^ p - 1| ≤ B₁ * |c| * ‖x‖ ^ q := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) q),
      ← mul_assoc] using hmvt
  have h1 : ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ (1 + c * ‖y‖ ^ q) ^ p) x‖ ≤
      B₁ * |c| * |q| * ‖x‖ ^ (q - 1) := by
    rw [(hasFDerivAt_conformal_rpow hn c p hx).fderiv, norm_smul, norm_fderiv_norm_rpow_of_ne q hx0,
      Real.norm_eq_abs, abs_mul]
    calc |p * (1 + c * ‖x‖ ^ q) ^ (p - 1)| * |c| * (|q| * ‖x‖ ^ (q - 1))
        ≤ B₁ * |c| * (|q| * ‖x‖ ^ (q - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb1 (abs_nonneg c)) (by positivity)
      _ = B₁ * |c| * |q| * ‖x‖ ^ (q - 1) := by ring
  have hBc : 0 ≤ B₁ * |c| := mul_nonneg hB₁ (abs_nonneg c)
  have hqn : -((n : ℝ) - 2) = q := by dsimp [q]; ring
  rw [hqn]
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right hBc (by linarith [abs_nonneg q]))
      (Real.rpow_nonneg (norm_nonneg x) _)),
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hBc)
      (Real.rpow_nonneg (norm_nonneg x) _))⟩

private theorem fderiv_fderiv_conformal_rpow {n : ℕ} (hn : 3 ≤ n) (c p : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : max 1 (2 * |c|) < ‖x‖) :
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦
        (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ p)) x =
      (p * (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (p - 1) * c) •
          fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ (2 - (n : ℝ))) x +
        ((p * (p - 1) * (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (p - 2) * c ^ 2) •
          fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ (2 - (n : ℝ))) x).smulRight
          (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ (2 - (n : ℝ))) x) := by
  set q : ℝ := 2 - (n : ℝ)
  have hx0 : x ≠ 0 := norm_pos_iff.1 ((zero_lt_one.trans_le (le_max_left 1 (2 * |c|))).trans hx)
  have hev : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ (1 + c * ‖y‖ ^ q) ^ p) =ᶠ[𝓝 x]
      fun y ↦ (p * (1 + c * ‖y‖ ^ q) ^ (p - 1) * c) •
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) y := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact (hasFDerivAt_conformal_rpow hn c p hy).fderiv
  have hdψ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ p * (1 + c * ‖y‖ ^ q) ^ (p - 1) * c)
      ((p * (p - 1) * (1 + c * ‖x‖ ^ q) ^ (p - 2) * c ^ 2) •
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x) x := by
    have hp2 : p - 1 - 1 = p - 2 := by ring
    have hrp := hasFDerivAt_conformal_rpow hn c (p - 1) hx
    exact ((hrp.const_mul p).mul_const c).congr_fderiv (by ext v; simp [hp2]; ring)
  have hdH : DifferentiableAt ℝ (fderiv ℝ fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x := by
    have hfd : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) =ᶠ[𝓝 x]
        fun z ↦ (q * ‖z‖ ^ (q - 2)) • innerSL ℝ z := by
      filter_upwards [eventually_ne_nhds hx0] with z hz; exact fderiv_norm_rpow_of_ne q hz
    exact (((hasFDerivAt_norm_rpow_of_ne (q - 2) hx0).const_mul q).differentiableAt.smul
      (innerSL ℝ).differentiableAt).congr_of_eventuallyEq hfd
  rw [hev.fderiv_eq, fderiv_fun_smul hdψ.differentiableAt hdH, hdψ.fderiv]

private theorem exists_conformal_rpow_second_decay {n : ℕ} (hn : 3 ≤ n) (c p : ℝ) :
    ∃ C₂ : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), max 1 (2 * |c|) < ‖x‖ →
      ‖fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦
          (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ p)) x‖ ≤
        C₂ * ‖x‖ ^ (-((n : ℝ) - 2) - 2) := by
  set q : ℝ := 2 - (n : ℝ)
  obtain ⟨B₁, _, hM₁⟩ := exists_nonneg_bound_one_add_rpow_Icc p (p - 1)
  obtain ⟨B₂, _, hM₂⟩ := exists_nonneg_bound_one_add_rpow_Icc (p * (p - 1)) (p - 2)
  refine ⟨B₁ * |c| * (|q| * (|q - 2| + 1)) + B₂ * c ^ 2 * q ^ 2, fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ ‖x‖ := (le_max_left 1 (2 * |c|)).trans hx.le
  have hx0 : x ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le hx1)
  have hb1 := hM₁ _ (mul_norm_rpow_mem_Icc hn c hx)
  have hb2 := hM₂ _ (mul_norm_rpow_mem_Icc hn c hx)
  rw [fderiv_fderiv_conformal_rpow hn c p hx]
  have ht1 : ‖(((p * (p - 1) * (1 + c * ‖x‖ ^ q) ^ (p - 2) * c ^ 2) •
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x)).smulRight
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x)‖ ≤
      B₂ * c ^ 2 * q ^ 2 * ‖x‖ ^ (q - 2) := by
    refine (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans ?_
    rw [norm_smul, norm_fderiv_norm_rpow_of_ne q hx0, Real.norm_eq_abs, abs_mul, abs_sq]
    have hqexp : ‖x‖ ^ (q - 1) * ‖x‖ ^ (q - 1) ≤ ‖x‖ ^ (q - 2) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hx1)]
      exact Real.rpow_le_rpow_of_exponent_le hx1
        (by dsimp [q]; linarith [(Nat.ofNat_le_cast.2 hn : (3 : ℝ) ≤ n)])
    calc |p * (p - 1) * (1 + c * ‖x‖ ^ q) ^ (p - 2)| * c ^ 2 *
          (|q| * ‖x‖ ^ (q - 1)) * (|q| * ‖x‖ ^ (q - 1))
        = |p * (p - 1) * (1 + c * ‖x‖ ^ q) ^ (p - 2)| * c ^ 2 * q ^ 2 *
            (‖x‖ ^ (q - 1) * ‖x‖ ^ (q - 1)) := by rw [← sq_abs q]; ring
      _ ≤ B₂ * c ^ 2 * q ^ 2 * ‖x‖ ^ (q - 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hb2 (sq_nonneg c)) (sq_nonneg q)) hqexp
            (by positivity) (by positivity)
  have ht2 : ‖(p * (1 + c * ‖x‖ ^ q) ^ (p - 1) * c) •
        fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x‖ ≤
      B₁ * |c| * (|q| * (|q - 2| + 1)) * ‖x‖ ^ (q - 2) := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hH : ‖fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x‖ ≤
        |q| * (|q - 2| + 1) * ‖x‖ ^ (q - 2) := by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
      exact norm_iteratedFDeriv_two_norm_rpow_le q hx0
    calc |p * (1 + c * ‖x‖ ^ q) ^ (p - 1)| * |c| *
          ‖fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ q) x‖
        ≤ B₁ * |c| * (|q| * (|q - 2| + 1) * ‖x‖ ^ (q - 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb1 (abs_nonneg c)) hH
            (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ = B₁ * |c| * (|q| * (|q - 2| + 1)) * ‖x‖ ^ (q - 2) := by ring
  have hqn : -((n : ℝ) - 2) - 2 = q - 2 := by dsimp [q]; ring
  rw [hqn, add_mul]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add ht2 ht1)

private theorem exists_schwarzschildModelFactor_decay {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), max 1 (2 * |c|) + 1 < ‖x‖ →
      |schwarzschildModelFactor n c x - 1| ≤ C * ‖x‖ ^ (-((n : ℝ) - 2)) ∧
      ‖fderiv ℝ (schwarzschildModelFactor n c) x‖ ≤ C * ‖x‖ ^ (-((n : ℝ) - 2) - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (schwarzschildModelFactor n c)) x‖ ≤
        C * ‖x‖ ^ (-((n : ℝ) - 2) - 2) := by
  obtain ⟨C₀, hC₀⟩ := exists_conformal_rpow_zero_first_decay hn c (4 / ((n : ℝ) - 2))
  obtain ⟨C₂, hC₂⟩ := exists_conformal_rpow_second_decay hn c (4 / ((n : ℝ) - 2))
  have hU : IsOpen {y : EuclideanSpace ℝ (Fin n) | max 1 (2 * |c|) + 1 < ‖y‖} :=
    isOpen_lt continuous_const continuous_norm
  refine ⟨max C₀ C₂, fun x hx ↦ ?_⟩
  have hx' : max 1 (2 * |c|) < ‖x‖ := by linarith
  have hev : schwarzschildModelFactor n c =ᶠ[𝓝 x]
      fun y ↦ (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun _ hy ↦ schwarzschildModelFactor_of_lt n c hy
  rw [hev.eq_of_nhds, hev.fderiv_eq, hev.fderiv.fderiv_eq]
  obtain ⟨h0, h1⟩ := hC₀ x hx'
  have hnn (k : ℝ) : 0 ≤ ‖x‖ ^ k := Real.rpow_nonneg (norm_nonneg x) k
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn _)),
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn _)),
    (hC₂ x hx').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hnn _))⟩

/-- The smooth conformally Euclidean Riemannian metric `schwarzschildModelFactor n c • g_eucl` on
`ℝⁿ` (`3 ≤ n`), equal outside a ball to `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) • g_eucl`. -/
def schwarzschildModelMetric {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) x) :=
  ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
    (schwarzschildModelFactor n c) (contDiff_schwarzschildModelFactor hn c).contMDiff
    (schwarzschildModelFactor_pos hn c)

/-- The non-flat conformally Euclidean end of order `n - 2` (`3 ≤ n`) associated with
`schwarzschildModelMetric hn c`. -/
def schwarzschildModelEnd {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    AsymptoticallyEuclideanEnd n (WithMetric (schwarzschildModelMetric hn c)) ((n : ℝ) - 2) :=
  AsymptoticallyEuclideanEnd.conformalEuclidean
    (r := max 1 (2 * |c|) + 1) (by linarith [le_max_left (1 : ℝ) (2 * |c|)])
    (contDiff_schwarzschildModelFactor hn c) (schwarzschildModelFactor_pos hn c)
    (exists_schwarzschildModelFactor_decay hn c)

/-- Excision radius of `schwarzschildModelEnd`. -/
@[simp]
theorem schwarzschildModelEnd_radius {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    (schwarzschildModelEnd hn c).radius = max 1 (2 * |c|) + 1 := by
  rw [schwarzschildModelEnd, AsymptoticallyEuclideanEnd.conformalEuclidean_radius]

/-- Outside `{x | ‖x‖ ≤ max 1 (2 |c|) + 1}`, the pulled-back metric coefficients of
`schwarzschildModelEnd hn c` equal `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) * δ_ij`. -/
theorem pullbackMetricCoeff_schwarzschildModelEnd {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : max 1 (2 * |c|) + 1 < ‖x‖) (i j : Fin n) :
    pullbackMetricCoeff (schwarzschildModelEnd hn c).toFun x i j =
      (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) * if i = j then 1 else 0 := by
  have hU : IsOpen {y : EuclideanSpace ℝ (Fin n) | max 1 (2 * |c|) + 1 < ‖y‖} :=
    isOpen_lt continuous_const continuous_norm
  have hfun : EqOn (schwarzschildModelEnd hn c).toFun
      (WithMetric.toWithMetric (schwarzschildModelMetric hn c))
      {y | max 1 (2 * |c|) + 1 < ‖y‖} := fun _ hy ↦ by
    rw [schwarzschildModelEnd]
    exact AsymptoticallyEuclideanEnd.conformalEuclidean_toFun_of_lt _ _ _ _ hy
  rw [(pullbackMetricCoeff_eventuallyEq_of_eqOn_open hU hfun hx i j).eq_of_nhds,
    schwarzschildModelMetric, pullbackMetricCoeff_toWithMetric_rescale,
    schwarzschildModelFactor_of_lt n c hx]

/-- The one-ended `FiniteEndedAE` manifold structure of order `n - 2` (`3 ≤ n`) on
`WithMetric (schwarzschildModelMetric hn c)`. -/
def schwarzschildModelAE {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    FiniteEndedAE n (WithMetric (schwarzschildModelMetric hn c)) ((n : ℝ) - 2) :=
  FiniteEndedAE.conformalEuclidean
    (r := max 1 (2 * |c|) + 1) (by linarith [le_max_left (1 : ℝ) (2 * |c|)])
    (contDiff_schwarzschildModelFactor hn c) (schwarzschildModelFactor_pos hn c)
    (exists_schwarzschildModelFactor_decay hn c)

end TauCeti
