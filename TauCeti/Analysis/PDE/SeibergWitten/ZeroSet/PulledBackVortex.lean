/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Analysis.PDE.Vortex.Flux.Basic
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The defect energy and the curvature current of a pulled-back plane vortex

Let `V = ℂ_base × ℂ_normal` be a Euclidean four-space with an orthonormal frame `e`, whose first two
vectors span the base plane and whose last two span the normal plane, with base and normal
coordinates `w = ⟪e₀, ·⟫ + i ⟪e₁, ·⟫` (`TauCeti.SeibergWitten.baseCoord`) and
`z = ⟪e₂, ·⟫ + i ⟪e₃, ·⟫` (`TauCeti.SeibergWitten.normalCoord`). A plane vortex `X` of degree `m`,
pulled back along the normal coordinate after dilation by `√(2r)`, is a solution of the flat
large-parameter Seiberg–Witten equations at parameter `r` which is constant along the base
(`sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff_equation_eq_zero` in
`TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`), with section `α(y) = α_X(√(2r) z(y))`. It is
the model of a large-parameter solution near a pseudoholomorphic curve, and this file computes the
two quantities through which Taubes's analysis sees the curve: the defect energy of balls and the
curvature current.

**The defect energy.** Taubes's defect energy of a set `B` is `E_r(B) = (r / 4) ∫_B |1 - |α|²|`.
The splitting `y ↦ (w(y), z(y))` carries the volume of `V` to that of `ℂ × ℂ`
(`TauCeti.SeibergWitten.measurePreserving_baseNormalCoordHomeomorph`), so the integral over a ball
of radius `σ` of a function of the normal coordinate is an integral over the normal plane weighted
by the area `π (σ² - |ζ - z(c)|²)` of the base slices of the ball
(`TauCeti.SeibergWitten.setIntegral_ball_comp_normalCoord`). The substitution `u = √(2r) ζ` then
gives, for every continuous `α_X`,

`E_r(B_σ(c)) = (π / 8) ∫_ℂ max (σ² - |u - u₀|² / (2 r)) 0 · |1 - |α_X(u)|²| du`,

with `u₀ = √(2r) z(c)` (`TauCeti.SeibergWitten.setIntegral_ball_mul_abs_one_sub_norm_sq_eq`). For a
vortex, `|α_X| ≤ 1` and `∫ (1 - |α_X|²) = 16 π m`
(`TauCeti.Vortex.integral_one_sub_sq_norm_sectionValue_eq_mul_card`), so

`2 π² m σ² - (π / (16 r)) ∫ |u - u₀|² (1 - |α_X(u)|²) du ≤ E_r(B_σ(c)) ≤ 2 π² m σ²`

for every radius `σ ≥ 0` and every centre `c`
(`TauCeti.SeibergWitten.setIntegral_ball_defect_le`,
`TauCeti.SeibergWitten.sub_le_setIntegral_ball_defect`). For a centre on the base plane `u₀ = 0`,
and `E_r(B_σ) = 2 π² m σ² + O(1 / r)` uniformly in `σ`, the constant being the second moment of the
vortex defect (`TauCeti.SeibergWitten.abs_setIntegral_ball_defect_sub_le`). So the quadratic
growth `E_r(B_σ) ≤ C σ²` of the defect energy, which Taubes's monotonicity inequality
(`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Monotonicity`) propagates, is attained, with the
constant `2 π² m`; the leading term `2 π² m σ²` is the case of equality `E = (σ / 2) dE / dσ` of the
differential inequality behind it.

**The curvature current.** The real curvature `F_r = -db_r` of the pulled-back connection is a
multiple of `e₂ ∧ e₃`, so its wedge with a two-form `ζ`, read on the frame, only sees
`ζ(e₀, e₁)` (`TauCeti.SeibergWitten.wedge_neg_extDeriv_normalConnection_apply`); for the vortex the
coefficient is `(r / 4) (1 - |α_X(√(2r) z)|²)`, of integral `2 π m` over each normal plane. These
densities concentrate on the base plane as `r → ∞`, so the curvature currents
`T_r(ζ) = (2π)⁻¹ ∫ F_r ∧ ζ` converge to `m` times the current of integration over the base plane
(`TauCeti.SeibergWitten.tendsto_integral_wedge_neg_extDeriv_normalConnection_dilateField`).

## Main results

* `TauCeti.SeibergWitten.measurePreserving_baseNormalCoordHomeomorph`: the frame coordinates
  `y ↦ (w(y), z(y))` preserve volume.
* `TauCeti.SeibergWitten.setIntegral_ball_comp_normalCoord`: the slice formula for integrals over
  a ball of functions of the normal coordinate.
* `TauCeti.SeibergWitten.setIntegral_ball_mul_abs_one_sub_norm_sq_eq`: the defect energy of a ball
  for a section pulled back along the dilated normal coordinate, as an integral over the plane.
* `TauCeti.SeibergWitten.setIntegral_ball_defect_le`,
  `TauCeti.SeibergWitten.sub_le_setIntegral_ball_defect`: the two-sided bound for a vortex.
* `TauCeti.SeibergWitten.abs_setIntegral_ball_defect_sub_le`: `E_r(B_σ) = 2 π² m σ² + O(1 / r)`
  for balls centred on the base plane.
* `TauCeti.SeibergWitten.wedge_neg_extDeriv_normalConnection_apply`: the curvature of a pulled-back
  connection wedged with a two-form.
* `TauCeti.SeibergWitten.tendsto_integral_wedge_neg_extDeriv_normalConnection_dilateField`: the
  curvature currents converge to `m` times the base plane.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Sections 3–5.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Set Complex Real Module
open scoped RealInnerProductSpace Topology

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (e : OrthonormalBasis (Fin 4) ℝ V)

/-! ### The frame coordinates preserve volume -/

section Splitting

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **The frame coordinates preserve volume**: `y ↦ (w(y), z(y))`, the base and normal
coordinates of an orthonormal frame, carries the volume of `V` to the product Lebesgue measure on
`ℂ × ℂ`. -/
theorem measurePreserving_baseNormalCoordHomeomorph :
    MeasurePreserving (baseNormalCoordHomeomorph e) volume volume := by
  have h : ⇑(baseNormalCoordHomeomorph e) = WithLp.ofLp ∘ baseNormalCoordEquiv e :=
    funext fun y ↦ by simp
  rw [h]
  exact (WithLp.volume_preserving_ofLp ℂ ℂ).comp (baseNormalCoordEquiv e).measurePreserving

/-- **The slice formula for a ball.** The integral over the ball of radius `σ ≥ 0` about `c` of a
continuous function of the normal coordinate `z` is an integral over the normal plane, weighted by
the area `π (σ² - |ζ - z(c)|²)` of the base slice of the ball at normal coordinate `ζ`:

`∫_{B_σ(c)} g(z(y)) dy = ∫_ℂ π max (σ² - |ζ - z(c)|²) 0 · g(ζ) dζ`. -/
theorem setIntegral_ball_comp_normalCoord {g : ℂ → ℝ} (hg : Continuous g) (c : V) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∫ y in ball c σ, g (normalCoord e y) =
      ∫ ζ, π * max (σ ^ 2 - ‖ζ - normalCoord e c‖ ^ 2) 0 * g ζ := by
  set a := baseCoord e c
  set b := normalCoord e c
  set S : Set (ℂ × ℂ) := {p | ‖p.1 - a‖ ^ 2 + ‖p.2 - b‖ ^ 2 < σ ^ 2}
  -- The ball is the preimage of the round ball `S` of `ℂ × ℂ`.
  have hball : ball c σ = baseNormalCoordHomeomorph e ⁻¹' S := by
    ext y
    simp only [mem_ball, dist_eq_norm, mem_preimage, baseNormalCoordHomeomorph_apply, S,
      mem_ofPred_eq, a, b,
      ← map_sub, norm_baseCoord_sq_add_norm_normalCoord_sq]
    exact (sq_lt_sq₀ (norm_nonneg _) hσ).symm
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  -- `S` lies in a compact set, so the continuous integrand is integrable on it.
  have hSK : S ⊆ closedBall (a, b) σ := fun p hp ↦ by
    simp only [S, mem_ofPred_eq] at hp
    rw [mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm, max_le_iff]
    constructor <;> refine (abs_le_of_sq_le_sq' ?_ hσ).2 <;> nlinarith [norm_nonneg (p.1 - a),
      norm_nonneg (p.2 - b), sq_abs (‖p.1 - a‖), sq_abs (‖p.2 - b‖)]
  have hint : Integrable (S.indicator fun p : ℂ × ℂ ↦ g p.2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, integrable_indicator_iff hS.measurableSet]
    exact ((hg.comp continuous_snd).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set hSK
  have hsnd (y : V) : normalCoord e y = (baseNormalCoordHomeomorph e y).2 := by simp
  simp_rw [hball, hsnd]
  rw [(measurePreserving_baseNormalCoordHomeomorph e).setIntegral_preimage_emb
    (baseNormalCoordHomeomorph e).measurableEmbedding (fun p : ℂ × ℂ ↦ g p.2) S,
    ← integral_indicator hS.measurableSet, Measure.volume_eq_prod, integral_prod_symm _ hint]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  -- The base slice of `S` at `ζ` is a disc of area `π max (σ² - |ζ - b|²) 0`.
  have hdisc (A : ℝ) : volume.real {u : ℂ | ‖u - a‖ ^ 2 < A} = π * max A 0 := by
    rcases le_or_gt A 0 with hA | hA
    · have : {u : ℂ | ‖u - a‖ ^ 2 < A} = ∅ :=
        eq_empty_of_forall_notMem fun u hu ↦ (hu.trans_le hA).not_ge (by positivity)
      simp [this, max_eq_right hA]
    · have : {u : ℂ | ‖u - a‖ ^ 2 < A} = ball a √A := by
        ext u
        rw [mem_ofPred_eq, mem_ball, dist_eq_norm, Real.lt_sqrt (norm_nonneg _)]
      rw [this, Complex.volume_real_ball a (Real.sqrt_nonneg A), Real.sq_sqrt hA.le,
        max_eq_left hA.le]
  have hslice : (fun u : ℂ ↦ S.indicator (fun p : ℂ × ℂ ↦ g p.2) (u, ζ)) =
      {u : ℂ | ‖u - a‖ ^ 2 < σ ^ 2 - ‖ζ - b‖ ^ 2}.indicator fun _ ↦ g ζ := by
    ext u
    simp only [indicator, S, mem_ofPred_eq, lt_sub_iff_add_lt]
  have hmeas : MeasurableSet {u : ℂ | ‖u - a‖ ^ 2 < σ ^ 2 - ‖ζ - b‖ ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  simp only [hslice, integral_indicator_const _ hmeas, hdisc, smul_eq_mul]

end Splitting

/-! ### The defect energy of a ball -/

section Defect

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- **The defect energy of a ball for a section pulled back along the dilated normal coordinate.**
For a continuous `α : ℂ → ℂ`, `r > 0` and `σ ≥ 0`, the defect energy of the ball `B_σ(c)` of the
section `y ↦ α(√(2r) z(y))` is

`(r / 4) ∫_{B_σ(c)} |1 - |α(√(2r) z(y))|²| dy
  = (π / 8) ∫_ℂ max (σ² - |u - u₀|² / (2 r)) 0 · |1 - |α(u)|²| du`,

with `u₀ = √(2r) z(c)`. -/
theorem setIntegral_ball_mul_abs_one_sub_norm_sq_eq {α : ℂ → ℂ} (hα : Continuous α) {r : ℝ}
    (hr : 0 < r) (c : V) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ y in ball c σ, r / 4 * |1 - ‖α (√(2 * r) • normalCoord e y)‖ ^ 2| =
      π / 8 * ∫ u, max (σ ^ 2 - ‖u - √(2 * r) • normalCoord e c‖ ^ 2 / (2 * r)) 0 *
        |1 - ‖α u‖ ^ 2| := by
  set t := √(2 * r)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  set b := normalCoord e c
  -- The integrand after the slice formula, as a function of `u = t ζ`.
  set H : ℂ → ℝ := fun u ↦ π * max (σ ^ 2 - ‖t⁻¹ • u - b‖ ^ 2) 0 * (r / 4 * |1 - ‖α u‖ ^ 2|)
  have hslice : ∫ y in ball c σ, r / 4 * |1 - ‖α (t • normalCoord e y)‖ ^ 2| =
      ∫ ζ, H (t • ζ) := by
    rw [setIntegral_ball_comp_normalCoord e (g := fun ζ ↦ r / 4 * |1 - ‖α (t • ζ)‖ ^ 2|)
      (by fun_prop) c hσ]
    exact integral_congr_ae (.of_forall fun ζ ↦ by simp only [H, b, inv_smul_smul₀ ht.ne'])
  have hscale (u : ℂ) : ‖t⁻¹ • u - b‖ ^ 2 = ‖u - t • b‖ ^ 2 / (2 * r) := by
    have : t⁻¹ • u - b = t⁻¹ • (u - t • b) := by rw [smul_sub, inv_smul_smul₀ ht.ne']
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_pow, ht2,
      inv_mul_eq_div]
  -- Substitute `u = t ζ`: the plane measure scales by `t² = 2 r`.
  rw [hslice, Measure.integral_comp_smul_of_nonneg volume H t (hR := ht.le),
    Complex.finrank_real_complex, ht2, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  simp only [H, hscale]
  field_simp
  ring

variable {X : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}

/-- The defect energy of a ball for the pulled-back vortex, with the absolute value removed. -/
private theorem setIntegral_ball_defect_eq (hX : ContDiff ℝ 2 X)
    (hsol : ∀ z, Vortex.equation X z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (X z 2 ^ 2 + X z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {r : ℝ}
    (hr : 0 < r) (c : V) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ y in ball c σ,
        r / 4 * |1 - ‖Vortex.sectionValue (Vortex.dilateField √(2 * r) X) (normalCoord e y)‖ ^ 2| =
      π / 8 * ∫ u, max (σ ^ 2 - ‖u - √(2 * r) • normalCoord e c‖ ^ 2 / (2 * r)) 0 *
        (1 - ‖Vortex.sectionValue X u‖ ^ 2) := by
  simp_rw [Vortex.sectionValue_dilateField]
  rw [setIntegral_ball_mul_abs_one_sub_norm_sq_eq e (Vortex.continuous_sectionValue hX.continuous)
    hr c hσ]
  congr 2 with u
  rw [abs_of_nonneg (Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim u)]

/-- For `r ≥ 0` the weight `max (σ² - |u - u₀|² / (2 r)) 0` is at most `σ²`. -/
private theorem max_sub_div_le {r : ℝ} (hr : 0 ≤ r) (σ : ℝ) (u u₀ : ℂ) :
    max (σ ^ 2 - ‖u - u₀‖ ^ 2 / (2 * r)) 0 ≤ σ ^ 2 :=
  max_le (sub_le_self _ (by positivity)) (sq_nonneg σ)

/-- The weight `max (σ² - |u - u₀|² / (2 r)) 0` times the vortex defect is integrable. -/
private theorem integrable_max_mul_defect (hX : ContDiff ℝ 2 X)
    (hsol : ∀ z, Vortex.equation X z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (X z 2 ^ 2 + X z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {r : ℝ}
    (hr : 0 ≤ r) (σ : ℝ) (u₀ : ℂ) :
    Integrable fun u ↦ max (σ ^ 2 - ‖u - u₀‖ ^ 2 / (2 * r)) 0 *
      (1 - ‖Vortex.sectionValue X u‖ ^ 2) := by
  have hnn := Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim
  have hf := Vortex.integrable_one_sub_sq_norm_sectionValue (μ := volume) hX hsol hlim
  have hα := Vortex.continuous_sectionValue hX.continuous
  refine (hf.const_mul (σ ^ 2)).mono' (by fun_prop) (.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hnn u))]
  exact mul_le_mul_of_nonneg_right (max_sub_div_le hr σ u u₀) (hnn u)

variable (hX : ContDiff ℝ 2 X) (hsol : ∀ z, Vortex.equation X z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (X z 2 ^ 2 + X z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (Vortex.sectionValue X) (Multiset.count · D))
include hX hsol hlim hD

/-- **Upper bound on the defect energy of a ball for the pulled-back vortex.** Let `X` be a `C²`
plane vortex with `|α| → 1` at infinity and zero divisor `D` of degree `m`. Pulled back along the
normal coordinate after dilation by `√(2r)`, `r > 0`, its defect energy on every ball of radius
`σ` is at most `2 π² m σ²`:

`(r / 4) ∫_{B_σ(c)} |1 - |α|²| ≤ 2 π² m σ²`. -/
theorem setIntegral_ball_defect_le {r : ℝ} (hr : 0 < r) (c : V) (σ : ℝ) :
    ∫ y in ball c σ,
        r / 4 * |1 - ‖Vortex.sectionValue (Vortex.dilateField √(2 * r) X) (normalCoord e y)‖ ^ 2| ≤
      2 * π ^ 2 * D.card * σ ^ 2 := by
  rcases lt_or_ge σ 0 with hσ | hσ
  · -- A ball of negative radius is empty.
    rw [ball_eq_empty.2 hσ.le, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hnn := Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim
  have hf := Vortex.integrable_one_sub_sq_norm_sectionValue (μ := volume) hX hsol hlim
  have hflux := Vortex.integral_one_sub_sq_norm_sectionValue_eq_mul_card hX hsol hlim hD
  rw [setIntegral_ball_defect_eq e hX hsol hlim hr c hσ]
  have h : ∫ u, max (σ ^ 2 - ‖u - √(2 * r) • normalCoord e c‖ ^ 2 / (2 * r)) 0 *
      (1 - ‖Vortex.sectionValue X u‖ ^ 2) ≤ ∫ u, σ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) :=
    integral_mono (integrable_max_mul_defect hX hsol hlim hr.le σ _) (hf.const_mul _)
      fun u ↦ mul_le_mul_of_nonneg_right (max_sub_div_le hr.le σ u _) (hnn u)
  rw [integral_const_mul, hflux] at h
  nlinarith [Real.pi_pos]

/-- **Lower bound on the defect energy of a ball for the pulled-back vortex.** Under the
hypotheses of `TauCeti.SeibergWitten.setIntegral_ball_defect_le`, the defect energy of the ball of
radius `σ ≥ 0` about `c` falls short of `2 π² m σ²` by at most `π / (16 r)` times the second
moment of the vortex defect about `u₀ = √(2r) z(c)`:

`2 π² m σ² - (π / (16 r)) ∫ |u - u₀|² (1 - |α_X(u)|²) du ≤ (r / 4) ∫_{B_σ(c)} |1 - |α|²|`. -/
theorem sub_le_setIntegral_ball_defect {r : ℝ} (hr : 0 < r) (c : V) {σ : ℝ} (hσ : 0 ≤ σ) :
    2 * π ^ 2 * D.card * σ ^ 2 - π / (16 * r) *
        ∫ u, ‖u - √(2 * r) • normalCoord e c‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) ≤
      ∫ y in ball c σ, r / 4 *
        |1 - ‖Vortex.sectionValue (Vortex.dilateField √(2 * r) X) (normalCoord e y)‖ ^ 2| := by
  have hnn := Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim
  have hf := Vortex.integrable_one_sub_sq_norm_sectionValue (μ := volume) hX hsol hlim
  have hflux := Vortex.integral_one_sub_sq_norm_sectionValue_eq_mul_card hX hsol hlim hD
  have hf2 := Vortex.integrable_norm_sub_sq_mul_one_sub_sq_norm_sectionValue (μ := volume) hX hsol
    hlim
  set u₀ := √(2 * r) • normalCoord e c
  rw [setIntegral_ball_defect_eq e hX hsol hlim hr c hσ]
  have h : ∫ u, (σ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) -
        (2 * r)⁻¹ * (‖u - u₀‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2))) ≤
      ∫ u, max (σ ^ 2 - ‖u - u₀‖ ^ 2 / (2 * r)) 0 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) := by
    refine integral_mono ((hf.const_mul _).sub ((hf2 u₀).const_mul _))
      (integrable_max_mul_defect hX hsol hlim hr.le σ _) fun u ↦ ?_
    have h1 : σ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) -
        (2 * r)⁻¹ * (‖u - u₀‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2)) =
        (σ ^ 2 - ‖u - u₀‖ ^ 2 / (2 * r)) * (1 - ‖Vortex.sectionValue X u‖ ^ 2) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn u)
  rw [integral_sub (hf.const_mul _) ((hf2 u₀).const_mul _), integral_const_mul,
    integral_const_mul, hflux] at h
  calc 2 * π ^ 2 * D.card * σ ^ 2 - π / (16 * r) *
        ∫ u, ‖u - u₀‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2)
      = π / 8 * (σ ^ 2 * (16 * π * D.card) -
          (2 * r)⁻¹ * ∫ u, ‖u - u₀‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2)) := by
        field_simp
        ring
    _ ≤ _ := by gcongr

/-- **The defect energy of a ball centred on the base plane.** Under the hypotheses of
`TauCeti.SeibergWitten.setIntegral_ball_defect_le`, if the centre `c` lies on the base plane,
`z(c) = 0`, then for every radius `σ ≥ 0`

`|(r / 4) ∫_{B_σ(c)} |1 - |α|²| - 2 π² m σ²| ≤ (π / (16 r)) ∫ |u|² (1 - |α_X(u)|²) du`,

so `E_r(B_σ(c)) = 2 π² m σ² + O(1 / r)` uniformly in `σ`, with the second moment of the vortex
defect as constant. -/
theorem abs_setIntegral_ball_defect_sub_le {r : ℝ} (hr : 0 < r) {c : V}
    (hc : normalCoord e c = 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    |(∫ y in ball c σ,
        r / 4 * |1 - ‖Vortex.sectionValue (Vortex.dilateField √(2 * r) X) (normalCoord e y)‖ ^ 2|) -
      2 * π ^ 2 * D.card * σ ^ 2| ≤
      π / (16 * r) * ∫ u, ‖u‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) := by
  have hnn := Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim
  have hlow := sub_le_setIntegral_ball_defect e hX hsol hlim hD hr c hσ
  have hup := setIntegral_ball_defect_le e hX hsol hlim hD hr c σ
  rw [hc, smul_zero] at hlow
  simp only [sub_zero] at hlow
  have hM : 0 ≤ π / (16 * r) * ∫ u, ‖u‖ ^ 2 * (1 - ‖Vortex.sectionValue X u‖ ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg fun u ↦ mul_nonneg (by positivity) (hnn u))
  rw [abs_sub_le_iff]
  exact ⟨(sub_nonpos.2 hup).trans hM, sub_le_comm.1 hlow⟩

end Defect

/-! ### Concentration of the curvature density -/

/-- **Concentration along the normal plane.** If `f ≥ 0` has integral `16 π m`, `m > 0`, and
`|u|² f(u) → 0` at infinity, then the measures `(r / 4) f(√(2r) n) dn` concentrate at `0` with
mass `2 π m`: against a continuous compactly supported `Ψ`,
`(2π)⁻¹ ∫ (r / 4) f(√(2r) n) Ψ(n) dn → m Ψ(0)` as `r → ∞`. -/
private theorem tendsto_integral_mul_comp_sqrt_smul_mul {f Ψ : ℂ → ℝ} {m : ℝ} (hm : 0 < m)
    (hnn : ∀ u, 0 ≤ f u) (hflux : ∫ u, f u = 16 * π * m)
    (hdecay : Tendsto (fun u ↦ ‖u‖ ^ 2 * f u) (cocompact ℂ) (𝓝 0)) (hΨ : Continuous Ψ)
    (hΨc : HasCompactSupport Ψ) :
    Tendsto (fun r ↦ (2 * π)⁻¹ * ∫ n, r / 4 * f (√(2 * r) • n) * Ψ n) atTop (𝓝 (m * Ψ 0)) := by
  -- The normalized defect `f / (16 π m)` is a peak function of integral one.
  have hφ₁ : ∫ u, f u / (16 * π * m) = 1 := by
    rw [integral_div, hflux]
    exact div_self (by positivity)
  have hdecay' : Tendsto (fun u ↦ ‖u‖ ^ finrank ℝ ℂ * (f u / (16 * π * m)))
      (Bornology.cobounded ℂ) (𝓝 0) := by
    rw [Complex.finrank_real_complex, cobounded_eq_cocompact]
    simpa only [zero_div, mul_div_assoc] using hdecay.div_const (16 * π * m)
  have hpeak := (tendsto_integral_comp_smul_smul_of_integrable
    (fun u ↦ div_nonneg (hnn u) (by positivity)) hφ₁ hdecay'
    (hΨ.integrable_of_hasCompactSupport hΨc) hΨ.continuousAt).comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos))
  refine (hpeak.const_mul m).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have ht2 : √(2 * r) ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  simp only [Function.comp_apply, id, Complex.finrank_real_complex, ht2, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun n ↦ ?_)
  field_simp
  ring

/-! ### The curvature current -/

/-- The base component `ζ(e₀, e₁)` of a continuous compactly supported two-form, read on `ℂ × ℂ`
through the frame coordinates, is continuous and compactly supported. -/
private theorem continuous_and_hasCompactSupport_apply_baseNormalCoordHomeomorph_symm
    {ζ : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) :
    Continuous (fun p ↦ ζ ((baseNormalCoordHomeomorph e).symm p) ![e 0, e 1]) ∧
      HasCompactSupport (fun p ↦ ζ ((baseNormalCoordHomeomorph e).symm p) ![e 0, e 1]) :=
  ⟨(continuous_eval_const _).comp (hζ.comp (baseNormalCoordHomeomorph e).symm.continuous),
    (hζc.comp_left (g := fun β : V [⋀^Fin 2]→L[ℝ] ℝ ↦ β ![e 0, e 1]) (by simp)).comp_homeomorph
      (baseNormalCoordHomeomorph e).symm⟩

section Current

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)}
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

include he in
/-- **The curvature current of a pulled-back connection.** For the connection pulled back from a
plane field `x` along the normal coordinate, the real curvature `F = -db` wedged with a two-form
`ζ` and evaluated on a positively oriented orthonormal frame is
`(F ∧ ζ)(e₀, e₁, e₂, e₃) = -(∂₁ b₂ - ∂₂ b₁)(z) ζ(e₀, e₁)`: the curvature current pairs `ζ` only with
its component along the base plane. -/
theorem wedge_neg_extDeriv_normalConnection_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}
    (hx : DifferentiableAt ℝ x (normalCoord e y)) (ζ : V [⋀^Fin 2]→L[ℝ] ℝ) :
    (-extDeriv (normalConnection e x) y).wedge ζ (e ∘ finCongr (hkl.trans Fact.out)) =
      -Vortex.curvature x (normalCoord e y) * ζ ![e 0, e 1] := by
  rw [o.wedge_apply_orthonormalBasis_eq_inner even_two hkl e he,
    alternatingFormEquiv_symm_neg_extDeriv_normalConnection hx, map_smul,
    o.hodgeStar_ιMulti_two_three hkl he, real_inner_smul_right,
    inner_alternatingFormEquiv_symm_ιMulti]

variable [MeasurableSpace V] [BorelSpace V] {X : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}

include hkl he in
/-- For `r > 0` the curvature current of the pulled-back vortex is an integral over the normal
plane of the density `(r / 4) (1 - |α_X(√(2r) n)|²)` against the integral of `ζ(e₀, e₁)` along the
base. -/
private theorem integral_wedge_neg_extDeriv_normalConnection_dilateField_eq (hX : ContDiff ℝ 2 X)
    (hsol : ∀ z, Vortex.equation X z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (X z 2 ^ 2 + X z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {ζ : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {r : ℝ}
    (hr : 0 < r) :
    ∫ y, (-extDeriv (normalConnection e (Vortex.dilateField √(2 * r) X)) y).wedge (ζ y)
        (e ∘ finCongr (hkl.trans Fact.out)) =
      ∫ n, r / 4 * (1 - ‖Vortex.sectionValue X (√(2 * r) • n)‖ ^ 2) *
        ∫ b, ζ ((baseNormalCoordHomeomorph e).symm (b, n)) ![e 0, e 1] := by
  have hα : Continuous (Vortex.sectionValue X) := Vortex.continuous_sectionValue hX.continuous
  obtain ⟨hψ, hψc⟩ :=
    continuous_and_hasCompactSupport_apply_baseNormalCoordHomeomorph_symm e hζ hζc
  set ψ : ℂ × ℂ → ℝ := fun p ↦ ζ ((baseNormalCoordHomeomorph e).symm p) ![e 0, e 1]
  set g : ℂ × ℂ → ℝ := fun p ↦ r / 4 * (1 - ‖Vortex.sectionValue X (√(2 * r) • p.2)‖ ^ 2) * ψ p
  have ht2 : √(2 * r) ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  -- Pointwise, the wedge is the vortex defect at the normal coordinate times `ζ(e₀, e₁)`.
  have hpt (y : V) : (-extDeriv (normalConnection e (Vortex.dilateField √(2 * r) X)) y).wedge
      (ζ y) (e ∘ finCongr (hkl.trans Fact.out)) = g (baseNormalCoordHomeomorph e y) := by
    rw [wedge_neg_extDeriv_normalConnection_apply e hkl he
      ((Vortex.contDiff_dilateField hX _).differentiable (by norm_num) _) (ζ y),
      Vortex.curvature_dilateField, Vortex.curvature_apply,
      Vortex.curvature_eq_of_equation_eq_zero (hsol _), ht2]
    simp only [g, ψ, Homeomorph.symm_apply_apply]
    simp only [baseNormalCoordHomeomorph_apply, Vortex.sq_norm_sectionValue, real_smul]
    ring
  -- `ψ` is integrable and the vortex factor is bounded by `r / 4`.
  have hint : Integrable g (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    refine (hψ.integrable_of_hasCompactSupport hψc).bdd_mul (c := r / 4) (by fun_prop)
      (.of_forall fun p ↦ ?_)
    have h1 := Vortex.sq_norm_sectionValue_le_one hX hsol hlim (√(2 * r) • p.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith [sq_nonneg ‖Vortex.sectionValue X (√(2 * r) • p.2)‖]
  simp_rw [hpt]
  rw [(measurePreserving_baseNormalCoordHomeomorph e).integral_comp
    (baseNormalCoordHomeomorph e).measurableEmbedding g, Measure.volume_eq_prod,
    integral_prod_symm g hint]
  refine integral_congr_ae (.of_forall fun n ↦ ?_)
  dsimp only [g, ψ]
  exact integral_const_mul _ _

include hkl he in
/-- **The curvature currents of the pulled-back vortex converge to the base plane with
multiplicity `m`.** Let `X` be a `C²` plane vortex with `|α| → 1` at infinity and zero divisor `D`
of degree `m`, and pull it back along the normal coordinate after dilation by `√(2r)`. The
curvature currents `T_r(ζ) = (2π)⁻¹ ∫ F_r ∧ ζ`, with `F_r = -db_r` the real curvature of the
pulled-back connection and top-degree coefficients read on the positively oriented orthonormal
frame `e`, converge as `r → ∞` to `m` times the current of integration over the base plane
`ℂ × {0}`, oriented by `(e₀, e₁)`: for every continuous compactly supported two-form `ζ`,

`T_r(ζ) → m ∫_ℂ ζ(Re w e₀ + Im w e₁)(e₀, e₁) dw`. -/
theorem tendsto_integral_wedge_neg_extDeriv_normalConnection_dilateField (hX : ContDiff ℝ 2 X)
    (hsol : ∀ z, Vortex.equation X z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (X z 2 ^ 2 + X z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (Vortex.sectionValue X) (Multiset.count · D))
    {ζ : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) :
    Tendsto (fun r ↦ (2 * π)⁻¹ * ∫ y, (-extDeriv (normalConnection e
        (Vortex.dilateField √(2 * r) X)) y).wedge (ζ y) (e ∘ finCongr (hkl.trans Fact.out)))
      atTop (𝓝 (D.card * ∫ w : ℂ, ζ (w.re • e 0 + w.im • e 1) ![e 0, e 1])) := by
  have hnn := Vortex.one_sub_sq_norm_sectionValue_nonneg hX hsol hlim
  have hf := Vortex.integrable_one_sub_sq_norm_sectionValue (μ := volume) hX hsol hlim
  have hflux := Vortex.integral_one_sub_sq_norm_sectionValue_eq_mul_card hX hsol hlim hD
  have hα : Continuous (Vortex.sectionValue X) := Vortex.continuous_sectionValue hX.continuous
  obtain ⟨hψ, hψc⟩ :=
    continuous_and_hasCompactSupport_apply_baseNormalCoordHomeomorph_symm e hζ hζc
  -- The integral of `ζ(e₀, e₁)` along the base, as a function of the normal coordinate.
  set Ψ : ℂ → ℝ := fun n ↦ ∫ b, ζ ((baseNormalCoordHomeomorph e).symm (b, n)) ![e 0, e 1]
  have hΨ : Continuous Ψ := continuous_integral_of_hasCompactSupport_uncurry
    (hψ.comp continuous_swap) (hψc.comp_homeomorph (.prodComm ℂ ℂ))
  have hΨc : HasCompactSupport Ψ :=
    hasCompactSupport_integral_of_hasCompactSupport_uncurry (hψc.comp_homeomorph (.prodComm ℂ ℂ))
  have hΨ0 : Ψ 0 = ∫ w : ℂ, ζ (w.re • e 0 + w.im • e 1) ![e 0, e 1] := by
    simp only [Ψ, baseNormalCoordHomeomorph_symm_apply, zero_re, zero_im, zero_smul, add_zero]
  rw [← hΨ0]
  refine Tendsto.congr' (f₁ := fun r ↦ (2 * π)⁻¹ *
      ∫ n, r / 4 * (1 - ‖Vortex.sectionValue X (√(2 * r) • n)‖ ^ 2) * Ψ n) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    rw [integral_wedge_neg_extDeriv_normalConnection_dilateField_eq e hkl he hX hsol hlim hζ hζc hr]
  by_cases hm : D.card = 0
  · -- Without zeros the vortex is the vacuum: its defect vanishes identically.
    have hf0 : (fun u ↦ 1 - ‖Vortex.sectionValue X u‖ ^ 2) = 0 := by
      rw [hm, Nat.cast_zero, mul_zero] at hflux
      exact ((by fun_prop : Continuous fun u ↦ 1 - ‖Vortex.sectionValue X u‖ ^ 2).ae_eq_iff_eq
        volume continuous_const).1 ((integral_eq_zero_iff_of_nonneg hnn hf).1 hflux)
    simp [funext_iff.1 hf0, hm]
  · exact tendsto_integral_mul_comp_sqrt_smul_mul (Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)) hnn
      hflux (Vortex.tendsto_norm_pow_mul_one_sub_sq_norm_sectionValue hX hsol hlim 2) hΨ hΨc

end Current

end TauCeti.SeibergWitten
