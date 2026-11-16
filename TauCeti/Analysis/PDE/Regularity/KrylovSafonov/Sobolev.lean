/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Krylov–Safonov estimates for strong solutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`
and the local maximum principle `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add` are proved
for classical super- and subsolutions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`,
respectively `≥ f`, at every point. Equations with measurable coefficients have, in general, only
strong solutions: functions `u ∈ W^{2,n}`, `n` the dimension, with a continuous representative `ū`,
satisfying the inequality almost everywhere with the weak Hessian `D²u`. This file proves both
estimates for them, by approximation with the classical solutions of
`TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp` and
`TauCeti.PDE.exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp`, which need no
regularity or measurability of the coefficients.

The power decay reads: if `u ≥ 0` is a strong supersolution near the closed ball `B(c, R)`,
centred at the centre of a dyadic cube `Q₀` of side `ℓ` with `R ≥ 4 ℓ √n`, with `ū ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then

`|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`), for coefficients with
ellipticity constants `λ ≤ Λ ≤ κ λ` and with `C`, `ε` and `ε₀` depending only on `n` and `κ`. It is
the step from the measure estimate to the weak Harnack inequality and to the interior Hölder
estimate of Krylov and Safonov for strong solutions.

The local maximum principle reads: if `u` is a strong subsolution, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f`, near the
closed ball `closedBall c R`, then for every `p > 0`, with `B = B(c, R)`,

`ū x ≤ C (R^(-n/p) ‖ū⁺‖_{Lᵖ(B)} + R ‖f⁻‖_{Lⁿ(B)} / λ)` for `x ∈ B(c, R / 2)`

(`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`), with `C` depending only on `n`,
`κ` and `p`. Together with the weak Harnack inequality it gives the Harnack inequality for strong
solutions.

## The argument

Given `ζ > 0`, take a smooth `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on
`closedBall c R`, a classical supersolution with right-hand side small enough for the classical
power decay. It is nonnegative on the closed ball and at most `1` where `ū ≤ 1`. On
`Q₀ ⊆ closedBall c R`, `w ≥ ū / (1 + 3 ζ)`, so `{ū ≥ t} ∩ Q₀` lies in the superlevel set of `w` at
`t / (1 + 3 ζ)`. Letting `ζ → 0` gives the bound at `t`.

For the local maximum principle, given `ε > 0` take a smooth classical subsolution `w` with
`ū - ε ≤ w ≤ ū` on `closedBall c R` and right-hand side within `ε` of `f⁻` in `Lⁿ(B)`. Then
`w⁺ ≤ ū⁺`, so the classical estimate for `w` bounds `ū x ≤ w x + ε` by the claimed right-hand side
up to a multiple of `ε`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: the power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`: the local maximum principle for
  strong subsolutions.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.20 (the local maximum principle).
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If a quantity is bounded by `C (t / (1 + 3 ζ))^(-ε) V` for every `ζ > 0`, with `V` finite, then
it is bounded by `C t^(-ε) V`. -/
private theorem le_ofReal_mul_rpow_neg_mul_of_forall_div {C ε t : ℝ} (ht : 0 < t)
    {m V : ℝ≥0∞} (hV : V ≠ ∞)
    (h : ∀ ζ : ℝ, 0 < ζ → m ≤ ENNReal.ofReal (C * (t / (1 + 3 * ζ)) ^ (-ε)) * V) :
    m ≤ ENNReal.ofReal (C * t ^ (-ε)) * V := by
  have hlim : Tendsto (fun ζ : ℝ ↦ ENNReal.ofReal (C * (t / (1 + 3 * ζ)) ^ (-ε)) * V)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (C * t ^ (-ε)) * V)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hV)
    refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have h : ContinuousAt (fun ζ : ℝ ↦ C * (t / (1 + 3 * ζ)) ^ (-ε)) 0 := by
      refine continuousAt_const.mul (ContinuousAt.rpow_const ?_ (Or.inl (by simp [ht.ne'])))
      exact continuousAt_const.div (by fun_prop) (by norm_num)
    simpa using h.tendsto
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ζ hζ ↦ h ζ hζ)

/-- **Power decay of the superlevel sets of a strong supersolution** (Gilbarg–Trudinger,
Section 9.7; Caffarelli–Cabré, Lemma 4.6). Let `κ > 0`. There are constants `C > 0`, `ε > 0` and
`ε₀ > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following property. Let
`Q₀` be a dyadic cube of level `k`, so of side `2ᵏ`, with centre `c`, let `R ≥ 4 · 2ᵏ √n`, and let
`Ω` be an open set containing `closedBall c R`. Let the coefficient matrix `a` be uniformly
elliptic on `B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` have a representative
`ū` continuous on `Ω` and nonnegative on `closedBall c R`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost
everywhere in `B(c, R)` for the weak Hessian and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `ū ≤ 1`
somewhere in `B(c, 2 · 2ᵏ √n)`, then `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`. The
coefficients need not be measurable or symmetric. -/
theorem exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄ (u : Wkp volume Ω (Fintype.card ι) 2),
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R → closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), ū x ≤ 1) →
        ∀ ⦃t : ℝ⦄, 0 < t → volume ({x | t ≤ ū x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (C * t ^ (-ε)) *
            volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
  -- The classical estimate is applied, for each `ζ > 0`, to a mollification of `u` shifted up by
  -- `ζ` and divided by `1 + 3 ζ`; then `ζ → 0`.
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  refine ⟨C, ε, ε₀, hC, hε, hε₀, ?_⟩
  intro lam Lam R k m c Ω a ū f u hc hR hRΩ ha hLam hcont hū hnonneg hsuper hf hx t ht
  set n := Fintype.card ι
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k m
  have hn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hk : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hlam : 0 < lam := ha.pos
  have hQ : Q ⊆ closedBall c R := fun y hy ↦ by
    have h := dist_toLp_lt_of_mem_dyadicCube hy (centre_mem_dyadicCube k m)
    rw [WithLp.toLp_ofLp, ← hc] at h
    rw [mem_closedBall]
    nlinarith [mul_pos hk hn]
  obtain ⟨x₀, hx₀, hux₀⟩ := hx
  have hx₀R : x₀ ∈ closedBall c R :=
    ball_subset_closedBall (ball_subset_ball (by nlinarith [mul_pos hk hn]) hx₀)
  -- The bound on the right-hand side, divided by `R`.
  have hfR : eLpNorm (fun x ↦ (f x)⁺) n (volume.restrict (ball c R)) ≤
      ENNReal.ofReal (ε₀ * lam / R) := by
    rw [ENNReal.ofReal_div_of_pos hR0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hR0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hf
  -- For every `ζ > 0` the classical estimate, applied to a rescaled mollification `w` of `u`
  -- with `ū / σ ≤ w ≤ (ū + 2 ζ) / σ`, `σ = 1 + 3 ζ`, bounds the superlevel set at `t` by the value
  -- at `t / σ`.
  refine le_ofReal_mul_rpow_neg_mul_of_forall_div ht
    ((measure_mono hQ).trans_lt measure_closedBall_lt_top).ne fun ζ hζ ↦ ?_
  have hσ : 0 < 1 + 3 * ζ := by positivity
  obtain ⟨w, g, hw, hwū, hwg, hg⟩ :=
    exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp (ENNReal.natCast_ne_top n) u
      hcont hū (isCompact_closedBall c R) hRΩ ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ha.abs_apply_le hx) hsuper
      (by positivity) hfR hζ
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hgR : ENNReal.ofReal R * eLpNorm (fun x ↦ (g x)⁺) n (volume.restrict (ball c R)) ≤
      ENNReal.ofReal (ε₀ * lam) := by
    calc _ ≤ ENNReal.ofReal R * ENNReal.ofReal (ε₀ * lam / R) := by gcongr
      _ = ENNReal.ofReal (ε₀ * lam) := by
          rw [← ENNReal.ofReal_mul hR0.le, mul_div_cancel₀ _ hR0.ne']
  refine le_trans (measure_mono ?_) (H hc hR ha hLam hw2.continuous.continuousOn hw2.contDiffOn
    (fun y hy ↦ (div_nonneg (hnonneg y hy) hσ.le).trans (hwū y hy).1) hwg hgR
    ⟨x₀, hx₀, (hwū x₀ hx₀R).2.trans ((div_le_one hσ).2 (by linarith))⟩ (div_pos ht hσ))
  -- On the cube, `w ≥ ū / σ`.
  rintro y ⟨hy1, hy2⟩
  exact ⟨(div_le_div_of_nonneg_right hy1 hσ.le).trans (hwū y (hQ hy2)).1, hy2⟩

/-- **The local maximum principle for strong subsolutions** (Gilbarg–Trudinger, Theorem 9.20,
without lower-order terms). Let `p > 0` and `κ` be given. There is a constant `C`, depending only
on the dimension `n ≥ 1`, on `κ` and on `p`, with the following property. Let `Ω` be an open set
containing `closedBall c R`, let the coefficient matrix `a` be uniformly elliptic on `B = B(c, R)`
with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on
`Ω`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` almost everywhere in `B` for the weak Hessian and `f⁻ ∈ Lⁿ(B)`. Then
for every `x ∈ B(c, R / 2)`,

`ū x ≤ C (R^(-n/p) ‖ū⁺‖_{Lᵖ(B)} + R ‖f⁻‖_{Lⁿ(B)} / λ)`.

The constant is that of the classical estimate
`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`. The coefficients need not be measurable
or symmetric. -/
theorem exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ᵐ x ∂volume.restrict (ball c R),
          f x ≤ ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i) →
        MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ x ∈ ball c (R / 2), ū x ≤ C * (R ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm (fun y ↦ (ū y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
          R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
            (volume.restrict (ball c R))).toReal) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨C, hC, H⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := ι) (κ := κ) hp
  refine ⟨C, hC, fun lam Lam R c Ω a ū f u hRΩ ha hLam hcont hū hsub hf x hx ↦ ?_⟩
  set n := Fintype.card ι
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hlam : 0 < lam := ha.pos
  set B := C * (R / lam) + 1 with hBdef
  have hB : 0 < B := by positivity
  -- `ū⁺` is continuous on the closed ball, so it lies in `Lᵖ(B)`.
  have hūp : MemLp (fun y ↦ (ū y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
    ContinuousOn.memLp_restrict_of_subset_isCompact
      (continuous_posPart.comp_continuousOn (hcont.mono hRΩ)) (isCompact_closedBall c R)
      measurableSet_ball ball_subset_closedBall _
  -- For every `ε > 0` the classical estimate, applied to a smooth `w` with `ū - ε / B ≤ w ≤ ū`
  -- on the closed ball, bounds `ū x` up to `ε`.
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨w, g, hw, hwū, hwg, hg⟩ :=
    exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp (ENNReal.natCast_ne_top n) u
      hcont hū (isCompact_closedBall c R) hRΩ ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ha.abs_apply_le hx) hsub
      (div_pos hε hB)
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hgf : eLpNorm (fun x ↦ (f x)⁻) n (volume.restrict (ball c R)) +
      ENNReal.ofReal (ε / B) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, ENNReal.ofReal_ne_top⟩
  have hcl := H ha hLam hw2.continuous.continuousOn hw2.contDiffOn hwg
    (hg.trans_lt hgf.lt_top) x hx
  -- `w⁺ ≤ ū⁺` on the ball, and the right-hand side of `w` is within `ε / B` of `f⁻` in `Lⁿ`.
  have hwp : (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal ≤
      (eLpNorm (fun y ↦ (ū y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal := by
    refine ENNReal.toReal_mono hūp.eLpNorm_ne_top (eLpNorm_mono_ae
      (continuous_posPart.comp hw2.continuous).aestronglyMeasurable ?_)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_of_nonneg (posPart_nonneg _)]
    exact posPart_mono (hwū y (ball_subset_closedBall hy)).2
  have hgF : (eLpNorm (fun x ↦ (g x)⁻) n (volume.restrict (ball c R))).toReal ≤
      (eLpNorm (fun x ↦ (f x)⁻) n (volume.restrict (ball c R))).toReal + ε / B := by
    refine (ENNReal.toReal_mono hgf hg).trans_eq ?_
    rw [ENNReal.toReal_add hf.eLpNorm_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (div_pos hε hB).le]
  have hux : ū x ≤ w x + ε / B := by
    linarith [(hwū x (ball_subset_closedBall (ball_subset_ball (by linarith) hx))).1]
  calc ū x ≤ C * (R ^ (-(n : ℝ) / p) *
          (eLpNorm (fun y ↦ (ū y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
          R / lam * ((eLpNorm (fun y ↦ (f y)⁻) n (volume.restrict (ball c R))).toReal +
            ε / B)) + ε / B := by
        refine hux.trans (add_le_add_left (hcl.trans ?_) _)
        gcongr
    _ = _ := by
        have hBε : B * (ε / B) = ε := mul_div_cancel₀ _ hB.ne'
        linear_combination hBε - ε / B * hBdef

end PDE

end TauCeti
