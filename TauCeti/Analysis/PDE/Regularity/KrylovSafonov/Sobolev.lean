/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.PreciseRepresentative
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Power decay and the Hölder estimate for strong solutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`
and the interior Hölder estimate `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le`
are proved for classical functions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`, or
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`, at every point. Equations with measurable coefficients have, in general,
only strong solutions: functions `u ∈ W^{2,n}`, `n` the dimension, with a continuous representative
`ū`, satisfying the inequality almost everywhere with the weak Hessian `D²u`. This file proves both
estimates for them, by approximation with the classical functions of
`TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp` and
`TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`, which need no
regularity or measurability of the coefficients.

The power decay reads: if `u ≥ 0` is a strong supersolution near the closed ball `B(c, R)`,
centred at the centre of a dyadic cube `Q₀` of side `ℓ` with `R ≥ 4 ℓ √n`, with `ū ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then

`|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`), for coefficients with
ellipticity constants `λ ≤ Λ ≤ κ λ` and with `C`, `ε` and `ε₀` depending only on `n` and `κ`. It is
the step from the measure estimate to the weak Harnack inequality.

The Hölder estimate reads: if `|ū| ≤ M` on `B(x₀, 2 r)` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost
everywhere there, with `f ∈ Lⁿ(B(x₀, 2 r))`, then

`|ū x - ū y| ≤ C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ) ‖x - y‖^α` for `x, y ∈ B(x₀, r)`

(`TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le_of_wkp`), with `0 < α ≤ 1` and
`C` depending only on `n` and `κ`. For a strong solution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` with `|u| ≤ M`
almost everywhere, the continuous representative is the precise representative of `u`, the limit
of its ball averages (`TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq_of_wkp`). This
is the interior Hölder estimate of Krylov and Safonov for strong solutions (Gilbarg–Trudinger,
Corollary 9.24).

## The argument

For the power decay, given `ζ > 0`, take a smooth `w` with
`ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on `closedBall c R`, a classical supersolution with
right-hand side small enough for the classical power decay. It is nonnegative on the closed ball
and at most `1` where `ū ≤ 1`. On `Q₀ ⊆ closedBall c R`, `w ≥ ū / (1 + 3 ζ)`, so `{ū ≥ t} ∩ Q₀`
lies in the superlevel set of `w` at `t / (1 + 3 ζ)`. Letting `ζ → 0` gives the bound at `t`.

For the Hölder estimate, fix `x, y ∈ B(x₀, r)` and a small `t > 0`. On the compact ball
`closedBall x₀ (2 (r - t)) ⊆ B(x₀, 2 r)` take a smooth `v` within `t` of `ū`, with
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv| ≤ g` on `B(x₀, 2 (r - t))` and `‖g‖_{Lⁿ} ≤ ‖f‖_{Lⁿ} + t`. The classical
estimate on `B(x₀, 2 (r - t))`, with the bound `M + t` for `|v|`, bounds `|v x - v y|`, hence
`|ū x - ū y|` up to `2 t`, by a quantity continuous in `t`; letting `t → 0` gives the bound with
the constants of the classical estimate.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: the power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le_of_wkp`: **the interior Hölder
  estimate of Krylov and Safonov** for strong solutions of `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq_of_wkp`: the same estimate for the
  precise representative of a strong solution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions), Corollary 9.24.
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6 and Proposition 4.10.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal Gradient NNReal

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

/-- **The Hölder bound for a strong solution at a smaller radius, up to an error.** There are
`0 < α ≤ 1` and `C > 0`, depending only on the dimension and on `κ`, with the following property.
Under the hypotheses of `exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le_of_wkp`, for
`0 < t < r` and `x, y ∈ B(x₀, r - t)`,
`|ū x - ū y| ≤ C (r - t)^(-α) (M + t + (r - t) (‖f‖_{Lⁿ(B(x₀, 2 r))} + t) / λ) ‖x - y‖^α + 2 t`.
This is the classical estimate on `B(x₀, 2 (r - t))` for a smooth function within `t` of `ū`. -/
private theorem exists_dist_le_of_abs_sum_mul_fderiv_fderiv_le_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M t : ℝ⦄ ⦃x₀ x y : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < t → t < r → ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball x₀ (2 * r), |ū x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        x ∈ ball x₀ (r - t) → y ∈ ball x₀ (r - t) →
        dist (ū x) (ū y) ≤ C * (r - t) ^ (-(α : ℝ)) * (M + t + (r - t) *
          ((eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal + t) / lam) *
            dist x y ^ (α : ℝ) + 2 * t := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨α, C, hα0, hα1, hC, H⟩ := exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M t x₀ x y Ω a ū f u ht0 htr hΩ ha hLam hcont hū hM hf hfp hx hy
  set n := Fintype.card ι
  have hlam : 0 < lam := ha.pos
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_ball_self (by linarith)))
  set F := (eLpNorm f n (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hr'0 : 0 < r - t := sub_pos.2 htr
  have hsub : ball x₀ (2 * (r - t)) ⊆ ball x₀ (2 * r) := ball_subset_ball (by linarith)
  have hK : closedBall x₀ (2 * (r - t)) ⊆ ball x₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hx2 : x ∈ closedBall x₀ (2 * (r - t)) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hx)
  have hy2 : y ∈ closedBall x₀ (2 * (r - t)) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hy)
  -- A smooth `v` within `t` of `ū`, whose right-hand side `g` has `Lⁿ` norm at most `F + t`.
  obtain ⟨v, g, hv, hvū, hvg, hgp, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top n) u hcont hū (isCompact_closedBall x₀ (2 * (r - t))) (hK.trans hΩ)
      ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hsub hz))
      (hfp.mono_measure (Measure.restrict_mono hsub le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hsub hf) ht0
  have hgF : (eLpNorm g n (volume.restrict (ball x₀ (2 * (r - t))))).toReal ≤ F + t := by
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) (hg.trans ?_)
    rw [ENNReal.ofReal_add hF ht0.le, ENNReal.ofReal_toReal hfp.eLpNorm_ne_top]
    gcongr
  -- The classical estimate for `v` on `B(x₀, 2 (r - t))`, where `|v| ≤ M + t`.
  have hHv := H hr'0 (ha.mono_set hsub) hLam (contDiff_infty.1 hv 2).contDiffOn
    (fun z hz ↦ by
      calc |v z| = |ū z + (v z - ū z)| := by rw [add_sub_cancel]
        _ ≤ |ū z| + |v z - ū z| := abs_add_le _ _
        _ ≤ M + t := add_le_add (hM z (hsub hz)) (hvū z (ball_subset_closedBall hz))) hvg hgp
  have hdist := hHv.dist_le hx hy
  rw [Real.coe_toNNReal _ (by positivity)] at hdist
  have hmono : C * (r - t) ^ (-(α : ℝ)) * (M + t + (r - t) * (eLpNorm g n
      (volume.restrict (ball x₀ (2 * (r - t))))).toReal / lam) * dist x y ^ (α : ℝ) ≤
      C * (r - t) ^ (-(α : ℝ)) * (M + t + (r - t) * (F + t) / lam) * dist x y ^ (α : ℝ) := by
    gcongr
  have htri : dist (ū x) (ū y) ≤ dist (v x) (v y) + 2 * t := by
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.1 (hvū x hx2)
    obtain ⟨h3, h4⟩ := abs_le.1 (hvū y hy2)
    constructor <;> linarith [le_abs_self (v x - v y), neg_abs_le (v x - v y)]
  linarith

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24; Caffarelli–Cabré, Proposition 4.10). Let `κ > 0`. There are `0 < α ≤ 1` and
`C > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following property. Let `Ω`
be an open set containing `B(x₀, 2 r)`, let the coefficient matrix `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` have a representative `ū`
continuous on `Ω` with `|ū| ≤ M` on `B(x₀, 2 r)` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in
`B(x₀, 2 r)` for the weak Hessian, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then `ū` is `α`-Hölder on
`B(x₀, r)` with constant `C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The constants are those of the estimate for classical solutions,
`TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le`. The coefficients need no
regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < r → ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball x₀ (2 * r), |ū x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α ū (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ :=
    exists_dist_le_of_abs_sum_mul_fderiv_fderiv_le_of_wkp (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M x₀ Ω a ū f u hr hΩ ha hLam hcont hū hM hf hfp
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  set d := dist x y ^ (α : ℝ)
  set ρ := max (dist x x₀) (dist y x₀)
  have hρ0 : 0 ≤ ρ := dist_nonneg.trans (le_max_left _ _)
  -- The bound at the parameter `t`, continuous at `t = 0`, where it is the claimed bound.
  set Φ : ℝ → ℝ := fun t ↦ C * (r - t) ^ (-(α : ℝ)) * (M + t + (r - t) * (F + t) / lam) * d + 2 * t
  have hΦ : Filter.Tendsto Φ (𝓝[>] 0) (𝓝 (C * r ^ (-(α : ℝ)) * (M + r * F / lam) * d)) := by
    have hc : ContinuousAt Φ 0 := by
      have h1 : ContinuousAt (fun t : ℝ ↦ (r - t) ^ (-(α : ℝ))) 0 :=
        (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simpa using hr.ne'))
      exact ((((continuousAt_const.mul h1).mul ((continuousAt_const.add continuousAt_id).add
        (((continuousAt_const.sub continuousAt_id).mul
          (continuousAt_const.add continuousAt_id)).div_const lam))).mul continuousAt_const).add
        (continuousAt_const.mul continuousAt_id))
    simpa [Φ] using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto
  refine ge_of_tendsto hΦ ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (max_lt hx hy))] with t ⟨ht0, htρ⟩
  have hρt : ρ < r - t := by linarith
  exact H u ht0 (by linarith) hΩ ha hLam hcont hū hM hf hfp ((le_max_left _ _).trans_lt hρt)
    ((le_max_right _ _).trans_lt hρt)

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24). Let `κ > 0`. There are `0 < α ≤ 1` and `C > 0`, depending only on the dimension
`n ≥ 1` and on `κ`, with the following property. Let `Ω` be an open set containing `B(x₀, 2 r)`,
let the coefficient matrix `a` be uniformly elliptic on `B(x₀, 2 r)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost
everywhere in `B(x₀, 2 r)` for the weak Hessian, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise
representative of `u`, which agrees with `u` almost everywhere on `Ω`
(`TauCeti.Wkp.ae_eq_preciseRepresentative`), is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < r → ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (MeasureTheory.preciseRepresentative volume (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ :=
    exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le_of_wkp (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, fun lam Lam r M x₀ Ω a f u hr hΩ ha hLam hM heq hf ↦ ?_⟩
  set ū := MeasureTheory.preciseRepresentative volume (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by rw [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  -- The almost everywhere bound on `u` holds at every point of the ball for the continuous `ū`.
  have hMū : ∀ x ∈ ball x₀ (2 * r), |ū x| ≤ M := by
    have hae : (fun x ↦ min |ū x| M) =ᵐ[volume.restrict (ball x₀ (2 * r))] fun x ↦ |ū x| := by
      filter_upwards [hM, ae_restrict_of_ae_restrict_of_subset hΩ hū] with x hx hxū
      exact min_eq_left (hxū ▸ hx)
    have hc : ContinuousOn (fun x ↦ |ū x|) (ball x₀ (2 * r)) := (hcont.mono hΩ).abs
    intro x hx
    have h : min |ū x| M = |ū x| := Measure.eqOn_open_of_ae_eq hae isOpen_ball (by fun_prop) hc hx
    exact h ▸ min_le_right _ _
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H u hr hΩ ha hLam hcont hū hMū (heq.mono fun x hx ↦ (hx ▸ (Real.norm_eq_abs _).ge))
    hf.norm

end PDE

end TauCeti
