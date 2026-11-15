/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# The Krylov–Safonov estimates for strong solutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`
and interior Hölder estimate `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le` are
proved for classical functions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`, or
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`, at every point. Equations with measurable coefficients have, in general,
only strong solutions: functions `u ∈ W^{2,n}`, `n` the dimension, with a continuous representative
`ū`, satisfying the inequality almost everywhere with the weak Hessian `D²u`. This file proves both
estimates for them, by approximation with smooth functions
(`TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_sub_le_of_wkp`), which needs
no regularity or measurability of the coefficients.

The power decay reads: if `u ≥ 0` is a strong supersolution near the closed ball `B(c, R)`,
centred at the centre of a dyadic cube `Q₀` of side `ℓ` with `R ≥ 4 ℓ √n`, with `ū ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then

`|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`), for coefficients with
ellipticity constants `λ ≤ Λ ≤ κ λ` and with `C`, `ε` and `ε₀` depending only on `n` and `κ`. It is
the step from the measure estimate to the weak Harnack inequality.

The interior Hölder estimate reads: if `|u| ≤ M` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in
`B(x₀, 2 r)`, then the precise representative of `u`, which is continuous since `W^{2,n}` functions
are, satisfies

`|ū(x) - ū(y)| ≤ C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ) ‖x - y‖^α` for `x, y ∈ B(x₀, r)`

(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`),
with `0 < α ≤ 1` and `C` depending only on `n` and `κ`.

## The argument

For the power decay, given `ζ > 0`, take a smooth `w` with
`ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on `closedBall c R`, a classical supersolution with
right-hand side small enough for the classical power decay. It is nonnegative on the closed ball
and at most `1` where `ū ≤ 1`. On `Q₀ ⊆ closedBall c R`, `w ≥ ū / (1 + 3 ζ)`, so `{ū ≥ t} ∩ Q₀`
lies in the superlevel set of `w` at `t / (1 + 3 ζ)`. Letting `ζ → 0` gives the bound at `t`.

For the Hölder estimate, first let `closedBall x₀ (2 r)` lie in the domain of `u`. Given `η > 0`,
take a smooth `v` with `|v - ū| ≤ η` on `closedBall x₀ (2 r)` whose principal part differs from that
of `u` by a function of `Lⁿ` norm at most `η`. Then `|v| ≤ M + η` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv| ≤ g` with
`‖g‖_{Lⁿ} ≤ ‖f‖_{Lⁿ} + η`, so the classical estimate bounds `|v(x) - v(y)|`, and
`|ū(x) - ū(y)| ≤ |v(x) - v(y)| + 2 η`. Letting `η → 0` gives the estimate. On the open ball
`B(x₀, 2 r)`, apply this on the balls `B(x₀, 2 ρ)`, `ρ < r`, and let `ρ → r`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: the power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`:
  **the interior Hölder estimate of Krylov and Safonov** for `u ∈ W^{2,n}` with
  `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq`: the same
  estimate for strong solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions), Corollary 9.24.
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6 and Proposition 4.10.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology TauCeti.MeasureTheory
open scoped ENNReal NNReal Gradient

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

/-- **The Hölder bound for a strong solution on a compactly contained ball.** The interior Hölder
estimate of `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le`, in pointwise form,
for a strong solution `u ∈ W^{2,n}(Ω)` with a representative `ū` continuous on `Ω`, when the closed
ball `closedBall x₀ (2 r)` lies in `Ω` and `F` bounds `‖f‖_{Lⁿ(B(x₀, 2 r))}`. -/
private theorem exists_dist_le_of_closedBall_subset_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M F : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < r → 0 ≤ F → closedBall x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball x₀ (2 * r), |ū x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) ≤ ENNReal.ofReal F →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
          dist (ū x) (ū y) ≤ C * r ^ (-(α : ℝ)) * (M + r * F / lam) * dist x y ^ (α : ℝ) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  obtain ⟨α, C, hα0, hα1, hC, H⟩ := exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M F x₀ Ω a ū f u hr hF0 hΩ ha hLam hcont hū hM hsol hfF x hx y hy
  set n := Fintype.card ι
  set B := ball x₀ (2 * r)
  have hlam : 0 < lam := ha.pos
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_ball_self (by linarith)))
  have hB : ball x₀ r ⊆ closedBall x₀ (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  set d := dist x y ^ (α : ℝ)
  set A := C * r ^ (-(α : ℝ))
  set K := A * (1 + r / lam) * d + 2
  have hK : 0 < K := by positivity
  -- For every `η > 0`, a smooth approximation `v` within `η` of `ū` obeys the classical estimate
  -- with `M + η` and `F + η` in place of `M` and `F`.
  have key (η : ℝ) (hη : 0 < η) : dist (ū x) (ū y) ≤ A * (M + r * F / lam) * d + η * K := by
    obtain ⟨v, g, hv, hvK, hvg, hgf⟩ :=
      exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
        (ENNReal.natCast_ne_top n) u hcont hū (isCompact_closedBall x₀ (2 * r)) hΩ
        ball_subset_closedBall ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦
          ha.abs_apply_le hz) hsol hη
    have hgF : eLpNorm g n (volume.restrict B) ≤ ENNReal.ofReal (F + η) := by
      rw [ENNReal.ofReal_add hF0 hη.le]
      exact hgf.trans (by gcongr)
    have hvM (z : EuclideanSpace ℝ ι) (hz : z ∈ B) : |v z| ≤ M + η := by
      linarith [abs_sub_abs_le_abs_sub (v z) (ū z), hvK z (ball_subset_closedBall hz), hM z hz]
    have hHol := H hr ha hLam (contDiff_infty.1 hv 2).contDiffOn hvM hvg
      (hgF.trans_lt ENNReal.ofReal_lt_top)
    have hgF' : (eLpNorm g n (volume.restrict B)).toReal ≤ F + η :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hgF
    have hvxy : |v x - v y| ≤ A * (M + η + r * (F + η) / lam) * d := by
      refine (hHol.dist_le hx hy).trans ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      gcongr
    have hη' : A * (M + η + r * (F + η) / lam) * d + 2 * η =
        A * (M + r * F / lam) * d + η * K := by
      simp only [K]
      ring
    have h1 := abs_le.1 (hvK x (hB hx))
    have h2 := abs_le.1 (hvK y (hB hy))
    have h3 := abs_le.1 hvxy
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  -- Letting `η → 0`.
  exact le_of_forall_pos_le_add fun ε hε ↦
    (key (ε / K) (by positivity)).trans_eq (by rw [div_mul_cancel₀ _ hK.ne'])

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions**
(Gilbarg–Trudinger, Corollary 9.24; Caffarelli–Cabré, Proposition 4.10). Let `κ > 0`. There are
`0 < α ≤ 1` and `C > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following
property. Let `Ω` be an open set containing `B(x₀, 2 r)`, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in `B(x₀, 2 r)` for the weak Hessian, where
`f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise representative of `u` is `α`-Hölder on `B(x₀, r)` with
constant `C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (preciseRepresentative volume (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ := exists_dist_le_of_closedBall_subset_of_wkp (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M x₀ Ω a f u hΩ ha hLam hM hsol hfm
  -- For `r ≤ 0` the ball `B(x₀, r)` is empty.
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]
    exact fun _ h ↦ h.elim
  set ū := preciseRepresentative volume (Wkp.value 2 u)
  set B := ball x₀ (2 * r)
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict B)).toReal
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by rw [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  -- The almost-everywhere bound `|u| ≤ M` holds at every point of `B` for the continuous `ū`.
  have hMB : ∀ x ∈ B, |ū x| ≤ M := by
    have heq : EqOn (fun x ↦ max |ū x| M) (fun _ ↦ M) B := by
      refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_ball
        ((continuous_abs.comp_continuousOn (hcont.mono hΩ)).sup continuousOn_const)
        continuousOn_const
      filter_upwards [hM, ae_restrict_of_ae_restrict_of_subset hΩ hū] with x hx hxū
      rw [← hxū]
      exact max_eq_right hx
    exact fun x hx ↦ (le_max_left _ _).trans (heq hx).le
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  -- Apply the estimate on the balls `B(x₀, 2 ρ)`, `ρ < r`, whose closures lie in `B`, and let
  -- `ρ → r`.
  have hlim : Tendsto (fun ρ ↦ C * ρ ^ (-(α : ℝ)) * (M + ρ * F / lam) * dist x y ^ (α : ℝ))
      (𝓝[<] r) (𝓝 (C * r ^ (-(α : ℝ)) * (M + r * F / lam) * dist x y ^ (α : ℝ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
    exact ((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hr.ne'))).mul
      (continuousAt_const.add ((continuousAt_id.mul continuousAt_const).div_const _))).mul
      continuousAt_const
  have hmax : max (dist x x₀) (dist y x₀) < r := max_lt (mem_ball.1 hx) (mem_ball.1 hy)
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hmax] with ρ hρ
  have hρ0 : 0 < ρ := (le_max_left _ _).trans_lt hρ.1 |>.trans_le' dist_nonneg
  have hρB : ball x₀ (2 * ρ) ⊆ B := ball_subset_ball (by linarith [hρ.2])
  have hfρ : eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * ρ))) ≤ ENNReal.ofReal F :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono hρB le_rfl)).trans
      (ENNReal.ofReal_toReal hfm.eLpNorm_ne_top).ge
  exact H u hρ0 ENNReal.toReal_nonneg ((closedBall_subset_ball (by linarith [hρ.2])).trans hΩ)
    (ha.mono_set hρB) hLam hcont hū (fun z hz ↦ hMB z (hρB hz))
    (ae_restrict_of_ae_restrict_of_subset hρB hsol) hfρ x
    (mem_ball.2 ((le_max_left _ _).trans_lt hρ.1)) y
    (mem_ball.2 ((le_max_right _ _).trans_lt hρ.1))

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** of
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` (Gilbarg–Trudinger, Corollary 9.24). Let `κ > 0`. There are `0 < α ≤ 1` and
`C > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following property. Let `Ω` be
an open set containing `B(x₀, 2 r)`, let `a` be uniformly elliptic on `B(x₀, 2 r)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere
in `B(x₀, 2 r)` for the weak Hessian, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise representative
of `u` is `α`-Hölder on `B(x₀, r)` with constant `C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (preciseRepresentative volume (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ :=
    exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, fun lam Lam r M x₀ Ω a f u hΩ ha hLam hM hsol hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H u hΩ ha hLam hM (hsol.mono fun x hx ↦ hx ▸ (Real.norm_eq_abs _).ge) hf.norm

end PDE

end TauCeti
