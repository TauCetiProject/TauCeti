/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.PreciseRepresentative
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.WeakHarnack
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.Order.OrderClosed

/-!
# Krylov–Safonov estimates for strong solutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`,
the local maximum principle `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add` and the
interior Hölder estimate `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le` are
proved for classical functions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`, `≥ f`,
respectively `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`, at every point. Equations with measurable coefficients have,
in general, only strong solutions: functions `u ∈ W^{2,n}`, `n` the dimension, satisfying the
inequality almost everywhere with the weak Hessian `D²u`; they are continuous
(`TauCeti.Wkp.continuousOn_preciseRepresentative`). This file proves these estimates for them, by
approximation with the smooth functions of
`TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp`,
`TauCeti.PDE.exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp` and
`TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`, which need no
regularity or measurability of the coefficients.

The power decay reads: if `u ≥ 0` is a strong supersolution near the closed ball `B(c, R)`,
centred at the centre of a dyadic cube `Q₀` of side `ℓ` with `R ≥ 4 ℓ √n`, with `ū ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then

`|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`), for coefficients with
ellipticity constants `λ ≤ Λ ≤ κ λ` and with `C`, `ε` and `ε₀` depending only on `n` and `κ`. It is
the step from the measure estimate to the weak Harnack inequality.

The Hölder estimate reads: if `|u| ≤ M` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in
`B(x₀, 2 r)`, with `f ∈ Lⁿ`, then the precise representative `ū` of `u` satisfies

`|ū x - ū y| ≤ C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ) ‖x - y‖^α` for `x, y ∈ B(x₀, r)`

(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`), with
`0 < α ≤ 1` and `C` depending only on `n` and `κ`. This is the interior Hölder estimate of Krylov
and Safonov for strong solutions.

The local maximum principle reads: if `u` is a strong subsolution, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f`, near the
closed ball `closedBall c R`, then for every `p > 0`, with `B = B(c, R)`,

`ū x ≤ C (R^(-n/p) ‖ū⁺‖_{Lᵖ(B)} + R ‖f⁻‖_{Lⁿ(B)} / λ)` for `x ∈ B(c, R / 2)`

(`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`), with `C` depending only on `n`,
`κ` and `p`.

Together with the weak Harnack inequality for strong supersolutions
(`TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart_of_wkp`) it gives the **Harnack
inequality** for strong solutions. Let `Ω ⊇ B(x₀, 2 r)` be open, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost
everywhere in `B(x₀, 2 r)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` (or only `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`) almost
everywhere there and `f ∈ Lⁿ(B(x₀, 2 r))`. No continuity of `u` is assumed: its precise
representative `ū` is continuous on `Ω` (`TauCeti.Wkp.continuousOn_preciseRepresentative`). Then

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)` for all `x, y ∈ B(x₀, r)`

(`TauCeti.PDE.exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq`), with `C`
depending only on `n` and `κ`. In particular `sup_{B(x₀, r)} ū ≤ C (inf_{B(x₀, r)} ū + r ‖f‖ / λ)`.

## The argument

Given `ζ > 0`, take a smooth `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on
`closedBall c R`, a classical supersolution with right-hand side small enough for the classical
power decay. It is nonnegative on the closed ball and at most `1` where `ū ≤ 1`. On
`Q₀ ⊆ closedBall c R`, `w ≥ ū / (1 + 3 ζ)`, so `{ū ≥ t} ∩ Q₀` lies in the superlevel set of `w` at
`t / (1 + 3 ζ)`. Letting `ζ → 0` gives the bound at `t`.

For the Hölder estimate, an almost-everywhere bound `|u| ≤ M` holds everywhere for the continuous
representative `ū`. Let `x, y ∈ B(x₀, r)`. When `‖x - y‖ ≥ r / 4`, the bound `|ū| ≤ M` suffices.
Otherwise take, for `η > 0`, a smooth `v` within `η` of `ū` on `closedBall x (r / 2)` whose
principal part is within `e` of that of `u` almost everywhere on `B(x, r / 2)`, with
`‖e‖_{Lⁿ} ≤ η`. Then `|v| ≤ M + η` there, and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv|` is bounded at every point by a
function equal to `f + e` almost everywhere. So the classical estimate on `B(x, r / 2)` bounds
`|v x - v y|`, and `|ū x - ū y|` up to `2 η`. Letting `η → 0` gives the bound.

For the local maximum principle, given `ε > 0` take a smooth classical subsolution `w` with
`ū - ε ≤ w ≤ ū` on `closedBall c R` and right-hand side within `ε` of `f⁻` in `Lⁿ(B)`. Then
`w⁺ ≤ ū⁺`, so the classical estimate for `w` bounds `ū x ≤ w x + ε` by the claimed right-hand side
up to a multiple of `ε`.

For the Harnack inequality, `ū ≥ 0` holds at every point of `B(x₀, 2 r)`, since there `ū` is
continuous and nonnegative almost everywhere. Let `z ∈ B(x₀, r)`, so that
`closedBall z r ⊆ B(x₀, 2 r)`, and put `δ = r / (16 √n)`. The local maximum principle on `B(z, δ)`,
at the exponent `p` of the weak Harnack inequality, bounds `ū(z)` by `δ^(-n/p) ‖ū‖_{Lᵖ(B(z, δ))}`
and `δ ‖f‖ₙ / λ`, and the weak Harnack inequality on `B(z, r)` bounds `‖ū‖_{Lᵖ(B(z, δ))}` by
`r^(n/p) (ū(w) + r ‖f‖ₙ / λ)` for every `w ∈ B(z, r / 4)`. Since `δ^(-n/p) r^(n/p) = (16 √n)^(n/p)`,
this gives `ū(z) ≤ C₀ (ū(w) + r ‖f‖ₙ / λ)` for `z, w ∈ B(x₀, r)` at distance at most `r / 5`. Two
points of `B(x₀, r)` are at distance less than `10 (r / 5)`, and a Harnack chain of ten steps along
the segment joining them gives the estimate with `C = 10 C₀¹⁰`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: the power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`: the local maximum principle for
  strong subsolutions.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`:
  the interior Hölder estimate of Krylov and Safonov for `W^{2,n}` functions with
  `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq`: the
  same estimate for strong solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`.
* `TauCeti.PDE.exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq`: the Harnack
  inequality for nonnegative strong solutions, and
  `TauCeti.PDE.exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le` under
  the bound `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions), Corollary 9.24.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.20 (the local maximum principle) and Corollary 9.25 (the Harnack inequality).
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6, Theorem 4.3 and Proposition 4.10.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology TauCeti.MeasureTheory
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
  have hφ : ContinuousAt (fun ζ : ℝ ↦ C * (t / (1 + 3 * ζ)) ^ (-ε)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.rpow_const ?_ (Or.inl (by simp [ht.ne'])))
    exact continuousAt_const.div (by fun_prop) (by norm_num)
  have hg := (ENNReal.continuous_mul_const hV).continuousAt.comp
    (ENNReal.continuous_ofReal.continuousAt.comp hφ)
  simpa using hg.continuousWithinAt.le_of_forall_gt_le h

omit [DecidableEq ι] in
/-- In dimension `n ≥ 1`, the exponent `n` of `W^{2,n}` exceeds half the dimension, so the precise
representative of a `W^{2,n}` function is continuous
(`TauCeti.Wkp.continuousOn_preciseRepresentative`). -/
private theorem finrank_lt_two_mul_card [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] :
    (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞) < 2 * Fintype.card ι := by
  have h : 1 ≤ Fintype.card ι := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι)
  rw [finrank_euclideanSpace]
  exact_mod_cast (by omega : Fintype.card ι < 2 * Fintype.card ι)

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

/-- The interior Hölder estimate of Krylov and Safonov for a `W^{2,n}(Ω)` function with a
continuous representative `ū`, on a ball whose closure lies in `Ω`, with `|ū| ≤ M` on the doubled
ball. This is the classical estimate
`TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le`, applied to the smooth
approximations of `TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`,
in the limit. -/
private theorem exists_holderOnWith_of_closedBall_subset [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < r → closedBall x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam → ContinuousOn ū Ω →
        (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball x₀ (2 * r), |ū x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α ū (ball x₀ r) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨α, C, hα0, hα1, hC, H⟩ := exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M x₀ Ω a ū f u hr hΩ ha hLam hcont hū hM hu hf
  set n := Fintype.card ι
  set B := ball x₀ (2 * r)
  set F := (eLpNorm f n (volume.restrict B)).toReal
  have hlam : 0 < lam := ha.pos
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_ball_self (by linarith)))
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  -- For every `η > 0`, the classical estimate for a smooth `v` within `η` of `ū`; then `η → 0`.
  refine le_of_forall_pos_mul_le (C := 2 + C * r ^ (-(α : ℝ)) * (1 + r / lam) *
    dist x y ^ (α : ℝ)) fun η hη ↦ ?_
  obtain ⟨v, g, hv, hvū, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top n) u hcont hū (isCompact_closedBall x₀ (2 * r)) hΩ
      ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le hz) hu hη
  have hgF : eLpNorm g n (volume.restrict B) ≤ ENNReal.ofReal (F + η) := by
    rw [ENNReal.ofReal_add hF hη.le, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    exact hg
  have hvM : ∀ z ∈ B, |v z| ≤ M + η := fun z hz ↦ by
    have h1 := hvū z (ball_subset_closedBall hz)
    have h2 := hM z hz
    linarith [abs_sub_abs_le_abs_sub (v z) (ū z)]
  have hHv := (H hr ha hLam (contDiff_infty.1 hv 2).contDiffOn hvM hvg
    (hgF.trans_lt ENNReal.ofReal_lt_top)).dist_le hx hy
  rw [Real.coe_toNNReal _ (by positivity)] at hHv
  have hxy : ∀ z ∈ ball x₀ r, dist (ū z) (v z) ≤ η := fun z hz ↦ by
    rw [dist_comm]
    exact hvū z (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
  calc dist (ū x) (ū y) ≤ dist (ū x) (v x) + dist (v x) (v y) + dist (v y) (ū y) :=
        dist_triangle4 _ _ _ _
    _ ≤ η + C * r ^ (-(α : ℝ)) * (M + η + r * (F + η) / lam) * dist x y ^ (α : ℝ) + η := by
        gcongr
        · exact hxy x hx
        · exact hHv.trans (by gcongr; exact ENNReal.toReal_le_of_le_ofReal (by positivity) hgF)
        · rw [dist_comm]
          exact hxy y hy
    _ = _ := by ring

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions**
(Gilbarg–Trudinger, Corollary 9.24; Caffarelli–Cabré, Proposition 4.10). Let `κ > 0`. There are
`0 < α ≤ 1` and `C > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following
property. Let `a` be uniformly elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, let `Ω` be an
open set containing `B(x₀, 2 r)`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in `B(x₀, 2 r)`, for the weak Hessian and some
`f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with
constant `C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < r → ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (MeasureTheory.preciseRepresentative volume (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ := exists_holderOnWith_of_closedBall_subset (ι := ι) hκ
  refine ⟨α, (C + 2) * 4 ^ (α : ℝ), hα0, hα1, by positivity, ?_⟩
  intro lam Lam r M x₀ Ω a f u hr hΩ ha hLam hM hu hf
  set B := ball x₀ (2 * r)
  set ū := MeasureTheory.preciseRepresentative volume (Wkp.value 2 u)
  set Q := M + r * (eLpNorm f (Fintype.card ι) (volume.restrict B)).toReal / lam
  have hlam : 0 < lam := ha.pos
  have hMū (x : EuclideanSpace ℝ ι) (hx : x ∈ B) : |ū x| ≤ M :=
    Wkp.abs_preciseRepresentative_le (finrank_lt_two_mul_card (ι := ι)) u isOpen_ball hΩ hM hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMū x₀ (mem_ball_self (by linarith)))
  have hQ : 0 ≤ Q := add_nonneg hM0 (by positivity)
  -- Points of `B(x₀, r)` closer than `s = r / 4` are compared by the estimate on `B(x, s)`, where
  -- `closedBall x (2 s) ⊆ B`; farther points by `|ū| ≤ M`. Both give the bound
  -- `(C + 2) Q s^(-α) ‖x - y‖^α`, and `s^(-α) = 4^α r^(-α)`.
  set s := r / 4 with hs_def
  have hs : 0 < s := by positivity
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  suffices h : dist (ū x) (ū y) ≤ (C + 2) * Q * (s ^ (-(α : ℝ)) * dist x y ^ (α : ℝ)) by
    refine h.trans_eq ?_
    rw [hs_def, Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul]
    ring
  have hQd : 0 ≤ Q * (s ^ (-(α : ℝ)) * dist x y ^ (α : ℝ)) := by positivity
  rcases lt_or_ge (dist x y) s with hd | hd
  · have hxB : closedBall x (2 * s) ⊆ B := fun z hz ↦ mem_ball.2 (by
      linarith [dist_triangle z x x₀, mem_closedBall.1 hz, mem_ball.1 hx, hs_def])
    have hSB : ball x (2 * s) ⊆ B := ball_subset_closedBall.trans hxB
    have h0 := (H u hs (hxB.trans hΩ) (ha.mono_set hSB) hLam
      (Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u)
      (Wkp.ae_eq_preciseRepresentative 2 u)
      (fun z hz ↦ hMū z (hSB hz)) (ae_restrict_of_ae_restrict_of_subset hSB hu)
      (hf.mono_measure (Measure.restrict_mono hSB le_rfl))).dist_le (mem_ball_self hs)
      (by rwa [mem_ball, dist_comm])
    rw [Real.coe_toNNReal _ (mul_nonneg (by positivity) (add_nonneg hM0 (by positivity)))] at h0
    have h1 := ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono hSB le_rfl))
    calc _ ≤ C * s ^ (-(α : ℝ)) * Q * dist x y ^ (α : ℝ) :=
          h0.trans (by gcongr; exact add_le_add_right (div_le_div_of_nonneg_right
            (mul_le_mul (by linarith) h1 ENNReal.toReal_nonneg hr.le) hlam.le) M)
      _ ≤ _ := by nlinarith
  · -- At distance at least `s`, `|ū x - ū y| ≤ 2 M ≤ 2 Q ≤ 2 Q (‖x - y‖ / s)^α`.
    have h1 : 1 ≤ s ^ (-(α : ℝ)) * dist x y ^ (α : ℝ) := by
      rw [Real.rpow_neg hs.le, inv_mul_eq_div, ← Real.div_rpow dist_nonneg hs.le]
      exact Real.one_le_rpow ((one_le_div hs).2 hd) α.coe_nonneg
    have hM1 := hMū x (ball_subset_ball (by linarith) hx)
    have hM2 := hMū y (ball_subset_ball (by linarith) hy)
    have hMQ : M ≤ Q := le_add_of_nonneg_right (by positivity)
    rw [Real.dist_eq]
    nlinarith [abs_sub (ū x) (ū y), mul_nonneg hC.le hQd]

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions**
(Gilbarg–Trudinger, Corollary 9.24). Let `κ > 0`. There are `0 < α ≤ 1` and `C > 0`, depending
only on the dimension `n ≥ 1` and on `κ`, with the following property. Let `a` be uniformly
elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, let `Ω` be an open set containing
`B(x₀, 2 r)`, and let `u ∈ W^{2,n}(Ω)` be a strong solution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` in
`B(x₀, 2 r)`, with `f ∈ Lⁿ(B(x₀, 2 r))` and `|u| ≤ M` almost everywhere there. Then the precise
representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq
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
    exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le (ι := ι) hκ
  refine ⟨α, C, hα0, hα1, hC, fun lam Lam r M x₀ Ω a f u hr hΩ ha hLam hM heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H u hr hΩ ha hLam hM (heq.mono fun x hx ↦ hx.symm ▸ (Real.norm_eq_abs _).ge) hf.norm

/-! ### The Harnack inequality -/

/-- The arithmetic of the fixed-scale Harnack step. Let `s ≥ 16`, and suppose that the local
maximum principle on `B(c, r / s)` bounds `u(c)` by an `Lᵖ` norm `L` of `u` on that ball and a
norm `F₁ ≤ F` of the right-hand side, and that the weak Harnack inequality on `B(c, r)` bounds `L`
by `u(w)` and a norm `F₂ ≤ F`. Then `u(c) ≤ C (u(w) + r F / λ)` with `C` depending only on the
constants of the two estimates, on `s` and on `n / p`. -/
private theorem le_max_mul_add_of_le_of_le {Cl Cw s n p r lam uc uw L F₁ F₂ F : ℝ} (hCl : 0 < Cl)
    (hCw : 0 ≤ Cw) (hs : 16 ≤ s) (hr : 0 < r) (hlam : 0 < lam) (huw : 0 ≤ uw) (hF₁ : 0 ≤ F₁)
    (hloc : uc ≤ Cl * ((r / s) ^ (-n / p) * L + r / s / lam * F₁))
    (hweak : L ≤ Cw * r ^ (n / p) * (uw + r / lam * F₂)) (hF₁F : F₁ ≤ F) (hF₂F : F₂ ≤ F) :
    uc ≤ max 1 (Cl * (s ^ (n / p) * Cw + 1)) * (uw + r * F / lam) := by
  have hδ : 0 < r / s := div_pos hr (by linarith)
  have hδr : r / s ≤ r := div_le_self hr.le (by linarith)
  have hF : 0 ≤ F := hF₁.trans hF₁F
  -- `(r / s)^(-n/p) r^(n/p) = s^(n/p)`.
  have hscale : (r / s) ^ (-n / p) * r ^ (n / p) = s ^ (n / p) := by
    rw [neg_div, Real.rpow_neg hδ.le, Real.div_rpow hr.le (by linarith), inv_div,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr _).ne']
  calc uc ≤ Cl * ((r / s) ^ (-n / p) * (Cw * r ^ (n / p) * (uw + r / lam * F)) +
        r / lam * F) := by
        refine hloc.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCl.le)
        · refine mul_le_mul_of_nonneg_left (hweak.trans ?_) (by positivity)
          gcongr
        · exact mul_le_mul (div_le_div_of_nonneg_right hδr hlam.le) hF₁F hF₁ (by positivity)
    _ = Cl * (s ^ (n / p) * Cw * (uw + r * F / lam) + r * F / lam) := by
        rw [← hscale]
        ring
    _ ≤ Cl * (s ^ (n / p) * Cw + 1) * (uw + r * F / lam) := by
        have : 0 ≤ r * F / lam := by positivity
        nlinarith [mul_nonneg hCl.le huw]
    _ ≤ max 1 (Cl * (s ^ (n / p) * Cw + 1)) * (uw + r * F / lam) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The Harnack chain on a ball. If `g z ≤ C (g w + K)` for all points `z, w` of `B(x₀, r)` at
distance at most `r / 5`, with `C ≥ 1` and `K ≥ 0`, then `g x ≤ C ^ N (g y + N K)` for all
`x, y ∈ B(x₀, r)` at distance at most `N r / 5`: cut the segment from `x` to `y`, which lies in
the ball, into `N` pieces. -/
private theorem le_pow_mul_add_mul_of_dist_le_div_five {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → ℝ} {C K r : ℝ} {x₀ : E} (hC : 1 ≤ C) (hK : 0 ≤ K)
    (h : ∀ z ∈ ball x₀ r, ∀ w ∈ ball x₀ r, dist z w ≤ r / 5 → g z ≤ C * (g w + K)) (N : ℕ)
    {x y : E} (hx : x ∈ ball x₀ r) (hy : y ∈ ball x₀ r) (hxy : dist x y ≤ N * (r / 5)) :
    g x ≤ C ^ N * (g y + N * K) := by
  induction N generalizing x with
  | zero =>
    rw [Nat.cast_zero, zero_mul, dist_le_zero] at hxy
    simp [hxy]
  | succ N ih =>
    -- The first piece ends at `w = x + (y - x) / (N + 1)`, at distance at most `N r / 5` from `y`.
    have hN : (0 : ℝ) < N + 1 := by positivity
    set θ : ℝ := ((N : ℝ) + 1)⁻¹
    have hθ : θ ∈ Icc (0 : ℝ) 1 := ⟨by positivity, inv_le_one_of_one_le₀ (by simp)⟩
    have hxy' : dist x y ≤ (N + 1) * (r / 5) := by exact_mod_cast hxy
    have hw : AffineMap.lineMap x y θ ∈ ball x₀ r := (convex_ball x₀ r).lineMap_mem hx hy hθ
    have hxw : dist x (AffineMap.lineMap x y θ) ≤ r / 5 := by
      rw [dist_left_lineMap, Real.norm_of_nonneg hθ.1]
      exact (inv_mul_le_iff₀ hN).2 hxy'
    have hwy : dist (AffineMap.lineMap x y θ) y ≤ N * (r / 5) := by
      rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.2 hθ.2)]
      calc (1 - θ) * dist x y ≤ (1 - θ) * ((N + 1) * (r / 5)) :=
            mul_le_mul_of_nonneg_left hxy' (sub_nonneg.2 hθ.2)
        _ = N * (r / 5) := by
            linear_combination (-(r / 5)) * (inv_mul_cancel₀ hN.ne' : θ * (N + 1) = 1)
    have : 0 ≤ C := zero_le_one.trans hC
    calc g x ≤ C * (g (AffineMap.lineMap x y θ) + K) := h x hx _ hw hxw
      _ ≤ C * (C ^ N * (g y + N * K) + K) := by gcongr; exact ih hw hwy
      _ ≤ C * (C ^ N * (g y + N * K) + C ^ N * K) := by
          gcongr
          exact le_mul_of_one_le_left hK (one_le_pow₀ hC)
      _ = C ^ (N + 1) * (g y + (N + 1 : ℕ) * K) := by push_cast; ring

/-- The weak Harnack inequality, in real form, for `u ∈ W^{2,n}(Ω)` with a representative `ū`
continuous on `Ω ⊇ closedBall c R` and nonnegative on `closedBall c R`, and with
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in `B(c, R)`. -/
private theorem exists_toReal_eLpNorm_le_mul_rpow_mul_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ y ∈ ball c (R / 4),
          (eLpNorm ū (ENNReal.ofReal p)
              (volume.restrict (ball c (R / (16 * √(Fintype.card ι)))))).toReal ≤
            C * R ^ ((Fintype.card ι : ℝ) / p) * (ū y + R / lam *
              (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal) := by
  obtain ⟨p, C, hp, hC, H⟩ :=
    exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart_of_wkp (ι := ι) hκ
  refine ⟨p, C, hp, hC, fun lam Lam R c Ω a ū f u hRΩ ha hLam hcont hū hnonneg habs hf y hy ↦ ?_⟩
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hlam : 0 < lam := ha.pos
  have huy : 0 ≤ ū y := hnonneg y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
  have hweak := H u hRΩ ha hLam hcont hū hnonneg (habs.mono fun x hx ↦ le_of_abs_le hx) y hy
  -- `f ≥ |∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≥ 0` almost everywhere on the ball, so `f⁺ = f` there.
  have hfpos : eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) =
      ENNReal.ofReal (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal := by
    rw [ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    exact eLpNorm_congr_ae <| habs.mono fun x hx ↦ posPart_eq_self.2 ((abs_nonneg _).trans hx)
  rw [hfpos, ← ENNReal.ofReal_mul (div_pos hR hlam).le, ← ENNReal.ofReal_add huy (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hweak
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hweak

/-- The local maximum principle at the centre of `B(c, R)`, in real form, for `u ∈ W^{2,n}(Ω)`
with a representative `ū` continuous on `Ω ⊇ closedBall c R` and nonnegative on `B(c, R)`, and
with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in `B(c, R)`. -/
private theorem exists_le_mul_rpow_mul_toReal_eLpNorm_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), 0 < R → closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball c R)) →
        ū c ≤ C * (R ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm ū (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
          R / lam * (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal) := by
  obtain ⟨C, hC, H⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp (ι := ι) (κ := κ) hp
  refine ⟨C, hC, fun lam Lam R c Ω a ū f u hR hRΩ ha hLam hcont hū hnonneg habs hf ↦ ?_⟩
  -- `f ≥ |∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≥ 0` almost everywhere on the ball, so `(-f)⁻ = f` there; and `ū⁺ = ū`
  -- on the ball.
  have hfneg : (fun x ↦ (-f x)⁻) =ᵐ[volume.restrict (ball c R)] f :=
    habs.mono fun x hx ↦ by
      simp only [negPart_neg, posPart_eq_self.2 ((abs_nonneg _).trans hx)]
  have hupos : eLpNorm (fun x ↦ (ū x)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R)) =
      eLpNorm ū (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
    eLpNorm_congr_ae <| ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      posPart_eq_self.2 (hnonneg x hx)
  have h := H u hRΩ ha hLam hcont hū (f := fun x ↦ -f x)
    (habs.mono fun x hx ↦ neg_le_of_abs_le hx) (hf.ae_eq hfneg.symm) c
    (mem_ball_self (half_pos hR))
  rwa [hupos, eLpNorm_congr_ae hfneg] at h

/-- **The Harnack inequality at a fixed scale, for strong solutions.** There is `C ≥ 1`,
depending only on the dimension and on `κ`, such that if `u ∈ W^{2,n}(Ω)` has a representative
`ū` continuous on `Ω ⊇ B(x₀, 2 r)` and nonnegative on `B(x₀, 2 r)`, with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`
almost everywhere in `B(x₀, 2 r)`, then `ū(z) ≤ C (ū(w) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)` for all
`z, w ∈ B(x₀, r)` at distance at most `r / 5`. -/
private theorem exists_le_mul_add_of_dist_le_div_five_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ ball x₀ (2 * r), 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ z ∈ ball x₀ r, ∀ w ∈ ball x₀ r, dist z w ≤ r / 5 → ū z ≤ C * (ū w + r *
          (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨p, Cw, hp, hCw, HW⟩ := exists_toReal_eLpNorm_le_mul_rpow_mul_add_of_wkp (ι := ι) hκ
  obtain ⟨Cl, hCl, HL⟩ := exists_le_mul_rpow_mul_toReal_eLpNorm_add_of_wkp (ι := ι) (κ := κ) hp
  set n : ℝ := (Fintype.card ι : ℝ)
  set s : ℝ := 16 * √n
  have hs : 16 ≤ s := by linarith [Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos : 1 ≤ n)]
  refine ⟨max 1 (Cl * (s ^ (n / p) * Cw + 1)), le_max_left _ _, ?_⟩
  intro lam Lam r x₀ Ω a ū f u hΩ ha hLam hcont hū hnonneg habs hf z hz w hw hzw
  have hr : 0 < r := pos_of_mem_ball hz
  have hlam : 0 < lam := ha.pos
  have huw : 0 ≤ ū w := hnonneg w (ball_subset_ball (by linarith) hw)
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : ∀ {t}, t ⊆ ball x₀ (2 * r) →
      (eLpNorm f (Fintype.card ι) (volume.restrict t)).toReal ≤ F := fun ht ↦
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono ht le_rfl))
  -- The balls about `z`: `B(z, r / s) ⊆ closedBall z r ⊆ B(x₀, 2 r)`.
  have hsub : closedBall z r ⊆ ball x₀ (2 * r) := fun v hv ↦ by
    rw [mem_closedBall] at hv
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle v z x₀]
  have hb : ball z r ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hsub
  have hδ : 0 < r / s := div_pos hr (by linarith)
  have hδr : r / s < r := div_lt_self hr (by linarith)
  have hbδ : ball z (r / s) ⊆ ball x₀ (2 * r) := (ball_subset_ball hδr.le).trans hb
  have hloc := HL u hδ (((closedBall_subset_ball hδr).trans hb).trans hΩ) (ha.mono_set hbδ) hLam
    hcont hū (fun x hx ↦ hnonneg x (hbδ hx)) (ae_restrict_of_ae_restrict_of_subset hbδ habs)
    (hf.mono_measure (Measure.restrict_mono hbδ le_rfl))
  have hweak := HW u (hsub.trans hΩ) (ha.mono_set hb) hLam hcont hū
    (fun x hx ↦ hnonneg x (hsub hx)) (ae_restrict_of_ae_restrict_of_subset hb habs)
    (hf.mono_measure (Measure.restrict_mono hb le_rfl)) w (by rw [mem_ball, dist_comm]; linarith)
  exact le_max_mul_add_of_le_of_le hCl hCw.le hs hr hlam huw ENNReal.toReal_nonneg hloc hweak
    (hF hbδ) (hF hb)

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.25; Caffarelli–Cabré, Theorem 4.3). For every `κ` there is `C > 0`, depending only on
the dimension `n ≥ 1` and on `κ`, with the following property. Let `Ω ⊇ B(x₀, 2 r)` be open, let
`a` be uniformly elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be
nonnegative almost everywhere in `B(x₀, 2 r)`, with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere there
for the weak Hessian, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise representative `ū` of `u`, which
is continuous on `Ω` and agrees with `u` almost everywhere, satisfies, for all `x, y ∈ B(x₀, r)`,

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), 0 ≤ Wkp.value 2 u x) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, preciseRepresentative volume (Wkp.value 2 u) x ≤
          C * (preciseRepresentative volume (Wkp.value 2 u) y + r *
            (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  -- For `κ ≤ 0` no coefficients satisfy `0 < λ ≤ Λ ≤ κ λ`.
  rcases le_or_gt κ 0 with hκ | hκ
  · refine ⟨1, one_pos, fun lam Lam r x₀ Ω a f u _ ha hLam _ _ _ ↦ absurd hLam ?_⟩
    have := ha.pos
    nlinarith [ha.le]
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_dist_le_div_five_of_wkp (ι := ι) hκ
  refine ⟨10 * C₀ ^ 10, by positivity, ?_⟩
  intro lam Lam r x₀ Ω a f u hΩ ha hLam hnonneg habs hf x hx y hy
  set ū := preciseRepresentative volume (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  -- `ū ≥ 0` on the ball: there it is continuous and nonnegative almost everywhere.
  have hū0 : ∀ z ∈ ball x₀ (2 * r), 0 ≤ ū z :=
    ContinuousOn.le_of_ae_le (f := fun _ ↦ 0) isOpen_ball continuousOn_const (hcont.mono hΩ) (by
      filter_upwards [hnonneg, ae_restrict_of_ae_restrict_of_subset hΩ hū] with z hz hz'
      exact hz' ▸ hz)
  have hr : 0 < r := pos_of_mem_ball hx
  have hlam : 0 < lam := ha.pos
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  -- Chain the fixed-scale estimate along the segment from `x` to `y`, cut into ten pieces.
  have hxy : dist x y ≤ (10 : ℕ) * (r / 5) := by
    have := dist_triangle_right x y x₀
    rw [mem_ball] at hx hy
    push_cast
    linarith
  have hchain := le_pow_mul_add_mul_of_dist_le_div_five hC₀ (by positivity)
    (H u hΩ ha hLam hcont hū hū0 habs hf) 10 hx hy hxy
  have huy : 0 ≤ ū y := hū0 y (ball_subset_ball (by linarith) hy)
  have hC10 : 0 ≤ C₀ ^ 10 := by positivity
  calc ū x ≤ C₀ ^ 10 * (ū y + (10 : ℕ) * (r * F / lam)) := hchain
    _ ≤ 10 * C₀ ^ 10 * (ū y + r * F / lam) := by
      push_cast
      nlinarith [mul_nonneg hC10 huy]

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.25). For every `κ` there is `C > 0`, depending only on the dimension `n ≥ 1` and on
`κ`, with the following property. Let `Ω ⊇ B(x₀, 2 r)` be open, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be a strong solution of
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` in `B(x₀, 2 r)`, nonnegative almost everywhere there, where
`f ∈ Lⁿ(B(x₀, 2 r))`. Then the precise representative `ū` of `u` satisfies, for all
`x, y ∈ B(x₀, r)`,

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), ball x₀ (2 * r) ⊆ Ω →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), 0 ≤ Wkp.value 2 u x) →
        (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, preciseRepresentative volume (Wkp.value 2 u) x ≤
          C * (preciseRepresentative volume (Wkp.value 2 u) y + r *
            (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ :=
    exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le (ι := ι) κ
  refine ⟨C, hC, fun lam Lam r x₀ Ω a f u hΩ ha hLam hnonneg heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H u hΩ ha hLam hnonneg (heq.mono fun x hx ↦ hx ▸ (Real.norm_eq_abs _).ge) hf.norm

end PDE

end TauCeti
