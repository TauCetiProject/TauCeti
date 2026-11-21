/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.PreciseRepresentative
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Harnack
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.MeasureTheory.Function.LpSeminorm.Haar
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Topology.Order.OrderClosed

/-!
# Krylov–Safonov estimates for `W^{2,n}` strong solutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`,
the local maximum principle `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`, the weak
Harnack inequality `TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`,
the Harnack inequality `TauCeti.PDE.exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le`, and the
interior Hölder estimate `TauCeti.PDE.exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le` are
proved for classical functions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`, `≥ f`,
respectively `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`, at every point.

Equations in non-divergence form with measurable coefficients have, in general, only strong
solutions: functions `u ∈ W^{2,n}(Ω)`, `n` the dimension, satisfying the differential inequality or
equation almost everywhere with the weak Hessian `D²u`. By Sobolev's embedding at the borderline
exponent `p = n`, the precise representative `ū = preciseRepresentative μ (Wkp.value 2 u)` is
continuous on `Ω` (`TauCeti.Wkp.continuousOn_preciseRepresentative`) and agrees with `u` almost
everywhere (`TauCeti.Wkp.ae_eq_preciseRepresentative`). This file transfers the classical
Krylov–Safonov theory — power decay, the local maximum principle, the weak Harnack inequality, the
Harnack inequality, and the interior Hölder estimate — to `W^{2,n}` strong subsolutions,
supersolutions, and solutions, without any regularity, measurability, or symmetry assumptions on the
coefficient matrix `a`.

## The approximation method

On any compact concentric sub-ball `closedBall x₀ s ⊂ B(x₀, R) ⊆ Ω`, interior mollification
(`TauCeti.PDE.exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp`,
`TauCeti.PDE.exists_contDiff_le_and_le_add_and_sum_mul_fderiv_fderiv_le_of_wkp`,
`TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`,
`TauCeti.PDE.exists_contDiff_le_and_le_add_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`, and
`TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp`) produces a smooth function
`w` within `η` of `ū` on `closedBall x₀ s` whose classical principal part controls the weak
principal part up to an `Lⁿ` error of norm at most `η`:

* For **power decay** (`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`),
  a rescaled mollification `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` lets `ζ → 0`.
* For **strong subsolutions** (`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` a.e.), approximating from below gives `w` with
  `ū - η ≤ w ≤ ū` on `closedBall c s`, so `w⁺ ≤ ū⁺` pointwise on `B(c, s)` while avoiding any
  quasi-triangle loss when `0 < p < 1`.
* For **strong supersolutions** (`u ≥ 0` and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` a.e. on `B(x₀, R)`), setting
  `θ' = √θ` so that `closedBall x₀ (θ' R) ⊂ B(x₀, R)` and `θ' (θ' R) = θ R`, approximating from
  above on `closedBall x₀ (θ' R)` gives `0 ≤ ū ≤ w ≤ ū + η`, so `‖ū‖_{Lᵖ} ≤ ‖w‖_{Lᵖ}` on
  `B(x₀, θ R)`.
* For **strong solutions** (`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` a.e. on `B(x₀, 2 r)`), approximating from above
  (for Harnack) or uniformly within `η` (for Hölder) on `closedBall x₀ (2 s) ⊂ B(x₀, 2 r)`
  transfers both estimates directly from their classical counterparts as `η → 0`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_preciseRepresentative_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`: **the local
  maximum principle** for `W^{2,n}` strong subsolutions on `B(c, R) ⊆ Ω` and arbitrary additive Haar
  measure.
* `TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_preciseRepresentative_add_of_wkp`: **the weak
  Harnack inequality** for `W^{2,n}` strong supersolutions.
* `TauCeti.PDE.exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le`,
  `TauCeti.PDE.exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq`: **the
  Harnack inequality** for `W^{2,n}` strong solutions.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`,
  `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq`: **the
  interior Hölder estimate** for `W^{2,n}` strong solutions.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7, Theorems 9.20 and 9.22 and Corollary 9.24.
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6, Theorem 4.8, Corollary 4.9, and Proposition 4.10.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Module Set TopologicalSpace Topology TauCeti.MeasureTheory
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

section StrongSolutions

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

omit [DecidableEq ι] in
/-- Scales the `mu`-to-`volume` restricted `Lⁿ` comparison from `Haar.lean` by `s / λ ≤ R / λ`
with `α₀^(1/n) ≤ K`. -/
private theorem memLp_volume_and_mul_eLpNorm_div_le
    {G F_fn : EuclideanSpace ℝ ι → ℝ} {S U : Set (EuclideanSpace ℝ ι)} {s R lam η K : ℝ}
    (hSU : S ⊆ U) (hs0 : 0 ≤ s) (hsR : s ≤ R) (hlam : 0 < lam) (hη : 0 ≤ η)
    (hK : (Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ ≤ K)
    (hf : MemLp F_fn (Fintype.card ι) (mu.restrict U))
    (hg : eLpNorm G (Fintype.card ι) (mu.restrict S) ≤
      eLpNorm F_fn (Fintype.card ι) (mu.restrict S) + ENNReal.ofReal η) :
    MemLp G (Fintype.card ι) (volume.restrict S) ∧
      s * (eLpNorm G (Fintype.card ι) (volume.restrict S)).toReal / lam ≤
        K * (R * ((eLpNorm F_fn (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) := by
  refine ⟨hf.restrict_of_isAddHaarMeasure_of_eLpNorm_le_add hSU ENNReal.ofReal_ne_top hg volume, ?_⟩
  have htr := toReal_eLpNorm_restrict_le_addHaarScalarFactor_rpow_mul_add G volume mu hSU hf
    ENNReal.ofReal_ne_top hg
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hη] at htr
  have hR : 0 ≤ R := hs0.trans hsR
  calc s * (eLpNorm G (Fintype.card ι) (volume.restrict S)).toReal / lam
      ≤ R * ((Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ *
          ((eLpNorm F_fn (Fintype.card ι) (mu.restrict U)).toReal + η)) / lam := by gcongr
    _ = (Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ *
          (R * ((eLpNorm F_fn (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) := by ring
    _ ≤ K * (R * ((eLpNorm F_fn (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) :=
        mul_le_mul_of_nonneg_right hK (by positivity)

/-- **The local maximum principle for strong subsolutions** (Gilbarg–Trudinger, Theorem 9.20,
without lower-order terms). Let `p > 0` and `κ` be given. There is a constant `C > 0`, depending
only on the dimension `n`, the additive Haar measure `mu`, `κ`, and `p`, with the following
property. Let `B(c, R) ⊆ Ω`, let `a` be uniformly elliptic on `B(c, R)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` almost everywhere in `B(c, R)`
for the weak Hessian, with `f⁻ ∈ Lⁿ(B(c, R))`. Then at every `x ∈ B(c, R / 2)`, the continuous
precise representative `ū` of `u` satisfies

`ū(x) ≤ C (R^(-n/p) ‖u⁺‖_{Lᵖ(B(c, R))} + R ‖f⁻‖_{Lⁿ(B(c, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp mu Ω (Fintype.card ι) 2),
        ball c R ⊆ Ω → UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂mu.restrict (ball c R),
          f x ≤ ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i) →
        MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (mu.restrict (ball c R)) →
        ∀ x ∈ ball c (R / 2),
          preciseRepresentative mu (Wkp.value 2 u) x ≤
            C * (R ^ (-(Fintype.card ι : ℝ) / p) *
              (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p)
                (mu.restrict (ball c R))).toReal +
              R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
                (mu.restrict (ball c R))).toReal) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  obtain ⟨C_M, hCM, HM⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := ι) (κ := κ) hp
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  set K_haar : ℝ := max (2 ^ (n / p) * α₀ ^ p⁻¹) (α₀ ^ n⁻¹)
  refine ⟨C_M * K_haar, mul_pos hCM (lt_max_of_lt_left (by positivity)), ?_⟩
  intro lam Lam R c Ω a f u hBΩ ha hLam hsub hf x hx
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by simp [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hup : MemLp (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R)) := by
    have hu_mem := W1p.memLp_value_of_convex_of_isBounded_of_finrank_le
      (by simp [finrank_euclideanSpace]) isOpen_ball (convex_ball c R) isBounded_ball hBΩ
      (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top (Wkp.lowerOrder 1 u)
    rw [Wkp.value_lowerOrder_one] at hu_mem
    exact hu_mem.posPart
  -- Pick `s` strictly between `max (2 dist x c) (R / 2)` and `R` so `closedBall c s ⊆ B(c, R) ⊆ Ω`
  -- and `x ∈ B(c, s / 2)`.
  obtain ⟨s, hs_gt, hsR⟩ :=
    exists_between (max_lt (by linarith [mem_ball.1 hx] : 2 * dist x c < R) (half_lt_self hR))
  have hsR2 : R / 2 < s := lt_of_le_of_lt (le_max_right _ _) hs_gt
  have hs0 : 0 < s := (half_pos hR).trans hsR2
  have hxs : x ∈ ball c (s / 2) := by
    rw [mem_ball]
    linarith [lt_of_le_of_lt (le_max_left (2 * dist x c) (R / 2)) hs_gt]
  have hcs_sub : closedBall c s ⊆ ball c R := closedBall_subset_ball hsR
  have hbs_sub : ball c s ⊆ ball c R := ball_subset_closedBall.trans hcs_sub
  set Np : ℝ :=
    (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R))).toReal
  set F : ℝ := (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (mu.restrict (ball c R))).toReal
  -- Approximate `u` from below within `η` on `closedBall c s` so `w⁺ ≤ ū⁺`, and let `η → 0`.
  refine le_of_forall_pos_mul_le (C := C_M * K_haar * (R / lam) + 1) fun η hη ↦ ?_
  obtain ⟨w, g, hw, hwK, hwg, hg_neg⟩ :=
    exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall c s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun y hy ↦ ha.abs_apply_le (hbs_sub hy))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub hsub) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hūx_le : ū x ≤ w x + η := by
    have hxK : x ∈ closedBall c s :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
    linarith [(hwK x hxK).1]
  obtain ⟨hg_vol, h2'⟩ := memLp_volume_and_mul_eLpNorm_div_le (K := K_haar) hbs_sub hs0.le hsR.le
    hlam hη.le (le_max_right _ _) hf hg_neg
  have hm := HM (ha.mono_set hbs_sub) hLam hw2.continuous.continuousOn hw2.contDiffOn hwg
    hg_vol x hxs
  rw [toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul (fun y ↦ (w y)⁺) (ENNReal.ofReal p)
    volume mu (ball c s), ENNReal.toReal_ofReal hp.le] at hm
  -- Bound `‖w⁺‖_{Lᵖ(B(c, s))} ≤ Np` via `w⁺ ≤ ū⁺`.
  have hw_lp : (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal ≤
      Np := by
    have hmono : eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s)) ≤
        eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R)) := by
      have hw_meas : AEStronglyMeasurable (fun y ↦ (w y)⁺) (mu.restrict (ball c s)) :=
        (continuous_posPart.comp hw2.continuous).aestronglyMeasurable
      refine le_trans (eLpNorm_mono_ae hw_meas ?_)
        (eLpNorm_mono_measure _ (Measure.restrict_mono hbs_sub le_rfl))
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae_restrict_of_subset (hbs_sub.trans hBΩ) hū] with y hy hyu
      rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_of_nonneg (posPart_nonneg _), hyu]
      exact posPart_mono (hwK y (ball_subset_closedBall hy)).2
    exact ENNReal.toReal_mono hup.eLpNorm_ne_top hmono
  have hs_rpow : s ^ (-n / p) ≤ 2 ^ (n / p) * R ^ (-n / p) := by
    rw [neg_div]
    exact Real.rpow_neg_le_mul_rpow_neg hR zero_le_two (by positivity) (by linarith)
  have h1 : s ^ (-n / p) * (α₀ ^ p⁻¹ *
      (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal) ≤
      K_haar * (R ^ (-n / p) * Np) := by
    calc s ^ (-n / p) * (α₀ ^ p⁻¹ *
            (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal)
        ≤ (2 ^ (n / p) * R ^ (-n / p)) * (α₀ ^ p⁻¹ * Np) := by gcongr
      _ = (2 ^ (n / p) * α₀ ^ p⁻¹) * (R ^ (-n / p) * Np) := by ring
      _ ≤ K_haar * (R ^ (-n / p) * Np) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have h2 : s / lam * (eLpNorm (fun y ↦ (g y)⁻) (Fintype.card ι)
      (volume.restrict (ball c s))).toReal ≤ K_haar * (R / lam * (F + η)) := by
    simpa only [F, div_mul_eq_mul_div, mul_div_assoc] using h2'
  calc ū x ≤ w x + η := hūx_le
    _ ≤ C_M * (K_haar * (R ^ (-n / p) * Np) + K_haar * (R / lam * (F + η))) + η := by
        linarith [hm, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCM.le]
    _ = C_M * K_haar * (R ^ (-n / p) * Np + R / lam * F) +
          η * (C_M * K_haar * (R / lam) + 1) := by ring

/-- **The weak Harnack inequality of Krylov and Safonov for strong supersolutions**
(Gilbarg–Trudinger, Theorem 9.22; Caffarelli–Cabré, Theorem 4.8). Let `κ` be given. There is an
exponent `p > 0`, depending only on the dimension `n` and on `κ`, such that for every `0 < θ < 1`
there is a constant `C > 0`, depending only on `n`, the additive Haar measure `mu`, `κ`, and `θ`,
with the following property. Let `B(x₀, R) ⊆ Ω`, let `a` be uniformly elliptic on `B(x₀, R)` with
constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost everywhere in `B(x₀, R)`
and satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere there for the weak Hessian, with
`f⁺ ∈ Lⁿ(B(x₀, R))`. Then at every `y ∈ B(x₀, θ R)`, the continuous precise representative `ū` of
`u` satisfies

`(θ R)^(-n/p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (ū(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_rpow_neg_mul_eLpNorm_le_mul_preciseRepresentative_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} :
    ∃ p : ℝ, 0 < p ∧ ∀ ⦃θ : ℝ⦄, 0 < θ → θ < 1 →
      ∃ C : ℝ, 0 < C ∧
        ∀ ⦃lam Lam R : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
          ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
          (u : Wkp mu Ω (Fintype.card ι) 2),
          ball x₀ R ⊆ Ω → UniformlyEllipticOn (ball x₀ R) a lam Lam → Lam ≤ κ * lam →
          (∀ᵐ x ∂mu.restrict (ball x₀ R), 0 ≤ Wkp.value 2 u x) →
          (∀ᵐ x ∂mu.restrict (ball x₀ R),
            ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
          MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (mu.restrict (ball x₀ R)) →
          ∀ y ∈ ball x₀ (θ * R),
            (θ * R) ^ (-(Fintype.card ι : ℝ) / p) *
              (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p)
                (mu.restrict (ball x₀ (θ * R)))).toReal ≤
            C * (preciseRepresentative mu (Wkp.value 2 u) y +
              R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
                (mu.restrict (ball x₀ R))).toReal / lam) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  obtain ⟨p, hp, HW'⟩ :=
    exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  refine ⟨p, hp, fun θ hθ0 hθ1 ↦ ?_⟩
  set θ' : ℝ := √θ
  have hθ'0 : 0 < θ' := Real.sqrt_pos.2 hθ0
  have hθ'1 : θ' < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hθ0.le hθ1
  obtain ⟨C_W, hCW, HW⟩ := HW' hθ'0 hθ'1
  set C_final : ℝ := (α₀ ^ p⁻¹)⁻¹ * C_W * max 1 (α₀ ^ n⁻¹)
  have hC_final : 0 < C_final := by positivity
  refine ⟨C_final, hC_final, ?_⟩
  intro lam Lam R x₀ Ω a f u hBΩ ha hLam hnn hsuper hf y hy
  have hθR : 0 < θ * R := pos_of_mem_ball hy
  have hR : 0 < R := (mul_pos_iff_of_pos_left hθ0).1 hθR
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by simp [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_nn : ∀ z ∈ ball x₀ R, 0 ≤ ū z :=
    Wkp.le_preciseRepresentative_of_ae_le (by simp [finrank_euclideanSpace]) u isOpen_ball hBΩ
      continuousOn_const hnn
  -- Work on `B(x₀, s)` with `s = √θ R < R`, so `closedBall x₀ s ⊆ B(x₀, R)` and `θ' s = θ R`.
  set s : ℝ := θ' * R
  have hs0 : 0 < s := mul_pos hθ'0 hR
  have hsR : s < R := mul_lt_of_lt_one_left hR hθ'1
  have hθ's : θ' * s = θ * R := by
    simp only [s, θ']
    rw [← mul_assoc, Real.mul_self_sqrt hθ0.le]
  have hcs_sub : closedBall x₀ s ⊆ ball x₀ R := closedBall_subset_ball hsR
  have hbs_sub : ball x₀ s ⊆ ball x₀ R := ball_subset_closedBall.trans hcs_sub
  set F : ℝ := (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (mu.restrict (ball x₀ R))).toReal
  -- Approximate `u` from above within `η` on `closedBall x₀ s` and let `η → 0`.
  refine le_of_forall_pos_mul_le (C := C_final * (1 + R / lam)) fun η hη ↦ ?_
  obtain ⟨w, g, hw, hwK, hwg, hg⟩ :=
    exists_contDiff_le_and_le_add_and_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall x₀ s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hbs_sub hz))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub hsuper) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hw_nn : ∀ z ∈ ball x₀ s, 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hwK z (ball_subset_closedBall hz)).1
  have hθR_sub_s : ball x₀ (θ * R) ⊆ ball x₀ s := by
    rw [← hθ's]
    exact ball_subset_ball (mul_le_of_le_one_left hs0.le hθ'1.le)
  have hwy_le : w y ≤ ū y + η := (hwK y (ball_subset_closedBall (hθR_sub_s hy))).2
  obtain ⟨hg_vol, h2⟩ := memLp_volume_and_mul_eLpNorm_div_le (K := max 1 (α₀ ^ n⁻¹)) hbs_sub hs0.le
    hsR.le hlam hη.le (le_max_right _ _) hf hg
  have hw_est := HW (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hwg hg_vol y (hθ's.symm ▸ hy)
  rw [hθ's, toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul w (ENNReal.ofReal p)
    volume mu (ball x₀ (θ * R)), ENNReal.toReal_ofReal hp.le] at hw_est
  have hw_mem : MemLp w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R))) :=
    hw2.continuous.continuousOn.memLp_restrict_of_subset_isCompact (isCompact_closedBall x₀ s)
      measurableSet_ball (hθR_sub_s.trans ball_subset_closedBall) _
  have hu_le_w : (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p)
      (mu.restrict (ball x₀ (θ * R)))).toReal ≤
      (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal := by
    refine ENNReal.toReal_mono hw_mem.eLpNorm_ne_top ?_
    refine eLpNorm_mono_ae ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hθR_sub_s.trans (hbs_sub.trans hBΩ)) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae_restrict_of_subset (hθR_sub_s.trans (hbs_sub.trans hBΩ)) hū] with z hz hzu
    have hznn := hū_nn z (hθR_sub_s.trans hbs_sub hz)
    have hzw := (hwK z (ball_subset_closedBall (hθR_sub_s hz))).1
    rw [hzu, Real.norm_of_nonneg hznn, Real.norm_of_nonneg (hznn.trans hzw)]
    exact hzw
  have h1 : w y ≤ max 1 (α₀ ^ n⁻¹) * (ū y + η) :=
    hwy_le.trans (le_mul_of_one_le_left
      (add_nonneg (hū_nn y (ball_subset_ball (mul_le_of_le_one_left hR.le hθ1.le) hy))
        hη.le) (le_max_left _ _))
  have hdiv : (θ * R) ^ (-n / p) *
      (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal ≤
      (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + η) + R * (F + η) / lam))) := by
    rw [le_inv_mul_iff₀ (by positivity)]
    calc α₀ ^ p⁻¹ * ((θ * R) ^ (-n / p) *
            (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal)
        = (θ * R) ^ (-n / p) * (α₀ ^ p⁻¹ *
            (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal) := by ring
      _ ≤ C_W * (w y + s * (eLpNorm (fun z ↦ (g z)⁺) (Fintype.card ι)
            (volume.restrict (ball x₀ s))).toReal / lam) := hw_est
      _ ≤ C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + η) + R * (F + η) / lam)) := by
            gcongr
            linarith [h1, h2]
  calc (θ * R) ^ (-n / p) *
        (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal
      ≤ (θ * R) ^ (-n / p) *
          (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal := by gcongr
    _ ≤ (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + η) + R * (F + η) / lam))) := hdiv
    _ = C_final * (ū y + R * F / lam) + η * (C_final * (1 + R / lam)) := by
        simp only [C_final]
        ring

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Theorem 9.22; Caffarelli–Cabré, Corollary 4.9), for functions in `W^{2,n}` satisfying the
two-sided inequality `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere. Let `κ` be given. There is a
constant `C > 0`, depending only on the dimension `n`, the additive Haar measure `mu`, and `κ`,
with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on `B(x₀, 2 r)`
with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost everywhere in
`B(x₀, 2 r)` with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere there and `f ∈ Lⁿ(B(x₀, 2 r))`. Then at
all `x, y ∈ B(x₀, r)`, the continuous precise representative `ū` of `u` satisfies

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp mu Ω (Fintype.card ι) 2),
        ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), 0 ≤ Wkp.value 2 u x) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
          preciseRepresentative mu (Wkp.value 2 u) x ≤
            C * (preciseRepresentative mu (Wkp.value 2 u) y +
              r * (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  set C : ℝ := C₀ * max 1 (α₀ ^ n⁻¹)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro lam Lam r x₀ Ω a f u hBΩ ha hLam hnn heq hf x hx y hy
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by simp [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_nn : ∀ z ∈ ball x₀ (2 * r), 0 ≤ ū z :=
    Wkp.le_preciseRepresentative_of_ae_le (by simp [finrank_euclideanSpace]) u isOpen_ball hBΩ
      continuousOn_const hnn
  -- Choose `r / 2 < s < r` with `x, y ∈ B(x₀, s)` so `closedBall x₀ (2 s) ⊆ B(x₀, 2 r) ⊆ Ω`.
  obtain ⟨s, -, hs_lt, hxs, hys⟩ :=
    TauCeti.exists_lt_mem_ball_of_mem_ball (half_lt_self (pos_of_mem_ball hx)) hx hy
  have hs0 : 0 < s := pos_of_mem_ball hxs
  have hcs_sub : closedBall x₀ (2 * s) ⊆ ball x₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  set F : ℝ := (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal
  refine le_of_forall_pos_mul_le (C := C * (1 + r / lam)) fun η hη ↦ ?_
  obtain ⟨w, g, hw, hwK, hwg, hg⟩ :=
    exists_contDiff_le_and_le_add_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall x₀ (2 * s)) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hbs_sub hz))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub heq) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hw_nn : ∀ z ∈ ball x₀ (2 * s), 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hwK z (ball_subset_closedBall hz)).1
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have hyK : y ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hys)
  obtain ⟨hg_vol, h2⟩ := memLp_volume_and_mul_eLpNorm_div_le (K := max 1 (α₀ ^ n⁻¹)) hbs_sub hs0.le
    hs_lt.le hlam hη.le (le_max_right _ _) hf hg
  have hw_har := H (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hwg hg_vol x hxs y hys
  have h1 : w y ≤ max 1 (α₀ ^ n⁻¹) * (ū y + η) :=
    (hwK y hyK).2.trans (le_mul_of_one_le_left
      (add_nonneg (hū_nn y (ball_subset_ball (by linarith) hy)) hη.le) (le_max_left _ _))
  calc ū x ≤ w x := (hwK x hxK).1
    _ ≤ C₀ * (max 1 (α₀ ^ n⁻¹) * (ū y + η) + max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam)) := by
        linarith [hw_har, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC₀.le]
    _ = C * (ū y + r * F / lam) + η * (C * (1 + r / lam)) := by
        simp only [C]
        ring

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Theorem 9.22), for solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `W^{2,n}`. Let `κ` be
given. There is a constant `C > 0`, depending only on the dimension `n`, the additive Haar measure
`mu`, and `κ`, with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost
everywhere in `B(x₀, 2 r)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere there and
`f ∈ Lⁿ(B(x₀, 2 r))`. Then at all `x, y ∈ B(x₀, r)`, the continuous precise representative `ū` of
`u` satisfies

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp mu Ω (Fintype.card ι) 2),
        ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), 0 ≤ Wkp.value 2 u x) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i = f x) →
        MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
          preciseRepresentative mu (Wkp.value 2 u) x ≤
            C * (preciseRepresentative mu (Wkp.value 2 u) y +
              r * (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ :=
    exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le
      (ι := ι) (mu := mu) (κ := κ)
  refine ⟨C, hC, fun lam Lam r x₀ Ω a f u hBΩ ha hLam hnn heq hf x hx y hy ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  refine H u hBΩ ha hLam hnn ?_ hf.norm x hx y hy
  filter_upwards [heq] with z hz
  rw [hz, Real.norm_eq_abs]

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24; Caffarelli–Cabré, Proposition 4.10), for functions in `W^{2,n}` satisfying the
two-sided inequality `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere. Let `κ` be given. There are
`0 < α ≤ 1` and `C > 0`, depending only on the dimension `n`, the additive Haar measure `mu`, and
`κ`, with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere in `B(x₀, 2 r)`, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the
continuous precise representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp mu Ω (Fintype.card ι) 2),
        ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
          |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x) →
        MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (mu.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (preciseRepresentative mu (Wkp.value 2 u)) (ball x₀ r) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  set κ' : ℝ := max κ 1
  have hκ' : 0 < κ' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨α, C₀, hα0, hα1, hC₀, H⟩ :=
    exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) hκ'
  have hα0' : (0 : ℝ) < α := NNReal.coe_pos.2 hα0
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  set C : ℝ := 2 * C₀ * max 1 (α₀ ^ n⁻¹)
  have hC : 0 < C := by positivity
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro lam Lam r M x₀ Ω a f u hBΩ ha hLam hM heq hf
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  have hr : 0 < r := pos_of_mem_ball hx
  have hlam : 0 < lam := ha.pos
  have hLam' : Lam ≤ κ' * lam :=
    hLam.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le)
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω :=
    Wkp.continuousOn_preciseRepresentative (by simp [finrank_euclideanSpace]) u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_abs : ∀ z ∈ ball x₀ (2 * r), |ū z| ≤ M := fun z hz ↦
    Wkp.abs_preciseRepresentative_le (by simp [finrank_euclideanSpace]) u isOpen_ball hBΩ hM hz
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hū_abs x (ball_subset_ball (by linarith) hx))
  -- Choose `r / 2 < s < r` with `x, y ∈ B(x₀, s)` so `closedBall x₀ (2 s) ⊆ B(x₀, 2 r) ⊆ Ω`.
  obtain ⟨s, hs_r2, hs_lt, hxs, hys⟩ :=
    TauCeti.exists_lt_mem_ball_of_mem_ball (half_lt_self hr) hx hy
  have hs0 : 0 < s := pos_of_mem_ball hxs
  have hcs_sub : closedBall x₀ (2 * s) ⊆ ball x₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  set F : ℝ := (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal
  have hs_rpow : s ^ (-(α : ℝ)) ≤ 2 * r ^ (-(α : ℝ)) := by
    calc s ^ (-(α : ℝ)) ≤ 2 ^ (α : ℝ) * r ^ (-(α : ℝ)) :=
          Real.rpow_neg_le_mul_rpow_neg hr zero_le_two hα0'.le (by linarith)
      _ ≤ 2 ^ (1 : ℝ) * r ^ (-(α : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two hα1')
            (by positivity)
      _ = 2 * r ^ (-(α : ℝ)) := by rw [Real.rpow_one]
  refine le_of_forall_pos_mul_le
    (C := C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) fun η hη ↦ ?_
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall x₀ (2 * s)) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hbs_sub hz))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub heq) hη
  have hv2 : ContDiff ℝ 2 v := contDiff_infty.1 hv 2
  have hv_abs : ∀ z ∈ ball x₀ (2 * s), |v z| ≤ M + η := fun z hz ↦ by
    have htri := abs_add_le (ū z) (v z - ū z)
    rw [add_sub_cancel] at htri
    exact htri.trans (add_le_add (hū_abs z (hbs_sub hz)) (hvK z (ball_subset_closedBall hz)))
  obtain ⟨hg_vol, h2⟩ := memLp_volume_and_mul_eLpNorm_div_le (K := max 1 (α₀ ^ n⁻¹)) hbs_sub hs0.le
    hs_lt.le hlam hη.le (le_max_right _ _) hf hg
  have hhold := (H hs0 (ha.mono_set hbs_sub) hLam' hv2.contDiffOn hv_abs hvg hg_vol).dist_le hxs hys
  have hv_dist : dist (v x) (v y) ≤
      C₀ * s ^ (-(α : ℝ)) * (M + η + s * (eLpNorm g (Fintype.card ι)
        (volume.restrict (ball x₀ (2 * s)))).toReal / lam) * dist x y ^ (α : ℝ) :=
    hhold.trans_eq (by rw [Real.coe_toNNReal _ (by positivity)])
  have h1 : M + η ≤ max 1 (α₀ ^ n⁻¹) * (M + η) :=
    le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have hyK : y ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hys)
  have hdist_u : dist (ū x) (ū y) ≤ dist (v x) (v y) + 2 * η := by
    have hdx : dist (ū x) (v x) ≤ η := by
      rw [dist_comm, Real.dist_eq]
      exact hvK x hxK
    have hdy : dist (v y) (ū y) ≤ η := by
      rw [Real.dist_eq]
      exact hvK y hyK
    linarith [dist_triangle4 (ū x) (v x) (v y) (ū y)]
  have hv_bound : dist (v x) (v y) ≤
      C * r ^ (-(α : ℝ)) * (M + η + r * (F + η) / lam) * dist x y ^ (α : ℝ) := by
    calc dist (v x) (v y)
        ≤ C₀ * s ^ (-(α : ℝ)) * (max 1 (α₀ ^ n⁻¹) * (M + η) +
            max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam)) * dist x y ^ (α : ℝ) :=
          hv_dist.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)) (by positivity))
      _ ≤ C₀ * (2 * r ^ (-(α : ℝ))) * (max 1 (α₀ ^ n⁻¹) * (M + η + r * (F + η) / lam)) *
            dist x y ^ (α : ℝ) := by
          have : max 1 (α₀ ^ n⁻¹) * (M + η) + max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam) =
              max 1 (α₀ ^ n⁻¹) * (M + η + r * (F + η) / lam) := by ring
          rw [this]
          gcongr
      _ = C * r ^ (-(α : ℝ)) * (M + η + r * (F + η) / lam) * dist x y ^ (α : ℝ) := by
          simp only [C]
          ring
  calc dist (ū x) (ū y) ≤ dist (v x) (v y) + 2 * η := hdist_u
    _ ≤ C * r ^ (-(α : ℝ)) * (M + η + r * (F + η) / lam) * dist x y ^ (α : ℝ) + 2 * η := by
        gcongr
    _ = C * r ^ (-(α : ℝ)) * (M + r * F / lam) * dist x y ^ (α : ℝ) +
          η * (C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) := by ring

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24), for solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `W^{2,n}`. Let `κ` be
given. There are `0 < α ≤ 1` and `C > 0`, depending only on the dimension `n`, the additive Haar
measure `mu`, and `κ`, with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly
elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M`
and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `B(x₀, 2 r)`, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the
continuous precise representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp mu Ω (Fintype.card ι) 2),
        ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i = f x) →
        MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (mu.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
          (preciseRepresentative mu (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, C, hα0, hα1, hC, H⟩ :=
    exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le
      (ι := ι) (mu := mu) (κ := κ)
  refine ⟨α, C, hα0, hα1, hC, fun lam Lam r M x₀ Ω a f u hBΩ ha hLam hM heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  refine H u hBΩ ha hLam hM ?_ hf.norm
  filter_upwards [heq] with z hz
  rw [hz, Real.norm_eq_abs]

end StrongSolutions

end PDE

end TauCeti
