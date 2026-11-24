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
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
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
  transfers both estimates directly from their classical counterparts as `η → 0`. For `volume`,
  `u` itself satisfies `u(x) ≤ C (u(y) + r ‖f‖ / λ)` for almost every `x` and almost every `y` in
  `B(x₀, r)` (`TauCeti.PDE.exists_ae_value_le_mul_add_of_sum_mul_iteratedGradient_eq`).

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
* `TauCeti.PDE.exists_ae_value_le_mul_add_of_sum_mul_iteratedGradient_eq` and
  `TauCeti.PDE.exists_ae_value_le_mul_add_of_abs_sum_mul_iteratedGradient_le`: the same Harnack
  inequalities for `u` itself (with respect to `volume`), at almost every pair of points.
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
  have h0 := hg.continuousWithinAt.le_of_forall_gt_le h
  dsimp only [Function.comp_apply] at h0
  rwa [mul_zero, add_zero, div_one] at h0

omit [DecidableEq ι] in
/-- In dimension `n ≥ 1`, the exponent `n` of `W^{2,n}` exceeds half the dimension, so the precise
representative of a `W^{2,n}` function is continuous
(`TauCeti.Wkp.continuousOn_preciseRepresentative`). -/
private theorem finrank_lt_two_mul_card [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] :
    (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞) < 2 * Fintype.card ι := by
  have h : 1 ≤ Fintype.card ι := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι)
  rw [finrank_euclideanSpace]
  exact_mod_cast (by omega : Fintype.card ι < 2 * Fintype.card ι)

/-- Entrywise `|a x i j| ≤ Lam` a.e. on a sub-ball `B(c, s) ⊆ B(x₀, R)` from uniform ellipticity
on `B(x₀, R)`. -/
private theorem ae_abs_apply_le_ball_of_uniformlyEllipticOn
    {mu : Measure (EuclideanSpace ℝ ι)} {x₀ c : EuclideanSpace ℝ ι} {R s lam Lam : ℝ}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (ha : UniformlyEllipticOn (ball x₀ R) a lam Lam)
    (hs : ball c s ⊆ ball x₀ R) :
    ∀ᵐ x ∂mu.restrict (ball c s), ∀ i j, |a x i j| ≤ Lam :=
  (ae_restrict_mem measurableSet_ball).mono fun _ hz ↦ ha.abs_apply_le (hs hz)

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
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
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
    rw [ENNReal.ofReal_div_of_pos hR0,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hR0).ne')
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
      (ae_abs_apply_le_ball_of_uniformlyEllipticOn ha Subset.rfl) hsuper
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

omit [DecidableEq ι] in
/-- Transfer `Lⁿ` integrability and a scaled `s * ‖g‖_{Lⁿ(S)} / λ ≤ K * (R * (‖f‖_{Lⁿ(U)} + η) / λ)`
bound from an additive Haar measure `mu` on `U` to `volume` on `S ⊆ U`. -/
private theorem memLp_and_mul_eLpNorm_div_le_of_isAddHaarMeasure
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {f g : EuclideanSpace ℝ ι → ℝ} {S U : Set (EuclideanSpace ℝ ι)}
    (hSU : S ⊆ U) (hf : MemLp f (Fintype.card ι) (mu.restrict U)) {η s R lam K : ℝ}
    (hη : 0 ≤ η) (hs : 0 ≤ s) (hsR : s ≤ R) (hlam : 0 < lam)
    (hK : (Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ ≤ K)
    (hg : eLpNorm g (Fintype.card ι) (mu.restrict S) ≤
      eLpNorm f (Fintype.card ι) (mu.restrict S) + ENNReal.ofReal η) :
    MemLp g (Fintype.card ι) (volume.restrict S) ∧
      s * (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal / lam ≤
        K * (R * ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) := by
  have hle : eLpNorm g (Fintype.card ι) (mu.restrict S) ≤
      eLpNorm f (Fintype.card ι) (mu.restrict U) + ENNReal.ofReal η :=
    hg.trans (add_le_add_left (eLpNorm_mono_measure _ (Measure.restrict_mono_set mu hSU)) _)
  have hfin : eLpNorm f (Fintype.card ι) (mu.restrict U) + ENNReal.ofReal η < ∞ :=
    ENNReal.add_lt_top.2 ⟨hf.eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩
  refine ⟨(memLp_iff.2 (hle.trans_lt hfin)).restrict_of_isAddHaarMeasure volume, ?_⟩
  have hmu_le : (eLpNorm g (Fintype.card ι) (mu.restrict S)).toReal ≤
      (eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η := by
    simpa only [ENNReal.toReal_ofReal hη] using
      (ENNReal.toReal_mono hfin.ne hle).trans_eq
        (ENNReal.toReal_add hf.eLpNorm_ne_top ENNReal.ofReal_ne_top)
  have htr : (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal ≤
      (Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ *
        ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η) := by
    rw [toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul g (Fintype.card ι) volume mu S,
      ENNReal.toReal_natCast]
    exact mul_le_mul_of_nonneg_left hmu_le (by positivity)
  have htr2 : (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal ≤
      K * ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η) :=
    htr.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  calc s * (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal / lam
      ≤ R * (K * ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η)) / lam :=
        div_le_div_of_nonneg_right
          (mul_le_mul hsR htr2 ENNReal.toReal_nonneg (hs.trans hsR)) hlam.le
    _ = K * (R * ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) := by ring

omit [DecidableEq ι] in
/-- Combine `A' ≤ A + η` with the Haar `Lⁿ` transfer on `S ⊆ U`, absorbing both into
`max 1 (α₀ ^ n⁻¹) * (A + R * ‖f‖_{Lⁿ(U)} / λ + η * (1 + R / λ))`. -/
private theorem memLp_and_add_mul_eLpNorm_div_le_of_isAddHaarMeasure
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {f g : EuclideanSpace ℝ ι → ℝ} {S U : Set (EuclideanSpace ℝ ι)}
    (hSU : S ⊆ U) (hf : MemLp f (Fintype.card ι) (mu.restrict U))
    {A A' η s R lam : ℝ} (hA : 0 ≤ A) (hA' : A' ≤ A + η) (hη : 0 ≤ η)
    (hs : 0 ≤ s) (hsR : s ≤ R) (hlam : 0 < lam)
    (hg : eLpNorm g (Fintype.card ι) (mu.restrict S) ≤
      eLpNorm f (Fintype.card ι) (mu.restrict S) + ENNReal.ofReal η) :
    MemLp g (Fintype.card ι) (volume.restrict S) ∧
      A' + s * (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal / lam ≤
        max 1 ((Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹) *
          (A + R * (eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal / lam +
            η * (1 + R / lam)) := by
  set K : ℝ := max 1 ((Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹)
  obtain ⟨hg_vol, h2⟩ := memLp_and_mul_eLpNorm_div_le_of_isAddHaarMeasure hSU hf hη hs hsR hlam
    (le_max_right 1 _) hg
  have h1 : A' ≤ K * (A + η) :=
    hA'.trans (le_mul_of_one_le_left (add_nonneg hA hη) (le_max_left _ _))
  refine ⟨hg_vol, ?_⟩
  calc A' + s * (eLpNorm g (Fintype.card ι) (volume.restrict S)).toReal / lam
      ≤ K * (A + η) +
          K * (R * ((eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal + η) / lam) :=
        add_le_add h1 h2
    _ = K * (A + R * (eLpNorm f (Fintype.card ι) (mu.restrict U)).toReal / lam +
          η * (1 + R / lam)) := by ring

omit [DecidableEq ι] in
/-- If a continuous function `w` satisfies `w ≤ ū` on `B(c, s) ⊆ B(c, R)`, then
`‖w⁺‖_{Lᵖ(B(c, s))} ≤ ‖u⁺‖_{Lᵖ(B(c, R))}`. -/
private theorem toReal_eLpNorm_posPart_ball_le_of_le [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {c : EuclideanSpace ℝ ι} {s R p : ℝ} {Ω : Opens (EuclideanSpace ℝ ι)}
    (u : Wkp mu Ω (Fintype.card ι) 2) (hBΩ : ball c R ⊆ Ω) (hbs_sub : ball c s ⊆ ball c R)
    {w : EuclideanSpace ℝ ι → ℝ} (hw : Continuous w)
    (hw_le : ∀ y ∈ ball c s, w y ≤ preciseRepresentative mu (Wkp.value 2 u) y)
    (hup : MemLp (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R))) :
    (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal ≤
      (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p)
        (mu.restrict (ball c R))).toReal := by
  refine toReal_eLpNorm_restrict_mono_ae hbs_sub
    (continuous_posPart.comp hw).aestronglyMeasurable hup.eLpNorm_ne_top ?_
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae_restrict_of_subset (hbs_sub.trans hBΩ)
      (Wkp.ae_eq_preciseRepresentative 2 u)] with y hy hyu
  rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_of_nonneg (posPart_nonneg _), hyu]
  exact posPart_mono (hw_le y hy)

omit [DecidableEq ι] in
/-- If a continuous function `w` satisfies `0 ≤ ū ≤ w` on `B(x₀, r) ⊆ Ω`, then
`‖u‖_{Lᵖ(B(x₀, r))} ≤ ‖w‖_{Lᵖ(B(x₀, r))}`. -/
private theorem toReal_eLpNorm_value_ball_le_of_le [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {x₀ : EuclideanSpace ℝ ι} {r p : ℝ} {Ω : Opens (EuclideanSpace ℝ ι)}
    (u : Wkp mu Ω (Fintype.card ι) 2) (hsub : ball x₀ r ⊆ Ω)
    {w : EuclideanSpace ℝ ι → ℝ} (hw : Continuous w)
    (hū_nn : ∀ z ∈ ball x₀ r, 0 ≤ preciseRepresentative mu (Wkp.value 2 u) z)
    (hū_le : ∀ z ∈ ball x₀ r, preciseRepresentative mu (Wkp.value 2 u) z ≤ w z) :
    (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p) (mu.restrict (ball x₀ r))).toReal ≤
      (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ r))).toReal := by
  have hw_mem : MemLp w (ENNReal.ofReal p) (mu.restrict (ball x₀ r)) :=
    hw.continuousOn.memLp_restrict_of_subset_isCompact (isCompact_closedBall x₀ r)
      measurableSet_ball ball_subset_closedBall (ENNReal.ofReal p)
  refine toReal_eLpNorm_restrict_mono_ae Subset.rfl
    ((Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hsub le_rfl))
    hw_mem.eLpNorm_ne_top ?_
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae_restrict_of_subset hsub (Wkp.ae_eq_preciseRepresentative 2 u)] with z hz hzu
  have hznn := hū_nn z hz
  have hzw := hū_le z hz
  rw [hzu, Real.norm_of_nonneg hznn, Real.norm_of_nonneg (hznn.trans hzw)]
  exact hzw

omit [DecidableEq ι] in
/-- Rescale the `s^(-n/p)` ball factor and absorb the `η` approximation error in the local maximum
principle on `B(c, s) ⊆ B(c, R)` with `R / 2 < s`. -/
private theorem lmp_absorb_subball {n p α₀ K C_M lam s R Nw Np G F ūx wx η : ℝ}
    (hn : 0 ≤ n) (hp : 0 < p) (hα₀ : 0 ≤ α₀) (hCM : 0 ≤ C_M) (hR : 0 < R) (hsR2 : R / 2 < s)
    (hK1 : 2 ^ (n / p) * α₀ ^ p⁻¹ ≤ K) (hNw : 0 ≤ Nw) (hNp : Nw ≤ Np) (hū : ūx ≤ wx + η)
    (hm : wx ≤ C_M * (s ^ (-n / p) * (α₀ ^ p⁻¹ * Nw) + s / lam * G))
    (h2 : s / lam * G ≤ K * (R / lam * (F + η))) :
    ūx ≤ C_M * K * (R ^ (-n / p) * Np + R / lam * F) + η * (C_M * K * (R / lam) + 1) := by
  have hNp0 : 0 ≤ Np := hNw.trans hNp
  have hs_rpow : s ^ (-n / p) ≤ 2 ^ (n / p) * R ^ (-n / p) := by
    rw [neg_div]
    exact Real.rpow_neg_le_mul_rpow_neg hR zero_le_two (by positivity) (by linarith)
  have h1 : s ^ (-n / p) * (α₀ ^ p⁻¹ * Nw) ≤ K * (R ^ (-n / p) * Np) := by
    calc s ^ (-n / p) * (α₀ ^ p⁻¹ * Nw)
        ≤ (2 ^ (n / p) * R ^ (-n / p)) * (α₀ ^ p⁻¹ * Np) := by gcongr
      _ = (2 ^ (n / p) * α₀ ^ p⁻¹) * (R ^ (-n / p) * Np) := by ring
      _ ≤ K * (R ^ (-n / p) * Np) := mul_le_mul_of_nonneg_right hK1 (by positivity)
  calc ūx ≤ wx + η := hū
    _ ≤ C_M * (K * (R ^ (-n / p) * Np) + K * (R / lam * (F + η))) + η := by
        linarith [hm, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCM]
    _ = C_M * K * (R ^ (-n / p) * Np + R / lam * F) + η * (C_M * K * (R / lam) + 1) := by ring

/-- The `η`-approximation step for the strong local maximum principle on a concentric sub-ball
`closedBall c s ⊆ B(c, R)` containing `x ∈ B(c, s / 2)`. -/
private theorem preciseRepresentative_le_add_mul_of_subball
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {κ p C_M K_haar lam Lam R s : ℝ} {c x : EuclideanSpace ℝ ι} {Ω : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (u : Wkp mu Ω (Fintype.card ι) 2) (hp : 0 < p) (hCM : 0 < C_M)
    (HM : ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
      ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
      (∀ x ∈ ball c R, f x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (volume.restrict (ball c R)) →
      ∀ x ∈ ball c (R / 2), u x ≤ C_M * (R ^ (-(Fintype.card ι : ℝ) / p) *
        (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
        R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
          (volume.restrict (ball c R))).toReal))
    (hBΩ : ball c R ⊆ Ω) (ha : UniformlyEllipticOn (ball c R) a lam Lam) (hLam : Lam ≤ κ * lam)
    (hsub : ∀ᵐ x ∂mu.restrict (ball c R),
      f x ≤ ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i)
    (hf : MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (mu.restrict (ball c R)))
    (hup : MemLp (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R)))
    (hR : 0 < R) (hsR2 : R / 2 < s) (hsR : s < R) (hxs : x ∈ ball c (s / 2)) {η : ℝ}
    (hη : 0 < η)
    (hK_haar : K_haar = max (2 ^ ((Fintype.card ι : ℝ) / p) *
      (Measure.addHaarScalarFactor volume mu : ℝ) ^ p⁻¹)
      ((Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹)) :
    preciseRepresentative mu (Wkp.value 2 u) x ≤
      C_M * K_haar * (R ^ (-(Fintype.card ι : ℝ) / p) *
        (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R))).toReal +
        R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (mu.restrict (ball c R))).toReal) +
      η * (C_M * K_haar * (R / lam) + 1) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  have hs0 : 0 < s := (half_pos hR).trans hsR2
  have hlam : 0 < lam := ha.pos
  have hcs_sub : closedBall c s ⊆ ball c R := closedBall_subset_ball hsR
  have hbs_sub : ball c s ⊆ ball c R := ball_subset_closedBall.trans hcs_sub
  -- Mollify `u` from below on `closedBall c s`.
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  obtain ⟨w, g, hw, hwK, hwg, hg_neg⟩ :=
    exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u
      (Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u)
      (Wkp.ae_eq_preciseRepresentative 2 u)
      (isCompact_closedBall c s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      (ae_abs_apply_le_ball_of_uniformlyEllipticOn ha hbs_sub)
      (ae_restrict_of_ae_restrict_of_subset hbs_sub hsub) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hūx_le : ū x ≤ w x + η := by
    have hxK : x ∈ closedBall c s :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
    linarith [(hwK x hxK).1]
  -- Transfer `g⁻` to `volume` and apply the classical local maximum principle to `w`.
  obtain ⟨hg_vol, h2⟩ := memLp_and_mul_eLpNorm_div_le_of_isAddHaarMeasure hbs_sub hf hη.le hs0.le
    hsR.le hlam (hK_haar ▸ le_max_right (2 ^ (n / p) * α₀ ^ p⁻¹) (α₀ ^ n⁻¹)) hg_neg
  have h2' : s / lam * (eLpNorm (fun y ↦ (g y)⁻) (Fintype.card ι)
      (volume.restrict (ball c s))).toReal ≤ K_haar * (R / lam *
        ((eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (mu.restrict (ball c R))).toReal + η)) := by
    rwa [div_mul_eq_mul_div, div_mul_eq_mul_div]
  have hm := HM (ha.mono_set hbs_sub) hLam hw2.continuous.continuousOn hw2.contDiffOn hwg
    hg_vol x hxs
  rw [toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul (fun y ↦ (w y)⁺) (ENNReal.ofReal p)
    volume mu (ball c s), ENNReal.toReal_ofReal hp.le] at hm
  -- Compare `‖w⁺‖_{Lᵖ(B(c, s))} ≤ ‖u⁺‖_{Lᵖ(B(c, R))}` and absorb `η`.
  have hw_lp := toReal_eLpNorm_posPart_ball_le_of_le u hBΩ hbs_sub hw2.continuous
    (fun y hy ↦ (hwK y (ball_subset_closedBall hy)).2) hup
  exact lmp_absorb_subball (Nat.cast_nonneg _) hp hα₀.le hCM.le hR hsR2
    (hK_haar ▸ le_max_left _ _) ENNReal.toReal_nonneg hw_lp hūx_le hm h2'

/-- **The local maximum principle for strong subsolutions** (Gilbarg–Trudinger, Theorem 9.20,
without lower-order terms). Let `κ` and `p > 0` be given. For every additive Haar measure `mu`
there is a constant `C > 0`, depending only on the dimension `n`, `mu`, `κ`, and `p`, with the
following property. Let `B(c, R) ⊆ Ω`, let `a` be uniformly elliptic on `B(c, R)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` almost everywhere in `B(c, R)`
for the weak Hessian, with `f⁻ ∈ Lⁿ(B(c, R))`. Then at every `x ∈ B(c, R / 2)`, the continuous
precise representative `ū` of `u` satisfies

`ū(x) ≤ C (R^(-n/p) ‖u⁺‖_{Lᵖ(B(c, R))} + R ‖f⁻‖_{Lⁿ(B(c, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) {p : ℝ} (hp : 0 < p) :
    ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure],
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
  intro mu _
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  set K_haar : ℝ := max (2 ^ ((Fintype.card ι : ℝ) / p) * α₀ ^ p⁻¹)
    (α₀ ^ (Fintype.card ι : ℝ)⁻¹)
  refine ⟨C_M * K_haar, mul_pos hCM (lt_max_of_lt_left (by positivity)), ?_⟩
  intro lam Lam R c Ω a f u hBΩ ha hLam hsub hf x hx
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hup := (Wkp.memLp_value_of_convex_of_isBounded_of_finrank_le (by norm_num)
    (by rw [finrank_euclideanSpace]) isOpen_ball (convex_ball c R) isBounded_ball hBΩ
    (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top u).posPart
  obtain ⟨s, hs_gt, hsR⟩ :=
    exists_between (max_lt (by linarith [mem_ball.1 hx] : 2 * dist x c < R) (half_lt_self hR))
  have hsR2 : R / 2 < s := lt_of_le_of_lt (le_max_right _ _) hs_gt
  have hxs : x ∈ ball c (s / 2) := by
    rw [mem_ball]
    linarith [lt_of_le_of_lt (le_max_left (2 * dist x c) (R / 2)) hs_gt]
  exact le_of_forall_pos_mul_le (C := C_M * K_haar * (R / lam) + 1) fun η hη ↦
    preciseRepresentative_le_add_mul_of_subball u hp hCM HM hBΩ ha hLam hsub hf hup hR hsR2 hsR
      hxs hη rfl

omit [DecidableEq ι] in
/-- Divide the Haar factor `α₀ ^ p⁻¹` out of the `Lᵖ` estimate on `B(x₀, θ R)` and absorb the
`η` error term in the weak Harnack inequality. -/
private theorem weakHarnack_absorb_subball {n p α₀ C_W C_final lam s R θ Nu Nw wy ūy G F η : ℝ}
    (hα₀ : 0 < α₀) (hCW : 0 ≤ C_W) (hθR : 0 ≤ θ * R) (hNu : Nu ≤ Nw)
    (hw_est : (θ * R) ^ (-n / p) * (α₀ ^ p⁻¹ * Nw) ≤ C_W * (wy + s * G / lam))
    (h12 : wy + s * G / lam ≤ max 1 (α₀ ^ n⁻¹) * (ūy + R * F / lam + η * (1 + R / lam)))
    (hC_final : C_final = (α₀ ^ p⁻¹)⁻¹ * C_W * max 1 (α₀ ^ n⁻¹)) :
    (θ * R) ^ (-n / p) * Nu ≤ C_final * (ūy + R * F / lam) + η * (C_final * (1 + R / lam)) := by
  have hdiv : (θ * R) ^ (-n / p) * Nw ≤
      (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * (ūy + R * F / lam + η * (1 + R / lam)))) := by
    rw [le_inv_mul_iff₀ (by positivity)]
    calc α₀ ^ p⁻¹ * ((θ * R) ^ (-n / p) * Nw)
        = (θ * R) ^ (-n / p) * (α₀ ^ p⁻¹ * Nw) := by ring
      _ ≤ C_W * (wy + s * G / lam) := hw_est
      _ ≤ C_W * (max 1 (α₀ ^ n⁻¹) * (ūy + R * F / lam + η * (1 + R / lam))) := by gcongr
  calc (θ * R) ^ (-n / p) * Nu ≤ (θ * R) ^ (-n / p) * Nw := by gcongr
    _ ≤ (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * (ūy + R * F / lam + η * (1 + R / lam)))) := hdiv
    _ = C_final * (ūy + R * F / lam) + η * (C_final * (1 + R / lam)) := by
        rw [hC_final]; ring

/-- The `η`-approximation step for the strong weak Harnack inequality on `closedBall x₀ (√θ R)`. -/
private theorem rpow_neg_mul_eLpNorm_le_add_mul_of_subball
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {κ p C_W C_final θ lam Lam R : ℝ} {x₀ y : EuclideanSpace ℝ ι}
    {Ω : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} (u : Wkp mu Ω (Fintype.card ι) 2) (hp : 0 < p) (hCW : 0 < C_W)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (HW : ∀ ⦃lam Lam R : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
      UniformlyEllipticOn (ball x₀ R) a lam Lam → Lam ≤ κ * lam →
      ContDiffOn ℝ 2 u (ball x₀ R) → (∀ x ∈ ball x₀ R, 0 ≤ u x) →
      (∀ x ∈ ball x₀ R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
      MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)) →
      ∀ y ∈ ball x₀ (√θ * R),
        (√θ * R) ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (√θ * R)))).toReal ≤
        C_W * (u y + R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball x₀ R))).toReal / lam))
    (hBΩ : ball x₀ R ⊆ Ω) (ha : UniformlyEllipticOn (ball x₀ R) a lam Lam) (hLam : Lam ≤ κ * lam)
    (hnn : ∀ᵐ x ∂mu.restrict (ball x₀ R), 0 ≤ Wkp.value 2 u x)
    (hsuper : ∀ᵐ x ∂mu.restrict (ball x₀ R),
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    (hf : MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (mu.restrict (ball x₀ R)))
    (hy : y ∈ ball x₀ (θ * R)) {η : ℝ} (hη : 0 < η)
    (hC_final : C_final = ((Measure.addHaarScalarFactor volume mu : ℝ) ^ p⁻¹)⁻¹ * C_W *
      max 1 ((Measure.addHaarScalarFactor volume mu : ℝ) ^ (Fintype.card ι : ℝ)⁻¹)) :
    (θ * R) ^ (-(Fintype.card ι : ℝ) / p) *
      (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal ≤
      C_final * (preciseRepresentative mu (Wkp.value 2 u) y +
        R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (mu.restrict (ball x₀ R))).toReal / lam) +
      η * (C_final * (1 + R / lam)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  have hR : 0 < R := (mul_pos_iff_of_pos_left hθ0).1 (pos_of_mem_ball hy)
  have hlam : 0 < lam := ha.pos
  -- Set up `s = √θ * R` so `θ * R = √θ * s` and `closedBall x₀ s ⊆ B(x₀, R)`.
  have hθ'0 : 0 < √θ := Real.sqrt_pos.2 hθ0
  have hθ'1 : √θ < 1 := Real.sqrt_one ▸ Real.sqrt_lt_sqrt hθ0.le hθ1
  set s : ℝ := √θ * R
  have hs0 : 0 < s := mul_pos hθ'0 hR
  have hsR : s < R := mul_lt_of_lt_one_left hR hθ'1
  have hθ's : √θ * s = θ * R := by simp only [s]; rw [← mul_assoc, Real.mul_self_sqrt hθ0.le]
  have hcs_sub : closedBall x₀ s ⊆ ball x₀ R := closedBall_subset_ball hsR
  have hbs_sub : ball x₀ s ⊆ ball x₀ R := ball_subset_closedBall.trans hcs_sub
  -- Mollify `u` from above on `closedBall x₀ s`.
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hū_nn : ∀ z ∈ ball x₀ R, 0 ≤ ū z := fun z hz ↦
    Wkp.preciseRepresentative_nonneg (finrank_lt_two_mul_card (ι := ι)) u isOpen_ball hBΩ hnn hz
  obtain ⟨w, g, hw, hwK, hwg, hg⟩ :=
    exists_contDiff_le_and_le_add_and_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u
      (Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u)
      (Wkp.ae_eq_preciseRepresentative 2 u)
      (isCompact_closedBall x₀ s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      (ae_abs_apply_le_ball_of_uniformlyEllipticOn ha hbs_sub)
      (ae_restrict_of_ae_restrict_of_subset hbs_sub hsuper) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hw_nn : ∀ z ∈ ball x₀ s, 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hwK z (ball_subset_closedBall hz)).1
  -- Transfer `g⁺` to `volume` and apply the classical weak Harnack inequality to `w`.
  have hθR_sub_s : ball x₀ (θ * R) ⊆ ball x₀ s :=
    hθ's ▸ ball_subset_ball (mul_le_of_le_one_left hs0.le hθ'1.le)
  have hyR : y ∈ ball x₀ R := ball_subset_ball (mul_le_of_le_one_left hR.le hθ1.le) hy
  obtain ⟨hg_vol, h12⟩ := memLp_and_add_mul_eLpNorm_div_le_of_isAddHaarMeasure hbs_sub hf
    (hū_nn y hyR) (hwK y (ball_subset_closedBall (hθR_sub_s hy))).2 hη.le hs0.le hsR.le hlam hg
  have hw_est := HW (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hwg hg_vol y (hθ's.symm ▸ hy)
  rw [hθ's, toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul w (ENNReal.ofReal p)
    volume mu (ball x₀ (θ * R)), ENNReal.toReal_ofReal hp.le] at hw_est
  -- Compare `‖u‖_{Lᵖ(B(x₀, θ R))} ≤ ‖w‖_{Lᵖ(B(x₀, θ R))}`, divide out `α₀ ^ p⁻¹`, and absorb `η`.
  have hu_le_w := toReal_eLpNorm_value_ball_le_of_le (p := p) u
    (hθR_sub_s.trans (hbs_sub.trans hBΩ)) hw2.continuous
    (fun z hz ↦ hū_nn z (hθR_sub_s.trans hbs_sub hz))
    (fun z hz ↦ (hwK z (ball_subset_closedBall (hθR_sub_s hz))).1)
  exact weakHarnack_absorb_subball hα₀ hCW.le (mul_pos hθ0 hR).le hu_le_w hw_est h12 hC_final

/-- **The weak Harnack inequality of Krylov and Safonov for strong supersolutions**
(Gilbarg–Trudinger, Theorem 9.22; Caffarelli–Cabré, Theorem 4.8). Let `κ` be given. There is an
exponent `p > 0`, depending only on the dimension `n` and on `κ`, such that for every additive Haar
measure `mu` and every `0 < θ < 1` there is a constant `C > 0`, depending only on `n`, `mu`, `κ`,
and `θ`, with the following property. Let `B(x₀, R) ⊆ Ω`, let `a` be uniformly elliptic on
`B(x₀, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost everywhere
in `B(x₀, R)` and satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere there for the weak Hessian, with
`f⁺ ∈ Lⁿ(B(x₀, R))`. Then at every `y ∈ B(x₀, θ R)`, the continuous precise representative `ū` of
`u` satisfies

`(θ R)^(-n/p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (ū(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_rpow_neg_mul_eLpNorm_le_mul_preciseRepresentative_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∃ p : ℝ, 0 < p ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃θ : ℝ⦄, 0 < θ → θ < 1 →
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
    exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le (ι := ι) κ
  refine ⟨p, hp, fun mu _ θ hθ0 hθ1 ↦ ?_⟩
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  have hθ'0 : 0 < √θ := Real.sqrt_pos.2 hθ0
  have hθ'1 : √θ < 1 := Real.sqrt_one ▸ Real.sqrt_lt_sqrt hθ0.le hθ1
  obtain ⟨C_W, hCW, HW⟩ := HW' hθ'0 hθ'1
  set C_final : ℝ := (α₀ ^ p⁻¹)⁻¹ * C_W * max 1 (α₀ ^ (Fintype.card ι : ℝ)⁻¹)
  refine ⟨C_final, by positivity, fun lam Lam R x₀ Ω a f u hBΩ ha hLam hnn hsuper hf y hy ↦ ?_⟩
  exact le_of_forall_pos_mul_le (C := C_final * (1 + R / lam)) fun η hη ↦
    rpow_neg_mul_eLpNorm_le_add_mul_of_subball u hp hCW hθ0 hθ1 HW hBΩ ha hLam hnn hsuper hf
      hy hη rfl

/-- The `η`-approximation step for the strong Harnack inequality on `closedBall x₀ (2 * s)`. -/
private theorem preciseRepresentative_le_add_mul_of_abs_subball
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {κ C₀ C lam Lam r s : ℝ} {x₀ x y : EuclideanSpace ℝ ι} {Ω : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (u : Wkp mu Ω (Fintype.card ι) 2) (hC₀ : 0 < C₀)
    (H : ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      Lam ≤ κ * lam → ContDiffOn ℝ 2 u (ball x₀ (2 * r)) →
      (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
      (∀ x ∈ ball x₀ (2 * r), |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
      MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
      ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, u x ≤ C₀ * (u y + r * (eLpNorm f (Fintype.card ι)
        (volume.restrict (ball x₀ (2 * r)))).toReal / lam))
    (hBΩ : ball x₀ (2 * r) ⊆ Ω) (ha : UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam)
    (hLam : Lam ≤ κ * lam) (hnn : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), 0 ≤ Wkp.value 2 u x)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
      |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x)
    (hf : MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))))
    (hs_lt : s < r) (hxs : x ∈ ball x₀ s) (hys : y ∈ ball x₀ s) {η : ℝ} (hη : 0 < η)
    (hC : C = C₀ * max 1 ((Measure.addHaarScalarFactor volume mu : ℝ) ^
      (Fintype.card ι : ℝ)⁻¹)) :
    preciseRepresentative mu (Wkp.value 2 u) x ≤
      C * (preciseRepresentative mu (Wkp.value 2 u) y +
        r * (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal / lam) +
      η * (C * (1 + r / lam)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hs0 : 0 < s := pos_of_mem_ball hxs
  have hlam : 0 < lam := ha.pos
  have hcs_sub : closedBall x₀ (2 * s) ⊆ ball x₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hū_nn : ∀ z ∈ ball x₀ (2 * r), 0 ≤ ū z := fun z hz ↦
    Wkp.preciseRepresentative_nonneg (finrank_lt_two_mul_card (ι := ι)) u isOpen_ball hBΩ hnn hz
  obtain ⟨w, g, hw, hwK, hwg, hg⟩ :=
    exists_contDiff_le_and_le_add_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u
      (Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u)
      (Wkp.ae_eq_preciseRepresentative 2 u)
      (isCompact_closedBall x₀ (2 * s)) (hcs_sub.trans hBΩ) ball_subset_closedBall
      (ae_abs_apply_le_ball_of_uniformlyEllipticOn ha hbs_sub)
      (ae_restrict_of_ae_restrict_of_subset hbs_sub heq) hη
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have hw_nn : ∀ z ∈ ball x₀ (2 * s), 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hwK z (ball_subset_closedBall hz)).1
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have hyK : y ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hys)
  obtain ⟨hg_vol, h12⟩ := memLp_and_add_mul_eLpNorm_div_le_of_isAddHaarMeasure hbs_sub hf
    (hū_nn y (ball_subset_ball (by linarith) (ball_subset_ball hs_lt.le hys))) (hwK y hyK).2 hη.le
    hs0.le hs_lt.le hlam hg
  have hw_har := H (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hwg hg_vol x hxs y hys
  set F : ℝ := (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal
  calc ū x ≤ w x := (hwK x hxK).1
    _ ≤ C₀ * (max 1 (α₀ ^ n⁻¹) * (ū y + r * F / lam + η * (1 + r / lam))) :=
        hw_har.trans (mul_le_mul_of_nonneg_left h12 hC₀.le)
    _ = C * (ū y + r * F / lam) + η * (C * (1 + r / lam)) := by
        rw [hC]
        ring

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Theorem 9.22; Caffarelli–Cabré, Corollary 4.9), for functions in `W^{2,n}` satisfying the
two-sided inequality `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere. Let `κ` be given. For every additive
Haar measure `mu` there is a constant `C > 0`, depending only on the dimension `n`, `mu`, and `κ`,
with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on `B(x₀, 2 r)`
with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be nonnegative almost everywhere in
`B(x₀, 2 r)` with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere there and `f ∈ Lⁿ(B(x₀, 2 r))`. Then at
all `x, y ∈ B(x₀, r)`, the continuous precise representative `ū` of `u` satisfies

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure],
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
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) κ
  intro mu _
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  set C : ℝ := C₀ * max 1 (α₀ ^ (Fintype.card ι : ℝ)⁻¹)
  refine ⟨C, by positivity, fun lam Lam r x₀ Ω a f u hBΩ ha hLam hnn heq hf x hx y hy ↦ ?_⟩
  have hr : 0 < r := pos_of_mem_ball hx
  obtain ⟨s, -, hs_lt, hxs, hys⟩ :=
    TauCeti.exists_lt_mem_ball_of_mem_ball (half_lt_self hr) hx hy
  exact le_of_forall_pos_mul_le (C := C * (1 + r / lam)) fun η hη ↦
    preciseRepresentative_le_add_mul_of_abs_subball u hC₀ H hBΩ ha hLam hnn heq hf hs_lt hxs hys
      hη rfl

/-- **The Harnack inequality of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Theorem 9.22), for solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `W^{2,n}`. Let `κ` be
given. For every additive Haar measure `mu` there is a constant `C > 0`, depending only on the
dimension `n`, `mu`, and `κ`, with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be
uniformly elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be
nonnegative almost everywhere in `B(x₀, 2 r)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere there and
`f ∈ Lⁿ(B(x₀, 2 r))`. Then at all `x, y ∈ B(x₀, r)`, the continuous precise representative `ū` of
`u` satisfies

`ū(x) ≤ C (ū(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_preciseRepresentative_le_mul_add_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure],
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
  intro mu _
  obtain ⟨C, hC, H⟩ :=
    exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le (ι := ι) κ mu
  refine ⟨C, hC, fun lam Lam r x₀ Ω a f u hBΩ ha hLam hnn heq hf x hx y hy ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  refine H u hBΩ ha hLam hnn ?_ hf.norm x hx y hy
  filter_upwards [heq] with z hz
  rw [hz, Real.norm_eq_abs]

omit [DecidableEq ι] in
/-- Rescale `s ^ (-α) ≤ 2 r ^ (-α)` for `r / 2 < s` and absorb the `2 η` approximation error in
the interior Hölder estimate. -/
private theorem holder_absorb_subball {α : ℝ≥0} {n α₀ C₀ C lam r s M G F du dv d η : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀) (hM0 : 0 ≤ M) (hr : 0 < r) (hs_r2 : r / 2 < s)
    (hlam : 0 < lam) (hF : 0 ≤ F) (hη : 0 ≤ η) (hd : 0 ≤ d) (hdist_u : du ≤ dv + 2 * η)
    (hv_dist : dv ≤ C₀ * s ^ (-(α : ℝ)) * (M + η + G) * d ^ (α : ℝ))
    (h12 : M + η + G ≤ max 1 (α₀ ^ n⁻¹) * (M + r * F / lam + η * (1 + r / lam)))
    (hC : C = 2 * C₀ * max 1 (α₀ ^ n⁻¹)) :
    du ≤ C * r ^ (-(α : ℝ)) * (M + r * F / lam) * d ^ (α : ℝ) +
      η * (C * r ^ (-(α : ℝ)) * (1 + r / lam) * d ^ (α : ℝ) + 2) := by
  have hs0 : 0 < s := by linarith
  have hs_rpow : s ^ (-(α : ℝ)) ≤ 2 * r ^ (-(α : ℝ)) := by
    have hα0' : (0 : ℝ) < α := NNReal.coe_pos.2 hα0
    have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
    calc s ^ (-(α : ℝ)) ≤ 2 ^ (α : ℝ) * r ^ (-(α : ℝ)) :=
          Real.rpow_neg_le_mul_rpow_neg hr zero_le_two hα0'.le (by linarith)
      _ ≤ 2 ^ (1 : ℝ) * r ^ (-(α : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two hα1')
            (by positivity)
      _ = 2 * r ^ (-(α : ℝ)) := by rw [Real.rpow_one]
  have hv_bound :
      dv ≤ C * r ^ (-(α : ℝ)) * (M + r * F / lam + η * (1 + r / lam)) * d ^ (α : ℝ) := by
    calc dv ≤ C₀ * s ^ (-(α : ℝ)) * (M + η + G) * d ^ (α : ℝ) := hv_dist
      _ ≤ C₀ * s ^ (-(α : ℝ)) * (max 1 (α₀ ^ n⁻¹) * (M + r * F / lam + η * (1 + r / lam))) *
            d ^ (α : ℝ) := by gcongr
      _ ≤ C₀ * (2 * r ^ (-(α : ℝ))) *
            (max 1 (α₀ ^ n⁻¹) * (M + r * F / lam + η * (1 + r / lam))) * d ^ (α : ℝ) := by gcongr
      _ = C * r ^ (-(α : ℝ)) * (M + r * F / lam + η * (1 + r / lam)) * d ^ (α : ℝ) := by
          rw [hC]; ring
  calc du ≤ dv + 2 * η := hdist_u
    _ ≤ C * r ^ (-(α : ℝ)) * (M + r * F / lam + η * (1 + r / lam)) * d ^ (α : ℝ) +
          2 * η := by gcongr
    _ = C * r ^ (-(α : ℝ)) * (M + r * F / lam) * d ^ (α : ℝ) +
          η * (C * r ^ (-(α : ℝ)) * (1 + r / lam) * d ^ (α : ℝ) + 2) := by ring

/-- The `η`-approximation step for the strong interior Hölder estimate on
`closedBall x₀ (2 * s)`. -/
private theorem dist_preciseRepresentative_le_add_mul_of_subball
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {α : ℝ≥0} {κ C₀ C lam Lam r M s : ℝ} {x₀ x y : EuclideanSpace ℝ ι}
    {Ω : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} (u : Wkp mu Ω (Fintype.card ι) 2)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀)
    (H : ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < r →
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ max κ 1 * lam →
      ContDiffOn ℝ 2 u (ball x₀ (2 * r)) → (∀ x ∈ ball x₀ (2 * r), |u x| ≤ M) →
      (∀ x ∈ ball x₀ (2 * r), |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
      MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
      HolderOnWith (C₀ * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
        (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α u (ball x₀ r))
    (hBΩ : ball x₀ (2 * r) ⊆ Ω) (ha : UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam)
    (hLam : Lam ≤ κ * lam)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
      |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x)
    (hf : MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))))
    (hū_abs : ∀ z ∈ ball x₀ (2 * r), |preciseRepresentative mu (Wkp.value 2 u) z| ≤ M)
    (hM0 : 0 ≤ M) (hr : 0 < r) (hs_r2 : r / 2 < s) (hs_lt : s < r)
    (hxs : x ∈ ball x₀ s) (hys : y ∈ ball x₀ s) {η : ℝ} (hη : 0 < η)
    (hC : C = 2 * C₀ * max 1 ((Measure.addHaarScalarFactor volume mu : ℝ) ^
      (Fintype.card ι : ℝ)⁻¹)) :
    dist (preciseRepresentative mu (Wkp.value 2 u) x)
        (preciseRepresentative mu (Wkp.value 2 u) y) ≤
      C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
        (mu.restrict (ball x₀ (2 * r)))).toReal / lam) * dist x y ^ (α : ℝ) +
      η * (C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) := by
  have hs0 : 0 < s := pos_of_mem_ball hxs
  have hlam : 0 < lam := ha.pos
  have hLam' : Lam ≤ max κ 1 * lam :=
    hLam.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le)
  have hcs_sub : closedBall x₀ (2 * s) ⊆ ball x₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  -- Mollify `u` uniformly within `η` on `closedBall x₀ (2 * s)`.
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u
      (Wkp.continuousOn_preciseRepresentative (finrank_lt_two_mul_card (ι := ι)) u)
      (Wkp.ae_eq_preciseRepresentative 2 u)
      (isCompact_closedBall x₀ (2 * s)) (hcs_sub.trans hBΩ) ball_subset_closedBall
      (ae_abs_apply_le_ball_of_uniformlyEllipticOn ha hbs_sub)
      (ae_restrict_of_ae_restrict_of_subset hbs_sub heq) hη
  have hv2 : ContDiff ℝ 2 v := contDiff_infty.1 hv 2
  have hv_abs : ∀ z ∈ ball x₀ (2 * s), |v z| ≤ M + η := fun z hz ↦ by
    have htri := abs_add_le (ū z) (v z - ū z)
    rw [add_sub_cancel] at htri
    exact htri.trans (add_le_add (hū_abs z (hbs_sub hz)) (hvK z (ball_subset_closedBall hz)))
  -- Transfer `g` to `volume` and apply the classical Hölder estimate to `v`.
  obtain ⟨hg_vol, h12⟩ := memLp_and_add_mul_eLpNorm_div_le_of_isAddHaarMeasure hbs_sub hf
    hM0 le_rfl hη.le hs0.le hs_lt.le hlam hg
  have hhold := (H hs0 (ha.mono_set hbs_sub) hLam' hv2.contDiffOn hv_abs hvg hg_vol).dist_le hxs hys
  have hv_dist : dist (v x) (v y) ≤
      C₀ * s ^ (-(α : ℝ)) * (M + η + s * (eLpNorm g (Fintype.card ι)
        (volume.restrict (ball x₀ (2 * s)))).toReal / lam) * dist x y ^ (α : ℝ) :=
    hhold.trans_eq (by rw [Real.coe_toNNReal _ (by positivity)])
  -- Compare `dist (ū x) (ū y)` to `dist (v x) (v y)` via the triangle inequality and absorb `η`.
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have hyK : y ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hys)
  have hdist_u : dist (ū x) (ū y) ≤ dist (v x) (v y) + 2 * η := by
    have hdx : dist (ū x) (v x) ≤ η := by rw [dist_comm, Real.dist_eq]; exact hvK x hxK
    have hdy : dist (v y) (ū y) ≤ η := by rw [Real.dist_eq]; exact hvK y hyK
    linarith [dist_triangle4 (ū x) (v x) (v y) (ū y)]
  exact holder_absorb_subball hα0 hα1 hC₀.le hM0 hr hs_r2 hlam ENNReal.toReal_nonneg hη.le
    dist_nonneg hdist_u hv_dist h12 hC

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24; Caffarelli–Cabré, Proposition 4.10), for functions in `W^{2,n}` satisfying the
two-sided inequality `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere. Let `κ` be given. There is an
exponent `0 < α ≤ 1`, depending only on the dimension `n` and on `κ`, such that for every additive
Haar measure `mu` there is a constant `C > 0`, depending only on `n`, `mu`, and `κ`, with the
following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on `B(x₀, 2 r)` with
constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`
almost everywhere in `B(x₀, 2 r)`, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the continuous precise
representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧
      ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure],
        ∃ C : ℝ, 0 < C ∧
          ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
            ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
            (u : Wkp mu Ω (Fintype.card ι) 2),
            ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
            (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
            (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
              |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤
                f x) →
            MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
            HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
              (mu.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
              (preciseRepresentative mu (Wkp.value 2 u)) (ball x₀ r) := by
  have : Nonempty ι :=
    Fintype.card_pos_iff.1 (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι))
  obtain ⟨α, C₀, hα0, hα1, hC₀, H⟩ :=
    exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) (κ := max κ 1)
      (zero_lt_one.trans_le (le_max_right _ _))
  refine ⟨α, hα0, hα1, fun mu _ ↦ ?_⟩
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  set C : ℝ := 2 * C₀ * max 1 (α₀ ^ (Fintype.card ι : ℝ)⁻¹)
  refine ⟨C, by positivity, fun lam Lam r M x₀ Ω a f u hBΩ ha hLam hM heq hf ↦ ?_⟩
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  have hr : 0 < r := pos_of_mem_ball hx
  have hū_abs : ∀ z ∈ ball x₀ (2 * r), |preciseRepresentative mu (Wkp.value 2 u) z| ≤ M :=
    fun z hz ↦ Wkp.abs_preciseRepresentative_le (finrank_lt_two_mul_card (ι := ι)) u isOpen_ball
      hBΩ hM hz
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hū_abs x (ball_subset_ball (by linarith) hx))
  obtain ⟨s, hs_r2, hs_lt, hxs, hys⟩ :=
    TauCeti.exists_lt_mem_ball_of_mem_ball (half_lt_self hr) hx hy
  exact le_of_forall_pos_mul_le
    (C := C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) fun η hη ↦
    dist_preciseRepresentative_le_add_mul_of_subball u hα0 hα1 hC₀ H hBΩ ha hLam heq hf
      hū_abs hM0 hr hs_r2 hs_lt hxs hys hη rfl

/-- **The interior Hölder estimate of Krylov and Safonov for strong solutions** (Gilbarg–Trudinger,
Corollary 9.24), for solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `W^{2,n}`. Let `κ` be
given. There is an exponent `0 < α ≤ 1`, depending only on the dimension `n` and on `κ`, such that
for every additive Haar measure `mu` there is a constant `C > 0`, depending only on `n`, `mu`, and
`κ`, with the following property. Let `B(x₀, 2 r) ⊆ Ω`, let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `|u| ≤ M` and
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere in `B(x₀, 2 r)`, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then the
continuous precise representative `ū` of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_holderOnWith_preciseRepresentative_of_sum_mul_iteratedGradient_eq
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (κ : ℝ) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧
      ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure],
        ∃ C : ℝ, 0 < C ∧
          ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
            ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃f : EuclideanSpace ℝ ι → ℝ⦄
            (u : Wkp mu Ω (Fintype.card ι) 2),
            ball x₀ (2 * r) ⊆ Ω → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
            (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), |Wkp.value 2 u x| ≤ M) →
            (∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
              ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i =
                f x) →
            MemLp f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r))) →
            HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
              (mu.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α
              (preciseRepresentative mu (Wkp.value 2 u)) (ball x₀ r) := by
  obtain ⟨α, hα0, hα1, H⟩ :=
    exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le (ι := ι) κ
  refine ⟨α, hα0, hα1, fun mu _ ↦ ?_⟩
  obtain ⟨C, hC, Hmu⟩ := H mu
  refine ⟨C, hC, fun lam Lam r M x₀ Ω a f u hBΩ ha hLam hM heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  refine Hmu u hBΩ ha hLam hM ?_ hf.norm
  filter_upwards [heq] with z hz
  rw [hz, Real.norm_eq_abs]

end StrongSolutions

/-- **The Harnack inequality of Krylov and Safonov, almost everywhere** (Gilbarg–Trudinger,
Corollary 9.25; Caffarelli–Cabré, Theorem 4.3). For every `κ` there is `C > 0`, depending only on
the dimension `n ≥ 1` and on `κ`, with the following property. Let `Ω ⊇ B(x₀, 2 r)` be open, let
`a` be uniformly elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be
nonnegative almost everywhere in `B(x₀, 2 r)`, with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere there
for the weak Hessian, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then for almost every `x` and almost every `y`
in `B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_ae_value_le_mul_add_of_abs_sum_mul_iteratedGradient_le
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
        ∀ᵐ x ∂volume.restrict (ball x₀ r), ∀ᵐ y ∂volume.restrict (ball x₀ r),
          Wkp.value 2 u x ≤ C * (Wkp.value 2 u y +
            r * (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ :=
    exists_preciseRepresentative_le_mul_add_of_abs_sum_mul_iteratedGradient_le (ι := ι) κ volume
  refine ⟨C, hC, fun lam Lam r x₀ Ω a f u hΩ ha hLam hnonneg habs hf ↦ ?_⟩
  -- On `B(x₀, r)`, `u` agrees almost everywhere with its precise representative, for which the
  -- inequality holds at every pair of points.
  have hr : ball x₀ r ⊆ ball x₀ (2 * r) := fun y hy ↦ by
    have := mem_ball.1 hy
    exact mem_ball.2 (by linarith [dist_nonneg (x := y) (y := x₀)])
  have hū : ∀ᵐ x ∂volume.restrict (ball x₀ r),
      x ∈ ball x₀ r ∧ Wkp.value 2 u x = preciseRepresentative volume (Wkp.value 2 u) x := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae_restrict_of_subset
      (hr.trans hΩ) (Wkp.ae_eq_preciseRepresentative 2 u)] with x hx hxū
    exact ⟨hx, hxū⟩
  filter_upwards [hū] with x hx
  filter_upwards [hū] with y hy
  rw [hx.2, hy.2]
  exact H u hΩ ha hLam hnonneg habs hf x hx.1 y hy.1

/-- **The Harnack inequality of Krylov and Safonov for strong solutions, almost everywhere**
(Gilbarg–Trudinger, Corollary 9.25). For every `κ` there is `C > 0`, depending only on the
dimension `n ≥ 1` and on `κ`, with the following property. Let `Ω ⊇ B(x₀, 2 r)` be open, let `a` be
uniformly elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be a
strong solution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` in `B(x₀, 2 r)`, nonnegative almost everywhere there, where
`f ∈ Lⁿ(B(x₀, 2 r))`. Then for almost every `x` and almost every `y` in `B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_ae_value_le_mul_add_of_sum_mul_iteratedGradient_eq
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
        ∀ᵐ x ∂volume.restrict (ball x₀ r), ∀ᵐ y ∂volume.restrict (ball x₀ r),
          Wkp.value 2 u x ≤ C * (Wkp.value 2 u y +
            r * (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ := exists_ae_value_le_mul_add_of_abs_sum_mul_iteratedGradient_le (ι := ι) κ
  refine ⟨C, hC, fun lam Lam r x₀ Ω a f u hΩ ha hLam hnonneg heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H u hΩ ha hLam hnonneg (heq.mono fun x hx ↦ hx ▸ (Real.norm_eq_abs _).ge) hf.norm

end PDE

end TauCeti
