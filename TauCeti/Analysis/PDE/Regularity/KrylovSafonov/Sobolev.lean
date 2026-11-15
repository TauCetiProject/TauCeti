/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Harnack
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.Analysis.Sobolev.Wkp.PreciseRepresentative
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Krylov–Safonov estimates for `W^{2,n}` strong solutions

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
(`TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp` and its two-sided
variant `TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`) produces a
smooth function `v` within `η` of `ū` on `closedBall x₀ s` whose classical principal part controls
the weak principal part up to an `Lⁿ` error of norm at most `η`:

* For **strong subsolutions** (`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` a.e.), applying one-sided mollification to `-u`
  and shifting down to `w = -v - η ≤ ū` makes `w⁺ ≤ ū⁺` pointwise on `B(c, s)` while keeping the
  same Hessian and `ū(x) ≤ w(x) + 2 η`, avoiding any quasi-triangle loss when `0 < p < 1`.
* For **strong supersolutions** (`u ≥ 0` and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` a.e. on `B(x₀, R)`), setting
  `θ' = √θ` so that `closedBall x₀ (θ' R) ⊂ B(x₀, R)` and `θ' (θ' R) = θ R`, mollifying on
  `closedBall x₀ (θ' R)` and shifting up to `w = v + η ≥ ū ≥ 0` gives `‖ū‖_{Lᵖ} ≤ ‖w‖_{Lᵖ}` on
  `B(x₀, θ R)` and `w(y) ≤ ū(y) + 2 η`.
* For **strong solutions** (`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` a.e. on `B(x₀, 2 r)`), two-sided mollification on
  `closedBall x₀ (2 s) ⊂ B(x₀, 2 r)` transfers both the Harnack inequality and the interior Hölder
  estimate directly from their classical counterparts as `η → 0`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.
* `TauCeti.PDE.exists_preciseRepresentative_le_mul_rpow_mul_eLpNorm_posPart_add_of_wkp`: **the local
  maximum principle** for `W^{2,n}` strong subsolutions.
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

section StrongSolutions

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

omit [Fintype ι] [DecidableEq ι] in
/-- If `a ≤ A + B η` for every `η > 0`, then `a ≤ A`. -/
private theorem le_of_forall_pos_le_add_mul {a A B : ℝ}
    (h : ∀ η : ℝ, 0 < η → a ≤ A + B * η) : a ≤ A := by
  have hcont : Continuous (fun η : ℝ ↦ A + B * η) := by fun_prop
  have hlim : Tendsto (fun η : ℝ ↦ A + B * η) (𝓝[>] 0) (𝓝 (A + B * 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto 0)
  simpa using ge_of_tendsto hlim (eventually_nhdsWithin_of_forall h)

omit [DecidableEq ι] in
private theorem nonempty_of_card_fact [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] : Nonempty ι :=
  Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)

omit [DecidableEq ι] in
private theorem volume_restrict_eq_smul (U : Set (EuclideanSpace ℝ ι)) :
    volume.restrict U = Measure.addHaarScalarFactor volume mu • mu.restrict U := by
  rw [← Measure.restrict_smul, ← Measure.isAddLeftInvariant_eq_smul volume mu]

omit [DecidableEq ι] in
private theorem toReal_eLpNorm_volume_restrict (g : EuclideanSpace ℝ ι → ℝ) (q : ℝ≥0∞)
    (U : Set (EuclideanSpace ℝ ι)) :
    (eLpNorm g q (volume.restrict U)).toReal =
      (Measure.addHaarScalarFactor volume mu : ℝ) ^ q.toReal⁻¹ *
        (eLpNorm g q (mu.restrict U)).toReal := by
  have hα : Measure.addHaarScalarFactor volume mu ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu).ne'
  rw [volume_restrict_eq_smul (mu := mu), eLpNorm_smul_measure_of_ne_zero' hα, ENNReal.smul_def,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_rpow]

omit [DecidableEq ι] in
private theorem memLp_volume_restrict_of_eLpNorm_lt_top {g : EuclideanSpace ℝ ι → ℝ} {q : ℝ≥0∞}
    {U : Set (EuclideanSpace ℝ ι)} (h : eLpNorm g q (mu.restrict U) < ∞) :
    MemLp g q (volume.restrict U) := by
  rw [volume_restrict_eq_smul (mu := mu)]
  exact (memLp_iff.2 h).smul_measure_nnreal

omit [DecidableEq ι] in
private theorem memLp_volume_and_toReal_eLpNorm_le_add {G F_fn : EuclideanSpace ℝ ι → ℝ}
    {q : ℝ≥0∞} {S U : Set (EuclideanSpace ℝ ι)} {η : ℝ} (hSU : S ⊆ U) (hη : 0 ≤ η)
    (hf : MemLp F_fn q (mu.restrict U))
    (hg : eLpNorm G q (mu.restrict S) ≤ eLpNorm F_fn q (mu.restrict S) + ENNReal.ofReal η) :
    MemLp G q (volume.restrict S) ∧
      (eLpNorm G q (mu.restrict S)).toReal ≤ (eLpNorm F_fn q (mu.restrict U)).toReal + η := by
  have hle : eLpNorm G q (mu.restrict S) ≤
      eLpNorm F_fn q (mu.restrict U) + ENNReal.ofReal η :=
    hg.trans (add_le_add_left (eLpNorm_mono_measure _ (Measure.restrict_mono hSU le_rfl)) _)
  have htop : eLpNorm F_fn q (mu.restrict U) + ENNReal.ofReal η < ∞ :=
    ENNReal.add_lt_top.2 ⟨hf.eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩
  refine ⟨memLp_volume_restrict_of_eLpNorm_lt_top (hle.trans_lt htop), ?_⟩
  have htr := ENNReal.toReal_mono htop.ne hle
  rwa [ENNReal.toReal_add hf.eLpNorm_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hη] at htr

omit [DecidableEq ι] in
private theorem exists_mem_ball_and_closedBall_two_mul_subset {x₀ x y : EuclideanSpace ℝ ι}
    {r : ℝ} (hx : x ∈ ball x₀ r) (hy : y ∈ ball x₀ r) :
    ∃ s : ℝ, r / 2 < s ∧ s < r ∧ x ∈ ball x₀ s ∧ y ∈ ball x₀ s ∧
      closedBall x₀ (2 * s) ⊆ ball x₀ (2 * r) := by
  have hr : 0 < r := pos_of_mem_ball hx
  refine ⟨(max (max (dist x x₀) (dist y x₀)) (r / 2) + r) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [le_max_right (max (dist x x₀) (dist y x₀)) (r / 2)]
  · linarith [max_lt (max_lt (mem_ball.1 hx) (mem_ball.1 hy)) (half_lt_self hr)]
  · rw [mem_ball]
    linarith [mem_ball.1 hx, le_trans (le_max_left (dist x x₀) (dist y x₀))
      (le_max_left (max (dist x x₀) (dist y x₀)) (r / 2))]
  · rw [mem_ball]
    linarith [mem_ball.1 hy, le_trans (le_max_right (dist x x₀) (dist y x₀))
      (le_max_left (max (dist x x₀) (dist y x₀)) (r / 2))]
  · exact closedBall_subset_ball
      (by linarith [max_lt (max_lt (mem_ball.1 hx) (mem_ball.1 hy)) (half_lt_self hr)])

omit [DecidableEq ι] in
private theorem continuousOn_preciseRepresentative_wkp_card
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ ι)}
    (u : Wkp mu Ω (Fintype.card ι) 2) :
    ContinuousOn (preciseRepresentative mu (Wkp.value 2 u)) Ω :=
  Wkp.continuousOn_preciseRepresentative (by simp [finrank_euclideanSpace]) u

omit [DecidableEq ι] in
private theorem preciseRepresentative_nonneg_of_ae_nonneg
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ ι)}
    (u : Wkp mu Ω (Fintype.card ι) 2) {U : Set (EuclideanSpace ℝ ι)} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hnn : ∀ᵐ x ∂mu.restrict U, 0 ≤ Wkp.value 2 u x) :
    ∀ x ∈ U, 0 ≤ preciseRepresentative mu (Wkp.value 2 u) x := by
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū U := (continuousOn_preciseRepresentative_wkp_card u).mono hUΩ
  have hae : (fun x ↦ ū x ⊓ 0) =ᵐ[mu.restrict U] fun _ ↦ (0 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUΩ (Wkp.ae_eq_preciseRepresentative 2 u),
      hnn] with x hxu hx0
    exact inf_eq_right.2 (by simpa only [ū, ← hxu] using hx0)
  have heq := Measure.eqOn_open_of_ae_eq hae hU (hcont.inf continuousOn_const) continuousOn_const
  exact fun x hx ↦ inf_eq_right.1 (heq hx)

omit [DecidableEq ι] in
private theorem abs_preciseRepresentative_le_of_ae_abs_le
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ ι)}
    (u : Wkp mu Ω (Fintype.card ι) 2) {U : Set (EuclideanSpace ℝ ι)} {M : ℝ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hM : ∀ᵐ x ∂mu.restrict U, |Wkp.value 2 u x| ≤ M) :
    ∀ x ∈ U, |preciseRepresentative mu (Wkp.value 2 u) x| ≤ M := by
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū U := (continuousOn_preciseRepresentative_wkp_card u).mono hUΩ
  have hae : (fun x ↦ |ū x| ⊔ M) =ᵐ[mu.restrict U] fun _ ↦ M := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUΩ (Wkp.ae_eq_preciseRepresentative 2 u),
      hM] with x hxu hxM
    exact sup_eq_right.2 (by simpa only [ū, ← hxu] using hxM)
  have heq := Measure.eqOn_open_of_ae_eq hae hU
    ((continuous_abs.comp_continuousOn hcont).sup continuousOn_const) continuousOn_const
  exact fun x hx ↦ sup_eq_right.1 (heq hx)

/-- **The local maximum principle for strong subsolutions** (Gilbarg–Trudinger, Theorem 9.20,
without lower-order terms). Let `p > 0` and `κ` be given. There is a constant `C > 0`, depending
only on the dimension `n`, the additive Haar measure `mu`, `κ`, and `p`, with the following
property. Let `B(c, R) ⊆ Ω`, let `a` be uniformly elliptic on `B(c, R)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` almost everywhere in `B(c, R)`
for the weak Hessian, with `u⁺ ∈ Lᵖ(B(c, R))` and `f⁻ ∈ Lⁿ(B(c, R))`. Then at every
`x ∈ B(c, R / 2)`, the continuous precise representative `ū` of `u` satisfies

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
        MemLp (fun x ↦ (Wkp.value 2 u x)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R)) →
        MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (mu.restrict (ball c R)) →
        ∀ x ∈ ball c (R / 2),
          preciseRepresentative mu (Wkp.value 2 u) x ≤
            C * (R ^ (-(Fintype.card ι : ℝ) / p) *
              (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p)
                (mu.restrict (ball c R))).toReal +
              R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
                (mu.restrict (ball c R))).toReal) := by
  have := nonempty_of_card_fact (ι := ι)
  obtain ⟨C_M, hCM, HM⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := ι) (κ := κ) hp
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  set K_haar : ℝ := max (2 ^ (n / p) * α₀ ^ p⁻¹) (α₀ ^ n⁻¹)
  refine ⟨C_M * K_haar, mul_pos hCM (lt_max_of_lt_left (by positivity)), ?_⟩
  intro lam Lam R c Ω a f u hBΩ ha hLam hsub hup hf x hx
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω := continuousOn_preciseRepresentative_wkp_card u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  -- Pick `s` strictly between `max (2 dist x c) (R / 2)` and `R` so `closedBall c s ⊆ B(c, R) ⊆ Ω`
  -- and `x ∈ B(c, s / 2)`.
  set s : ℝ := (max (2 * dist x c) (R / 2) + R) / 2
  have hxc : 2 * dist x c < R := by linarith [mem_ball.1 hx]
  have hsR2 : R / 2 < s := by
    simp only [s]
    linarith [le_max_right (2 * dist x c) (R / 2)]
  have hsR : s < R := by
    simp only [s]
    linarith [max_lt hxc (half_lt_self hR)]
  have hxs : x ∈ ball c (s / 2) := by
    rw [mem_ball]
    simp only [s]
    linarith [le_max_left (2 * dist x c) (R / 2)]
  have hcs_sub : closedBall c s ⊆ ball c R := closedBall_subset_ball hsR
  have hbs_sub : ball c s ⊆ ball c R := ball_subset_closedBall.trans hcs_sub
  set Np : ℝ :=
    (eLpNorm (fun y ↦ (Wkp.value 2 u y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c R))).toReal
  set F : ℝ := (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (mu.restrict (ball c R))).toReal
  -- Express `-u` as a strong supersolution on `B(c, s)` with right-hand side `-f`.
  have hnū : (Wkp.value 2 (-u) : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] fun y ↦ -ū y := by
    have hval_neg : Wkp.value 2 (-u) = -Wkp.value 2 u := by
      simp only [← Wkp.valueL_apply, map_neg]
    exact (hval_neg ▸ Lp.coeFn_neg (Wkp.value 2 u)).trans hū.neg
  have hnsuper : ∀ᵐ y ∂mu.restrict (ball c s),
      ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 (-u) y (EuclideanSpace.single j 1) i ≤ -f y := by
    have hgrad_neg_eq : Wkp.iteratedGradient 1 (-u) = -Wkp.iteratedGradient 1 u := by
      simp only [← Wkp.iteratedGradientL_apply, map_neg]
    have hgrad_neg : Wkp.iteratedGradient 1 (-u) =ᵐ[mu.restrict (ball c s)]
        -Wkp.iteratedGradient 1 u :=
      ae_restrict_of_ae_restrict_of_subset (hbs_sub.trans hBΩ)
        (hgrad_neg_eq ▸ Lp.coeFn_neg (Wkp.iteratedGradient 1 u))
    filter_upwards [hgrad_neg, ae_restrict_of_ae_restrict_of_subset hbs_sub hsub] with y hy hfy
    have hsum_neg : ∑ i, ∑ j, a y i j *
        Wkp.iteratedGradient 1 (-u) y (EuclideanSpace.single j 1) i =
        -∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i := by
      rw [hy]
      simp [mul_neg, Finset.sum_neg_distrib]
    rw [hsum_neg]
    exact neg_le_neg hfy
  -- Approximate `-u` within `η` on `closedBall c s`, shift `w = -v - η ≤ ū`, and let `η → 0`.
  refine le_of_forall_pos_le_add_mul (B := C_M * K_haar * (R / lam) + 2) fun η hη ↦ ?_
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) (-u) hcont.neg hnū
      (isCompact_closedBall c s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun y hy ↦ ha.abs_apply_le (hbs_sub hy))
      hnsuper hη
  set w : EuclideanSpace ℝ ι → ℝ := fun y ↦ (-1 : ℝ) * v y + (-η)
  have hw2 : ContDiff ℝ 2 w :=
    contDiff_infty.1 ((contDiff_const.mul hv).add contDiff_const) 2
  have hw_le_ū : ∀ y ∈ closedBall c s, w y ≤ ū y := fun y hy ↦ by
    have h := (abs_le.1 (hvK y hy)).1
    simp only [w, Pi.neg_apply] at h ⊢
    linarith
  have hūx_le : ū x ≤ w x + 2 * η := by
    have hxK : x ∈ closedBall c s :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
    have h := (abs_le.1 (hvK x hxK)).2
    simp only [w, Pi.neg_apply] at h ⊢
    linarith
  have hw_sub : ∀ y ∈ ball c s, -g y ≤ ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun y hy ↦ by
    have hfd : fderiv ℝ w = fderiv ℝ (fun z ↦ (-1 : ℝ) * v z) :=
      funext fun z ↦ fderiv_add_const (-η)
    rw [hfd, sum_mul_fderiv_fderiv_const_mul]
    linarith [hvg y hy]
  have hnf_eq : (fun y ↦ (-f y)⁺) = fun y ↦ (f y)⁻ := funext fun y ↦ posPart_neg (f y)
  have hng_eq : (fun y ↦ (-g y)⁻) = fun y ↦ (g y)⁺ := funext fun y ↦ negPart_neg (g y)
  obtain ⟨hg_vol, hg_lp⟩ := memLp_volume_and_toReal_eLpNorm_le_add hbs_sub hη.le hf
    (G := fun y ↦ (-g y)⁻) (by rwa [hng_eq, ← hnf_eq])
  have hm := HM (ha.mono_set hbs_sub) hLam hw2.continuous.continuousOn hw2.contDiffOn hw_sub
    hg_vol x hxs
  rw [toReal_eLpNorm_volume_restrict (mu := mu), toReal_eLpNorm_volume_restrict (mu := mu),
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_natCast] at hm
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
      exact posPart_mono (hw_le_ū y (ball_subset_closedBall hy))
    exact ENNReal.toReal_mono hup.eLpNorm_ne_top hmono
  have hs_rpow : s ^ (-n / p) ≤ 2 ^ (n / p) * R ^ (-n / p) := by
    have h2_rpow : ((2 : ℝ) ^ (-n / p))⁻¹ = 2 ^ (n / p) := by
      rw [neg_div, Real.rpow_neg (by norm_num), inv_inv]
    calc s ^ (-n / p) ≤ (R / 2) ^ (-n / p) :=
          Real.rpow_le_rpow_of_nonpos (half_pos hR) hsR2.le
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Nat.cast_nonneg _)) hp.le)
      _ = 2 ^ (n / p) * R ^ (-n / p) := by
          rw [div_eq_mul_inv, Real.mul_rpow hR.le (by norm_num),
            Real.inv_rpow (by norm_num), h2_rpow, mul_comm]
  have h1 : s ^ (-n / p) * (α₀ ^ p⁻¹ *
      (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal) ≤
      K_haar * (R ^ (-n / p) * Np) := by
    calc s ^ (-n / p) * (α₀ ^ p⁻¹ *
            (eLpNorm (fun y ↦ (w y)⁺) (ENNReal.ofReal p) (mu.restrict (ball c s))).toReal)
        ≤ (2 ^ (n / p) * R ^ (-n / p)) * (α₀ ^ p⁻¹ * Np) := by gcongr
      _ = (2 ^ (n / p) * α₀ ^ p⁻¹) * (R ^ (-n / p) * Np) := by ring
      _ ≤ K_haar * (R ^ (-n / p) * Np) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have h2 : s / lam * (α₀ ^ n⁻¹ *
      (eLpNorm (fun y ↦ (-g y)⁻) (Fintype.card ι) (mu.restrict (ball c s))).toReal) ≤
      K_haar * (R / lam * (F + η)) := by
    have hs_le : s / lam ≤ R / lam := div_le_div_of_nonneg_right hsR.le hlam.le
    calc s / lam * (α₀ ^ n⁻¹ *
            (eLpNorm (fun y ↦ (-g y)⁻) (Fintype.card ι) (mu.restrict (ball c s))).toReal)
        ≤ R / lam * (α₀ ^ n⁻¹ * (F + η)) := by gcongr
      _ = α₀ ^ n⁻¹ * (R / lam * (F + η)) := by ring
      _ ≤ K_haar * (R / lam * (F + η)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc ū x ≤ w x + 2 * η := hūx_le
    _ ≤ C_M * (K_haar * (R ^ (-n / p) * Np) + K_haar * (R / lam * (F + η))) + 2 * η := by
        linarith [hm, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCM.le]
    _ = C_M * K_haar * (R ^ (-n / p) * Np + R / lam * F) +
          (C_M * K_haar * (R / lam) + 2) * η := by ring

/-- **The weak Harnack inequality of Krylov and Safonov for strong supersolutions**
(Gilbarg–Trudinger, Theorem 9.22; Caffarelli–Cabré, Theorem 4.8). Let `κ` and `0 < θ < 1` be
given. There are an exponent `p > 0` and a constant `C > 0`, depending only on the dimension `n`,
the additive Haar measure `mu`, `κ`, and `θ`, with the following property. Let `B(x₀, R) ⊆ Ω`, let
`a` be uniformly elliptic on `B(x₀, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` be
nonnegative almost everywhere in `B(x₀, R)` and satisfy `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere there
for the weak Hessian, with `f⁺ ∈ Lⁿ(B(x₀, R))`. Then at every `y ∈ B(x₀, θ R)`, the continuous
precise representative `ū` of `u` satisfies

`(θ R)^(-n/p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (ū(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_rpow_neg_mul_eLpNorm_le_mul_preciseRepresentative_add_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
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
  have := nonempty_of_card_fact (ι := ι)
  set θ' : ℝ := √θ
  have hθ'0 : 0 < θ' := Real.sqrt_pos.2 hθ0
  have hθ'1 : θ' < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hθ0.le hθ1
  obtain ⟨p, C_W, hp, hCW, HW⟩ :=
    exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
      hθ'0 hθ'1
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  set C_final : ℝ := (α₀ ^ p⁻¹)⁻¹ * C_W * max 1 (α₀ ^ n⁻¹)
  have hC_final : 0 < C_final := by positivity
  refine ⟨p, C_final, hp, hC_final, ?_⟩
  intro lam Lam R x₀ Ω a f u hBΩ ha hLam hnn hsuper hf y hy
  have hθR : 0 < θ * R := pos_of_mem_ball hy
  have hR : 0 < R := (mul_pos_iff_of_pos_left hθ0).1 hθR
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω := continuousOn_preciseRepresentative_wkp_card u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_nn : ∀ z ∈ ball x₀ R, 0 ≤ ū z :=
    preciseRepresentative_nonneg_of_ae_nonneg u isOpen_ball hBΩ hnn
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
  -- Approximate `u` within `η` on `closedBall x₀ s`, shift `w = v + η ≥ ū ≥ 0`, and let `η → 0`.
  refine le_of_forall_pos_le_add_mul (B := C_final * (2 + R / lam)) fun η hη ↦ ?_
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall x₀ s) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hbs_sub hz))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub hsuper) hη
  set w : EuclideanSpace ℝ ι → ℝ := fun z ↦ v z + η
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 (hv.add contDiff_const) 2
  have hū_le_w : ∀ z ∈ closedBall x₀ s, ū z ≤ w z := fun z hz ↦ by
    have h := (abs_le.1 (hvK z hz)).1
    simp only [w]
    linarith
  have hw_nn : ∀ z ∈ ball x₀ s, 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hū_le_w z (ball_subset_closedBall hz))
  have hwy_le : w y ≤ ū y + 2 * η := by
    have hyK : y ∈ closedBall x₀ s := by
      rw [← hθ's] at hy
      exact ball_subset_closedBall (ball_subset_ball (mul_le_of_le_one_left hs0.le hθ'1.le) hy)
    have h := (abs_le.1 (hvK y hyK)).2
    simp only [w]
    linarith
  have hw_super : ∀ z ∈ ball x₀ s, ∑ i, ∑ j, a z i j * fderiv ℝ (fderiv ℝ w) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g z := fun z hz ↦ by
    have hfd : fderiv ℝ w = fderiv ℝ v := funext fun q ↦ fderiv_add_const η
    rw [hfd]
    exact hvg z hz
  obtain ⟨hg_vol, hg_lp⟩ := memLp_volume_and_toReal_eLpNorm_le_add hbs_sub hη.le hf hg
  have hw_est := HW (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hw_super hg_vol y
    (hθ's.symm ▸ hy)
  rw [hθ's, toReal_eLpNorm_volume_restrict (mu := mu), toReal_eLpNorm_volume_restrict (mu := mu),
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_natCast] at hw_est
  have hw_mem : MemLp w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R))) := by
    have hsub_cb : ball x₀ (θ * R) ⊆ closedBall x₀ s := by
      rw [← hθ's]
      exact (ball_subset_ball (mul_le_of_le_one_left hs0.le hθ'1.le)).trans ball_subset_closedBall
    exact hw2.continuous.continuousOn.memLp_restrict_of_subset_isCompact
      (isCompact_closedBall x₀ s) measurableSet_ball hsub_cb _
  have hu_le_w : (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p)
      (mu.restrict (ball x₀ (θ * R)))).toReal ≤
      (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal := by
    refine ENNReal.toReal_mono hw_mem.eLpNorm_ne_top ?_
    have hθR_sub_s : ball x₀ (θ * R) ⊆ ball x₀ s := by
      rw [← hθ's]
      exact ball_subset_ball (mul_le_of_le_one_left hs0.le hθ'1.le)
    refine eLpNorm_mono_ae ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hθR_sub_s.trans (hbs_sub.trans hBΩ)) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae_restrict_of_subset (hθR_sub_s.trans (hbs_sub.trans hBΩ)) hū] with z hz hzu
    have hznn := hū_nn z (hθR_sub_s.trans hbs_sub hz)
    have hzw := hū_le_w z (ball_subset_closedBall (hθR_sub_s hz))
    rw [hzu, Real.norm_of_nonneg hznn, Real.norm_of_nonneg (hznn.trans hzw)]
    exact hzw
  have hRHS : w y + s * (α₀ ^ n⁻¹ *
      (eLpNorm (fun z ↦ (g z)⁺) (Fintype.card ι) (mu.restrict (ball x₀ s))).toReal) / lam ≤
      max 1 (α₀ ^ n⁻¹) * ((ū y + 2 * η) + R * (F + η) / lam) := by
    have h1 : w y ≤ max 1 (α₀ ^ n⁻¹) * (ū y + 2 * η) :=
      hwy_le.trans (le_mul_of_one_le_left
        (add_nonneg (hū_nn y (ball_subset_ball (mul_le_of_le_one_left hR.le hθ1.le) hy))
          (by positivity)) (le_max_left _ _))
    have h2 : s * (α₀ ^ n⁻¹ *
        (eLpNorm (fun z ↦ (g z)⁺) (Fintype.card ι) (mu.restrict (ball x₀ s))).toReal) / lam ≤
        max 1 (α₀ ^ n⁻¹) * (R * (F + η) / lam) := by
      calc s * (α₀ ^ n⁻¹ *
              (eLpNorm (fun z ↦ (g z)⁺) (Fintype.card ι) (mu.restrict (ball x₀ s))).toReal) / lam
          ≤ R * (α₀ ^ n⁻¹ * (F + η)) / lam := by
            have : s ≤ R := hsR.le
            gcongr
        _ = α₀ ^ n⁻¹ * (R * (F + η) / lam) := by ring
        _ ≤ max 1 (α₀ ^ n⁻¹) * (R * (F + η) / lam) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    linarith
  have hdiv : (θ * R) ^ (-n / p) *
      (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal ≤
      (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + 2 * η) + R * (F + η) / lam))) := by
    rw [le_inv_mul_iff₀ (by positivity)]
    calc α₀ ^ p⁻¹ * ((θ * R) ^ (-n / p) *
            (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal)
        = (θ * R) ^ (-n / p) * (α₀ ^ p⁻¹ *
            (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal) := by ring
      _ ≤ C_W * (w y + s * (α₀ ^ n⁻¹ *
            (eLpNorm (fun z ↦ (g z)⁺) (Fintype.card ι)
              (mu.restrict (ball x₀ s))).toReal) / lam) := hw_est
      _ ≤ C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + 2 * η) + R * (F + η) / lam)) := by gcongr
  calc (θ * R) ^ (-n / p) *
        (eLpNorm (Wkp.value 2 u) (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal
      ≤ (θ * R) ^ (-n / p) *
          (eLpNorm w (ENNReal.ofReal p) (mu.restrict (ball x₀ (θ * R)))).toReal := by gcongr
    _ ≤ (α₀ ^ p⁻¹)⁻¹ * (C_W * (max 1 (α₀ ^ n⁻¹) * ((ū y + 2 * η) + R * (F + η) / lam))) := hdiv
    _ = C_final * (ū y + R * F / lam) + C_final * (2 + R / lam) * η := by
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
  have := nonempty_of_card_fact (ι := ι)
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
  set C : ℝ := C₀ * max 1 (α₀ ^ n⁻¹)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro lam Lam r x₀ Ω a f u hBΩ ha hLam hnn heq hf x hx y hy
  have hr : 0 < r := pos_of_mem_ball hx
  have hlam : 0 < lam := ha.pos
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hcont : ContinuousOn ū Ω := continuousOn_preciseRepresentative_wkp_card u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_nn : ∀ z ∈ ball x₀ (2 * r), 0 ≤ ū z :=
    preciseRepresentative_nonneg_of_ae_nonneg u isOpen_ball hBΩ hnn
  -- Choose `s < r` with `x, y ∈ B(x₀, s)` so `closedBall x₀ (2 s) ⊆ B(x₀, 2 r) ⊆ Ω`.
  obtain ⟨s, hs_gt, hs_lt, hxs, hys, hcs_sub⟩ :=
    exists_mem_ball_and_closedBall_two_mul_subset hx hy
  have : 0 < s := (half_pos hr).trans hs_gt
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  set F : ℝ := (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal
  refine le_of_forall_pos_le_add_mul (B := C * (2 + r / lam)) fun η hη ↦ ?_
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp
      (ENNReal.natCast_ne_top (Fintype.card ι)) u hcont hū
      (isCompact_closedBall x₀ (2 * s)) (hcs_sub.trans hBΩ) ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ ha.abs_apply_le (hbs_sub hz))
      (ae_restrict_of_ae_restrict_of_subset hbs_sub heq) hη
  set w : EuclideanSpace ℝ ι → ℝ := fun z ↦ v z + η
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 (hv.add contDiff_const) 2
  have hū_le_w : ∀ z ∈ closedBall x₀ (2 * s), ū z ≤ w z := fun z hz ↦ by
    have h := (abs_le.1 (hvK z hz)).1
    simp only [w]
    linarith
  have hw_nn : ∀ z ∈ ball x₀ (2 * s), 0 ≤ w z := fun z hz ↦
    (hū_nn z (hbs_sub hz)).trans (hū_le_w z (ball_subset_closedBall hz))
  have hwy_le : w y ≤ ū y + 2 * η := by
    have hyK : y ∈ closedBall x₀ (2 * s) :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hys)
    have h := (abs_le.1 (hvK y hyK)).2
    simp only [w]
    linarith
  have hw_eq : ∀ z ∈ ball x₀ (2 * s), |∑ i, ∑ j, a z i j * fderiv ℝ (fderiv ℝ w) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ g z := fun z hz ↦ by
    have hfd : fderiv ℝ w = fderiv ℝ v := funext fun q ↦ fderiv_add_const η
    rw [hfd]
    exact hvg z hz
  obtain ⟨hg_vol, hg_lp⟩ := memLp_volume_and_toReal_eLpNorm_le_add hbs_sub hη.le hf hg
  have hw_har := H (ha.mono_set hbs_sub) hLam hw2.contDiffOn hw_nn hw_eq hg_vol x hxs y hys
  rw [toReal_eLpNorm_volume_restrict (mu := mu), ENNReal.toReal_natCast] at hw_har
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have h1 : w y ≤ max 1 (α₀ ^ n⁻¹) * (ū y + 2 * η) :=
    hwy_le.trans (le_mul_of_one_le_left
      (add_nonneg (hū_nn y (ball_subset_ball (by linarith) hy)) (by positivity)) (le_max_left _ _))
  have h2 : s * (α₀ ^ n⁻¹ *
      (eLpNorm g (Fintype.card ι) (mu.restrict (ball x₀ (2 * s)))).toReal) / lam ≤
      max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam) := by
    calc s * (α₀ ^ n⁻¹ *
            (eLpNorm g (Fintype.card ι) (mu.restrict (ball x₀ (2 * s)))).toReal) / lam
        ≤ r * (α₀ ^ n⁻¹ * (F + η)) / lam := by
          have : s ≤ r := hs_lt.le
          gcongr
      _ = α₀ ^ n⁻¹ * (r * (F + η) / lam) := by ring
      _ ≤ max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc ū x ≤ w x := hū_le_w x hxK
    _ ≤ C₀ * (max 1 (α₀ ^ n⁻¹) * (ū y + 2 * η) + max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam)) := by
        linarith [hw_har, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC₀.le]
    _ = C * (ū y + r * F / lam) + C * (2 + r / lam) * η := by
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
  have := nonempty_of_card_fact (ι := ι)
  set κ' : ℝ := max κ 1
  have hκ' : 0 < κ' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨α, C₀, hα0, hα1, hC₀, H⟩ :=
    exists_holderOnWith_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) hκ'
  have hα0' : (0 : ℝ) < α := NNReal.coe_pos.2 hα0
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  set n : ℝ := (Fintype.card ι : ℝ)
  set α₀ : ℝ := (Measure.addHaarScalarFactor volume mu : ℝ)
  have hα₀ : 0 < α₀ :=
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume mu)
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
  have hcont : ContinuousOn ū Ω := continuousOn_preciseRepresentative_wkp_card u
  have hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū :=
    Wkp.ae_eq_preciseRepresentative 2 u
  have hū_abs : ∀ z ∈ ball x₀ (2 * r), |ū z| ≤ M :=
    abs_preciseRepresentative_le_of_ae_abs_le u isOpen_ball hBΩ hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hū_abs x (ball_subset_ball (by linarith) hx))
  -- Choose `r / 2 < s < r` with `x, y ∈ B(x₀, s)` so `closedBall x₀ (2 s) ⊆ B(x₀, 2 r) ⊆ Ω`.
  obtain ⟨s, hs_gt, hs_lt, hxs, hys, hcs_sub⟩ :=
    exists_mem_ball_and_closedBall_two_mul_subset hx hy
  have hs0 : 0 < s := (half_pos hr).trans hs_gt
  have hbs_sub : ball x₀ (2 * s) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hcs_sub
  set F : ℝ := (eLpNorm f (Fintype.card ι) (mu.restrict (ball x₀ (2 * r)))).toReal
  have hs_rpow : s ^ (-(α : ℝ)) ≤ 2 * r ^ (-(α : ℝ)) := by
    have h2_rpow : ((2 : ℝ) ^ (-(α : ℝ)))⁻¹ = 2 ^ (α : ℝ) := by
      rw [Real.rpow_neg (by norm_num), inv_inv]
    calc s ^ (-(α : ℝ)) ≤ (r / 2) ^ (-(α : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (half_pos hr) hs_gt.le (neg_nonpos.2 hα0'.le)
      _ = 2 ^ (α : ℝ) * r ^ (-(α : ℝ)) := by
          rw [div_eq_mul_inv, Real.mul_rpow hr.le (by norm_num),
            Real.inv_rpow (by norm_num), h2_rpow, mul_comm]
      _ ≤ 2 ^ (1 : ℝ) * r ^ (-(α : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two hα1')
            (by positivity)
      _ = 2 * r ^ (-(α : ℝ)) := by rw [Real.rpow_one]
  refine le_of_forall_pos_le_add_mul
    (B := C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) fun η hη ↦ ?_
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
  obtain ⟨hg_vol, hg_lp⟩ := memLp_volume_and_toReal_eLpNorm_le_add hbs_sub hη.le hf hg
  have hhold := (H hs0 (ha.mono_set hbs_sub) hLam' hv2.contDiffOn hv_abs hvg hg_vol).dist_le hxs hys
  rw [toReal_eLpNorm_volume_restrict (mu := mu), ENNReal.toReal_natCast] at hhold
  have hv_dist : dist (v x) (v y) ≤
      C₀ * s ^ (-(α : ℝ)) * (M + η + s * (α₀ ^ n⁻¹ *
        (eLpNorm g (Fintype.card ι) (mu.restrict (ball x₀ (2 * s)))).toReal) / lam) *
      dist x y ^ (α : ℝ) := by
    refine hhold.trans ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  have h1 : M + η ≤ max 1 (α₀ ^ n⁻¹) * (M + η) :=
    le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  have h2 : s * (α₀ ^ n⁻¹ *
      (eLpNorm g (Fintype.card ι) (mu.restrict (ball x₀ (2 * s)))).toReal) / lam ≤
      max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam) := by
    calc s * (α₀ ^ n⁻¹ *
            (eLpNorm g (Fintype.card ι) (mu.restrict (ball x₀ (2 * s)))).toReal) / lam
        ≤ r * (α₀ ^ n⁻¹ * (F + η)) / lam := by
          have : s ≤ r := hs_lt.le
          gcongr
      _ = α₀ ^ n⁻¹ * (r * (F + η) / lam) := by ring
      _ ≤ max 1 (α₀ ^ n⁻¹) * (r * (F + η) / lam) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hxK : x ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxs)
  have hyK : y ∈ closedBall x₀ (2 * s) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hys)
  have hdist_u : dist (ū x) (ū y) ≤ dist (v x) (v y) + 2 * η := by
    have htx := dist_triangle (ū x) (v x) (ū y)
    have hty := dist_triangle (v x) (v y) (ū y)
    have hdx : dist (ū x) (v x) ≤ η := by
      rw [dist_comm, Real.dist_eq]
      exact hvK x hxK
    have hdy : dist (v y) (ū y) ≤ η := by
      rw [Real.dist_eq]
      exact hvK y hyK
    linarith
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
          (C * r ^ (-(α : ℝ)) * (1 + r / lam) * dist x y ^ (α : ℝ) + 2) * η := by ring

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
