/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.DeGiorgi
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Decay of upper level sets of weak subsolutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`. Suppose that on a ball
`B(x₀, 2R) ⊆ Ω` we have `u ≤ M`, and that on the concentric ball `B_R = B(x₀, R)` the sublevel
set `{u ≤ k}` occupies at least a fixed proportion `θ > 0` of `B_R`, for some level `k < M`.
Along the levels `kⱼ = M - (M - k)/2ʲ`, which rise from `k` to `M`, this file proves De Giorgi's
**decay estimate for upper level sets**

`√j · |{u ≥ kⱼ} ∩ B_R| ≤ C |B_R|`,

with `C` depending only on `λ`, `Λ`, `θ` and the dimension. In particular `{u ≥ kⱼ}` occupies an
arbitrarily small proportion of `B_R` once `j` is large.

The proof combines three estimates for the truncations `(u - kⱼ)⁺`: the Caccioppoli inequality
on the pair of balls `B_R ⊆ B_{2R}`
(`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le`), which bounds
`∫_{B_R} |∇(u - kⱼ)⁺|²` by `R⁻² (M - kⱼ)² |B_{2R}|`; De Giorgi's isoperimetric inequality on
`B_R` between the levels `kⱼ` and `kⱼ₊₁`, followed by the Cauchy–Schwarz inequality on the strip
`{kⱼ < u < kⱼ₊₁}` (`TauCeti.W1p.sq_sub_mul_measureReal_mul_measureReal_le_of_ball_subset`).
Together they give
`|{u ≥ kⱼ₊₁} ∩ B_R|² ≤ C² |B_R| |{kⱼ < u < kⱼ₊₁} ∩ B_R|`, and the strips are disjoint.

Combined with local boundedness
(`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral`), which turns smallness of
`{u ≥ kⱼ}` into a pointwise bound on a smaller ball, this is the step of De Giorgi's proof of
Hölder continuity that makes the oscillation of a weak solution decay from one ball to the next.

## Main declarations

* `TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`: the decay estimate.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* L. Caffarelli, A. Vasseur, *The De Giorgi method for regularity of solutions of elliptic
  equations and its applications to fluid dynamics*, Discrete Contin. Dyn. Syst. Ser. S (2010).
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- Caccioppoli on `B_R ⊆ B_{2R}`, followed by the bound `(u - k)⁺ ≤ M - k` coming from
`u ≤ M` almost everywhere on the larger ball. -/
private theorem exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_of_ae_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R k M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → k ≤ M →
      (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      ∫ x in ball x₀ R,
          ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) k u hwLp) x‖ ^ 2 ∂mu ≤
        (2 * Lam / lam) ^ 2 * (c / R) ^ 2 *
          ((M - k) ^ 2 * mu.real (ball x₀ (2 * R))) := by
  obtain ⟨c, hc0, hcacc⟩ := exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le (ι := ι)
  refine ⟨c, hc0, ?_⟩
  intro mu _ Omega a lam Lam u x₀ R k M h ha hu hR hball hkM hwLp hM
  have henergy := hcacc hwLp h ha hu hR (by linarith : R < 2 * R) hball
  rw [(by ring : 2 * R - R = R)] at henergy
  refine henergy.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (setIntegral_mono_ae_restrict (g := fun _ => (M - k) ^ 2)
    (IntegrableOn.mono_set hwLp.integrable_sq hball)
    (integrableOn_const measure_ball_lt_top.ne) ?_).trans_eq (by
      rw [setIntegral_const, smul_eq_mul, mul_comm])
  filter_upwards [hM] with x hx
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le (sub_le_sub_right hx k) (sub_nonneg.2 hkM)) 2

/-- **Decay of upper level sets of weak subsolutions (De Giorgi).** Fix ellipticity constants
`λ, Λ` and a proportion `θ > 0`. There is `C > 0`, depending only on these and the dimension,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0`
for every nonnegative `v ∈ H¹₀(Ω)`. Let `B(x₀, 2R) ⊆ Ω` and levels `k < M` be such that
`(u - k)⁺ ∈ L²(Ω)`, `u ≤ M` almost everywhere on `B(x₀, 2R)`, and
`|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Then for every `j`,

`√j · |{u ≥ M - (M - k)/2ʲ} ∩ B(x₀, R)| ≤ C |B(x₀, R)|`.

The constant is independent of `R` and of the additive Haar measure `μ`. No regularity of the
coefficients beyond measurability is assumed. -/
theorem exists_sqrt_mul_measureReal_le_mul_measureReal_ball {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R k M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → k < M →
      MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k} →
      ∀ j : ℕ, √j * (mu.restrict (ball x₀ R)).real {x | M - (M - k) / 2 ^ j ≤ W1p.value u x} ≤
        C * mu.real (ball x₀ R) := by
  obtain ⟨c, hc0, henergy⟩ :=
    exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_of_ae_le (ι := ι)
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set K : ℝ := 2 ^ (3 * n + 4) * (1 + (2 * Lam / lam) ^ 2) * c ^ 2 / θ ^ 2
  have hK : 0 < K := by positivity
  refine ⟨√K, Real.sqrt_pos.2 hK, ?_⟩
  intro mu _ Omega a u x₀ R k M h ha hu hR hball hkM hwLp hM hθk J
  set nu := mu.restrict (ball x₀ R)
  have : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set V := mu.real (ball x₀ R)
  set d := M - k
  have hd : 0 < d := sub_pos.2 hkM
  set lev : ℕ → ℝ := fun j => M - d / 2 ^ j
  set A : ℕ → ℝ := fun j => nu.real {x | lev j ≤ W1p.value u x}
  set D : ℕ → ℝ := fun j => nu.real {x | lev j < W1p.value u x ∧ W1p.value u x < lev (j + 1)}
  have hballR : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball
  -- Scaling of the balls: `|B(x₀, ρ)| = ρⁿ μ(B(0, 1))`.
  have hVeq : V = R ^ n * mu.real (ball 0 1) := mu.addHaar_real_ball_of_pos x₀ hR
  have hV2 : mu.real (ball x₀ (2 * R)) = 2 ^ n * V := by
    rw [mu.addHaar_real_ball_of_pos x₀ (by positivity), hVeq]
    ring
  have hV : 0 < V := by
    rw [hVeq]
    exact mul_pos (pow_pos hR n)
      (ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)
  have hω : mu.real (ball 0 1) * (2 * R) ^ (n + 1) = 2 ^ (n + 1) * R * V := by
    rw [hVeq]
    ring
  -- The levels increase from `k` to `M`.
  have hlev_mono : Monotone lev := fun i j hij => by
    simp only [lev]
    gcongr
    · exact one_le_two
  have hk_le : ∀ j, k ≤ lev j := fun j => by
    simpa [lev, d] using hlev_mono (Nat.zero_le j)
  have hlev_succ : ∀ j, lev (j + 1) - lev j = d / 2 ^ j / 2 := fun j => by
    simp only [lev, pow_succ]
    field_simp
    ring
  -- One step: `A (j + 1)² ≤ K V D j`.
  have hstep : ∀ j, A (j + 1) ^ 2 ≤ K * V * D j := by
    intro j
    have hlt : lev j < lev (j + 1) := by
      rw [← sub_pos, hlev_succ]
      positivity
    have hwj : MemLp (fun x => max (W1p.value u x - lev j) 0) 2 (mu.restrict Omega) :=
      W1p.memLp_posPartAbove_of_le u (hk_le j) hwLp
    set w := W1p.posPartAboveOfMemLp (by norm_num) (lev j) u hwj
    -- The energy of the truncation on `B_R`, from Caccioppoli on `B_R ⊆ B_{2R}`.
    have hE : ∫ x in ball x₀ R, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
        (2 * Lam / lam) ^ 2 * (c / R) ^ 2 * ((d / 2 ^ j) ^ 2 * (2 ^ n * V)) := by
      have hdj : M - lev j = d / 2 ^ j := by simp [lev]
      have hlevM : lev j ≤ M := by
        simp only [lev]
        exact sub_le_self _ (by positivity)
      simpa only [w, hdj, hV2] using henergy h ha hu hR hball hlevM hwj hM
    have hθj : θ * V ≤ nu.real {x | W1p.value u x ≤ lev j} :=
      hθk.trans (measureReal_mono fun x (hx : W1p.value u x ≤ k) =>
        hx.trans (hk_le j))
    have hiso := W1p.sq_sub_mul_measureReal_mul_measureReal_le_of_ball_subset hR.le hballR u hlt hwj
    rw [hlev_succ, hω] at hiso
    have hpos : 0 < θ ^ 2 * (d / 2 ^ j / 2) ^ 2 * V ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    calc A (j + 1) ^ 2 * (θ ^ 2 * (d / 2 ^ j / 2) ^ 2 * V ^ 2)
        = (d / 2 ^ j / 2 * A (j + 1) * (θ * V)) ^ 2 := by ring
      _ ≤ (d / 2 ^ j / 2 * A (j + 1) * nu.real {x | W1p.value u x ≤ lev j}) ^ 2 := by gcongr
      _ ≤ (2 ^ (n + 1) * R * V) ^ 2 * D j *
            ((2 * Lam / lam) ^ 2 * (c / R) ^ 2 * ((d / 2 ^ j) ^ 2 * (2 ^ n * V))) :=
          hiso.trans (mul_le_mul_of_nonneg_left hE (mul_nonneg (sq_nonneg _) measureReal_nonneg))
      _ = 2 ^ (3 * n + 4) * (2 * Lam / lam) ^ 2 * c ^ 2 / θ ^ 2 * V * D j *
            (θ ^ 2 * (d / 2 ^ j / 2) ^ 2 * V ^ 2) := by
          field_simp
          ring
      _ ≤ K * V * D j * (θ ^ 2 * (d / 2 ^ j / 2) ^ 2 * V ^ 2) := by
          have hKle : 2 ^ (3 * n + 4) * (2 * Lam / lam) ^ 2 * c ^ 2 / θ ^ 2 ≤ K := by
            simp only [K]
            gcongr
            linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKle hV.le) measureReal_nonneg) hpos.le
  -- Sum the steps over the pairwise disjoint strips.
  have hm : Measurable (W1p.value u : EuclideanSpace ℝ ι → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have hA_anti : ∀ {i j : ℕ}, i ≤ j → A j ≤ A i := fun hij =>
    measureReal_mono fun x (hx : lev _ ≤ W1p.value u x) =>
      (hlev_mono hij).trans hx
  have hDsum : ∑ j ∈ Finset.range J, D j ≤ V := by
    refine (sum_measureReal_le_measureReal_univ (fun j _ =>
      (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const))
        ?_).trans_eq (measureReal_restrict_apply_univ _)
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    simp only [mem_ofPred_eq] at hi1 hi2 hj1 hj2
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · linarith [hlev_mono (by omega : i + 1 ≤ j)]
    · linarith [hlev_mono (by omega : j + 1 ≤ i)]
  have hsq : (J : ℝ) * A J ^ 2 ≤ K * V ^ 2 :=
    calc (J : ℝ) * A J ^ 2 = ∑ _ ∈ Finset.range J, A J ^ 2 := by simp
      _ ≤ ∑ j ∈ Finset.range J, A (j + 1) ^ 2 := Finset.sum_le_sum fun j hj =>
          pow_le_pow_left₀ measureReal_nonneg
            (hA_anti (Finset.mem_range.1 hj)) 2
      _ ≤ ∑ j ∈ Finset.range J, K * V * D j := Finset.sum_le_sum fun j _ => hstep j
      _ = K * V * ∑ j ∈ Finset.range J, D j := by rw [Finset.mul_sum]
      _ ≤ K * V * V := mul_le_mul_of_nonneg_left hDsum (by positivity)
      _ = K * V ^ 2 := by ring
  calc √J * A J = √(J * A J ^ 2) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq measureReal_nonneg]
    _ ≤ √(K * V ^ 2) := Real.sqrt_le_sqrt hsq
    _ = √K * V := by rw [Real.sqrt_mul hK.le, Real.sqrt_sq hV.le]

end PDE

end TauCeti
