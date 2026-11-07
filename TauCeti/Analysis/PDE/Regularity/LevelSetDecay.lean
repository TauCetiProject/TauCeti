/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.DeGiorgi
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Decay of upper level sets of weak subsolutions (De Giorgi)

Let `u ∈ H¹(Ω)`, let `B_R = B(x₀, R) ⊆ Ω` and let `k < M` be levels such that the sublevel set
`{u ≤ k}` occupies at least a fixed proportion `θ > 0` of `B_R`. Along the levels
`kⱼ = M - (M - k)/2ʲ`, which rise from `k` to `M`, this file proves De Giorgi's **decay estimate
for upper level sets**

`√j · |{u ≥ kⱼ} ∩ B_R| ≤ C |B_R|`.

In particular `{u ≥ kⱼ}` occupies an arbitrarily small proportion of `B_R` once `j` is large.

The only property of `u` that enters is an energy bound for its truncations: for every level
`l ∈ [k, M)`,

`∫_{B_R} |∇(u - l)⁺|² ≤ Q R⁻² (M - l)² |B_R|`.

Under this hypothesis the estimate holds with the explicit constant `C = 2^{n+2} √Q / θ`
(`TauCeti.PDE.sqrt_mul_measureReal_le_mul_measureReal_ball_of_forall_setIntegral_le`). The bound
is scale invariant, and no equation appears in it. The proof combines it with De Giorgi's
isoperimetric inequality on `B_R` between the levels `kⱼ` and `kⱼ₊₁`, followed by the
Cauchy–Schwarz inequality on the strip `{kⱼ < u < kⱼ₊₁}`
(`TauCeti.W1p.sq_sub_mul_measureReal_mul_measureReal_le_of_ball_subset`). Together they give
`|{u ≥ kⱼ₊₁} ∩ B_R|² ≤ C² |B_R| |{kⱼ < u < kⱼ₊₁} ∩ B_R|`, and the strips are disjoint.

The energy bound holds for weak subsolutions with `u ≤ M` on `B(x₀, 2R)`: the Caccioppoli
inequality on the pair of balls `B_R ⊆ B_{2R}` bounds `∫_{B_R} |∇(u - l)⁺|²` by a multiple of
`R⁻² ∫_{B_{2R}} ((u - l)⁺)² ≤ R⁻² (M - l)² |B_{2R}|`. This gives the estimate

* for subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, with `C` depending only on `λ`, `Λ`, `θ` and the
  dimension (`TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`);
* for subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` with `‖b‖ ≤ β` and `c ≥ 0`, at levels
  `k ≥ 0`, with `C √(1 + (βR/λ)²)` in place of `C`
  (`TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball_lowerOrder`). The drift term
  of the Caccioppoli inequality is not invariant under dilations, which is why the constant
  depends on `βR/λ`; the sign condition on `c` and on the levels is what lets the mass term be
  dropped from it.

Combined with local boundedness
(`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral`), which turns smallness of
`{u ≥ kⱼ}` into a pointwise bound on a smaller ball, this is the step of De Giorgi's proof of
Hölder continuity that makes the oscillation of a weak solution decay from one ball to the next.

## Main declarations

* `TauCeti.PDE.sqrt_mul_measureReal_le_mul_measureReal_ball_of_forall_setIntegral_le`: the decay
  estimate for any `u ∈ H¹(Ω)` whose truncations satisfy the energy bound.
* `TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`: the decay estimate for weak
  subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`.
* `TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball_lowerOrder`: the decay
  estimate for weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` with `c ≥ 0`.

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

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- One step of De Giorgi's iteration: the De Giorgi isoperimetric inequality between the levels
`l < l'`, together with the energy bound at `l` and a lower density bound for `{u ≤ l}`, controls
the square of `|{u ≥ l'}|` by the measure of the strip `u ⁻¹' Ioo l l'`, when
`M - l = 2 (l' - l)`. -/
private theorem sq_measureReal_le_of_setIntegral_le
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M Q θ l l' : ℝ} (hR : 0 < R)
    (hball : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hθ : 0 < θ) (hQ : 0 ≤ Q)
    (hll' : l < l') (hM : M - l = 2 * (l' - l))
    (hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    (hE : ∫ x in ball x₀ R, ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hwl) x‖ ^ 2
      ∂mu ≤ Q * (M - l) ^ 2 / R ^ 2 * mu.real (ball x₀ R))
    (hθl : θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ l}) :
    (mu.restrict (ball x₀ R)).real {x | l' ≤ W1p.value u x} ^ 2 ≤
      (2 ^ (finrank ℝ (EuclideanSpace ℝ ι) + 2) * √Q / θ) ^ 2 * mu.real (ball x₀ R) *
        (mu.restrict (ball x₀ R)).real (W1p.value u ⁻¹' Ioo l l') := by
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set V := mu.real (ball x₀ R)
  have hVeq : V = R ^ n * mu.real (ball 0 1) := mu.addHaar_real_ball_of_pos x₀ hR
  have hV : 0 < V := by
    rw [hVeq]
    exact mul_pos (pow_pos hR n)
      (ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)
  have hiso := W1p.sq_sub_mul_measureReal_mul_measureReal_le_of_ball_subset hR.le hball u hll' hwl
  rw [show mu.real (ball 0 1) * (2 * R) ^ (n + 1) = 2 ^ (n + 1) * R * V by rw [hVeq]; ring]
    at hiso
  rw [hM] at hE
  have hh : 0 < l' - l := sub_pos.2 hll'
  set h := l' - l
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < θ ^ 2 * h ^ 2 * V ^ 2)
  calc _ = (h * (mu.restrict (ball x₀ R)).real {x | l' ≤ W1p.value u x} * (θ * V)) ^ 2 := by
        ring
    _ ≤ (h * (mu.restrict (ball x₀ R)).real {x | l' ≤ W1p.value u x} *
          (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ l}) ^ 2 := by gcongr
    _ ≤ (2 ^ (n + 1) * R * V) ^ 2 *
          (mu.restrict (ball x₀ R)).real (W1p.value u ⁻¹' Ioo l l') *
          (Q * (2 * h) ^ 2 / R ^ 2 * V) :=
        hiso.trans (mul_le_mul_of_nonneg_left hE (mul_nonneg (sq_nonneg _) measureReal_nonneg))
    _ = _ := by
        simp only [div_pow, mul_pow, Real.sq_sqrt hQ]
        field_simp
        ring


/-- **De Giorgi's decay of upper level sets.** Let `u ∈ H¹(Ω)`, let `B(x₀, R) ⊆ Ω` with `R > 0`,
let `k < M` with `(u - k)⁺ ∈ L²(Ω)`, and let `θ > 0` with
`|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Suppose that for every level `l ∈ [k, M)` the truncation
`(u - l)⁺` satisfies the energy bound

`∫_{B(x₀, R)} |∇(u - l)⁺|² ≤ Q R⁻² (M - l)² |B(x₀, R)|`.

Then for every `j`, with `n` the dimension,

`√j · |{u ≥ M - (M - k)/2ʲ} ∩ B(x₀, R)| ≤ 2^{n+2} √Q / θ · |B(x₀, R)|`.

The energy bound holds for weak subsolutions of elliptic equations in divergence form that are
bounded above by `M` on a larger ball, by the Caccioppoli inequality; it is the only property of
`u` used. The truncations are supplied through `TauCeti.W1p.posPartAboveOfMemLp`, which does not
depend on the `L²` proof passed to it. -/
theorem sqrt_mul_measureReal_le_mul_measureReal_ball_of_forall_setIntegral_le
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R k M Q θ : ℝ} (hR : 0 < R)
    (hball : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hkM : k < M) (hθ : 0 < θ)
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    (henergy : ∀ l, k ≤ l → l < M →
      ∀ hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega),
        ∫ x in ball x₀ R, ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
          Q * (M - l) ^ 2 / R ^ 2 * mu.real (ball x₀ R))
    (hθk : θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k})
    (J : ℕ) :
    √J * (mu.restrict (ball x₀ R)).real {x | M - (M - k) / 2 ^ J ≤ W1p.value u x} ≤
      2 ^ (finrank ℝ (EuclideanSpace ℝ ι) + 2) * √Q / θ * mu.real (ball x₀ R) := by
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set nu := mu.restrict (ball x₀ R)
  have : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set V := mu.real (ball x₀ R)
  set d := M - k
  have hd : 0 < d := sub_pos.2 hkM
  set lev : ℕ → ℝ := fun j => M - d / 2 ^ j
  set A : ℕ → ℝ := fun j => nu.real {x | lev j ≤ W1p.value u x}
  set D : ℕ → ℝ := fun j => nu.real (W1p.value u ⁻¹' Ioo (lev j) (lev (j + 1)))
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos mu x₀ hR).ne' measure_ball_lt_top.ne
  -- The energy bound at the level `k` forces `Q ≥ 0`.
  have hQ : 0 ≤ Q := by
    have h0 := (integral_nonneg fun x => sq_nonneg _).trans (henergy k le_rfl hkM hwLp)
    exact nonneg_of_mul_nonneg_left (by simpa only [mul_div_assoc, mul_assoc] using h0)
      (by positivity)
  set K : ℝ := (2 ^ (n + 2) * √Q / θ) ^ 2
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
  have hstep : ∀ j, A (j + 1) ^ 2 ≤ K * V * D j := fun j => by
    have hwj := W1p.memLp_posPartAbove_of_le u (hk_le j) hwLp
    exact sq_measureReal_le_of_setIntegral_le hR hball hθ hQ
      (by rw [← sub_pos, hlev_succ]; positivity) (by rw [hlev_succ]; simp only [lev]; ring) hwj
      (henergy _ (hk_le j) (by simp only [lev]; exact sub_lt_self _ (by positivity)) hwj)
      (hθk.trans (measureReal_mono fun x (hx : W1p.value u x ≤ k) => hx.trans (hk_le j)))
  -- Sum the steps over the pairwise disjoint strips.
  have hDsum : ∑ j ∈ Finset.range J, D j ≤ V :=
    (sum_measureReal_le_measureReal_univ
      (fun j _ => (Lp.stronglyMeasurable _).measurable measurableSet_Ioo)
      fun i _ j _ hij => (hlev_mono.pairwise_disjoint_on_Ioo_succ hij).preimage _).trans_eq
      (measureReal_restrict_apply_univ _)
  have hA_anti : ∀ {i j : ℕ}, i ≤ j → A j ≤ A i := fun hij =>
    measureReal_mono fun x (hx : lev _ ≤ W1p.value u x) => (hlev_mono hij).trans hx
  have hsq : (J : ℝ) * A J ^ 2 ≤ K * V ^ 2 :=
    calc (J : ℝ) * A J ^ 2 = ∑ _ ∈ Finset.range J, A J ^ 2 := by simp
      _ ≤ ∑ j ∈ Finset.range J, A (j + 1) ^ 2 := Finset.sum_le_sum fun j hj =>
          pow_le_pow_left₀ measureReal_nonneg (hA_anti (Finset.mem_range.1 hj)) 2
      _ ≤ ∑ j ∈ Finset.range J, K * V * D j := Finset.sum_le_sum fun j _ => hstep j
      _ = K * V * ∑ j ∈ Finset.range J, D j := by rw [Finset.mul_sum]
      _ ≤ K * V * V := mul_le_mul_of_nonneg_left hDsum (by positivity)
      _ = K * V ^ 2 := by ring
  calc √J * A J = √(J * A J ^ 2) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq measureReal_nonneg]
    _ ≤ √(K * V ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 ^ (n + 2) * √Q / θ * V := by
        rw [← mul_pow, Real.sqrt_sq (by positivity)]

/-- If `u ≤ M` almost everywhere on `B(x₀, 2R)`, a bound of `E` by `K` times the `L²` mass of
`(u - l)⁺` on `B(x₀, 2R)`, which is the form the Caccioppoli inequality on
`B(x₀, R) ⊆ B(x₀, 2R)` takes, gives the bound `Q R⁻² (M - l)² |B(x₀, R)|` with `Q = 2ⁿ K R²`. -/
private theorem le_mul_sq_div_sq_mul_measureReal_ball_of_le_mul_setIntegral
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R l M K E : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hlM : l ≤ M) (hM : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M)
    (hE : E ≤ K * ∫ x in ball x₀ (2 * R), max (W1p.value u x - l) 0 ^ 2 ∂mu) :
    E ≤ 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * K * R ^ 2 * (M - l) ^ 2 / R ^ 2 *
      mu.real (ball x₀ R) := by
  have hsup : ∫ x in ball x₀ (2 * R), max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      (M - l) ^ 2 * mu.real (ball x₀ (2 * R)) :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const_ae measure_ball_lt_top (by
      filter_upwards [hM] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by linarith)) 2))
  refine hE.trans ((mul_le_mul_of_nonneg_left hsup hK).trans_eq ?_)
  rw [mu.addHaar_real_ball_of_pos x₀ (by positivity), mu.addHaar_real_ball_of_pos x₀ hR]
  field_simp
  ring

variable [DecidableEq ι]

/-- **Decay of upper level sets of weak subsolutions (De Giorgi).** Fix ellipticity constants
`λ, Λ` and a proportion `θ > 0`. There is `C > 0`, depending only on these and the dimension,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0`
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
  obtain ⟨c, hc0, hcacc⟩ := exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le (ι := ι)
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  refine ⟨2 ^ (n + 2) * √((1 + (2 * Lam / lam) ^ 2) * c ^ 2 * 2 ^ n) / θ, by positivity, ?_⟩
  intro mu _ Omega a u x₀ R k M h ha hu hR hball hkM hwLp hM hθk j
  refine (sqrt_mul_measureReal_le_mul_measureReal_ball_of_forall_setIntegral_le
    (Q := (2 * Lam / lam) ^ 2 * c ^ 2 * 2 ^ n) hR ((ball_subset_ball (by linarith)).trans hball)
    hkM hθ hwLp (fun l hkl hlM hl => ?_) hθk j).trans ?_
  · -- Caccioppoli on `B_R ⊆ B_{2R}`, followed by the bound `(u - l)⁺ ≤ M - l` on `B_{2R}`.
    have henergy := hcacc hl h ha hu hR (by linarith : R < 2 * R) hball
    rw [(by ring : 2 * R - R = R)] at henergy
    refine (le_mul_sq_div_sq_mul_measureReal_ball_of_le_mul_setIntegral hR (by positivity) hlM.le
      hM henergy).trans_eq ?_
    field_simp
    ring
  · gcongr
    nlinarith [sq_nonneg (2 * Lam / lam)]

/-- **Decay of upper level sets of weak subsolutions with lower-order terms (De Giorgi).** Fix
ellipticity constants `λ, Λ` and a proportion `θ > 0`. There is `C > 0`, depending only on these
and the dimension, such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on
`Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`, that is
`a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with drift
`b` and mass coefficient `c`. Let `B(x₀, 2R) ⊆ Ω` and levels `0 ≤ k < M` be such that `u ≤ M`
almost everywhere on `B(x₀, 2R)` and `|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Then for every `j`,

`√j · |{u ≥ M - (M - k)/2ʲ} ∩ B(x₀, R)| ≤ C √(1 + (βR/λ)²) |B(x₀, R)|`.

The constant is independent of `R`, `β`, `γ` and the additive Haar measure `μ`; the radius enters
only through `βR/λ`. The sign conditions `c ≥ 0` and `k ≥ 0` make the mass term `c u (u - l)⁺`
nonnegative at every level `l ≥ k`. -/
theorem exists_sqrt_mul_measureReal_le_mul_measureReal_ball_lowerOrder {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {beta gamma : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R k M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 0 ≤ k → k < M →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k} →
      ∀ j : ℕ, √j * (mu.restrict (ball x₀ R)).real {x | M - (M - k) / 2 ^ j ≤ W1p.value u x} ≤
        C * √(1 + (beta * R / lam) ^ 2) * mu.real (ball x₀ R) := by
  obtain ⟨C₀, hC₀, hcacc⟩ :=
    exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_lowerOrder (ι := ι)
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set X : ℝ := 2 * (2 * Lam / lam) ^ 2 * C₀ ^ 2
  refine ⟨2 ^ (n + 2) * √((X + 4) * 2 ^ n) / θ, by positivity, ?_⟩
  intro mu _ Omega a b c beta gamma u x₀ R k M h ha hb hc hb_bound hc_bound hc_nonneg hu hR hball
    hk hkM hM hθk j
  set y : ℝ := (beta * R / lam) ^ 2
  refine (sqrt_mul_measureReal_le_mul_measureReal_ball_of_forall_setIntegral_le
    (Q := (X + 4 * y) * 2 ^ n) hR ((ball_subset_ball (by linarith)).trans hball) hkM hθ
    (W1p.memLp_posPartAbove hk u) (fun l hkl hlM hl => ?_) hθk j).trans ?_
  · -- Caccioppoli on `B_R ⊆ B_{2R}`, followed by the bound `(u - l)⁺ ≤ M - l` on `B_{2R}`.
    have hl0 : 0 ≤ l := hk.trans hkl
    have henergy := hcacc hl0 h ha hb hc hb_bound hc_bound hc_nonneg hu hR
      (by linarith : R < 2 * R) hball
    rw [(by ring : 2 * R - R = R),
      W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) hl0 u hl |>.symm] at henergy
    refine (le_mul_sq_div_sq_mul_measureReal_ball_of_le_mul_setIntegral hR (by positivity) hlM.le
      hM henergy).trans_eq ?_
    simp only [X, y]
    field_simp
    ring
  · -- `X + 4y ≤ (X + 4)(1 + y)`, since `X, y ≥ 0`.
    have hX : 0 ≤ X := by positivity
    have hy : 0 ≤ y := by positivity
    have hQ : (X + 4 * y) * 2 ^ n ≤ (X + 4) * 2 ^ n * (1 + y) := by
      nlinarith [mul_nonneg hX hy, pow_pos (two_pos : (0 : ℝ) < 2) n]
    calc 2 ^ (n + 2) * √((X + 4 * y) * 2 ^ n) / θ * mu.real (ball x₀ R)
        ≤ 2 ^ (n + 2) * √((X + 4) * 2 ^ n * (1 + y)) / θ * mu.real (ball x₀ R) := by
          gcongr
      _ = 2 ^ (n + 2) * √((X + 4) * 2 ^ n) / θ * √(1 + y) * mu.real (ball x₀ R) := by
          rw [Real.sqrt_mul (by positivity)]
          ring

end PDE

end TauCeti
