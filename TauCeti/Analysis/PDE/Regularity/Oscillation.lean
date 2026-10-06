/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.LevelSetDecay
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness
import Mathlib.Analysis.SpecialFunctions.Log.Base
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Oscillation decay for weak solutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ`, `n ≥ 3`, with constants `0 < λ ≤ Λ`.
This file proves the two steps of De Giorgi's proof of Hölder continuity that turn the measure
estimates for level sets into a pointwise gain on a smaller ball.

* **Reduction of the supremum.** Let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0` with
  `u ≤ M` on `B(x₀, 2R) ⊆ Ω`, and suppose the sublevel set `{u ≤ k}` occupies at least a
  proportion `θ > 0` of `B(x₀, R)`. Then `u ≤ M - δ (M - k)` on `B(x₀, R/2)`, where `δ ∈ (0, 1)`
  depends only on `λ`, `Λ`, `θ`, the dimension and the normalization of the Haar measure.
* **Oscillation decay.** If `u` is a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0` with `m ≤ u ≤ M` on
  `B(x₀, 2R)`, then on `B(x₀, R/2)` either `u ≤ M - δ (M - m)` or `u ≥ m + δ (M - m)`. Either
  way the oscillation of `u` drops from `M - m` to at most `(1 - δ)(M - m)`.
* **Power-law decay.** Iterating over the balls `B(x₀, R / 4ʲ)`, the oscillation of a weak
  solution on `B(x₀, R / 4ʲ)` is at most `(1 - δ)ʲ` times its oscillation on `B(x₀, R)`, hence
  at most `C (r / R)^α` times it on `B(x₀, r)` for every `0 < r ≤ R`, with `0 < α ≤ 1` and `C`
  depending only on `λ`, `Λ`, the dimension and the Haar normalization.
* **Interior oscillation estimate.** Combined with De Giorgi's local boundedness theorem, the
  oscillation of a weak solution on `B(x₀, r)`, `r ≤ R/2`, is at most
  `C (r / R)^α R^{-n/2} ‖u‖_{L²(B(x₀, R))}` whenever `B(x₀, R) ⊆ Ω`.

The reduction of the supremum combines De Giorgi's decay of upper level sets
(`TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`) with local boundedness above
a level (`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`):
along the levels `kⱼ = M - (M - k)/2ʲ`, the set `{u ≥ kⱼ}` occupies a proportion `O(j^{-1/2})` of
`B(x₀, R)`, so the `L²` mass of `(u - kⱼ)⁺` there is `O((M - kⱼ)² j^{-1/2} Rⁿ)`, and local
boundedness gives `u ≤ kⱼ + (M - kⱼ)/2` on `B(x₀, R/2)` once `j` is large. Oscillation decay
applies this to `u` or to `-u` at the mid level `(m + M)/2`, whichever sublevel set fills at least
half of `B(x₀, R)`. The power-law decay is the a-priori estimate behind the interior Hölder
continuity of weak solutions: a function whose essential oscillation on balls decays like a power
of the radius agrees almost everywhere with a Hölder continuous function.

Oscillation is tracked through explicit a.e. bounds: `u` takes values in an interval `[m', m' + L]`
almost everywhere on a ball, rather than through an essential oscillation functional.

## Main declarations

* `TauCeti.PDE.exists_ae_value_le_sub_mul_sub`: the reduction of the supremum.
* `TauCeti.PDE.exists_ae_value_le_sub_mul_sub_or_add_mul_sub_le`: oscillation decay.
* `TauCeti.PDE.exists_ae_value_mem_Icc_add_pow_mul_sub`: geometric decay of the oscillation
  along the balls `B(x₀, R / 4ʲ)`.
* `TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub`: the power law
  `osc(B(x₀, r)) ≤ C (r / R)^α osc(B(x₀, R))`.
* `TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral`: the interior
  oscillation estimate in terms of the `L²` norm.

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
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **Reduction of the supremum (De Giorgi).** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`), and fix a proportion
`θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Let
`B(x₀, 2R) ⊆ Ω` and levels `k ≤ M` be such that `u ≤ M` almost everywhere on `B(x₀, 2R)` and
`|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Then

`u ≤ M - δ (M - k)` almost everywhere on `B(x₀, R/2)`.

No regularity of the coefficients beyond measurability is assumed. -/
theorem exists_ae_value_le_sub_mul_sub {pstar : ℝ≥0∞} (hpstar : pstar ≠ (∞ : ℝ≥0∞))
    (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R k M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → k ≤ M →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k} →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ≤ M - δ * (M - k) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_sqrt_mul_measureReal_le_mul_measureReal_ball (ι := ι) (lam := lam) (Lam := Lam) hθ
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv (mu := mu)
      (lam := lam) (Lam := Lam) hpstar hexp
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  -- After `j` steps of the level-set decay, local boundedness halves the remaining gap.
  set j : ℕ := ⌈(4 * D ^ 2 * C * ω) ^ 2⌉₊
  have hj : 4 * D ^ 2 * C * ω ≤ √j :=
    (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).2 (Nat.le_ceil _)
  have hjpos : 0 < √(j : ℝ) := lt_of_lt_of_le (by positivity) hj
  refine ⟨1 / 2 ^ (j + 1), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ one_lt_two (Nat.succ_ne_zero j)
  intro Omega a u x₀ R k M h ha hu hR hball hkM hM hθk
  have hhalf : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  rcases hkM.eq_or_lt with rfl | hkM
  · -- Equal levels: the bound is the hypothesis `u ≤ k`.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalf hM] with x hx
    simpa using hx
  set l := M - (M - k) / 2 ^ j
  have hlM : l ≤ M := sub_le_self _ (by positivity)
  have hballR : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball
  -- The upper level set `{u ≥ l}` is small, by the decay estimate. It is applied to the
  -- restriction of `u` to `U = B(x₀, 2R)`, which has finite measure, so that `(u - k)⁺` is square
  -- integrable on `U`.
  set V := mu.real (ball x₀ R)
  set A := (mu.restrict (ball x₀ R)).real {x | l ≤ W1p.value u x}
  have hA : √j * A ≤ C * V := by
    set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (2 * R), isOpen_ball⟩
    have hU : U ≤ Omega := hball
    have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    set w := W1p.restrictL hU u
    have hw : W1p.value w =ᵐ[mu.restrict (ball x₀ (2 * R))] W1p.value u :=
      W1p.value_restrictL_ae hU u
    have hlev : ∀ p : ℝ → Prop, (mu.restrict (ball x₀ R)).real {x | p (W1p.value w x)} =
        (mu.restrict (ball x₀ R)).real {x | p (W1p.value u x)} := fun p => by
      refine measureReal_congr (Filter.eventuallyEqSet_iff.2 ?_)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hw]
        with x hx
      rw [hx]
    have hMw : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value w x ≤ M := by
      filter_upwards [hM, hw] with x hx hwx
      rwa [hwx]
    have hdw := hdecay (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (energyFormH1_restrictL_nonpos hU hu) hR subset_rfl hkM
      ((Lp.memLp _).sub (memLp_const k)).pos_part hMw ((hlev (· ≤ k)).symm ▸ hθk) j
    rwa [hlev (M - (M - k) / 2 ^ j ≤ ·)] at hdw
  -- Hence so is the `L²` mass of `(u - l)⁺` on `B(x₀, R)`.
  set I := ∫ x in ball x₀ R, max (W1p.value u x - l) 0 ^ 2 ∂mu
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hI : I ≤ (M - l) ^ 2 * A :=
    MeasureTheory.integral_max_sub_sq_le_mul_measureReal (Lp.stronglyMeasurable _).measurable
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hM)
  -- The scale factor of local boundedness cancels the volume of the ball.
  set P := R ^ (-(Fintype.card ι : ℝ) / 2)
  have hPV : P ^ 2 * V = ω := by
    have hP : P ^ 2 = (R ^ Fintype.card ι)⁻¹ := by
      rw [← Real.rpow_natCast P, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R,
        ← Real.rpow_neg hR.le]
      ring_nf
    have hV : V = R ^ finrank ℝ (EuclideanSpace ℝ ι) * ω := mu.addHaar_real_ball_of_pos x₀ hR
    rw [hP, hV, finrank_euclideanSpace,
      inv_mul_cancel_left₀ (pow_pos hR _).ne']
  have hP0 : 0 < P := Real.rpow_pos_of_pos hR _
  have hDPA : D * P * √A ≤ 1 / 2 := by
    have hsq : (D * P * √A) ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt measureReal_nonneg]
      refine le_of_mul_le_mul_left ?_ hjpos
      calc √j * ((D * P) ^ 2 * A) = D ^ 2 * P ^ 2 * (√j * A) := by ring
        _ ≤ D ^ 2 * P ^ 2 * (C * V) := by gcongr
        _ = D ^ 2 * C * ω := by rw [← hPV]; ring
        _ ≤ √j * (1 / 2) ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 hsq
  have hgap : D * P * √I ≤ (M - l) / 2 :=
    calc D * P * √I ≤ D * P * √((M - l) ^ 2 * A) := by gcongr
      _ = (M - l) * (D * P * √A) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.2 hlM)]
        ring
      _ ≤ (M - l) * (1 / 2) := mul_le_mul_of_nonneg_left hDPA (sub_nonneg.2 hlM)
      _ = (M - l) / 2 := by ring
  -- Local boundedness above the level `l`.
  filter_upwards [hbound (k := l) h ha hu hR hballR] with x hx
  calc W1p.value u x ≤ l + D * P * √I := hx
    _ ≤ l + (M - l) / 2 := by linarith
    _ = M - 1 / 2 ^ (j + 1) * (M - k) := by
        simp only [l, pow_succ]
        field_simp
        ring

/-- **Oscillation decay for weak solutions (De Giorgi).** Let `2*` be the Sobolev exponent of
`W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There
is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, the dimension and the normalization of the additive
Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`, that is
`a(u, v) = 0` for every `v ∈ H¹₀(Ω)`. Let `B(x₀, 2R) ⊆ Ω` and `m, M` be such that
`m ≤ u ≤ M` almost everywhere on `B(x₀, 2R)`. Then almost everywhere on `B(x₀, R/2)`, either

`u ≤ M - δ (M - m)` throughout, or `m + δ (M - m) ≤ u` throughout.

In particular the essential oscillation of `u` on `B(x₀, R/2)` is at most `(1 - δ)(M - m)`. -/
theorem exists_ae_value_le_sub_mul_sub_or_add_mul_sub_le {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R m M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), m ≤ W1p.value u x ∧ W1p.value u x ≤ M) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ≤ M - δ * (M - m)) ∨
        ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), m + δ * (M - m) ≤ W1p.value u x := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨δ / 2, by positivity, by linarith, ?_⟩
  intro Omega a u x₀ R m M h ha hu hR hball hmM'
  have hmM : m ≤ M := by
    have : (ae (mu.restrict (ball x₀ (2 * R)))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₀ (by linarith)).ne'
    obtain ⟨x, hx⟩ := hmM'.exists
    exact hx.1.trans hx.2
  set k := (m + M) / 2
  have hmk : m ≤ k := by simp only [k]; linarith
  have hkM : k ≤ M := by simp only [k]; linarith
  have hballR : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hm : Measurable (W1p.value u : EuclideanSpace ℝ ι → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  by_cases hθ : 1 / 2 * mu.real (ball x₀ R) ≤
      (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k}
  · -- `{u ≤ k}` fills half of the ball: the supremum drops.
    left
    filter_upwards [hred h ha (fun v _ => (hu v).le) hR hball hkM
      (by filter_upwards [hmM'] with x hx using hx.2) hθ] with x hx
    calc W1p.value u x ≤ M - δ * (M - k) := hx
      _ = M - δ / 2 * (M - m) := by simp only [k]; ring
  · -- Otherwise `{u ≥ k}` fills half of the ball: the infimum rises, by the same argument
    -- applied to the subsolution `-u`.
    right
    have hneg : ⇑(W1p.value (-u)) =ᵐ[mu.restrict Omega] -W1p.value u := by
      simpa only [← W1p.valueL_apply, map_neg] using Lp.coeFn_neg (W1p.value u)
    have hu' : ∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 (-u) (v : W1p mu Omega 2) ≤ 0 := fun v _ => by
      rw [← neg_one_smul ℝ u, energyFormH1_smul_left, hu v, mul_zero]
    have hM' : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value (-u) x ≤ -m := by
      filter_upwards [hmM', ae_restrict_of_ae_restrict_of_subset hball hneg] with x hx hxn
      rw [hxn, Pi.neg_apply, neg_le_neg_iff]
      exact hx.1
    have hθ' : 1 / 2 * mu.real (ball x₀ R) ≤
        (mu.restrict (ball x₀ R)).real {x | W1p.value (-u) x ≤ -k} := by
      have hS : MeasurableSet {x | W1p.value u x ≤ k} := measurableSet_le hm measurable_const
      have hcompl := measureReal_add_measureReal_compl (μ := mu.restrict (ball x₀ R)) hS
      rw [measureReal_restrict_apply_univ] at hcompl
      have hset : {x | W1p.value (-u) x ≤ -k} =ᵐ[mu.restrict (ball x₀ R)]
          {x | k ≤ W1p.value u x} := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hballR hneg] with x hxn
        simp only [hxn, Pi.neg_apply, neg_le_neg_iff]
      have hsub : (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k}ᶜ ≤
          (mu.restrict (ball x₀ R)).real {x | W1p.value (-u) x ≤ -k} := by
        rw [measureReal_congr hset]
        exact measureReal_mono fun x (hx : ¬W1p.value u x ≤ k) => (not_le.1 hx).le
      linarith
    filter_upwards [hred h ha hu' hR hball (neg_le_neg hmk) hM' hθ',
      ae_restrict_of_ae_restrict_of_subset ((ball_subset_ball (by linarith)).trans hball) hneg]
      with x hx hxn
    rw [hxn, Pi.neg_apply] at hx
    calc m + δ / 2 * (M - m) = m + δ * (k - m) := by simp only [k]; ring
      _ ≤ W1p.value u x := by linarith

/-- **Iterated oscillation decay (De Giorgi).** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There is
`δ ∈ (0, 1)`, depending only on `λ`, `Λ`, the dimension and the normalization of the additive
Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. If
`B(x₀, R) ⊆ Ω` and `u ∈ [m, M]` almost everywhere on `B(x₀, R)`, then for every `j`, almost
everywhere on `B(x₀, R / 4ʲ)` the function `u` takes values in an interval of length
`(1 - δ)ʲ (M - m)`. -/
theorem exists_ae_value_mem_Icc_add_pow_mul_sub {pstar : ℝ≥0∞} (hpstar : pstar ≠ (∞ : ℝ≥0∞))
    (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R m M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), W1p.value u x ∈ Icc m M) →
      ∀ j : ℕ, ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ (R / 4 ^ j)),
        W1p.value u x ∈ Icc m' (m' + (1 - δ) ^ j * (M - m)) := by
  obtain ⟨δ, hδ0, hδ1, hdecay⟩ :=
    exists_ae_value_le_sub_mul_sub_or_add_mul_sub_le (mu := mu) (lam := lam) (Lam := Lam)
      hpstar hexp
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Omega a u x₀ R m M h ha hu hR hball hmM j
  induction j with
  | zero => exact ⟨m, by simpa using hmM⟩
  | succ j ih =>
    obtain ⟨m', hm'⟩ := ih
    -- One step of oscillation decay on `B(x₀, 2r)` with `2r = R / 4ʲ`.
    set r := R / 4 ^ j / 2 with hr_def
    set L := (1 - δ) ^ j * (M - m)
    have h2r : R / 4 ^ j = 2 * r := by rw [hr_def]; ring
    have hr2 : R / 4 ^ (j + 1) = r / 2 := by rw [hr_def, pow_succ]; ring
    have hr : 0 < r := by positivity
    have hball' : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := by
      refine (ball_subset_ball ?_).trans hball
      rw [← h2r]
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    rw [h2r] at hm'
    have hhalf : ball x₀ (r / 2) ⊆ ball x₀ (2 * r) := ball_subset_ball (by linarith)
    have hmM' : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)),
        m' ≤ W1p.value u x ∧ W1p.value u x ≤ m' + L := by
      filter_upwards [hm'] with x hx using mem_Icc.1 hx
    rw [hr2]
    rcases hdecay h ha hu hr hball' hmM' with hle | hge
    · -- The supremum drops: the lower bound `m'` is unchanged.
      refine ⟨m', ?_⟩
      filter_upwards [hle, ae_restrict_of_ae_restrict_of_subset hhalf hmM'] with x hx hx'
      refine mem_Icc.2 ⟨hx'.1, hx.trans (le_of_eq ?_)⟩
      simp only [L, pow_succ]
      ring
    · -- The infimum rises: the upper bound `m' + L` is unchanged.
      refine ⟨m' + δ * L, ?_⟩
      filter_upwards [hge, ae_restrict_of_ae_restrict_of_subset hhalf hmM'] with x hx hx'
      refine mem_Icc.2 ⟨le_of_eq_of_le ?_ hx, hx'.2.trans (le_of_eq ?_)⟩
      · ring
      · simp only [L, pow_succ]
        ring

/-- **Power-law oscillation decay (De Giorgi).** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. If `B(x₀, R) ⊆ Ω` and `u ∈ [m, M]` almost everywhere on `B(x₀, R)`, then
for every radius `0 < r ≤ R`, almost everywhere on `B(x₀, r)` the function `u` takes values in
an interval of length `C (r / R)^α (M - m)`.

The exponent is `α = min (log(1/(1 - δ)) / log 4) 1`, where `δ` is the constant of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_pow_mul_sub`, and `C = 4^α`; the cap at `1` is the
range in which the estimate yields Hölder continuity. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_sub {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R r m M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < r → r ≤ R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), W1p.value u x ∈ Icc m M) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ r),
        W1p.value u x ∈ Icc m' (m' + C * (r / R) ^ α * (M - m)) := by
  obtain ⟨δ, hδ0, hδ1, hiter⟩ :=
    exists_ae_value_mem_Icc_add_pow_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
  have hδ' : 0 < 1 - δ := sub_pos.2 hδ1
  -- The exponent `α₀` is defined by `4^(-α₀) = 1 - δ`; the Hölder exponent is `α = min α₀ 1`.
  set α₀ := Real.logb 4 (1 - δ)⁻¹ with hα₀_def
  have hα₀ : 0 < α₀ := Real.logb_pos (by norm_num) ((one_lt_inv₀ hδ').2 (by linarith))
  have h4α₀ : (4 : ℝ) ^ (-α₀) = 1 - δ := by
    rw [Real.rpow_neg (by norm_num), hα₀_def, Real.rpow_logb (by norm_num) (by norm_num)
      (inv_pos.2 hδ'), inv_inv]
  set α := min α₀ 1 with hα_def
  have hα : 0 < α := lt_min hα₀ one_pos
  refine ⟨α, 4 ^ α, hα, min_le_right _ _, by positivity, ?_⟩
  intro Omega a u x₀ R r m M h ha hu hr hrR hball hmM
  have hR : 0 < R := hr.trans_le hrR
  have hmM' : m ≤ M := by
    have : (ae (mu.restrict (ball x₀ R))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₀ hR).ne'
    obtain ⟨x, hx⟩ := hmM.exists
    exact nonempty_Icc.1 ⟨_, hx⟩
  -- Choose `j` with `4ʲ ≤ R / r < 4ʲ⁺¹`, so that `B(x₀, r) ⊆ B(x₀, R / 4ʲ)` and
  -- `(1 - δ)ʲ = (4ʲ)^(-α₀) ≤ (4ʲ)^(-α) ≤ (4 r / R)^α`.
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ((one_le_div hr).2 hrR) (by norm_num : (1 : ℝ) < 4)
  obtain ⟨m', hm'⟩ := hiter h ha hu hR hball hmM j
  have hsub : ball x₀ r ⊆ ball x₀ (R / 4 ^ j) := by
    refine ball_subset_ball ?_
    rw [le_div_iff₀ (by positivity), mul_comm, ← le_div_iff₀ hr]
    exact hj
  have hpow : (1 - δ) ^ j ≤ 4 ^ α * (r / R) ^ α := by
    -- `(1 - δ)ʲ = (4^(-α₀))ʲ = (4ʲ)^(-α₀) = ((4ʲ)⁻¹)^α₀ ≤ ((4ʲ)⁻¹)^α`, since `(4ʲ)⁻¹ ≤ 1` and
    -- `α ≤ α₀`.
    have h1 : (1 - δ) ^ j ≤ ((4 : ℝ) ^ j)⁻¹ ^ α :=
      calc (1 - δ) ^ j = ((4 : ℝ) ^ (-α₀)) ^ j := by rw [h4α₀]
        _ = ((4 : ℝ) ^ j) ^ (-α₀) := Real.rpow_pow_comm (by norm_num) _ _
        _ = ((4 : ℝ) ^ j)⁻¹ ^ α₀ := Real.rpow_neg_eq_inv_rpow _ _
        _ ≤ ((4 : ℝ) ^ j)⁻¹ ^ α :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity)
            (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) (min_le_left _ _)
    -- `(4ʲ)⁻¹ = 4 / 4ʲ⁺¹ ≤ 4 / (R / r) = 4 r / R`, since `R / r < 4ʲ⁺¹`.
    have h2 : ((4 : ℝ) ^ j)⁻¹ ≤ 4 * (r / R) :=
      calc ((4 : ℝ) ^ j)⁻¹ = 4 * (1 / 4 ^ (j + 1)) := by rw [pow_succ]; field_simp
        _ ≤ 4 * (1 / (R / r)) := by gcongr
        _ = 4 * (r / R) := by rw [one_div_div]
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact h1.trans (Real.rpow_le_rpow (by positivity) h2 hα.le)
  refine ⟨m', ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hm'] with x hx
  refine mem_Icc.2 ⟨(mem_Icc.1 hx).1, (mem_Icc.1 hx).2.trans ?_⟩
  gcongr

/-- **De Giorgi's interior oscillation estimate.** Let `2*` be the Sobolev exponent of `W^{1,2}`
in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. If `B(x₀, R) ⊆ Ω` and `0 < r ≤ R/2`, then almost everywhere on `B(x₀, r)`
the function `u` takes values in an interval of length

`C (r / R)^α R^{-n/2} ‖u‖_{L²(B(x₀, R))}`.

No bound on `u` is assumed: the oscillation of `u` on `B(x₀, R/2)` is controlled by its `L²`
norm through De Giorgi's local boundedness theorem, and the power law
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub` propagates it to smaller balls. This
is the a-priori estimate behind the interior Hölder continuity of weak solutions. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < r → r ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ r),
        W1p.value u x ∈ Icc m' (m' + C * (r / R) ^ α * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu))) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
      hpstar hexp
  obtain ⟨α, C, hα, hα1, hC, hpow⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_sub (mu := mu) (lam := lam) (Lam := Lam)
      hpstar hexp
  refine ⟨α, C * 2 ^ α * (2 * D), hα, hα1, by positivity, ?_⟩
  intro Omega a u x₀ R r h ha hu hr hrR hball
  have hR : 0 < R := by linarith
  set K := D * R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  -- Local boundedness: `u ∈ [-K, K]` on `B(x₀, R/2)`.
  have hK : ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ∈ Icc (-K) K := by
    filter_upwards [hbound h ha hu hR hball] with x hx
    exact mem_Icc.2 (abs_le.1 hx)
  obtain ⟨m', hm'⟩ := hpow h ha hu hr hrR ((ball_subset_ball (half_le_self hR.le)).trans hball) hK
  refine ⟨m', ?_⟩
  have hrpow : (r / (R / 2)) ^ α = 2 ^ α * (r / R) ^ α := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    field_simp
  have heq : m' + C * (r / (R / 2)) ^ α * (K - -K) = m' + C * 2 ^ α * (2 * D) * (r / R) ^ α *
      (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)) := by
    rw [hrpow]
    ring
  rwa [heq] at hm'

end PDE

end TauCeti
