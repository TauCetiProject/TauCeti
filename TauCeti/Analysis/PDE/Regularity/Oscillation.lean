/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.LevelSetDecay
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness
import TauCeti.MeasureTheory.Measure.AddHaar

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

The reduction of the supremum combines De Giorgi's decay of upper level sets
(`TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`) with local boundedness above
a level (`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`):
along the levels `kⱼ = M - (M - k)/2ʲ`, the set `{u ≥ kⱼ}` occupies a proportion `O(j^{-1/2})` of
`B(x₀, R)`, so the `L²` mass of `(u - kⱼ)⁺` there is `O((M - kⱼ)² j^{-1/2} Rⁿ)`, and local
boundedness gives `u ≤ kⱼ + (M - kⱼ)/2` on `B(x₀, R/2)` once `j` is large. Oscillation decay
applies this to `u` or to `-u` at the mid level `(m + M)/2`, whichever sublevel set fills at least
half of `B(x₀, R)`. Iterating oscillation decay over shrinking balls gives the interior Hölder
continuity of weak solutions.

## Main declarations

* `TauCeti.PDE.exists_ae_value_le_sub_mul_sub`: the reduction of the supremum.
* `TauCeti.PDE.exists_ae_value_le_sub_mul_sub_or_add_mul_sub_le`: oscillation decay.

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

omit [DecidableEq ι] in
/-- On a ball where `u ≤ M`, the `L²` mass of `(u - l)⁺` is at most `(M - l)²` times the measure
of the upper level set `{u ≥ l}`. -/
private theorem setIntegral_ball_max_sub_sq_le {f : EuclideanSpace ℝ ι → ℝ}
    (hf : Measurable f) {x₀ : EuclideanSpace ℝ ι} {R l M : ℝ} (hlM : l ≤ M)
    (hM : ∀ᵐ x ∂mu.restrict (ball x₀ R), f x ≤ M) :
    ∫ x in ball x₀ R, max (f x - l) 0 ^ 2 ∂mu ≤
      (M - l) ^ 2 * (mu.restrict (ball x₀ R)).real {x | l ≤ f x} := by
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hS : MeasurableSet {x | l ≤ f x} := measurableSet_le measurable_const hf
  calc ∫ x in ball x₀ R, max (f x - l) 0 ^ 2 ∂mu
      ≤ ∫ x in ball x₀ R, {x | l ≤ f x}.indicator (fun _ => (M - l) ^ 2) x ∂mu := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          ((integrable_const _).indicator hS) ?_
        filter_upwards [hM] with x hx
        by_cases hlx : l ≤ f x
        · rw [indicator_of_mem (by exact hlx)]
          exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by linarith)) 2
        · rw [indicator_of_notMem (by exact hlx), max_eq_right (by linarith)]
          norm_num
    _ = (M - l) ^ 2 * (mu.restrict (ball x₀ R)).real {x | l ≤ f x} := by
        rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]

/-- **Reduction of the supremum (De Giorgi).** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`), and fix a proportion
`θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Let
`B(x₀, 2R) ⊆ Ω` and levels `k ≤ M` be such that `(u - k)⁺ ∈ L²(Ω)`, `u ≤ M` almost everywhere on
`B(x₀, 2R)`, and `|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Then

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
      MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega) →
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
  intro Omega a u x₀ R k M h ha hu hR hball hkM hwLp hM hθk
  have hhalf : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  rcases hkM.eq_or_lt with rfl | hkM
  · -- Equal levels: the bound is the hypothesis `u ≤ k`.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalf hM] with x hx
    simpa using hx
  set l := M - (M - k) / 2 ^ j
  have hkl : k ≤ l := by
    have : (M - k) / 2 ^ j ≤ M - k :=
      div_le_self (sub_nonneg.2 hkM.le) (one_le_pow₀ one_le_two)
    simp only [l]
    linarith
  have hlM : l ≤ M := sub_le_self _ (by positivity)
  have hballR : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball
  -- The upper level set `{u ≥ l}` is small, by the decay estimate.
  set V := mu.real (ball x₀ R)
  set A := (mu.restrict (ball x₀ R)).real {x | l ≤ W1p.value u x}
  have hA : √j * A ≤ C * V := hdecay h ha hu hR hball hkM hwLp hM hθk j
  -- Hence so is the `L²` mass of `(u - l)⁺` on `B(x₀, R)`.
  set I := ∫ x in ball x₀ R, max (W1p.value u x - l) 0 ^ 2 ∂mu
  have hI : I ≤ (M - l) ^ 2 * A :=
    setIntegral_ball_max_sub_sq_le (Lp.stronglyMeasurable _).measurable hlM
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
  filter_upwards [hbound h ha hu (W1p.memLp_posPartAbove_of_le u hkl hwLp) hR hballR] with x hx
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
`m ≤ u ≤ M` almost everywhere on `B(x₀, 2R)`, and such that `(u - k)⁺` and `(k - u)⁺` lie in
`L²(Ω)` for the mid level `k = (m + M)/2`. Then almost everywhere on `B(x₀, R/2)`, either

`u ≤ M - δ (M - m)` throughout, or `m + δ (M - m) ≤ u` throughout.

In particular the essential oscillation of `u` on `B(x₀, R/2)` is at most `(1 - δ)(M - m)`. The
integrability hypotheses hold automatically when `Ω` has finite measure. -/
theorem exists_ae_value_le_sub_mul_sub_or_add_mul_sub_le {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R m M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp (fun x => max (W1p.value u x - (m + M) / 2) 0) 2 (mu.restrict Omega) →
      MemLp (fun x => max ((m + M) / 2 - W1p.value u x) 0) 2 (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), m ≤ W1p.value u x ∧ W1p.value u x ≤ M) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ≤ M - δ * (M - m)) ∨
        ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), m + δ * (M - m) ≤ W1p.value u x := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨δ / 2, by positivity, by linarith, ?_⟩
  intro Omega a u x₀ R m M h ha hu hR hball hwLp hwLp' hmM'
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
    filter_upwards [hred h ha (fun v _ => (hu v).le) hR hball hkM hwLp
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
    have hwLp'' : MemLp (fun x => max (W1p.value (-u) x - -k) 0) 2 (mu.restrict Omega) :=
      hwLp'.ae_eq (by
        filter_upwards [hneg] with x hx
        rw [hx, Pi.neg_apply]
        ring_nf)
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
    filter_upwards [hred h ha hu' hR hball (neg_le_neg hmk) hwLp'' hM' hθ',
      ae_restrict_of_ae_restrict_of_subset ((ball_subset_ball (by linarith)).trans hball) hneg]
      with x hx hxn
    rw [hxn, Pi.neg_apply] at hx
    calc m + δ / 2 * (M - m) = m + δ * (k - m) := by simp only [k]; ring
      _ ≤ W1p.value u x := by linarith

end PDE

end TauCeti
