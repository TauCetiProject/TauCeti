/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.Regularity.LevelSetDecay
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness
import TauCeti.MeasureTheory.Measure.AddHaar

/-!
# Decay of the supremum of weak subsolutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ`, `n ≥ 3`, with constants `0 < λ ≤ Λ`,
and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`. Suppose that on a ball
`B(x₀, 2R) ⊆ Ω` we have `u ≤ M`, and that on `B(x₀, R)` the sublevel set `{u ≤ k}` occupies at
least a fixed proportion `θ > 0` of the ball. This file proves De Giorgi's
**reduction of the supremum**: there is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the
dimension and the normalization of the Haar measure, such that

`u ≤ M - δ (M - k)` almost everywhere on `B(x₀, R/2)`.

Applied to `u` and `-u` for a weak solution, on whichever side the median of `u` lies, this is the
step that makes the oscillation of a weak solution decay by a fixed factor from one ball to a
concentric ball of a quarter of the radius, and iterating it gives Hölder continuity.

The proof combines the two halves of De Giorgi's method. Along the levels
`kⱼ = M - (M - k)/2ʲ`, the decay of upper level sets
(`TauCeti.PDE.exists_sqrt_mul_measureReal_le_mul_measureReal_ball`) makes `{u ≥ kⱼ}` an
arbitrarily small proportion of `B(x₀, R)` once `j` is large. Local boundedness
(`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`), applied to
`u - kⱼ`, then bounds `u - kⱼ` on `B(x₀, R/2)` by `(M - kⱼ)/2`. Since `u - kⱼ` is only a Sobolev
function on a domain of finite measure, the argument runs on the ball `B(x₀, 2R)` itself, to which
weak subsolutions restrict (`TauCeti.PDE.energyFormH1_restrictL_nonpos`).

## Main declarations

* `TauCeti.PDE.exists_ae_value_le_sub_mul_sub`: the reduction of the supremum.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4, Lemma 4.8.
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

/-- The arithmetic that closes De Giorgi's reduction of the supremum: once the proportion `A` of
`B_R` above the level is at most `C |B_R| / √j` with `j ≥ 16 D⁴ C² ω²`, local boundedness with
constant `D` and height `e` bounds the excess by `e / 2`. Here `|B_R| = Rⁿ ω`. -/
private theorem mul_rpow_mul_sqrt_le_half {D C ω R e A j : ℝ} {n : ℕ} (hD : 0 < D) (hC : 0 < C)
    (hω : 0 < ω) (hR : 0 < R) (he : 0 ≤ e) (hA : 0 ≤ A) (hj : 16 * D ^ 4 * C ^ 2 * ω ^ 2 ≤ j)
    (hdecay : √j * A ≤ C * (R ^ n * ω)) :
    D * R ^ (-(n : ℝ) / 2) * √(e ^ 2 * A) ≤ e / 2 := by
  have hsqrt : 4 * D ^ 2 * C * ω ≤ √j := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * D ^ 2 * C * ω)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- The level set is small: `4 D² A ≤ Rⁿ`.
  have hsmall : 4 * D ^ 2 * A ≤ R ^ n := by
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < C * ω)
    calc 4 * D ^ 2 * A * (C * ω) = (4 * D ^ 2 * C * ω) * A := by ring
      _ ≤ √j * A := mul_le_mul_of_nonneg_right hsqrt hA
      _ ≤ C * (R ^ n * ω) := hdecay
      _ = R ^ n * (C * ω) := by ring
  have hRpow : (R ^ (-(n : ℝ) / 2)) ^ 2 = (R ^ n)⁻¹ := by
    rw [← Real.rpow_natCast (R ^ (-(n : ℝ) / 2)) 2, ← Real.rpow_mul hR.le,
      show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring, Real.rpow_neg hR.le,
      Real.rpow_natCast]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hRpow]
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [div_pow, le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 2)]
  calc D ^ 2 * (R ^ n)⁻¹ * (e ^ 2 * A) * 2 ^ 2 = e ^ 2 * (4 * D ^ 2 * A) * (R ^ n)⁻¹ := by ring
    _ ≤ e ^ 2 * R ^ n * (R ^ n)⁻¹ := by gcongr
    _ = e ^ 2 := by field_simp

/-- **Reduction of the supremum of weak subsolutions (De Giorgi).** Let `2*` be the Sobolev
exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces
`n ≥ 3`), and fix ellipticity constants `λ, Λ` and a proportion `θ > 0`. There is `δ ∈ (0, 1)`,
depending only on these and on the normalization of the additive Haar measure `μ`, such that the
following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every
nonnegative `v ∈ H¹₀(Ω)`. Let `B(x₀, 2R) ⊆ Ω`, and let `k, M` be levels such that `u ≤ M` almost
everywhere on `B(x₀, 2R)` and `|{u ≤ k} ∩ B(x₀, R)| ≥ θ |B(x₀, R)|`. Then

`u ≤ M - δ (M - k)` almost everywhere on `B(x₀, R/2)`.

The constant is independent of `Ω`, the coefficients, `u`, the ball and the levels. No
regularity of the coefficients beyond measurability is assumed. -/
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
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k} →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ≤ M - δ * (M - k) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_sqrt_mul_measureReal_le_mul_measureReal_ball (ι := ι) (lam := lam) (Lam := Lam) hθ
  obtain ⟨D, hD, hbdd⟩ := exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv
    (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  set j : ℕ := ⌈16 * D ^ 4 * C ^ 2 * ω ^ 2⌉₊ + 1
  have hj : 16 * D ^ 4 * C ^ 2 * ω ^ 2 ≤ (j : ℝ) :=
    (Nat.le_ceil _).trans (by simp only [j]; push_cast; linarith)
  refine ⟨(1 / 2) ^ (j + 1), by positivity,
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero j), ?_⟩
  intro Omega a u x₀ R k M h ha hu hR hball hM hθk
  have hRR : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  rcases le_or_gt M k with hkM | hkM
  · -- If `M ≤ k` the claim is weaker than `u ≤ M`.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hRR hM] with x hx
    nlinarith [(by positivity : (0 : ℝ) < (1 / 2) ^ (j + 1))]
  -- Work on the ball `B = B(x₀, 2R)`, which has finite measure.
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (2 * R), isOpen_ball⟩
  have hBΩ : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set v := W1p.restrictL hBΩ u
  have hvu : ⇑(W1p.value v) =ᵐ[mu.restrict (ball x₀ (2 * R))] W1p.value u :=
    W1p.value_restrictL_ae hBΩ u
  have hv : ∀ φ : W1p0 mu B 2,
      (∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (φ : W1p mu B 2) x) →
        energyFormH1 a 0 0 v (φ : W1p mu B 2) ≤ 0 :=
    energyFormH1_restrictL_nonpos hBΩ hu
  have hB : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hball
  have haB : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  have hRB : ball x₀ R ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have hvuR : ⇑(W1p.value v) =ᵐ[mu.restrict (ball x₀ R)] W1p.value u :=
    ae_restrict_of_ae_restrict_of_subset hRB hvu
  have hMv : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value v x ≤ M := by
    filter_upwards [hvu, hM] with x h1 h2
    rwa [h1]
  have hθv : θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value v x ≤ k} := by
    refine hθk.trans_eq (measureReal_congr ?_)
    filter_upwards [hvuR] with x hx
    simp only [hx]
  -- The decay of upper level sets, at the level `ℓ = M - (M - k)/2ʲ`.
  set d := M - k
  set ℓ := M - d / 2 ^ j
  have hA := hdecay hB haB hv hR (subset_refl _) hkM
    ((Lp.memLp (W1p.value v)).sub (memLp_const k)).pos_part hMv hθv j
  -- Local boundedness for `w = v - ℓ`, again a weak subsolution on `B`.
  set w : W1p mu B 2 := v - W1p.const ℓ
  have hwv : ⇑(W1p.value w) =ᵐ[mu.restrict (ball x₀ (2 * R))] fun x => W1p.value v x - ℓ :=
    W1p.value_sub_const_ae v ℓ
  have hw : ∀ φ : W1p0 mu B 2,
      (∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (φ : W1p mu B 2) x) →
        energyFormH1 a 0 0 w (φ : W1p mu B 2) ≤ 0 := fun φ hφ =>
    (energyFormH1_sub_const_left ℓ v _).trans_le (hv φ hφ)
  have hL := hbdd hB haB hw hR hRB
  -- The `L²` mass of `(v - ℓ)⁺` on `B(x₀, R)` is at most `(M - ℓ)² |{v ≥ ℓ} ∩ B(x₀, R)|`.
  have hm : Measurable (W1p.value v : EuclideanSpace ℝ ι → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have hMℓ : M - ℓ = d / 2 ^ j := by simp only [ℓ]; ring
  set A := (mu.restrict (ball x₀ R)).real {x | ℓ ≤ W1p.value v x}
  have hI : ∫ x in ball x₀ R, max (W1p.value w x) 0 ^ 2 ∂mu ≤ (d / 2 ^ j) ^ 2 * A := by
    have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    calc ∫ x in ball x₀ R, max (W1p.value w x) 0 ^ 2 ∂mu
        ≤ ∫ x in ball x₀ R, {x | ℓ ≤ W1p.value v x}.indicator (fun _ => (d / 2 ^ j) ^ 2) x ∂mu := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
            ((integrable_const _).indicator (measurableSet_le measurable_const hm)) ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hRB hwv,
            ae_restrict_of_ae_restrict_of_subset hRB hMv] with x h1 h2
          rw [h1]
          by_cases hx : ℓ ≤ W1p.value v x
          · rw [indicator_of_mem (by exact hx : x ∈ {x | ℓ ≤ W1p.value v x}), ← hMℓ]
            exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by linarith)) 2
          · rw [indicator_of_notMem (by exact hx : x ∉ {x | ℓ ≤ W1p.value v x}),
              max_eq_right (by linarith)]
            norm_num
      _ = (d / 2 ^ j) ^ 2 * A := by
          rw [integral_indicator_const _ (measurableSet_le measurable_const hm), smul_eq_mul,
            mul_comm]
  have hvol : mu.real (ball x₀ R) = R ^ Fintype.card ι * ω := by
    rw [mu.addHaar_real_ball_of_pos x₀ hR, finrank_euclideanSpace]
  have hhalf := mul_rpow_mul_sqrt_le_half (e := d / 2 ^ j) hD hC hω hR (by positivity)
    measureReal_nonneg hj (by rwa [← hvol])
  -- Conclude on `B(x₀, R/2)`.
  filter_upwards [hL, ae_restrict_of_ae_restrict_of_subset hRR hwv,
    ae_restrict_of_ae_restrict_of_subset hRR hvu] with x h1 h2 h3
  rw [h2] at h1
  rw [← h3]
  have hbound : W1p.value v x - ℓ ≤ d / 2 ^ j / 2 :=
    h1.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hI) (by positivity)).trans hhalf)
  have hδ : (1 / 2 : ℝ) ^ (j + 1) * (M - k) = d / 2 ^ j / 2 := by
    simp only [d, one_div, inv_pow, pow_succ]
    field_simp
  rw [hδ]
  simp only [ℓ] at hbound
  linarith

end PDE

end TauCeti
