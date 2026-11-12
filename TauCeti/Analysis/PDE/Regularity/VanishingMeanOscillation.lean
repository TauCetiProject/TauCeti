/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.SharpMaximalFunction

/-!
# The `W^{1,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u ∈ H¹(ℝ^{n+1})` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G`,

that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`. Suppose that `a` is bounded by `Λ`
and has small mean oscillation at every scale: on every ball `B` there is a constant matrix `A`,
uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation `⨍_B ‖a - A‖` from `a` is at
most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`. For `A` the average of `a` over `B` this is the mean oscillation
of `a`. Uniformly elliptic coefficients are bounded by `Λ`
(`TauCeti.PDE.UniformlyEllipticOn.opNorm_matrixBilinearForm_le`), but ellipticity is only needed
for the frozen matrices `A`. This file proves the a priori estimate

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ` and is integrable, with `C` and the threshold `δ`
depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`). Only the
mean oscillation of `a` is controlled, not its modulus of continuity. Coefficients of vanishing
mean oscillation have small mean oscillation on small balls only; the passage from small balls to
all scales, by localization, is not treated here. The integrability of `∇u` is the a priori
integrability that the Fefferman–Stein inequality requires; it holds for instance when `∇u ∈ Lᵖ`
vanishes outside a bounded set, as for a cutoff of a local solution.

## The argument

The proof is Krylov's sharp function method, applied to Krylov's mean oscillation estimate for the
gradient in `TauCeti.Analysis.PDE.Regularity.MeanOscillation`.

* **One ball.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on
  `B_r` at the matrix `A` given by the hypothesis. The mean oscillation estimate, with the square
  mean oscillation of `∇u` on `B_r` bounded by `4 ⨍_{B_r} ‖∇u‖²`, and the bound `‖a - A‖ ≤ 2Λ`,
  bound the square mean oscillation of `∇u` on `B_ρ` by
  `κ⁻² ⨍_{B_r} ‖∇u‖² + κ^(n + 1) (⨍_{B_r} ‖G‖² + δ^(1/q') (⨍_{B_r} ‖∇u‖^(2q))^(1/q))`, up to
  constants, for Hölder conjugate exponents `q, q'`.
* **The sharp function.** Every average over `B_r ∋ x` is at most `2^(n + 1)` times the centred
  maximal function at `x`. Taking the supremum over the balls containing `x`, the square of the
  sharp maximal function of `∇u` is bounded pointwise by
  `κ⁻² M(‖∇u‖²) + κ^(n + 1) M(‖G‖²) + κ^(n + 1) δ^(1/q') M(‖∇u‖^(2q))^(1/q)`.
* **Absorption.** The Fefferman–Stein inequality for Euclidean balls
  (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`) and the strong
  maximal inequality with the exponents `p / 2` and `p / (2q)`, where `1 < q < p / 2`, turn this
  into
  `∫ ‖∇u‖^p ≤ (c₁ κ^(-p) + c₃ δ^(p/(2q'))) ∫ ‖∇u‖^p + c₂ ∫ ‖G‖^p`. Choosing first `κ` large and
  then `δ` small, the first term is absorbed, since `∫ ‖∇u‖^p` is finite.

The restriction `p > 2` comes from the `L²` mean oscillation estimate.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`: the
  `W^{1,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* S.-S. Byun, L. Wang, *Elliptic equations with BMO coefficients in Reifenberg domains*, Comm.
  Pure Appl. Math. **57** (2004), 1283–1310 (coefficients of small mean oscillation at every
  scale).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Distributions Gradient InnerProductSpace Topology

namespace TauCeti

/-! ### Averages -/

section Averages

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
  {F : Type*} [NormedAddCommGroup F]

/-- The average of `‖h‖ ^ k` read in `ℝ≥0∞`. -/
private theorem ofReal_setAverage_norm_rpow {h : X → F} {k : ℝ} (hk : 0 ≤ k)
    (hi : IntegrableOn (fun x => ‖h x‖ ^ k) s μ) :
    ENNReal.ofReal (⨍ x in s, ‖h x‖ ^ k ∂μ) = ⨍⁻ x in s, ‖h x‖ₑ ^ k ∂μ := by
  rw [ofReal_setAverage hi (ae_of_all _ fun x => by positivity), setLAverage_eq]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hk, ofReal_norm]

end Averages

namespace PDE

variable {n : ℕ}

/-- An average over a ball containing `x` is at most `2^(n + 1)` times the centred maximal function
at `x`. -/
private theorem setLAverage_le_two_pow_mul_maximalFunction
    (g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) {x c : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    (hx : x ∈ ball c r) :
    ⨍⁻ y in ball c r, g y ≤ 2 ^ (n + 1) * maximalFunction volume g x := by
  have h := setLIntegral_ball_le_two_pow_mul_measure_mul_maximalFunction volume g hx
  simp only [enorm_eq_self, finrank_euclideanSpace, Fintype.card_fin] at h
  have h0 : volume (ball c r) ≠ 0 := (measure_ball_pos _ _ (pos_of_mem_ball hx)).ne'
  have ht : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  rw [setLAverage_eq]
  calc (∫⁻ y in ball c r, g y) / volume (ball c r)
      ≤ 2 ^ (n + 1) * volume (ball c r) * maximalFunction volume g x / volume (ball c r) := by
        gcongr
    _ = 2 ^ (n + 1) * maximalFunction volume g x := by
        rw [mul_right_comm, ENNReal.mul_div_cancel_right h0 ht]

/-- The constant of the decaying term in the one-ball estimate. -/
private noncomputable def decayConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  16 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3))

/-- The constant of the forcing term in the one-ball estimate. -/
private noncomputable def forcingConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 * (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2

/-- **The mean oscillation estimate on one ball.** Let `u ∈ H¹(ℝ^{n+1})` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, let `x ∈ B_ρ = ball c ρ` and `κ ≥ 1`, and freeze the coefficients
on `B_{κρ}` at an elliptic constant matrix `A` whose mean deviation from `a` there is at most `δ`.
Then the square of the mean oscillation of `g = ∇u` on `B_ρ` is bounded by the maximal functions
at `x` of `‖g‖²`, of `‖G‖²` and of `‖g‖^(2q)`, the first with the small factor `κ⁻²` and the last
with the factor `δ^(1/q')`. -/
private theorem sq_setLAverage_enorm_gradient_sub_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' : ℝ} (hq : q.HolderConjugate q')
    (hqp : ENNReal.ofReal (2 * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c x : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hx : x ∈ ball c ρ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    (⨍⁻ y in ball c ρ, ‖W1p.gradient u y - ⨍ z in ball c ρ, W1p.gradient u z‖ₑ) ^ 2 ≤
      ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹) *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  set g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set r := κ * ρ with hr_def
  set M₁ := maximalFunction volume (fun y => ‖g y‖ₑ ^ 2) x
  set M₂ := maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x
  set M₃ := maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x
  set D : ℝ := 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3) with hD_def
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hr : 0 < r := mul_pos hκ0 hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  have hxr : x ∈ ball c r := ball_subset_ball hρr hx
  have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)
  have hq0 : 0 < q := hq.pos
  have hq'0 : 0 < q' := hq.symm.pos
  have hD : 0 ≤ D := by positivity
  have hBt : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The coefficient deviation is at most `2Λ` on `B_r`.
  have haK : ∀ y ∈ ball c r, ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun y _ =>
    (norm_sub_le (matrixBilinearForm (a y)) (matrixBilinearForm A)).trans (by
      linarith [hbd y,
        hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)])
  -- Integrability on the balls.
  have hg2 : ∀ t, MemLp g 2 (volume.restrict (ball c t)) := fun t => by
    have : IsFiniteMeasure (volume.restrict (ball c t)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact (hgp.restrict _).mono_exponent h2p
  have hG2 : MemLp G 2 (volume.restrict (ball c r)) := (hGp.restrict _).mono_exponent h2p
  have hgq : MemLp g (ENNReal.ofReal (2 * q)) (volume.restrict (ball c r)) :=
    (hgp.restrict _).mono_exponent hqp
  have hθ0 : 0 ≤ ⨍ y in ball c r, ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ :=
    average_nonneg fun y => norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A)
  -- Krylov's mean oscillation estimate, with `c = 0`.
  have key :=
    setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le
      hA ha.restrict haK (G := G) (c := 0) (u := u) (fun φ => by simpa using hu φ) (by simp)
      (by simpa using hG2) hq hgq hρ hρr
  simp only [sub_zero] at key
  -- The mean deviation enters through `δ`.
  have hδ' : ((2 * Lam) ^ (2 * q' - 1) *
      ⨍ y in ball c r, ‖matrixBilinearForm (a y) - matrixBilinearForm A‖) ^ q'⁻¹ ≤
      ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ := by
    gcongr
  -- The terms of the estimate in `ℝ≥0∞`.
  have hint2 : ∀ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ),
      MemLp h 2 (volume.restrict (ball c t)) →
        IntegrableOn (fun y => ‖h y‖ ^ 2) (ball c t) := fun h t hh =>
    hh.integrable_norm_pow two_ne_zero
  have hsq : ∀ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ),
      MemLp h 2 (volume.restrict (ball c t)) →
        ENNReal.ofReal (⨍ y in ball c t, ‖h y‖ ^ 2) = ⨍⁻ y in ball c t, ‖h y‖ₑ ^ 2 :=
    fun h t hh => by
      simpa only [Real.rpow_two, ENNReal.rpow_two] using
        ofReal_setAverage_norm_rpow zero_le_two (by simpa only [Real.rpow_two] using hint2 h t hh)
  have hO : ∀ t, 0 < t → ENNReal.ofReal (⨍ y in ball c t, ‖g y - ⨍ z in ball c t, g z‖ ^ 2) =
      ⨍⁻ y in ball c t, ‖g y - ⨍ z in ball c t, g z‖ₑ ^ 2 := fun t _ => by
    have : IsFiniteMeasure (volume.restrict (ball c t)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact hsq _ t ((hg2 t).sub (memLp_const _))
  have hE1 : ENNReal.ofReal (⨍ y in ball c r, ‖g y - ⨍ z in ball c r, g z‖ ^ 2) ≤
      4 * (2 ^ (n + 1) * M₁) := by
    have hreal : ⨍ y in ball c r, ‖g y - ⨍ z in ball c r, g z‖ ^ 2 ≤
        4 * ⨍ y in ball c r, ‖g y‖ ^ 2 := by
      simp only [setAverage_eq, smul_eq_mul]
      rw [mul_left_comm]
      gcongr
      simpa [setAverage_eq] using setIntegral_norm_sub_setAverage_sq_le hBt
        ((hg2 r).integrable one_le_two) (c := 0) (by simpa using hint2 g r (hg2 r))
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), hsq g r (hg2 r), ENNReal.ofReal_ofNat]
    gcongr
    exact setLAverage_le_two_pow_mul_maximalFunction _ hxr
  have hE2 : ENNReal.ofReal (⨍ y in ball c r, ‖G y‖ ^ 2) ≤ 2 ^ (n + 1) * M₂ := by
    rw [hsq G r hG2]
    exact setLAverage_le_two_pow_mul_maximalFunction _ hxr
  have hE3 : ENNReal.ofReal ((⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹) ≤
      (2 ^ (n + 1) * M₃) ^ q⁻¹ := by
    have hi : IntegrableOn (fun y => ‖g y‖ ^ (2 * q)) (ball c r) := by
      have := hgq.integrable_norm_rpow (ENNReal.ofReal_pos.2 (by positivity)).ne'
        ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * q)] at this
    rw [← ENNReal.ofReal_rpow_of_nonneg (average_nonneg fun y => by positivity)
      (inv_nonneg.2 hq0.le), ofReal_setAverage_norm_rpow (by positivity) hi]
    gcongr
    exact setLAverage_le_two_pow_mul_maximalFunction _ hxr
  -- Jensen's inequality on `B_ρ`.
  have hjensen : (⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ) ^ 2 ≤
      ⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ ^ 2 := by
    have h := rpow_laverage_le_laverage_rpow (μ := volume.restrict (ball c ρ))
      (u := fun y => ‖g y - ⨍ z in ball c ρ, g z‖ₑ) one_le_two
    simpa only [ENNReal.rpow_two] using h
  have hκρ : ρ / r = κ⁻¹ := by rw [hr_def]; field_simp
  have hrρ : r / ρ = κ := by rw [hr_def]; field_simp
  rw [hκρ, hrρ] at key
  have hO0 : 0 ≤ ⨍ y in ball c r, ‖g y - ⨍ z in ball c r, g z‖ ^ 2 :=
    average_nonneg fun y => by positivity
  have hI₂ : 0 ≤ ⨍ y in ball c r, ‖G y‖ ^ 2 := average_nonneg fun y => by positivity
  have hI₃ : 0 ≤ (⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹ :=
    Real.rpow_nonneg (average_nonneg fun y => by positivity) _
  have hX : 0 ≤ ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ :=
    Real.rpow_nonneg (mul_nonneg (by positivity) ((hθ0.trans hδ))) _
  have hkey : ⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ 2 ≤
      4 * D * (κ⁻¹) ^ 2 * (⨍ y in ball c r, ‖g y - ⨍ z in ball c r, g z‖ ^ 2) +
        2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * ((⨍ y in ball c r, ‖G y‖ ^ 2) +
          ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹) := by
    refine key.trans ?_
    gcongr
  generalize (⨍ y in ball c r, ‖g y - ⨍ z in ball c r, g z‖ ^ 2) = O at hO0 hkey hE1
  generalize (⨍ y in ball c r, ‖G y‖ ^ 2) = I₂ at hI₂ hkey hE2
  generalize (⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹ = I₃ at hI₃ hkey hE3
  generalize ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ = X at hX hkey ⊢
  have hD4 : 0 ≤ 4 * D * (κ⁻¹) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hF0 : 0 ≤ 2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) :=
    mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (pow_nonneg hκ0.le _)
  have hX' : (0 : ℝ) ≤ 2 ^ (n + 1) := by positivity
  calc (⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ) ^ 2
      ≤ ENNReal.ofReal (⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ 2) := by
        rw [hO ρ hρ]; exact hjensen
    _ ≤ ENNReal.ofReal (4 * D * (κ⁻¹) ^ 2 * O +
          2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * (I₂ + X * I₃)) :=
        ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal (4 * D * (κ⁻¹) ^ 2) * ENNReal.ofReal O +
          ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1)) *
            (ENNReal.ofReal I₂ + ENNReal.ofReal X * ENNReal.ofReal I₃) := by
        rw [ENNReal.ofReal_add (mul_nonneg hD4 hO0)
            (mul_nonneg hF0 (add_nonneg hI₂ (mul_nonneg hX hI₃))),
          ENNReal.ofReal_mul hD4, ENNReal.ofReal_mul hF0,
          ENNReal.ofReal_add hI₂ (mul_nonneg hX hI₃), ENNReal.ofReal_mul hX]
    _ ≤ ENNReal.ofReal (4 * D * (κ⁻¹) ^ 2) * (4 * (2 ^ (n + 1) * M₁)) +
          ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1)) *
            (2 ^ (n + 1) * M₂ + ENNReal.ofReal X * (2 ^ (n + 1) * M₃) ^ q⁻¹) := by
        gcongr
    _ = _ := by
        have hq1 : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
        have h2 : ENNReal.ofReal (2 ^ (n + 1)) = (2 : ℝ≥0∞) ^ (n + 1) := by
          rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
        have e1 : decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1) =
            4 * D * (κ⁻¹) ^ 2 * (4 * 2 ^ (n + 1)) := by
          rw [hD_def]; unfold decayConst; field_simp; ring
        have e2 : forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1) =
            2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * 2 ^ (n + 1) := by
          rw [hD_def]; unfold forcingConst; ring
        have e3 : forcingConst n lam Lam * κ ^ (n + 1) * X * (2 ^ (n + 1)) ^ q⁻¹ =
            2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * X * (2 ^ (n + 1)) ^ q⁻¹ := by
          rw [hD_def]; unfold forcingConst; ring
        have f1 : ENNReal.ofReal (4 * D * (κ⁻¹) ^ 2 * (4 * 2 ^ (n + 1))) =
            ENNReal.ofReal (4 * D * (κ⁻¹) ^ 2) * (4 * 2 ^ (n + 1)) := by
          rw [ENNReal.ofReal_mul hD4, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
            ENNReal.ofReal_ofNat, h2]
        have f2 : ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * 2 ^ (n + 1)) =
            ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1)) * 2 ^ (n + 1) := by
          rw [ENNReal.ofReal_mul hF0, h2]
        have f3 : ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) * X *
              (2 ^ (n + 1)) ^ q⁻¹) =
            ENNReal.ofReal (2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1)) * ENNReal.ofReal X *
              (2 ^ (n + 1)) ^ q⁻¹ := by
          rw [ENNReal.ofReal_mul (mul_nonneg hF0 hX), ENNReal.ofReal_mul hF0,
            ← ENNReal.ofReal_rpow_of_nonneg hX' hq1, h2]
        rw [e1, e2, e3, f1, f2, f3, ENNReal.mul_rpow_of_nonneg _ _ hq1]
        ring

/-- **Krylov's pointwise estimate for the sharp maximal function of the gradient.** Under the
hypotheses of the main theorem, for every `κ ≥ 1` the square of the sharp maximal function of
`g = ∇u` is bounded pointwise by the maximal functions of `‖g‖²`, of `‖G‖²` and of `‖g‖^(2q)`. -/
private theorem sq_sharpMaximalFunction_gradient_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' : ℝ} (hq : q.HolderConjugate q')
    (hqp : ENNReal.ofReal (2 * q) ≤ p) {κ : ℝ} (hκ : 1 ≤ κ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ 2 ≤
      ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹) *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  rw [← ENNReal.rpow_two, ← ENNReal.le_rpow_inv_iff two_pos]
  refine sharpMaximalFunction_le fun c ρ hx => ?_
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.1 hx)
  obtain ⟨A, hA, hδ⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  rw [ENNReal.le_rpow_inv_iff two_pos, ENNReal.rpow_two]
  exact sq_setLAverage_enorm_gradient_sub_le ha hbd hu h2p hgp hGp hq hqp hρ hκ hx hA hδ

/-- Integrating a pointwise bound of `g²` by three maximal functions: if
`g² ≤ α₁ M h₁ + α₂ M h₂ + α₃ (M h₃)^(1/q)` and `2q < s`, then the strong-type maximal inequality
with the exponents `s / 2` and `s / (2q)` bounds `∫ g^s` by the integrals of `h₁^(s/2)`, `h₂^(s/2)`
and `h₃^(s/(2q))`. -/
private theorem lintegral_rpow_le_of_sq_le_maximalFunction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {g h₁ h₂ h₃ : E → ℝ≥0∞} (h₁m : AEMeasurable h₁ μ)
    (h₂m : AEMeasurable h₂ μ) (h₃m : AEMeasurable h₃ μ) {α₁ α₂ α₃ : ℝ≥0∞} {q s : ℝ}
    (hq : 1 < q) (hqs : 2 * q < s)
    (hg : ∀ x, g x ^ 2 ≤ α₁ * maximalFunction μ h₁ x + α₂ * maximalFunction μ h₂ x +
      α₃ * maximalFunction μ h₃ x ^ q⁻¹) :
    ∫⁻ x, g x ^ s ∂μ ≤ 2 ^ (s / 2 - 1) * (2 ^ (s / 2 - 1) *
        (α₁ ^ (s / 2) * (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₁ x ^ (s / 2) ∂μ) +
          α₂ ^ (s / 2) * (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₂ x ^ (s / 2) ∂μ)) +
        α₃ ^ (s / 2) * (ENNReal.ofReal (2 * (s / 2 / q) * 2 ^ (s / 2 / q - 1) / (s / 2 / q - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₃ x ^ (s / 2 / q) ∂μ)) := by
  set r := s / 2
  have hr : 1 < r := by simp only [r]; linarith
  have hrq : 1 < r / q := by rw [one_lt_div (by linarith)]; simp only [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  set M₁ := maximalFunction μ h₁
  set M₂ := maximalFunction μ h₂
  set M₃ := maximalFunction μ h₃
  have hM₁ : Measurable M₁ := measurable_maximalFunction μ h₁
  have hM₂ : Measurable M₂ := measurable_maximalFunction μ h₂
  have hM₃ : Measurable M₃ := measurable_maximalFunction μ h₃
  -- The maximal inequality; the `‖·‖ₑ` of `ℝ≥0∞` is the identity.
  have hmax : ∀ {h : E → ℝ≥0∞}, AEMeasurable h μ → ∀ {e : ℝ}, 1 < e →
      ∫⁻ x, maximalFunction μ h x ^ e ∂μ ≤
        ENNReal.ofReal (2 * e * 2 ^ (e - 1) / (e - 1)) * 4 ^ Module.finrank ℝ E *
          ∫⁻ x, h x ^ e ∂μ := fun {h} hh {e} he => by
    simpa only [enorm_eq_self] using lintegral_rpow_maximalFunction_le μ (f := h) hh he
  -- Pointwise: `g^s = (g²)^r ≤ 2^(r-1) (2^(r-1) ((α₁ M₁)^r + (α₂ M₂)^r) + (α₃ M₃^(1/q))^r)`.
  have hpt : ∀ x, g x ^ s ≤ 2 ^ (r - 1) * (2 ^ (r - 1) *
      (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) + α₃ ^ r * M₃ x ^ (r / q)) := fun x => by
    have hgs : g x ^ s = (g x ^ 2) ^ r := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; congr 1; simp only [r]; push_cast; ring
    rw [hgs]
    refine (ENNReal.rpow_le_rpow (hg x) hr0).trans ?_
    refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le).trans ?_
    gcongr
    · refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le).trans_eq ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ENNReal.mul_rpow_of_nonneg _ _ hr0]
    · rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul, inv_mul_eq_div]
  have m₁ : Measurable fun x => α₁ ^ r * M₁ x ^ r := (hM₁.pow_const r).const_mul _
  have m₂ : Measurable fun x => α₂ ^ r * M₂ x ^ r := (hM₂.pow_const r).const_mul _
  have m₃ : Measurable fun x => α₃ ^ r * M₃ x ^ (r / q) := (hM₃.pow_const _).const_mul _
  have m₁₂ : Measurable fun x => α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r := m₁.add m₂
  have m : Measurable fun x => 2 ^ (r - 1) * (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) +
      α₃ ^ r * M₃ x ^ (r / q) := (m₁₂.const_mul _).add m₃
  calc ∫⁻ x, g x ^ s ∂μ
      ≤ ∫⁻ x, 2 ^ (r - 1) * (2 ^ (r - 1) *
          (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) + α₃ ^ r * M₃ x ^ (r / q)) ∂μ :=
        lintegral_mono hpt
    _ = 2 ^ (r - 1) * (2 ^ (r - 1) * (α₁ ^ r * ∫⁻ x, M₁ x ^ r ∂μ +
          α₂ ^ r * ∫⁻ x, M₂ x ^ r ∂μ) + α₃ ^ r * ∫⁻ x, M₃ x ^ (r / q) ∂μ) := by
        rw [lintegral_const_mul _ m, lintegral_add_right _ m₃, lintegral_const_mul _ m₁₂,
          lintegral_add_right _ m₂, lintegral_const_mul _ (hM₁.pow_const r),
          lintegral_const_mul _ (hM₂.pow_const r), lintegral_const_mul _ (hM₃.pow_const _)]
    _ ≤ _ := by
        gcongr
        · exact hmax h₁m hr
        · exact hmax h₂m hr
        · exact hmax h₃m hrq

/-- If `f → 0` along `l`, then eventually `K ofReal(f)^e < ε` for finite `K`, `e > 0` and
`ε > 0`; this is how the absorbed terms are made small. -/
private theorem eventually_mul_ofReal_rpow_lt {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto f l (𝓝 0)) {K : ℝ≥0∞} (hK : K ≠ ∞) {e : ℝ} (he : 0 < e) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∀ᶠ x in l, K * ENNReal.ofReal (f x) ^ e < ε := by
  have h := ENNReal.Tendsto.const_mul
    (((ENNReal.continuous_rpow_const (y := e)).tendsto _).comp (ENNReal.tendsto_ofReal hf))
    (Or.inr hK)
  rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos he, mul_zero] at h
  exact h.eventually (gt_mem_nhds hε)

/-- The estimate before absorption: `∫ ‖∇u‖^s` is bounded by the Fefferman–Stein constant times
the integrated pointwise bound for the sharp maximal function, in which `∫ ‖∇u‖^s` reappears with
the factors `κ⁻²` and `δ^(1/q')`. -/
private theorem lintegral_enorm_gradient_rpow_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' s : ℝ} (hqq : q.HolderConjugate q') (hq : 1 < q)
    (hqs : 2 * q < s) (hqp : ENNReal.ofReal (2 * q) ≤ p) {κ : ℝ} (hκ : 1 ≤ κ) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤
      CFS * ∫⁻ x, sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ s) :
    ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤ CFS * (2 ^ (s / 2 - 1) * (2 ^ (s / 2 - 1) *
        (ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (s / 2) *
          (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
            4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
              ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s) +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (s / 2) *
          (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
            4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) * ∫⁻ x, ‖G x‖ₑ ^ s)) +
      ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
          ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹) ^ (s / 2) *
        (ENNReal.ofReal (2 * (s / 2 / q) * 2 ^ (s / 2 / q - 1) / (s / 2 / q - 1)) *
          4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
            ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s))) := by
  have hpt := sq_sharpMaximalFunction_gradient_le ha hbd hosc hu h2p hgp hGp hqq hqp hκ
  generalize (⇑(W1p.gradient u) : EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (n + 1))) = g at hgp hpt hFS ⊢
  have hgm : AEStronglyMeasurable g volume := hgp.aestronglyMeasurable
  have hsq : ∀ (y : ℝ≥0∞) (e : ℝ), e * (s / e) = s → (y ^ e) ^ (s / e) = y ^ s :=
    fun y e he => by rw [← ENNReal.rpow_mul, he]
  have hy2 : ∀ y : ℝ≥0∞, (y ^ 2) ^ (s / 2) = y ^ s := fun y => by
    rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    exact hsq y 2 (by ring)
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hy3 : ∀ y : ℝ≥0∞, (y ^ (2 * q)) ^ (s / 2 / q) = y ^ s := fun y => by
    rw [div_div]; exact hsq y (2 * q) (by field_simp)
  have hbound := lintegral_rpow_le_of_sq_le_maximalFunction (g := fun x =>
      sharpMaximalFunction volume g x) volume
    (h₁ := fun y => ‖g y‖ₑ ^ 2) (h₂ := fun y => ‖G y‖ₑ ^ 2) (h₃ := fun y => ‖g y‖ₑ ^ (2 * q))
    (hgm.enorm.pow_const 2) (hGp.aestronglyMeasurable.enorm.pow_const 2)
    (hgm.enorm.pow_const _) hq hqs hpt
  simp only [hy2, hy3] at hbound
  exact hFS.trans (mul_le_mul_right hbound _)

/-- The absorption step: if `I ≤ A I + K J + B I` with `A, B ≤ 1/4` and `I < ∞`, then
`I ≤ 2 K J`. -/
private theorem le_two_mul_mul_of_le_mul_add_mul_add_mul {I J A B K : ℝ≥0∞} (hI : I ≠ ∞)
    (hA : A ≤ 2⁻¹ / 2) (hB : B ≤ 2⁻¹ / 2) (h : I ≤ A * I + K * J + B * I) : I ≤ 2 * K * J := by
  have hhalf : 2⁻¹ * I + 2⁻¹ * I ≤ 2⁻¹ * I + K * J := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    refine h.trans ?_
    calc A * I + K * J + B * I ≤ 2⁻¹ / 2 * I + K * J + 2⁻¹ / 2 * I := by gcongr
      _ = 2⁻¹ * I + K * J := by rw [add_right_comm, ← add_mul, ENNReal.add_halves]
  calc I = 2 * (2⁻¹ * I) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * (K * J) := by
        gcongr 2 * ?_
        exact ENNReal.le_of_add_le_add_left (a := 2⁻¹ * I) (ENNReal.mul_ne_top (by simp) hI) hhalf
    _ = 2 * K * J := (mul_assoc _ _ _).symm

/-- The algebra rearranging the estimate before absorption. -/
private theorem mul_mul_add_mul_add_mul_eq {R : Type*} [CommSemiring R]
    (C t m m' X₁ X₂ X₃ I J : R) :
    C * (t * (t * (X₁ * (m * I) + X₂ * (m * J)) + X₃ * (m' * I))) =
      C * t * t * m * X₁ * I + C * t * t * X₂ * m * J + C * t * m' * X₃ * I := by
  ring

/-- The choice of the parameters: for finite `K₁, K₃`, there are `κ ≥ 1` and `δ > 0` making the
decaying term and the coefficient term of the estimate before absorption at most `1/4`. -/
private theorem exists_one_le_and_pos_of_ne_top (lam Lam : ℝ) {q q' s : ℝ} (hq' : 0 < q')
    (hs : 0 < s) {K₁ K₃ : ℝ≥0∞} (hK₁ : K₁ ≠ ∞) (hK₃ : K₃ ≠ ∞) :
    ∃ κ : ℝ, 1 ≤ κ ∧
      K₁ * ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (s / 2) ≤ 2⁻¹ / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧
        K₃ * ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
          ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹) ^ (s / 2) ≤ 2⁻¹ / 2 := by
  have hquarter : (0 : ℝ≥0∞) < 2⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  have hs2 : 0 < s / 2 := by linarith
  have h1 : Tendsto (fun κ : ℝ => decayConst n lam Lam / κ ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h0 := h1.mul_const ((2 : ℝ) ^ (n + 1))
  rw [zero_mul] at h0
  obtain ⟨κ, hκ, hκ1⟩ := ((eventually_ge_atTop 1).and
    (eventually_mul_ofReal_rpow_lt h0 hK₁ hs2 hquarter)).exists
  refine ⟨κ, hκ, hκ1.le, ?_⟩
  have hq'' : 0 < q'⁻¹ := inv_pos.2 hq'
  set c₃ : ℝ → ℝ := fun δ => forcingConst n lam Lam * κ ^ (n + 1) *
    ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹
  have hc : ContinuousAt c₃ 0 := by
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hq''.le)).comp (by fun_prop)
  have hc0' : Tendsto c₃ (𝓝[>] 0) (𝓝 0) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hc0 : c₃ 0 = 0 := by simp [c₃, Real.zero_rpow hq''.ne']
    rwa [hc0] at h
  obtain ⟨δ, hδ1, hδ⟩ := ((eventually_mul_ofReal_rpow_lt hc0' hK₃ hs2 hquarter).and
    self_mem_nhdsWithin).exists
  exact ⟨δ, hδ, hδ1.le⟩

/-- The estimate for fixed parameters `κ` and `δ` small enough for the absorption. -/
private theorem eLpNorm_gradient_le_of_le_quarter
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' s : ℝ} (hs_def : s = p.toReal) (hs : 2 < s)
    (hqq : q.HolderConjugate q') (hq : 1 < q) (hqs : 2 * q < s)
    (hqp : ENNReal.ofReal (2 * q) ≤ p) {κ : ℝ} (hκ : 1 ≤ κ) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤
      CFS * ∫⁻ x, sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ s)
    (hκ1 : CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
        (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
          4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))) *
        ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (s / 2) ≤ 2⁻¹ / 2)
    (hδ1 : CFS * 2 ^ (s / 2 - 1) *
        (ENNReal.ofReal (2 * (s / 2 / q) * 2 ^ (s / 2 / q - 1) / (s / 2 / q - 1)) *
          4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))) *
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
          ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹) ^ (s / 2) ≤ 2⁻¹ / 2) :
    eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) p volume ≤
      (2 * (CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (s / 2) *
          (ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
            4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))))) ^ (1 / s) *
        eLpNorm G p volume := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans hp).ne'
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.2 (zero_le_two.trans hs.le)
  have key := lintegral_enorm_gradient_rpow_le ha hbd hosc hu hp.le hgp hGp hqq hq hqs hqp hκ hFS
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hgp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hGp.aestronglyMeasurable, ← hs_def,
    ← ENNReal.mul_rpow_of_nonneg _ _ hs1]
  have hI := (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hgp.eLpNorm_lt_top).ne
  rw [← hs_def] at hI
  exact ENNReal.rpow_le_rpow (le_two_mul_mul_of_le_mul_add_mul_add_mul hI hκ1 hδ1
    (key.trans_eq (mul_mul_add_mul_add_mul_eq _ _ _ _ _ _ _ _ _))) hs1

/-- **The `W^{1,p}` estimate for coefficients of small mean oscillation.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`, such
that on every ball `B` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of the attached bilinear
forms. Let `u ∈ H¹(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ Lᵖ`, and let `∇u` be integrable
and in `Lᵖ`. Then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. -/
theorem exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          Integrable
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          MemLp G p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = p.toReal := ⟨_, rfl⟩
  have hs : 2 < s := by
    rw [hs_def]
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp_top).2 hp
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = (1 + s / 2) / 2 := ⟨_, rfl⟩
  have hq : 1 < q := by rw [hq_def]; linarith
  have hqs : 2 * q < s := by rw [hq_def]; linarith
  obtain ⟨q', hqq⟩ : ∃ q' : ℝ, q.HolderConjugate q' :=
    ⟨_, Real.HolderConjugate.conjExponent hq⟩
  have hqp : ENNReal.ofReal (2 * q) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp_top, ← hs_def]
    exact ENNReal.ofReal_le_ofReal hqs.le
  obtain ⟨CFS, hFS⟩ := exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow
    (ι := Fin (n + 1)) (F := EuclideanSpace ℝ (Fin (n + 1))) (show 1 < s by linarith)
  set cM : ℝ≥0∞ := ENNReal.ofReal (2 * (s / 2) * 2 ^ (s / 2 - 1) / (s / 2 - 1)) *
    4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set cM' : ℝ≥0∞ := ENNReal.ofReal (2 * (s / 2 / q) * 2 ^ (s / 2 / q - 1) / (s / 2 / q - 1)) *
    4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  have hcM : cM ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have hcM' : cM' ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have h2 : (2 : ℝ≥0∞) ^ (s / 2 - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  obtain ⟨κ, hκ, hκ1, δ, hδ, hδ1⟩ := exists_one_le_and_pos_of_ne_top (n := n) lam Lam (q := q)
    hqq.symm.pos (by linarith : 0 < s)
    (K₁ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * cM)
    (K₃ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * cM')
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2) hcM)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) hcM')
  have hK₂ : (2 * ((CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
      ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (s / 2) * cM)) ^
        (1 / s) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (by linarith)) (ENNReal.mul_ne_top
      ENNReal.ofNat_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) hcM))
  refine ⟨ENNReal.toNNReal ((2 * ((CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
      ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (s / 2) * cM)) ^
        (1 / s)), δ, hδ, fun {a} ha hbd hosc u G hu hint hgp hGp => ?_⟩
  rw [ENNReal.coe_toNNReal hK₂]
  exact eLpNorm_gradient_le_of_le_quarter ha hbd hosc hu hp hp_top hgp hGp hs_def hs hqq hq hqs
    hqp hκ (hFS _ hint) hκ1 hδ1

end PDE

end TauCeti
