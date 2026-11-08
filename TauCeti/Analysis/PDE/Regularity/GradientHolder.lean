/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the gradient for `-div(a ∇u) = -div G`

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in an
open set `Ω ⊆ ℝ^{n+1}`, that is

`∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`,

and let `0 < α < 1`. This file proves that `∇u` is as regular as the coefficients and the data
in the interior: if the open `R`-thickening `S_R` of a set `S` lies in `Ω`, `a` is uniformly
elliptic on `S_R` with constants `λ ≤ Λ ≤ κ λ`, and `a` and `G` are `α`-Hölder on `S_R` with
constants `K_a` and `K_G`, then the precise representative of `∇u` is `α`-Hölder on `S` with
constant

`C (K_G / λ + (R^{-(n+1)/2-α} + (K_a / λ)^{((n+1)/2+α)/α}) ‖∇u‖_{L²(Ω)})`,

where `C` depends only on `n`, `α` and `κ`. This is the interior Schauder estimate for
divergence-form equations with Hölder continuous coefficients, and its proof is Campanato's. The
coefficient enters only through the ratio `K_a / λ`, which is unchanged under `a ↦ t a` for
`t > 0`, and the ellipticity ratio `Λ / λ`; for `a = 1` the estimate reads
`[∇u]_{α, S} ≤ C ([G]_{α, S_R} + R^{-(n+1)/2-α} ‖∇u‖)`.

## The argument

Fix a ball `B_r = ball x r ⊆ Ω` and freeze the coefficients at its centre. The replacement `w`
of `u` on `B_r` solving `-div(a(x) ∇w) = 0` with the boundary values of `u`
(`TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le`)
satisfies

`∫_{B_r} ‖∇u - ∇w‖² ≤ 2 r^{2α} λ^{-2} (K_a² ∫_{B_r} ‖∇u‖² + K_G² |B_r|)`,

and both `∫_{B_ρ} ‖∇w‖²` and the square mean oscillation of `∇w` decay from `B_r` to `B_ρ`,
like `(ρ / r)^{n+1}` and `(ρ / r)^{n+3}`
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero`,
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`).
So `φ(t) = ∫_{B_t} ‖∇u‖²` and `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfy, for `0 < ρ ≤ r`,

`φ(ρ) ≤ A ((ρ / r)^{n+1} φ(r) + F(r))` and `ψ(ρ) ≤ A ((ρ / r)^{n+3} ψ(r) + F(r))`,

with `F(r)` the right side of the energy error. The term `r^{2α} K_a² φ(r)` is not of higher
order by itself, so the estimate is bootstrapped in three passes, each using the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add`, on balls small enough that
`K_a r^α ≤ δ λ`:

* **Morrey's estimate.** The coefficient term is a small perturbation of the decay of `φ`, so
  `φ(ρ) = O(ρ^{n+1-α})`.
* **A first Campanato estimate.** Then `F(r) = O(r^{n+1+α})`, so `ψ(ρ) = O(ρ^{n+1+α})`: the mean
  oscillation of `∇u` on `B_ρ` is `O(ρ^{α/2})`, and
  `MeasureTheory.Lp.norm_preciseRepresentative_le_of_setAverage_norm_sub_le` bounds the precise
  representative of `∇u` near `S`.
* **The sharp Campanato estimate.** For bounded `∇u`, `φ(r) = O(r^{n+1})`, so
  `F(r) = O(r^{n+1+2α})` and `ψ(ρ) = O(ρ^{n+1+2α})`: `∇u` is `α`-Hölder
  (`MeasureTheory.Lp.dist_preciseRepresentative_le_of_forall_setAverage_norm_sub_le`).

Balls whose radius violates the smallness condition are avoided by shrinking `R`, which is where
the term `(K_a / λ)^{((n+1)/2+α)/α}` comes from.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`: the interior Hölder estimate
  for `∇u`, with explicit dependence on `K_a / λ`, `K_G / λ`, `R` and `‖∇u‖_{L²(Ω)}`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Theorems 5.17 and 5.19.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Theorems 3.8 and 3.13.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.32.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- The constant `4 · 2^{n+1} κ^{(n+1)/2} + 2` of the comparison estimate for `∫_{B_t} ‖∇u‖²`. -/
private def massConst (n : ℕ) (κ : ℝ) : ℝ := 4 * (2 ^ (n + 1) * √κ ^ (n + 1)) + 2

/-- The constant `4 · 2^{3n+13} (n+2)² κ^{(n+3)/2} + 2` of the comparison estimate for the square
mean oscillation of `∇u`. -/
private def oscConst (n : ℕ) (κ : ℝ) : ℝ :=
  4 * (2 ^ (3 * (n + 1) + 10) * ((n : ℝ) + 2) ^ 2 * √κ ^ (n + 3)) + 2

private theorem massConst_nonneg (n : ℕ) (κ : ℝ) : 0 ≤ massConst n κ := by
  unfold massConst
  positivity

private theorem oscConst_nonneg (n : ℕ) (κ : ℝ) : 0 ≤ oscConst n κ := by
  unfold oscConst
  positivity

/-- The measure `ω` of the unit ball of `ℝ^{n+1}`. -/
private def unitBallVolume (n : ℕ) : ℝ :=
  volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

private theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n :=
  measureReal_nonneg

/-- The volume of a ball of radius `t > 0` in `ℝ^{n+1}` is `t^{n+1}` times that of the unit
ball. -/
private theorem measureReal_ball_eq (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 0 < t) :
    volume.real (ball x t) = t ^ (n + 1) * unitBallVolume n := by
  rw [Measure.addHaar_real_ball_of_pos _ _ ht, finrank_euclideanSpace_fin, unitBallVolume]

/-- The data part of the energy error on `B_t = ball x t`:
`2 (t^α)² λ^{-2} K² |B_t| = 2 ω (K / λ)² t^{n+1+2α}`, where `ω` is the measure of the unit
ball. -/
private theorem two_mul_rpow_sq_div_mul_measureReal_ball_eq (x : EuclideanSpace ℝ (Fin (n + 1)))
    {t : ℝ} (ht : 0 < t) (a lam K : ℝ) :
    2 * (t ^ a) ^ 2 / lam ^ 2 * (K ^ 2 * volume.real (ball x t)) =
      2 * unitBallVolume n * (K / lam) ^ 2 * t ^ ((n : ℝ) + 1 + 2 * a) := by
  rw [measureReal_ball_eq x ht, show (n : ℝ) + 1 + 2 * a = 2 * a + (n + 1 : ℕ) by push_cast; ring,
    ← Real.rpow_sq_mul_rpow ht, Real.rpow_natCast, div_pow]
  ring

/-- Assembling a comparison estimate: if `X ≤ 4 A Y + (4 B + 2) E` with the decay constants
`A ≤ D q` and `B ≤ D` and the energy error `E ≤ F`, then `X ≤ (4 D + 2) (q Y + F)`. -/
private theorem le_mul_add_of_le_mul_add {X Y E F A B D q : ℝ} (hY : 0 ≤ Y) (hE0 : 0 ≤ E)
    (hq : 0 ≤ q) (hD : 0 ≤ D) (hA : A ≤ D * q) (hB : B ≤ D) (hE : E ≤ F)
    (h : X ≤ 4 * A * Y + (4 * B + 2) * E) : X ≤ (4 * D + 2) * (q * Y + F) :=
  calc X ≤ 4 * A * Y + (4 * B + 2) * E := h
    _ ≤ 4 * D * (q * Y) + (4 * D + 2) * F := by
        rw [← mul_assoc _ q, mul_assoc 4 D q]
        gcongr
    _ ≤ (4 * D + 2) * (q * Y) + (4 * D + 2) * F := by
        gcongr
        linarith
    _ = (4 * D + 2) * (q * Y + F) := by ring

/-- Squaring an energy estimate `λ X ≤ t (K_a N + K_G √V)` gives
`X² ≤ 2 t² λ^{-2} (K_a² N² + K_G² V)`. -/
private theorem sq_le_of_mul_le_mul_add {lam X N V t Ka KG : ℝ} (hlam : 0 < lam) (hX : 0 ≤ X)
    (hV : 0 ≤ V) (h : lam * X ≤ t * (Ka * N + KG * √V)) :
    X ^ 2 ≤ 2 * t ^ 2 / lam ^ 2 * (Ka ^ 2 * N ^ 2 + KG ^ 2 * V) := by
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  have h2 : (Ka * N + KG * √V) ^ 2 ≤ 2 * (Ka ^ 2 * N ^ 2 + KG ^ 2 * V) := by
    nlinarith [sq_nonneg (Ka * N - KG * √V), Real.sq_sqrt hV]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc X ^ 2 * lam ^ 2 = (lam * X) ^ 2 := by ring
    _ ≤ t ^ 2 * (Ka * N + KG * √V) ^ 2 := by rw [← mul_pow]; exact hsq
    _ ≤ t ^ 2 * (2 * (Ka ^ 2 * N ^ 2 + KG ^ 2 * V)) := by gcongr
    _ = 2 * t ^ 2 * (Ka ^ 2 * N ^ 2 + KG ^ 2 * V) := by ring

/-- The common hypotheses of the comparison estimates on `B_r = ball x r`: `u ∈ H¹(Ω)` solves
`-div(a ∇u) = -div G` weakly on `Ω ⊇ B_r`, `a(x)` is elliptic with constants `λ ≤ Λ ≤ κ λ`, and `a`
and `G` are `α`-Hölder on `B_r` with constants `K_a` and `K_G`. -/
private structure FrozenData (Omega : Opens (EuclideanSpace ℝ (Fin (n + 1))))
    (u : W1p volume Omega 2)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (lam Lam κ : ℝ) (α Ka KG : ℝ≥0) (x : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) : Prop where
  elliptic : UniformlyEllipticOn {x} a lam Lam
  ratio : Lam ≤ κ * lam
  pos : 0 < α
  holder_coeff : HolderOnWith Ka α (fun y => matrixBilinearForm (a y)) (ball x r)
  holder_data : HolderOnWith KG α G (ball x r)
  eq : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ y in Omega, ⟪G y, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ
  subset : ball x r ⊆ Omega

namespace FrozenData

variable {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam κ : ℝ}
  {α Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ}

private theorem mono (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) {r' : ℝ} (hr : r' ≤ r) :
    FrozenData Omega u a G lam Lam κ α Ka KG x r' where
  elliptic := h.elliptic
  ratio := h.ratio
  pos := h.pos
  holder_coeff := h.holder_coeff.mono (ball_subset_ball hr)
  holder_data := h.holder_data.mono (ball_subset_ball hr)
  eq := h.eq
  subset := (ball_subset_ball hr).trans h.subset

/-- **The frozen replacement.** On `B_r`, the solution `w` of `-div(a(x) ∇w) = 0` with the
boundary values of `u` satisfies
`∫_{B_r} ‖∇u - ∇w‖² ≤ 2 (r^α)² λ^{-2} (K_a² ∫_{B_r} ‖∇u‖² + K_G² |B_r|)`. -/
private theorem exists_replacement (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) :
    ∃ w : W1p volume (⟨ball x r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ v : W1p0 volume (⟨ball x r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
        energyFormH1 (fun _ => a x) 0 0 w (v : W1p volume _ 2) = 0) ∧
      MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict (ball x r)) ∧
      ∫ y in ball x r, ‖W1p.gradient u y - W1p.gradient w y‖ ^ 2 ≤
        2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
            KG ^ 2 * volume.real (ball x r)) := by
  have hB : (⟨ball x r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ Omega := h.subset
  obtain ⟨w, -, hw0, hest⟩ :=
    h.elliptic.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le (mem_singleton x) h.pos
      h.holder_coeff h.holder_data hB subset_rfl h.eq
  refine ⟨w, hw0, Lp.memLp (W1p.gradient w), ?_⟩
  have hN : ‖W1p.gradient (W1p.restrictL hB u)‖ ^ 2 = ∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hB u] with y hy
    rw [hy]
  calc ∫ y in ball x r, ‖W1p.gradient u y - W1p.gradient w y‖ ^ 2
      = ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 :=
        W1p.setIntegral_norm_gradient_sub_sq_eq hB u w
    _ ≤ _ := by
        rw [← hN]
        exact sq_le_of_mul_le_mul_add h.elliptic.pos (norm_nonneg _) measureReal_nonneg hest

/-- `∇u` is square integrable on `B_r`. -/
private theorem memLp_gradient (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) :
    MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x r)) :=
  (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono h.subset le_rfl)

/-- `‖∇u‖²` is integrable on `B_r`. -/
private theorem integrableOn_norm_gradient_sq (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) :
    IntegrableOn (fun y => ‖W1p.gradient u y‖ ^ 2) (ball x r) :=
  h.memLp_gradient.integrable_norm_pow two_ne_zero

/-- The frozen matrix `a(x)` is elliptic with constants `λ` and `Λ`. -/
private theorem frozen_bounds (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) :
    (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
      ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
  ⟨h.elliptic.lower_bound (mem_singleton x), fun ξ => (le_abs_self _).trans
    (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le
      (h.elliptic.upper_bound (mem_singleton x)) ξ)⟩

/-- The ellipticity ratio `Λ / λ` is at most `κ`. -/
private theorem div_le (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) : Lam / lam ≤ κ :=
  (div_le_iff₀ h.elliptic.pos).2 h.ratio

/-- **The comparison estimate for the `L²` mass of the gradient.** For `0 < ρ ≤ r`,
`φ(ρ) ≤ A₀ ((ρ / r)^{n+1} φ(r) + F(r))`, where `φ(t) = ∫_{B_t} ‖∇u‖²`,
`F(r) = 2 (r^α)² λ^{-2} (K_a² φ(r) + K_G² |B_r|)` and `A₀` depends only on `n` and `κ`. -/
private theorem setIntegral_norm_sq_le (h : FrozenData Omega u a G lam Lam κ α Ka KG x r)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ y in ball x ρ, ‖W1p.gradient u y‖ ^ 2 ≤
      massConst n κ * ((ρ / r) ^ (n + 1) * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
        2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
            KG ^ 2 * volume.real (ball x r))) := by
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, hwm, hE⟩ := h.exists_replacement
  obtain ⟨hlow, hAu⟩ := h.frozen_bounds
  have hdec := setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero
    h.elliptic.pos hlow hAu hw0 (x₀ := x) (R := r) subset_rfl hρ.le hρr
  rw [Fintype.card_fin] at hdec
  have hq0 : 0 ≤ (ρ / r) ^ (n + 1) := by positivity
  have hfm := h.memLp_gradient
  have hcomp := setIntegral_norm_sub_sq_le_add_of_le (b := 0) (k := 0) (c := 0)
    (f := fun y => W1p.gradient u y) (K := fun y => W1p.gradient w y)
    (ball_subset_ball hρr) (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) hq0
    (pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr))
    (hfm.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne 0)
    (hwm.integrableOn_norm_sub_sq_of_subset (ball_subset_ball hρr) measure_ball_lt_top.ne 0)
    ((hfm.sub hwm).integrable_norm_pow two_ne_zero) le_rfl
    (by simpa only [sub_zero, mul_assoc] using hdec)
  simp only [sub_zero] at hcomp
  -- The decay constant is at most the one for `Λ / λ = κ`.
  have hD : 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1) ≤ 2 ^ (n + 1) * √κ ^ (n + 1) := by
    gcongr
    exact h.div_le
  exact le_mul_add_of_le_mul_add (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)
    (integral_nonneg fun _ => by positivity) hq0 (by positivity)
    (mul_le_mul_of_nonneg_right hD hq0) hD hE (hcomp.trans_eq (by ring))

/-- **The perturbed decay of the `L²` mass of the gradient.** If the coefficient part of the energy
error on `B_r` is at most `ε` and its data part at most `D`, then for `0 < ρ ≤ r`
`φ(ρ) ≤ A₀ ((ρ / r)^{n+1} + ε) φ(r) + A₀ D`, where `φ(t) = ∫_{B_t} ‖∇u‖²` and `A₀` is the constant
of `setIntegral_norm_sq_le`. -/
private theorem setIntegral_norm_sq_le_of_le (h : FrozenData Omega u a G lam Lam κ α Ka KG x r)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) {ε D : ℝ} (hε : 2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * Ka ^ 2 ≤ ε)
    (hD : 2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * (KG ^ 2 * volume.real (ball x r)) ≤ D) :
    ∫ y in ball x ρ, ‖W1p.gradient u y‖ ^ 2 ≤
      massConst n κ * ((ρ / r) ^ ((n : ℝ) + 1) + ε) * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
        massConst n κ * D := by
  have hc := h.setIntegral_norm_sq_le hρ hρr
  have hpow : (ρ / r) ^ (n + 1) = (ρ / r) ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast, Nat.cast_add_one]
  have hA := massConst_nonneg n κ
  have hφ : 0 ≤ ∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  rw [hpow] at hc
  calc _ ≤ _ := hc
    _ = massConst n κ * ((ρ / r) ^ ((n : ℝ) + 1) * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
          2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * Ka ^ 2 * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
          2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * (KG ^ 2 * volume.real (ball x r))) := by ring
    _ ≤ massConst n κ * ((ρ / r) ^ ((n : ℝ) + 1) * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
          ε * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) + D) := by gcongr
    _ = _ := by ring

/-- **The comparison estimate for the mean oscillation of the gradient.** For `0 < ρ ≤ r`,
`ψ(ρ) ≤ A₁ ((ρ / r)^{n+3} ψ(r) + F(r))`, where `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`,
`F(r) = 2 (r^α)² λ^{-2} (K_a² ∫_{B_r} ‖∇u‖² + K_G² |B_r|)` and `A₁` depends only on `n` and `κ`. -/
private theorem setIntegral_norm_sub_setAverage_sq_le
    (h : FrozenData Omega u a G lam Lam κ α Ka KG x r) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
      oscConst n κ * ((ρ / r) ^ (n + 3) *
          (∫ y in ball x r, ‖W1p.gradient u y - ⨍ z in ball x r, W1p.gradient u z‖ ^ 2) +
        2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2) +
            KG ^ 2 * volume.real (ball x r))) := by
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, hwm, hE⟩ := h.exists_replacement
  obtain ⟨hlow, hAu⟩ := h.frozen_bounds
  have hdec :=
    setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
      h.elliptic.pos hlow hAu hw0 (x₀ := x) (R := r) subset_rfl
      (⨍ y in ball x r, W1p.gradient u y) hρ.le hρr
  simp only [Fintype.card_fin] at hdec
  have hfm := h.memLp_gradient
  have hcomp := setIntegral_norm_sub_setAverage_sq_le_add_of_subset (ball_subset_ball hρr)
    measure_ball_lt_top.ne hfm hwm (by positivity) hdec
  have hq0 : 0 ≤ (ρ / r) ^ (n + 3) := by positivity
  have hq1 : (ρ / r) ^ (n + 3) ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  -- The decay constant is at most the one for `Λ / λ = κ`.
  have hD : 2 ^ (3 * (n + 1) + 10) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * √(Lam / lam) ^ (n + 3) ≤
      2 ^ (3 * (n + 1) + 10) * ((n : ℝ) + 2) ^ 2 * √κ ^ (n + 3) := by
    push_cast
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    gcongr
    exact h.div_le
  have hD0 : 0 ≤ 2 ^ (3 * (n + 1) + 10) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * √(Lam / lam) ^ (n + 3) :=
    by positivity
  exact le_mul_add_of_le_mul_add (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)
    (integral_nonneg fun _ => by positivity) hq0 (by positivity)
    (mul_le_mul_of_nonneg_right hD hq0) ((mul_le_of_le_one_right hD0 hq1).trans hD) hE hcomp

end FrozenData

/-- **Campanato decay of the gradient.** Let `A ≥ 0` and `β < n + 3`. There is `C`, depending
only on `n`, `A` and `β`, such that the following holds. Let `u ∈ H¹(Ω)` with `ball x R ⊆ Ω`, and
suppose that the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies
`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B r^β` for `0 < ρ ≤ r ≤ R`, with `B ≥ 0`. Then
`ψ(ρ) ≤ C ((ρ / R)^β ‖∇u‖²_{L²(Ω)} + B ρ^β)` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le {A β : ℝ} (hA : 0 ≤ A)
    (hβ : β < n + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2} {x : EuclideanSpace ℝ (Fin (n + 1))} {R B : ℝ}, 0 ≤ B →
      ball x R ⊆ Omega →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          A * (ρ / r) ^ (n + 3) *
              (∫ y in ball x r, ‖W1p.gradient u y - ⨍ z in ball x r, W1p.gradient u z‖ ^ 2) +
            B * r ^ β) →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * ((ρ / R) ^ β * ‖W1p.gradient u‖ ^ 2 + B * ρ ^ β) := by
  have hβ' : β < ((n + 3 : ℕ) : ℝ) := by push_cast; exact hβ
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA hβ' hβ'
  refine ⟨C, hC.le, ?_⟩
  intro Omega u x R B hB hball hcomp ρ hρ hρR
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set ψ : ℝ → ℝ := fun t => ∫ y in ball x t, ‖f y - ⨍ z in ball x t, f z‖ ^ 2
  have hfint : ∀ t ≤ R, IntegrableOn f (ball x t) ∧
      ∀ c, IntegrableOn (fun y => ‖f y - c‖ ^ 2) (ball x t) := fun t ht =>
    ⟨(Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne,
      (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne⟩
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => setIntegral_nonneg measurableSet_ball fun _ _ => by
    positivity
  -- `ψ` is nondecreasing, since the average is the best constant in square mean.
  have hmono : MonotoneOn ψ (Ioc 0 R) := fun s hs t ht hst =>
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfint s hs.2).1 ((hfint s hs.2).2 _)).trans
      (setIntegral_mono_set ((hfint t ht.2).2 _) (ae_of_all _ fun _ => by positivity)
        (ball_subset_ball hst).eventuallyLE)
  have hdec := hit (φ := ψ) (R := R) (B := B) (ε := 0) hB hε₀.le hmono (fun t _ => hψ0 t)
    (fun s t hs hst htR => by
      simpa only [add_zero, Real.rpow_natCast, mul_assoc] using hcomp s t hs hst htR)
    ρ R hρ hρR le_rfl
  -- `ψ R ≤ ‖∇u‖²`.
  have hψR : ψ R ≤ ‖W1p.gradient u‖ ^ 2 := by
    have h0 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
      measure_ball_lt_top.ne (hfint R le_rfl).1 ((hfint R le_rfl).2 0)
    simp only [sub_zero] at h0
    exact h0.trans (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) hball)
  refine hdec.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact add_le_add_left (mul_le_mul_of_nonneg_left hψR
    (Real.rpow_nonneg (div_nonneg hρ.le (hρ.trans_le hρR).le) β)) _

/-- Squaring `N ≤ M R^{(n+1)/2+α}` gives `N² ≤ M² R^{n+1+2α}`. -/
private theorem sq_le_mul_rpow_of_le {N M R α : ℝ} (hR : 0 < R) (hN : 0 ≤ N)
    (h : N ≤ M * R ^ (((n : ℝ) + 1) / 2 + α)) : N ^ 2 ≤ M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) := by
  have h2 : (R ^ (((n : ℝ) + 1) / 2 + α)) ^ 2 = R ^ ((n : ℝ) + 1 + 2 * α) := by
    rw [← Real.rpow_mul_natCast hR.le]
    ring_nf
  rw [← h2, ← mul_pow]
  exact pow_le_pow_left₀ hN h 2

end Comparison

section Passes

variable {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam κ : ℝ}
  {α Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ}

/-- From `K_G / λ ≤ M` with `λ > 0`: `0 ≤ M` and `(K_G / λ)² ≤ M²`. -/
private theorem nonneg_and_div_sq_le_sq (hlam : 0 < lam) (hM : KG / lam ≤ M) :
    0 ≤ M ∧ ((KG : ℝ) / lam) ^ 2 ≤ M ^ 2 :=
  have h0 : (0 : ℝ) ≤ KG / lam := by positivity
  ⟨h0.trans hM, pow_le_pow_left₀ h0 hM 2⟩

/-- On balls of radius `R` with `K_a R^α ≤ δ λ`, `(K_a / λ)² (R^α)² ≤ δ²`. -/
private theorem div_sq_mul_rpow_sq_le {δ : ℝ} (hlam : 0 < lam) (hR : 0 < R)
    (hsmall : Ka * R ^ (α : ℝ) ≤ δ * lam) :
    ((Ka : ℝ) / lam) ^ 2 * (R ^ (α : ℝ)) ^ 2 ≤ δ ^ 2 :=
  calc ((Ka : ℝ) / lam) ^ 2 * (R ^ (α : ℝ)) ^ 2 = (Ka * R ^ (α : ℝ)) ^ 2 / lam ^ 2 := by ring
    _ ≤ (δ * lam) ^ 2 / lam ^ 2 := by gcongr
    _ = δ ^ 2 := by field_simp

/-- On balls of radius at most `R` with `K_a R^α ≤ δ λ`, the coefficient part of the energy error
is `2 (r^α)² λ^{-2} K_a² ≤ 2 δ²`. -/
private theorem two_mul_rpow_sq_div_mul_le {δ r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (hrR : r ≤ R)
    (hsmall : Ka * R ^ (α : ℝ) ≤ δ * lam) :
    2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * Ka ^ 2 ≤ 2 * δ ^ 2 :=
  calc 2 * (r ^ (α : ℝ)) ^ 2 / lam ^ 2 * Ka ^ 2 = 2 * (((Ka : ℝ) / lam) ^ 2 * (r ^ (α : ℝ)) ^ 2) :=
        by ring
    _ ≤ 2 * δ ^ 2 := by
        gcongr
        exact div_sq_mul_rpow_sq_le hlam hr
          ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrR α.2) Ka.2).trans hsmall)

/-- If `K_G / λ ≤ M`, the data part of the energy error on `B_t = ball x t` is
`2 (t^α)² λ^{-2} K_G² |B_t| ≤ 2 ω M² t^{n+1+2α}`, where `ω` is the measure of the unit ball. -/
private theorem two_mul_rpow_sq_div_mul_measureReal_ball_le (x : EuclideanSpace ℝ (Fin (n + 1)))
    {t : ℝ} (ht : 0 < t) (hlam : 0 < lam) (hM : KG / lam ≤ M) :
    2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (KG ^ 2 * volume.real (ball x t)) ≤
      2 * unitBallVolume n * M ^ 2 * t ^ ((n : ℝ) + 1 + 2 * α) := by
  rw [two_mul_rpow_sq_div_mul_measureReal_ball_eq x ht]
  have := unitBallVolume_nonneg n
  gcongr

/-- On balls of radius `t ≤ R` with `K_a R^α ≤ δ λ`, Morrey's bound
`N ≤ C M² R^{3α} t^{n+1-α}` on `N = ∫_{B_t} ‖∇u‖²` makes the coefficient part of the energy error
`2 (t^α)² λ^{-2} K_a² N ≤ 2 δ² C M² R^α t^{n+1+α}`. -/
private theorem two_mul_rpow_sq_div_mul_mul_le {δ C t N : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C)
    (ht : 0 < t) (htR : t ≤ R) (hsmall : Ka * R ^ (α : ℝ) ≤ δ * lam)
    (hN : N ≤ C * M ^ 2 * R ^ (3 * (α : ℝ)) * t ^ ((n : ℝ) + 1 - α)) :
    2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (Ka ^ 2 * N) ≤
      2 * δ ^ 2 * C * M ^ 2 * R ^ (α : ℝ) * t ^ ((n : ℝ) + 1 + α) := by
  have hR : 0 < R := ht.trans_le htR
  have hR3 : R ^ (3 * (α : ℝ)) = (R ^ (α : ℝ)) ^ 2 * R ^ (α : ℝ) := by
    rw [Real.rpow_sq_mul_rpow hR]
    ring_nf
  have ht1 : (t ^ (α : ℝ)) ^ 2 * t ^ ((n : ℝ) + 1 - α) = t ^ ((n : ℝ) + 1 + α) := by
    rw [Real.rpow_sq_mul_rpow ht]
    ring_nf
  calc 2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (Ka ^ 2 * N)
      = 2 * ((Ka : ℝ) / lam) ^ 2 * (t ^ (α : ℝ)) ^ 2 * N := by field_simp
    _ ≤ 2 * ((Ka : ℝ) / lam) ^ 2 * (t ^ (α : ℝ)) ^ 2 *
          (C * M ^ 2 * R ^ (3 * (α : ℝ)) * t ^ ((n : ℝ) + 1 - α)) := by gcongr
    _ = 2 * C * M ^ 2 * R ^ (α : ℝ) * (((Ka : ℝ) / lam) ^ 2 * (R ^ (α : ℝ)) ^ 2) *
          ((t ^ (α : ℝ)) ^ 2 * t ^ ((n : ℝ) + 1 - α)) := by
        rw [hR3]
        ring
    _ ≤ 2 * C * M ^ 2 * R ^ (α : ℝ) * δ ^ 2 * t ^ ((n : ℝ) + 1 + α) := by
        rw [ht1]
        gcongr
        exact div_sq_mul_rpow_sq_le hlam hR hsmall
    _ = _ := by ring

/-- **Morrey's estimate.** Let `0 < α`. There are `δ > 0` and `C`, depending only on `n`, `α`
and `κ`, such that the following holds. Under the hypotheses of the comparison estimates on
`B_R = ball x R`, if `K_a R^α ≤ δ λ`, `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}` and `K_G / λ ≤ M`, then
`∫_{B_ρ} ‖∇u‖² ≤ C M² R^{3α} ρ^{n+1-α}` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_norm_sq_le (hα : 0 < α) (κ : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ},
      FrozenData Omega u a G lam Lam κ α Ka KG x R → Ka * R ^ (α : ℝ) ≤ δ * lam →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) → KG / lam ≤ M →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y‖ ^ 2 ≤
          C * M ^ 2 * R ^ (3 * (α : ℝ)) * ρ ^ ((n : ℝ) + 1 - α) := by
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
    (massConst_nonneg n κ) (α := (n : ℝ) + 1) (β := (n : ℝ) + 1 - α) (γ := (n : ℝ) + 1 - α)
    (by linarith) (by linarith)
  have hω0 := unitBallVolume_nonneg n
  refine ⟨√(ε₀ / 2), C * (1 + 2 * massConst n κ * unitBallVolume n), by positivity, by
    have := massConst_nonneg n κ; positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG x R M h hsmall hM1 hM2 ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hlam : 0 < lam := h.elliptic.pos
  have hM := (nonneg_and_div_sq_le_sq hlam hM2).1
  have hδ : 2 * √(ε₀ / 2) ^ 2 = ε₀ := by rw [Real.sq_sqrt (by positivity)]; ring
  set φ : ℝ → ℝ := fun t => ∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => setIntegral_nonneg measurableSet_ball fun _ _ => by
    positivity
  have hmono : MonotoneOn φ (Ioc 0 R) := fun s hs t ht hst =>
    setIntegral_mono_set (h.mono ht.2).integrableOn_norm_gradient_sq
      (ae_of_all _ fun _ => by positivity) (ball_subset_ball hst).eventuallyLE
  -- The data part of the energy error is `O(t^{n+1+2α}) ≤ O(R^{3α} t^{n+1-α})`.
  have hdata : ∀ t, 0 < t → t ≤ R →
      2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (KG ^ 2 * volume.real (ball x t)) ≤
        2 * unitBallVolume n * M ^ 2 * R ^ (3 * (α : ℝ)) * t ^ ((n : ℝ) + 1 - α) := by
    intro t ht htR
    refine (two_mul_rpow_sq_div_mul_measureReal_ball_le x ht hlam hM2).trans ?_
    rw [show (n : ℝ) + 1 + 2 * α = 3 * α + ((n : ℝ) + 1 - α) by ring, Real.rpow_add ht,
      ← mul_assoc]
    gcongr
  -- The comparison estimate in the form of the iteration lemma, with `ε = 2 δ² = ε₀`.
  have hstep : ∀ s t, 0 < s → s ≤ t → t ≤ R →
      φ s ≤ massConst n κ * ((s / t) ^ ((n : ℝ) + 1) + ε₀) * φ t +
        massConst n κ * 2 * unitBallVolume n * M ^ 2 * R ^ (3 * (α : ℝ)) *
          t ^ ((n : ℝ) + 1 - α) := by
    intro s t hs hst htR
    have ht : 0 < t := hs.trans_le hst
    have hsm := two_mul_rpow_sq_div_mul_le hlam ht htR hsmall
    rw [hδ] at hsm
    refine ((h.mono htR).setIntegral_norm_sq_le_of_le hs hst hsm (hdata t ht htR)).trans_eq ?_
    ring
  have hdec := hit (φ := φ) (R := R)
    (B := massConst n κ * 2 * unitBallVolume n * M ^ 2 * R ^ (3 * (α : ℝ))) (ε := ε₀)
    (by have := massConst_nonneg n κ; positivity) le_rfl hmono (fun t _ => hφ0 t) hstep
    ρ R hρ hρR le_rfl
  -- `φ R ≤ ‖∇u‖² ≤ M² R^{n+1+2α}`.
  have hφR : φ R ≤ M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) :=
    (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) h.subset).trans
      (sq_le_mul_rpow_of_le hR (norm_nonneg _) hM1)
  have hρR' : (ρ / R) ^ ((n : ℝ) + 1 - α) * R ^ ((n : ℝ) + 1 + 2 * α) =
      R ^ (3 * (α : ℝ)) * ρ ^ ((n : ℝ) + 1 - α) := by
    rw [Real.div_rpow_mul_rpow hρ.le hR,
      show (n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1 - α) = 3 * α by ring]
  have h1 : (ρ / R) ^ ((n : ℝ) + 1 - α) * φ R ≤
      M ^ 2 * R ^ (3 * (α : ℝ)) * ρ ^ ((n : ℝ) + 1 - α) := by
    calc (ρ / R) ^ ((n : ℝ) + 1 - α) * φ R
        ≤ (ρ / R) ^ ((n : ℝ) + 1 - α) * (M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α)) := by gcongr
      _ = _ := by rw [mul_left_comm, hρR', mul_assoc]
  calc φ ρ ≤ C * ((ρ / R) ^ ((n : ℝ) + 1 - α) * φ R +
        massConst n κ * 2 * unitBallVolume n * M ^ 2 * R ^ (3 * (α : ℝ)) *
          ρ ^ ((n : ℝ) + 1 - α)) := hdec
    _ ≤ C * (M ^ 2 * R ^ (3 * (α : ℝ)) * ρ ^ ((n : ℝ) + 1 - α) +
        massConst n κ * 2 * unitBallVolume n * M ^ 2 * R ^ (3 * (α : ℝ)) *
          ρ ^ ((n : ℝ) + 1 - α)) := by gcongr
    _ = _ := by ring

/-- **Campanato decay from a bound on the energy error.** Let `β < n + 3`. There is `C`, depending
only on `n`, `κ` and `β`, such that the following holds. Under the hypotheses of the comparison
estimates on `B_R = ball x R`, if the energy error
`2 (t^α)² λ^{-2} (K_a² ∫_{B_t} ‖∇u‖² + K_G² |B_t|)` is at most `B t^β` for `0 < t ≤ R`, with
`B ≥ 0`, and `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C (M² R^{n+1+2α-β} ρ^β + B ρ^β)` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_norm_sub_setAverage_sq_le_of_energy_le {β : ℝ}
    (hβ : β < n + 3) (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {R M B : ℝ},
      FrozenData Omega u a G lam Lam κ α Ka KG x R → 0 ≤ B →
      (∀ t, 0 < t → t ≤ R →
        2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2) + KG ^ 2 * volume.real (ball x t)) ≤
          B * t ^ β) →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * (M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α - β) * ρ ^ β + B * ρ ^ β) := by
  have hA := oscConst_nonneg n κ
  obtain ⟨C₄, hC₄, hit⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le (n := n) hA hβ
  refine ⟨C₄ * (1 + oscConst n κ), by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG x R M B h hB hF hM1 ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hdec := hit (mul_nonneg hA hB) h.subset (fun s t hs hst htR => by
    refine ((h.mono htR).setIntegral_norm_sub_setAverage_sq_le hs hst).trans ?_
    rw [mul_add, ← mul_assoc]
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left (hF t (hs.trans_le hst) htR) hA).trans_eq
      (mul_assoc _ _ _).symm)) ρ hρ hρR
  have hX : 0 ≤ M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α - β) * ρ ^ β := by positivity
  have hY : 0 ≤ B * ρ ^ β := by positivity
  refine hdec.trans ?_
  calc C₄ * ((ρ / R) ^ β * ‖W1p.gradient u‖ ^ 2 + oscConst n κ * B * ρ ^ β)
      ≤ C₄ * (M ^ 2 * ((ρ / R) ^ β * R ^ ((n : ℝ) + 1 + 2 * α)) + oscConst n κ * B * ρ ^ β) := by
        rw [mul_left_comm (M ^ 2)]
        gcongr
        exact sq_le_mul_rpow_of_le hR (norm_nonneg _) hM1
    _ = C₄ * (M ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α - β) * ρ ^ β + oscConst n κ * (B * ρ ^ β)) := by
        rw [Real.div_rpow_mul_rpow hρ.le hR]
        ring
    _ ≤ _ := by nlinarith [mul_nonneg hC₄ (mul_nonneg hA hX), mul_nonneg hC₄ hY]

/-- **A first Campanato estimate.** Let `0 < α < 1`. There are `δ > 0` and `C`, depending only on
`n`, `α` and `κ`, such that the following holds. Under the hypotheses of the comparison
estimates on `B_R = ball x R`, if `K_a R^α ≤ δ λ`, `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}` and
`K_G / λ ≤ M`, then `∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C M² R^α ρ^{n+1+α}` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_norm_sub_setAverage_sq_le_of_small (hα : 0 < α)
    (hα1 : α < 1) (κ : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ},
      FrozenData Omega u a G lam Lam κ α Ka KG x R → Ka * R ^ (α : ℝ) ≤ δ * lam →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) → KG / lam ≤ M →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * M ^ 2 * R ^ (α : ℝ) * ρ ^ ((n : ℝ) + 1 + α) := by
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  obtain ⟨δ, C₁, hδ, hC₁, hmorrey⟩ := exists_setIntegral_norm_sq_le hα κ (n := n)
  obtain ⟨C₄, hC₄, hcamp⟩ := exists_setIntegral_norm_sub_setAverage_sq_le_of_energy_le (n := n)
    (α := α) (β := (n : ℝ) + 1 + α) (by linarith) κ
  have hω0 := unitBallVolume_nonneg n
  refine ⟨δ, C₄ * (1 + 2 * (δ ^ 2 * C₁ + unitBallVolume n)), hδ, by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG x R M h hsmall hM1 hM2 ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hlam : 0 < lam := h.elliptic.pos
  have hM := (nonneg_and_div_sq_le_sq hlam hM2).1
  -- Both parts of the energy error are `O(R^α t^{n+1+α})`.
  have hF : ∀ t, 0 < t → t ≤ R →
      2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2) + KG ^ 2 * volume.real (ball x t)) ≤
        2 * (δ ^ 2 * C₁ + unitBallVolume n) * M ^ 2 * R ^ (α : ℝ) * t ^ ((n : ℝ) + 1 + α) := by
    intro t ht htR
    have hcoef := two_mul_rpow_sq_div_mul_mul_le hlam hC₁ ht htR hsmall
      (hmorrey h hsmall hM1 hM2 t ht htR)
    have hdata : 2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (KG ^ 2 * volume.real (ball x t)) ≤
        2 * unitBallVolume n * M ^ 2 * R ^ (α : ℝ) * t ^ ((n : ℝ) + 1 + α) := by
      refine (two_mul_rpow_sq_div_mul_measureReal_ball_le x ht hlam hM2).trans ?_
      rw [show (n : ℝ) + 1 + 2 * α = α + ((n : ℝ) + 1 + α) by ring, Real.rpow_add ht,
        ← mul_assoc]
      gcongr
    rw [mul_add]
    exact (add_le_add hcoef hdata).trans_eq (by ring)
  refine (hcamp h (by positivity) hF hM1 ρ hρ hρR).trans_eq ?_
  rw [show (n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1 + α) = α by ring]
  ring

/-- **The gradient is bounded.** Let `0 < α < 1`. There are `δ > 0` and `c`, depending only on
`n`, `α` and `κ`, such that the following holds. Under the hypotheses of the comparison estimates
on `B_R = ball z R`, if `K_a R^α ≤ δ λ`, `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}` and `K_G / λ ≤ M`, then
the precise representative of `∇u` satisfies `‖∇u*(z)‖ ≤ c M R^α`. -/
private theorem exists_norm_preciseRepresentative_gradient_le (hα : 0 < α) (hα1 : α < 1)
    (κ : ℝ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {z : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ},
      FrozenData Omega u a G lam Lam κ α Ka KG z R → Ka * R ^ (α : ℝ) ≤ δ * lam →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) → KG / lam ≤ M → 0 < R →
        ‖preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) z‖ ≤
          c * M * R ^ (α : ℝ) := by
  obtain ⟨δ, C₂, hδ, hC₂, hcamp⟩ := exists_setIntegral_norm_sub_setAverage_sq_le_of_small hα hα1 κ
    (n := n)
  set θ : ℝ≥0 := α / 2
  have hθ : 0 < θ := by positivity
  have hθα : (θ : ℝ) = α / 2 := by simp [θ]
  have hcθ := Real.one_sub_two_rpow_neg_pos (NNReal.coe_pos.2 hθ)
  set ω' := (√(unitBallVolume n))⁻¹
  have hω'0 : 0 ≤ ω' := inv_nonneg.2 (Real.sqrt_nonneg _)
  refine ⟨δ, 2 ^ (n + 1) / (1 - 2 ^ (-(θ : ℝ))) * ω' * √C₂ + ω', hδ, by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG z R M h hsmall hM1 hM2 hR
  have hM := (nonneg_and_div_sq_le_sq h.elliptic.pos hM2).1
  have hRθ : (R ^ (θ : ℝ)) ^ 2 = R ^ (α : ℝ) := by
    rw [← Real.rpow_mul_natCast hR.le, hθα]
    ring_nf
  -- The mean oscillation of `∇u` on `closedBall z t` is `O(t^{α/2})`.
  have hosc : ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        ω' * (√C₂ * M * R ^ (θ : ℝ)) * t ^ (θ : ℝ) := fun t ht htR => by
    refine setAverage_norm_sub_le_of_setIntegral_norm_sub_sq_le (Lp.memLp (W1p.gradient u))
      ((ball_subset_ball htR).trans h.subset) ht (by positivity) ?_
    rw [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one]
    refine (hcamp h hsmall hM1 hM2 t ht htR).trans_eq ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₂, hRθ, hθα]
    ring_nf
  have hb := Lp.norm_preciseRepresentative_le_of_setAverage_norm_sub_le one_le_two
    ENNReal.ofNat_ne_top (W1p.gradient u) (NNReal.coe_pos.2 hθ) hR h.subset hosc
  rw [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one, ENNReal.toReal_ofNat,
    ← Real.inv_sqrt_eq_rpow] at hb
  -- `R^{-(n+1)/2-θ} ‖∇u‖ ≤ M R^θ`.
  have hgrad : R ^ (-(((n : ℝ) + 1) / 2 + θ)) * ‖W1p.gradient u‖ ≤ M * R ^ (θ : ℝ) := by
    calc R ^ (-(((n : ℝ) + 1) / 2 + θ)) * ‖W1p.gradient u‖
        ≤ R ^ (-(((n : ℝ) + 1) / 2 + θ)) * (M * R ^ (((n : ℝ) + 1) / 2 + α)) := by gcongr
      _ = M * R ^ (θ : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hR, hθα]
        ring_nf
  refine hb.trans ?_
  calc (2 ^ (n + 1) / (1 - 2 ^ (-(θ : ℝ))) * (ω' * (√C₂ * M * R ^ (θ : ℝ))) +
        ω' * (R ^ (-(((n : ℝ) + 1) / 2 + θ)) * ‖W1p.gradient u‖)) * R ^ (θ : ℝ)
      ≤ (2 ^ (n + 1) / (1 - 2 ^ (-(θ : ℝ))) * (ω' * (√C₂ * M * R ^ (θ : ℝ))) +
        ω' * (M * R ^ (θ : ℝ))) * R ^ (θ : ℝ) := by gcongr
    _ = (2 ^ (n + 1) / (1 - 2 ^ (-(θ : ℝ))) * ω' * √C₂ + ω') * M * (R ^ (θ : ℝ)) ^ 2 := by ring
    _ = _ := by rw [hRθ]

/-- **The sharp Campanato estimate.** Let `0 < α < 1`, `δ` and `c`. There is `C`, depending only
on `n`, `α`, `κ`, `δ` and `c`, such that the following holds. Under the hypotheses of the
comparison estimates on `B_R = ball x R`, if `K_a R^α ≤ δ λ`, `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}`,
`K_G / λ ≤ M` and `‖∇u‖ ≤ c M R^α` almost everywhere on `B_R`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C M² ρ^{n+1+2α}` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_norm_sub_setAverage_sq_le_of_bounded (hα1 : α < 1) (κ δ c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {x : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ},
      FrozenData Omega u a G lam Lam κ α Ka KG x R → Ka * R ^ (α : ℝ) ≤ δ * lam →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) → KG / lam ≤ M →
      (∀ᵐ y ∂volume.restrict (ball x R), ‖W1p.gradient u y‖ ≤ c * M * R ^ (α : ℝ)) →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * M ^ 2 * ρ ^ ((n : ℝ) + 1 + 2 * α) := by
  have hα1' : (α : ℝ) < 1 := hα1
  obtain ⟨C₄, hC₄, hcamp⟩ := exists_setIntegral_norm_sub_setAverage_sq_le_of_energy_le (n := n)
    (α := α) (β := (n : ℝ) + 1 + 2 * α) (by linarith) κ
  have hω0 := unitBallVolume_nonneg n
  refine ⟨C₄ * (1 + 2 * unitBallVolume n * (δ ^ 2 * c ^ 2 + 1)), by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG x R M h hsmall hM1 hM2 hbd ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hlam : 0 < lam := h.elliptic.pos
  have hM := (nonneg_and_div_sq_le_sq hlam hM2).1
  have hKa := div_sq_mul_rpow_sq_le hlam hR hsmall
  -- For bounded `∇u`, the energy error is `O(t^{n+1+2α})`.
  have hF : ∀ t, 0 < t → t ≤ R →
      2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 *
          (Ka ^ 2 * (∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2) + KG ^ 2 * volume.real (ball x t)) ≤
        2 * unitBallVolume n * (δ ^ 2 * c ^ 2 + 1) * M ^ 2 * t ^ ((n : ℝ) + 1 + 2 * α) := by
    intro t ht htR
    -- `∫_{B_t} ‖∇u‖² ≤ (c M R^α)² |B_t|`.
    have hφ : ∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2 ≤
        (c * M * R ^ (α : ℝ)) ^ 2 * volume.real (ball x t) := by
      have hbdt := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball htR) hbd
      calc ∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2
          ≤ ∫ _ in ball x t, (c * M * R ^ (α : ℝ)) ^ 2 :=
            setIntegral_mono_ae_restrict (h.mono htR).integrableOn_norm_gradient_sq
              (integrableOn_const measure_ball_lt_top.ne)
              (hbdt.mono fun y hy => pow_le_pow_left₀ (norm_nonneg _) hy 2)
        _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hcoef : 2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 *
        (Ka ^ 2 * (∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2)) ≤
        2 * unitBallVolume n * (δ * c * M) ^ 2 * t ^ ((n : ℝ) + 1 + 2 * α) :=
      calc 2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 * (Ka ^ 2 * (∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2))
          ≤ 2 * (t ^ (α : ℝ)) ^ 2 / lam ^ 2 *
              ((Ka * (c * M * R ^ (α : ℝ))) ^ 2 * volume.real (ball x t)) := by
            rw [mul_pow, mul_assoc]
            gcongr
        _ = 2 * unitBallVolume n * ((Ka : ℝ) / lam) ^ 2 * (R ^ (α : ℝ)) ^ 2 * (c * M) ^ 2 *
              t ^ ((n : ℝ) + 1 + 2 * α) := by
            rw [two_mul_rpow_sq_div_mul_measureReal_ball_eq x ht]
            ring
        _ ≤ 2 * unitBallVolume n * δ ^ 2 * (c * M) ^ 2 * t ^ ((n : ℝ) + 1 + 2 * α) := by
            rw [mul_assoc _ (((Ka : ℝ) / lam) ^ 2)]
            gcongr
        _ = _ := by ring
    rw [mul_add]
    exact (add_le_add hcoef (two_mul_rpow_sq_div_mul_measureReal_ball_le x ht hlam hM2)).trans_eq
      (by ring)
  refine (hcamp h (by positivity) hF hM1 ρ hρ hρR).trans_eq ?_
  rw [sub_self, Real.rpow_zero]
  ring

/-- The hypotheses of the comparison estimates hold on `ball z R` for every `z` in the
`R`-thickening of `S` if they hold on the `2R`-thickening. -/
private theorem FrozenData.of_mem_thickening {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam κ : ℝ}
    {α Ka KG : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ}
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hell : UniformlyEllipticOn (thickening (2 * R) S) a lam Lam) (hκ : Lam ≤ κ * lam)
    (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun y => matrixBilinearForm (a y)) (thickening (2 * R) S))
    (hGK : HolderOnWith KG α G (thickening (2 * R) S))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ y in Omega, ⟪G y, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ)
    (hR : 0 ≤ R) (hsub : thickening (2 * R) S ⊆ Omega) (hz : z ∈ thickening R S) :
    FrozenData Omega u a G lam Lam κ α Ka KG z R :=
  have hball : ball z R ⊆ thickening (2 * R) S :=
    (ball_subset_thickening hz R).trans (by rw [two_mul]; exact thickening_thickening_subset R R S)
  { elliptic := hell.mono_set (singleton_subset_iff.2 (thickening_mono (by linarith) S hz))
    ratio := hκ
    pos := hα
    holder_coeff := haK.mono hball
    holder_data := hGK.mono hball
    eq := hu
    subset := hball.trans hsub }

/-- **The interior estimate for coefficients of small oscillation.** Let `0 < α < 1`. There are
`δ > 0` and `C`, depending only on `n`, `α` and `κ`, such that the following holds. Let
`u ∈ H¹(Ω)` solve `-div(a ∇u) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, and suppose that the open
`2R`-thickening of `S` lies in `Ω`, that `a` is uniformly elliptic there with constants
`λ ≤ Λ ≤ κ λ`, and that `a` and `G` are `α`-Hölder there with constants `K_a` and `K_G`. If
`K_a R^α ≤ δ λ`, `‖∇u‖_{L²(Ω)} ≤ M R^{(n+1)/2+α}` and `K_G / λ ≤ M`, then
`|∇u*(x) - ∇u*(y)| ≤ C M |x - y|^α` for `x, y ∈ S`. -/
private theorem exists_dist_preciseRepresentative_gradient_le_of_small (hα : 0 < α)
    (hα1 : α < 1) (κ : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R M : ℝ},
      UniformlyEllipticOn (thickening (2 * R) S) a lam Lam → Lam ≤ κ * lam →
      HolderOnWith Ka α (fun y => matrixBilinearForm (a y)) (thickening (2 * R) S) →
      HolderOnWith KG α G (thickening (2 * R) S) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ y in Omega, ⟪G y, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ) →
      0 < R → thickening (2 * R) S ⊆ Omega → Ka * R ^ (α : ℝ) ≤ δ * lam →
      ‖W1p.gradient u‖ ≤ M * R ^ (((n : ℝ) + 1) / 2 + α) → KG / lam ≤ M →
      ∀ x ∈ S, ∀ y ∈ S,
        dist (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y) ≤
          C * M * dist x y ^ (α : ℝ) := by
  obtain ⟨δ, c, hδ, hc, hbound⟩ := exists_norm_preciseRepresentative_gradient_le hα hα1 κ (n := n)
  obtain ⟨C₅, hC₅, hsharp⟩ :=
    exists_setIntegral_norm_sub_setAverage_sq_le_of_bounded hα1 κ δ c (n := n)
  set ω' := (√(unitBallVolume n))⁻¹
  have hω'0 : 0 ≤ ω' := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hcα := Real.one_sub_two_rpow_neg_pos (NNReal.coe_pos.2 hα)
  refine ⟨δ, 2 * 2 ^ (α : ℝ) * (2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) + ω') * (ω' * √C₅ + 1), hδ,
    by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG S R M hell hκ haK hGK hu hR hsub hsmall hM1 hM2 x hx y hy
  have hM := (nonneg_and_div_sq_le_sq hell.pos hM2).1
  have hFD : ∀ z ∈ thickening R S, FrozenData Omega u a G lam Lam κ α Ka KG z R := fun z hz =>
    FrozenData.of_mem_thickening hell hκ hα haK hGK hu hR.le hsub hz
  have hS : ∀ z ∈ S, z ∈ thickening R S := fun z hz => self_subset_thickening hR S hz
  -- `∇u` is bounded by `c M R^α` almost everywhere on `ball z R` for `z ∈ S`.
  have hae := ae_eq_restrict_preciseRepresentative Omega.isOpen
    (W1p.locallyIntegrableOn_gradient u)
  have hbd : ∀ z ∈ S, ∀ᵐ w ∂volume.restrict (ball z R),
      ‖W1p.gradient u w‖ ≤ c * M * R ^ (α : ℝ) := fun z hz => by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hFD z (hS z hz)).subset hae,
      ae_restrict_mem measurableSet_ball] with w hw hwB
    rw [hw]
    exact hbound (hFD w (ball_subset_thickening hz R hwB)) hsmall hM1 hM2 hR
  -- The mean oscillation of `∇u` on `closedBall z t` is `O(t^α)` for `z ∈ S`.
  have hosc : ∀ z ∈ S, ∀ t, 0 < t → t ≤ R →
      ⨍ w in closedBall z t, ‖W1p.gradient u w - ⨍ v in closedBall z t, W1p.gradient u v‖ ≤
        ω' * (√C₅ * M) * t ^ (α : ℝ) := fun z hz t ht htR => by
    refine setAverage_norm_sub_le_of_setIntegral_norm_sub_sq_le (Lp.memLp (W1p.gradient u))
      ((ball_subset_ball htR).trans (hFD z (hS z hz)).subset) ht (by positivity) ?_
    rw [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one]
    refine (hsharp (hFD z (hS z hz)) hsmall hM1 hM2 (hbd z hz) t ht htR).trans_eq ?_
    rw [mul_pow, Real.sq_sqrt hC₅]
  have h := Lp.dist_preciseRepresentative_le_of_forall_setAverage_norm_sub_le one_le_two
    ENNReal.ofNat_ne_top (W1p.gradient u) (NNReal.coe_pos.2 hα) hR (by positivity)
    (fun z hz => (hFD z (hS z hz)).subset) hosc hx hy
  rw [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one, ENNReal.toReal_ofNat,
    ← Real.inv_sqrt_eq_rpow] at h
  have hgrad : R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ ≤ M := by
    calc R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖
        ≤ R ^ (-(((n : ℝ) + 1) / 2 + α)) * (M * R ^ (((n : ℝ) + 1) / 2 + α)) := by gcongr
      _ = M := by rw [mul_left_comm, ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero, mul_one]
  refine h.trans ?_
  calc 2 * 2 ^ (α : ℝ) * (2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) + ω') *
        (ω' * (√C₅ * M) + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) * dist x y ^ (α : ℝ)
      ≤ 2 * 2 ^ (α : ℝ) * (2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) + ω') *
        (ω' * (√C₅ * M) + M) * dist x y ^ (α : ℝ) := by gcongr
    _ = _ := by ring

end Passes

/-- **Interior Hölder continuity of the gradient for `-div(a ∇u) = -div G`.** Let `0 < α < 1` and
`κ ∈ ℝ`. There is a constant `C`, depending only on `n`, `α` and `κ`, such that the following
holds. Let `Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function
`φ`. Suppose that the open `R`-thickening `S_R` of `S` (the points at distance less than `R` from
`S`) lies in `Ω`, that `a` is uniformly elliptic on `S_R` with constants `λ ≤ Λ ≤ κ λ`, and that
`a`, in the operator norm of the attached bilinear forms, and `G` are `α`-Hölder on `S_R` with
constants `K_a` and `K_G`. Then the precise representative of `∇u` is `α`-Hölder on `S`, with
constant

`C (K_G / λ + (R^{-(n+1)/2-α} + (K_a / λ)^{((n+1)/2+α)/α}) ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). The exponent of `a` and `G`
passes to `∇u` without loss; this is false for `α = 1`, which is why `α < 1` is assumed. Every term
of the constant scales like the Hölder seminorm of `∇u` under dilations, and the constant is
unchanged under `(a, G) ↦ (t a, t G)`, `t > 0`. -/
theorem exists_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
      {Ka KG : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn (thickening R S) a lam Lam → Lam ≤ κ * lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (KG / lam + (R ^ (-(((n : ℝ) + 1) / 2 + α)) +
            (Ka / lam) ^ ((((n : ℝ) + 1) / 2 + α) / α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨δ, C, hδ, hC, hsmall⟩ :=
    exists_dist_preciseRepresentative_gradient_le_of_small hα hα1 κ (n := n)
  refine ⟨C * (2 ^ (((n : ℝ) + 1) / 2 + α) + δ ^ (-((((n : ℝ) + 1) / 2 + α) / α)) + 1),
    by positivity, ?_⟩
  intro Omega u a G lam Lam Ka KG S R hell hκ haK hGK hu hR hsub
  generalize hq : ((n : ℝ) + 1) / 2 + (α : ℝ) = q
  generalize hp : q / (α : ℝ) = p
  have hlam : 0 < lam := hell.pos
  -- The estimate on balls of any radius `r ≤ R / 2` on which `K_a r^α ≤ δ λ`.
  have key : ∀ r, 0 < r → 2 * r ≤ R → Ka * r ^ (α : ℝ) ≤ δ * lam → ∀ x ∈ S, ∀ y ∈ S,
      dist (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y) ≤
        C * (KG / lam + r ^ (-q) * ‖W1p.gradient u‖) * dist x y ^ (α : ℝ) := by
    intro r hr hrR hKa x hx y hy
    have hth : thickening (2 * r) S ⊆ thickening R S := thickening_mono hrR S
    refine hsmall (hell.mono_set hth) hκ (haK.mono hth) (hGK.mono hth) hu hr (hth.trans hsub)
      hKa ?_ (le_add_of_nonneg_right (by positivity)) x hx y hy
    rw [hq]
    calc ‖W1p.gradient u‖ = r ^ (-q) * ‖W1p.gradient u‖ * r ^ q := by
          rw [mul_right_comm, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ (KG / lam + r ^ (-q) * ‖W1p.gradient u‖) * r ^ q := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  obtain ⟨r, hr, hrR, hKa, hrq⟩ := Real.exists_mul_rpow_le_and_rpow_neg_le
    (NNReal.coe_pos.2 hα) Ka.coe_nonneg (mul_pos hδ hlam) hR q
  rw [hp, show (Ka : ℝ) / (δ * lam) = δ⁻¹ * (Ka / lam) by field_simp,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
    at hrq
  refine HolderOnWith.of_dist_le fun x hx y hy => (key r hr hrR hKa x hx y hy).trans ?_
  refine (mul_le_mul_of_nonneg_right ?_ (by positivity)).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  have hN := norm_nonneg (W1p.gradient u)
  have hKG : (0 : ℝ) ≤ KG / lam := by positivity
  have h1 : r ^ (-q) ≤ (2 ^ q + δ ^ (-p) + 1) * (R ^ (-q) + (Ka / lam) ^ p) := by
    have := Real.rpow_nonneg hR.le (-q)
    have : (0 : ℝ) ≤ (Ka / lam) ^ p := by positivity
    have : (0 : ℝ) ≤ 2 ^ q := by positivity
    have : (0 : ℝ) ≤ δ ^ (-p) := by positivity
    nlinarith
  calc C * (KG / lam + r ^ (-q) * ‖W1p.gradient u‖)
      ≤ C * (KG / lam + (2 ^ q + δ ^ (-p) + 1) * (R ^ (-q) + (Ka / lam) ^ p) *
          ‖W1p.gradient u‖) := by gcongr
    _ ≤ C * ((2 ^ q + δ ^ (-p) + 1) * (KG / lam) +
          (2 ^ q + δ ^ (-p) + 1) * (R ^ (-q) + (Ka / lam) ^ p) * ‖W1p.gradient u‖) := by
        have h2q : (0 : ℝ) ≤ 2 ^ q := by positivity
        have hδp : (0 : ℝ) ≤ δ ^ (-p) := by positivity
        gcongr
        exact le_mul_of_one_le_left hKG (by linarith)
    _ = _ := by ring

end PDE

end TauCeti
