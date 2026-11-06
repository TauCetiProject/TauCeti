/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Schauder estimates for divergence-form equations with Hölder coefficients

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in an open set `Ω ⊆ ℝ^{n+1}`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, with a variable coefficient
matrix `a` and a vector field `G`, and let `0 < α < 1`. This file proves the interior Schauder
estimate: if the open `R`-thickening of a set `S` lies in `Ω`, `a` is uniformly elliptic with
constants `λ`, `Λ` at the points of `S`, and `a` and `G` are `α`-Hölder on the thickening with
constants `K_a` and `K_G`, then the precise representative of `∇u` is `α`-Hölder on `S` with
constant

`C (K_G + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`,

where `C` depends only on `n`, `α`, `λ`, `Λ` and a bound `M ≥ R^α K_a`. Hölder continuity of the
coefficients is measured in the operator norm of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`. The constant is invariant under dilations, since `R^α K_a` is.
For the Laplacian, `a = 1`, the estimate is
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`.

## The argument

The proof is Campanato's, by comparison with the problem frozen at the centre of each ball. Fix a
centre `z ∈ S` and write `Φ(t) = ∫_{B_t} ‖∇u‖²` and `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` for
the balls `B_t = ball z t`. On `B_r` let `w` solve `-∂ᵢ(a(z)ⁱʲ ∂ⱼw) = 0` with the boundary values
of `u`. Its energy distance from `u` is `O(r^{2α} (K_a² Φ(r) + K_G² r^{n+1}))`
(`TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le`), while
`Φ` and `ψ` decay for `w` with exponents `n + 1` and `n + 3`
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`).
For `0 < ρ ≤ r` this gives

`Φ(ρ) ≤ A ((ρ / r)^{n+1} + r^{2α} K_a² / λ²) Φ(r) + A K_G² r^{n+1+2α} / λ²`,
`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A r^{2α} (K_a² Φ(r) + K_G² r^{n+1}) / λ²`.

The coefficient oscillation `r^{2α} K_a²` is not small on `B_R` itself, only on `B_{θR}` for a
small `θ`, depending on `M`. There the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turns the two inequalities into
decay estimates in four steps:

1. Morrey decay `Φ(t) ≲ (t / R)^{n+1-α}`, from the first inequality, where the coefficient term
   is a small perturbation.
2. Campanato decay `ψ(t) ≲ (t / R)^{n+1+α}`, from the second inequality and step 1.
3. Morrey decay `Φ(t) ≲ (t / R)^{n+1}`: by step 2 and Campanato's theorem the averages of `∇u`
   over the balls `B_t` stay bounded.
4. Campanato decay `ψ(t) ≲ (t / R)^{n+1+2α}`, from the second inequality and step 3. This needs
   `α < 1`.

By Jensen's inequality, step 4 bounds the mean oscillation of `∇u` on balls of radius `t` by a
multiple of `t^α`, and the local form of Campanato's theorem
(`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`) gives the
Hölder estimate.

## Main declarations

* `exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`: the
  interior Schauder estimate for `∇u`, in the `TauCeti.PDE` namespace.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations with
  variable coefficients, by freezing the coefficients).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- The squared norm of the weak gradient of the restriction of `u` to `B` is the integral of
`‖∇u‖²` over `B`. -/
private theorem norm_gradient_restrictL_sq {Omega B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hB : B ≤ Omega) (u : W1p volume Omega 2) :
    ‖W1p.gradient (W1p.restrictL hB u)‖ ^ 2 =
      ∫ x in B, ‖W1p.gradient u x‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
  rw [hx]

/-- The volume of a ball of radius `t` in `ℝ^{n+1}` is `ω t^{n+1}`, where `ω` is the volume of
the unit ball. -/
private theorem measureReal_ball_eq_pow (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 0 < t) :
    volume.real (ball x t) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * t ^ (n + 1) := by
  rw [Measure.addHaar_real_ball_of_pos _ _ ht, finrank_euclideanSpace_fin, mul_comm]

/-- Squaring the energy estimate `λ E ≤ t (K_a X + K_G Y)` of a frozen replacement, with
`X² = Φ` and `Y² = ω V`. -/
private theorem sq_le_of_mul_le_mul_add_mul {lam t E X Y Ka KG ω V Φ : ℝ} (hlam : 0 < lam)
    (hE : 0 ≤ E) (hω : 0 ≤ ω) (hV : 0 ≤ V) (hest : lam * E ≤ t * (Ka * X + KG * Y))
    (hXΦ : X ^ 2 = Φ) (hYV : Y ^ 2 = ω * V) :
    E ^ 2 ≤ 2 * (1 + ω) * (t ^ 2 * (Ka ^ 2 * Φ + KG ^ 2 * V) / lam ^ 2) := by
  have h1 : (lam * E) ^ 2 ≤ (t * (Ka * X + KG * Y)) ^ 2 := pow_le_pow_left₀ (by positivity) hest 2
  have h2 : (t * (Ka * X + KG * Y)) ^ 2 ≤ 2 * t ^ 2 * (Ka ^ 2 * X ^ 2 + KG ^ 2 * Y ^ 2) := by
    nlinarith [sq_nonneg (Ka * X - KG * Y), sq_nonneg t]
  have h3 : Ka ^ 2 * X ^ 2 + KG ^ 2 * Y ^ 2 ≤ (1 + ω) * (Ka ^ 2 * Φ + KG ^ 2 * V) := by
    rw [hXΦ, hYV]
    have : 0 ≤ Ka ^ 2 * X ^ 2 * ω := by positivity
    have : 0 ≤ KG ^ 2 * V := by positivity
    rw [← hXΦ]
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * t ^ 2)
  rw [mul_div_assoc', le_div_iff₀ (by positivity), mul_comm, ← mul_pow]
  linarith

/-- **The frozen replacement on a ball.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`, let `ball x₀ r ⊆ Ω`, let `a(x₀)` be uniformly elliptic with lower constant `λ`, and
let `a` and `G` be `α`-Hölder on `ball x₀ r` with constants `K_a` and `K_G`. The solution `w` of
the problem frozen at `x₀` with the boundary values of `u` satisfies
`∫_{B_r} ‖∇u - ∇w‖² ≤ 2 (1 + ω) r^{2α} (K_a² ∫_{B_r} ‖∇u‖² + K_G² r^{n+1}) / λ²`, where `ω` is the
volume of the unit ball. -/
private theorem exists_frozen_setIntegral_norm_gradient_sub_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    {α Ka KG : ℝ≥0} {lam Lam : ℝ} (h : UniformlyEllipticOn s a lam Lam) (hx₀ : x₀ ∈ s)
    (hα : 0 < α) (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    (hGK : HolderOnWith KG α G (ball x₀ r))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) (hr : 0 < r) :
    ∃ w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
        energyFormH1 (fun _ => a x₀) 0 0 w (v : W1p volume _ 2) = 0) ∧
      ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
        2 * (1 + volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
          (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
            (KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) / lam ^ 2) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hlam : 0 < lam := h.pos
  have hB : (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ Omega := hball
  obtain ⟨w, -, hw0, hest⟩ := h.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le hx₀ hα
    haK hGK hB subset_rfl hu
  refine ⟨w, hw0, ?_⟩
  have hE := W1p.setIntegral_norm_gradient_sub_sq_eq hB u w
  simp only [Opens.coe_mk] at hE
  rw [hE]
  have hX := norm_gradient_restrictL_sq hB u
  simp only [Opens.coe_mk] at hX hest
  have hY : √(volume.real (ball x₀ r)) ^ 2 = ω * r ^ ((n : ℝ) + 1) := by
    rw [Real.sq_sqrt measureReal_nonneg]
    rw [measureReal_ball_eq_pow x₀ hr, ← Real.rpow_natCast]
    push_cast
    rfl
  have hr2 : (r ^ (α : ℝ)) ^ 2 = r ^ (2 * (α : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    ring_nf
  rw [← hr2]
  exact sq_le_of_mul_le_mul_add_mul h.pos (norm_nonneg _) hω (by positivity) hest hX hY

/-- The constants of the two comparison estimates combine into one. -/
private theorem le_mul_add_mul_of_le {D E ω q X Y e err : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hω : 0 ≤ ω) (hqX : 0 ≤ q * X) (he0 : 0 ≤ e) (he : e ≤ 2 * (1 + ω) * err)
    (hY : Y ≤ 4 * D * q * X + (4 * D + 2) * e) :
    Y ≤ 2 * (4 * (D + E) + 2) * (1 + ω) * q * X + 2 * (4 * (D + E) + 2) * (1 + ω) * err := by
  have herr : 0 ≤ err := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 4 * D + 2)
  have : 0 ≤ D * ω * (q * X) := by positivity
  have : 0 ≤ E * (q * X) := by positivity
  have : 0 ≤ E * ω * (q * X) := by positivity
  have : 0 ≤ ω * (q * X) := by positivity
  have : 0 ≤ E * err := by positivity
  have : 0 ≤ E * ω * err := by positivity
  nlinarith

/-- **Decay of the `L²` mass of the gradient, by comparison.** Let `u ∈ H¹(Ω)`, let
`ball x₀ r ⊆ Ω`, and let `w ∈ H¹(B_r)` solve `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` weakly on `B_r` for a constant
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²`, `λ > 0`. Then for `0 < ρ ≤ r`
`∫_{B_ρ} ‖∇u‖² ≤ 4 D (ρ / r)^{n+1} ∫_{B_r} ‖∇u‖² + (4 D + 2) ∫_{B_r} ‖∇u - ∇w‖²`, with
`D = 2^{n+1} (Λ / λ)^{(n+1)/2}`. -/
private theorem setIntegral_norm_gradient_sq_le_add_of_frozen
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {r ρ : ℝ} (hlam : 0 < lam)
    (hAl : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw0 : ∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0)
    (hball : ball x₀ r ⊆ Omega) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
      4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) * (ρ / r) ^ (n + 1) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
        (4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) + 2) *
          ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hfm : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    Lp.memLp (W1p.gradient w)
  have hq0 : 0 ≤ ρ / r := by positivity
  have hdec := setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ r, isOpen_ball⟩) hlam hAl hAu hw0 (x₀ := x₀) (R := r)
    (fun _ hx => hx) hρ.le hρr
  rw [Fintype.card_fin] at hdec
  have hf2 : IntegrableOn (fun x => ‖W1p.gradient u x‖ ^ 2) (ball x₀ r) :=
    hfm.integrable_norm_pow two_ne_zero
  have hH2 : IntegrableOn (fun x => ‖W1p.gradient w x‖ ^ 2) (ball x₀ r) :=
    hHm.integrable_norm_pow two_ne_zero
  have hcomp := setIntegral_norm_sub_sq_le_add_of_le (b := 0) (k := 0) (c := 0)
    (D := 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) (ball_subset_ball hρr) (by positivity)
    (pow_nonneg hq0 _) (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (by simpa only [sub_zero] using hf2)
    (by simpa only [sub_zero] using hH2.mono_set (ball_subset_ball hρr))
    ((hfm.sub hHm).integrable_norm_pow two_ne_zero) le_rfl
    (by simpa only [sub_zero] using hdec)
  simpa only [sub_zero] using hcomp

/-- **Decay of the mean oscillation of the gradient, by comparison.** Let `u ∈ H¹(Ω)`, let
`ball x₀ r ⊆ Ω`, and let `w ∈ H¹(B_r)` solve `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` weakly on `B_r` for a constant
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²`, `λ > 0`. Then for `0 < ρ ≤ r` the square mean
oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies
`ψ(ρ) ≤ 4 D (ρ / r)^{n+3} ψ(r) + (4 D + 2) ∫_{B_r} ‖∇u - ∇w‖²`, with
`D = 2^{3n+13} (n + 2)² (Λ / λ)^{(n+3)/2}`. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {r ρ : ℝ} (hlam : 0 < lam)
    (hAl : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw0 : ∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0)
    (hball : ball x₀ r ⊆ Omega) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)) *
          (ρ / r) ^ (n + 1 + 2) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * (2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)) + 2) *
          ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hfm : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    Lp.memLp (W1p.gradient w)
  have hq0 : 0 ≤ ρ / r := by positivity
  have hρs : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hdec := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ r, isOpen_ball⟩) hlam hAl hAu hw0 (x₀ := x₀) (R := r)
    (fun _ hx => hx) (⨍ y in ball x₀ r, W1p.gradient u y) hρ.le hρr
  rw [Fintype.card_fin] at hdec
  exact setIntegral_norm_sub_sq_le_add_of_le hρs
    (D := 2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2))
    (by positivity) (pow_nonneg hq0 _)
    (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (hfm.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne _)
    (hHm.integrableOn_norm_sub_sq_of_subset hρs measure_ball_lt_top.ne _)
    ((hfm.sub hHm).integrable_norm_pow two_ne_zero)
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfm.integrableOn_of_subset one_le_two hρs measure_ball_lt_top.ne)
      (hfm.integrableOn_norm_sub_sq_of_subset hρs measure_ball_lt_top.ne _)) hdec

/-- **Comparison with the frozen problem on a ball.** There is `A`, depending only on `n`, `λ`
and `Λ`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`, let `ball x₀ r ⊆ Ω`, let `a(x₀)` be uniformly elliptic with constants `λ`, `Λ`, and
let `a` and `G` be `α`-Hölder on `ball x₀ r` with constants `K_a` and `K_G`. Write
`Φ(t) = ∫_{B_t} ‖∇u‖²` and `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`, and
`e = r^{2α} (K_a² Φ(r) + K_G² r^{n+1}) / λ²`. Then for `0 < ρ ≤ r`,
`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A e` and `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A e`. -/
private theorem exists_comparison (n : ℕ) (lam Lam : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {r ρ : ℝ} {α Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → x₀ ∈ s → 0 < α →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r) →
      HolderOnWith KG α G (ball x₀ r) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball x₀ r ⊆ Omega → 0 < ρ → ρ ≤ r →
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 1) * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
                (KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) / lam ^ 2) ∧
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 3) *
              (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
                (KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) / lam ^ 2) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  set D₀ : ℝ := 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)
  set D₁ : ℝ := 2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)
  have hD₀ : 0 ≤ D₀ := by positivity
  have hD₁ : 0 ≤ D₁ := by positivity
  refine ⟨2 * (4 * (D₀ + D₁) + 2) * (1 + ω), by positivity, ?_⟩
  intro Omega u a G s x₀ r ρ α Ka KG h hx₀ hα haK hGK hu hball hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, he⟩ :=
    exists_frozen_setIntegral_norm_gradient_sub_sq_le h hx₀ hα haK hGK hu hball hr
  have he0 : 0 ≤ ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  -- The frozen matrix `a x₀` satisfies the two quadratic-form bounds.
  have hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
    fun ξ => (le_abs_self _).trans
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (h.upper_bound hx₀) ξ)
  refine ⟨?_, ?_⟩
  · have hrp : (ρ / r) ^ ((n : ℝ) + 1) = (ρ / r) ^ (n + 1) := by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    rw [hrp]
    exact le_mul_add_mul_of_le hD₀ hD₁ hω (by positivity) he0 he
      (setIntegral_norm_gradient_sq_le_add_of_frozen h.pos (h.lower_bound hx₀) hAu hw0 hball hρ
        hρr)
  · have hrp : (ρ / r) ^ ((n : ℝ) + 3) = (ρ / r) ^ (n + 1 + 2) := by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    rw [hrp]
    exact le_mul_add_mul_of_le (E := D₀) hD₁ hD₀ hω (by positivity) he0 he
      (setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen h.pos (h.lower_bound hx₀) hAu
        hw0 hball hρ hρr) |>.trans_eq (by ring)

end Comparison

section Iteration

/-- `r^{2α} K_a² ≤ (r / R)^{2α} M²` when `K_a R^α ≤ M`. -/
private theorem rpow_mul_sq_le {r R Ka M a : ℝ} (hr : 0 < r) (hR : 0 < R) (hKa : 0 ≤ Ka)
    (hM : Ka * R ^ a ≤ M) : r ^ (2 * a) * Ka ^ 2 ≤ (r / R) ^ (2 * a) * M ^ 2 := by
  have h1 : r ^ (2 * a) = (r / R) ^ (2 * a) * (R ^ a) ^ 2 := by
    rw [Real.div_rpow hr.le hR.le, ← Real.rpow_natCast, ← Real.rpow_mul hR.le, Nat.cast_two,
      mul_comm a 2, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hR _).ne']
  rw [h1, mul_assoc, ← mul_pow, mul_comm (R ^ a)]
  gcongr

/-- `r^{2α} K_G² r^d ≤ V (r / R)^{d+2α}` when `K_G² R^{d+2α} ≤ V`. -/
private theorem rpow_mul_mul_rpow_le {r R KG V a d : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hKG : KG ^ 2 * R ^ (d + 2 * a) ≤ V) :
    r ^ (2 * a) * (KG ^ 2 * r ^ d) ≤ V * (r / R) ^ (d + 2 * a) := by
  have h1 : r ^ (2 * a) * (KG ^ 2 * r ^ d) =
      (r / R) ^ (d + 2 * a) * (KG ^ 2 * R ^ (d + 2 * a)) := by
    rw [Real.div_rpow hr.le hR.le, add_comm d, Real.rpow_add hr]
    field_simp
  rw [h1, mul_comm V]
  gcongr

/-- On `(0, R]`, the powers of `r / R` decrease with the exponent. -/
private theorem div_rpow_le_div_rpow {r R a b : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hab : b ≤ a) :
    (r / R) ^ a ≤ (r / R) ^ b :=
  Real.rpow_le_rpow_of_exponent_ge (div_pos hr (hr.trans_le hrR)) ((div_le_one₀
    (hr.trans_le hrR)).2 hrR) hab

/-- `(ρ / (θ R))^γ = θ^{-γ} (ρ / R)^γ`. -/
private theorem div_mul_rpow_eq {ρ θ R γ : ℝ} (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hR : 0 < R) :
    (ρ / (θ * R)) ^ γ = θ ^ (-γ) * (ρ / R) ^ γ := by
  rw [div_mul_eq_div_div_swap, div_eq_inv_mul (ρ / R), Real.mul_rpow (inv_nonneg.2 hθ.le)
    (div_nonneg hρ hR.le), Real.inv_rpow hθ.le, Real.rpow_neg hθ.le]

/-- One step of the Morrey decay. For `r ≤ θ R`, the error term
`A r^{2α} (K_a² Φ_r + K_G² r^d) / λ²` of the comparison estimate splits into a perturbation
`A θ^{2α} M² / λ²` of the decay factor and an inhomogeneity `A V R^{-β} r^β / λ²`, for every
`β ≤ d + 2α`, when `K_a R^α ≤ M` and `K_G² R^{d+2α} ≤ V`. -/
private theorem le_mul_add_mul_rpow_of_le_of_mul_rpow_le {A lam θ M Ka KG R V r q Φρ Φr a d β : ℝ}
    (hA : 0 ≤ A) (hr : 0 < r) (hR : 0 < R) (hrθ : r ≤ θ * R) (hrR : r ≤ R) (ha : 0 ≤ a)
    (hKa : 0 ≤ Ka) (hM : Ka * R ^ a ≤ M) (hV : KG ^ 2 * R ^ (d + 2 * a) ≤ V) (hV0 : 0 ≤ V)
    (hΦr : 0 ≤ Φr) (hβ : β ≤ d + 2 * a)
    (h1 : Φρ ≤ A * q * Φr + A * (r ^ (2 * a) * (Ka ^ 2 * Φr + KG ^ 2 * r ^ d) / lam ^ 2)) :
    Φρ ≤ A * (q + θ ^ (2 * a) * M ^ 2 / lam ^ 2) * Φr + A * V * R ^ (-β) / lam ^ 2 * r ^ β := by
  have hrθR : (r / R) ^ (2 * a) ≤ θ ^ (2 * a) :=
    Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hR).2 hrθ) (by positivity)
  have k1 : r ^ (2 * a) * Ka ^ 2 * Φr ≤ θ ^ (2 * a) * M ^ 2 * Φr :=
    mul_le_mul_of_nonneg_right ((rpow_mul_sq_le hr hR hKa hM).trans
      (mul_le_mul_of_nonneg_right hrθR (sq_nonneg M))) hΦr
  have k2 : r ^ (2 * a) * (KG ^ 2 * r ^ d) ≤ V * R ^ (-β) * r ^ β := by
    have hq : (r / R) ^ β = R ^ (-β) * r ^ β := by
      rw [Real.div_rpow hr.le hR.le, Real.rpow_neg hR.le]
      ring
    refine (rpow_mul_mul_rpow_le hr hR hV).trans ?_
    rw [mul_assoc, ← hq]
    exact mul_le_mul_of_nonneg_left (div_rpow_le_div_rpow hr hrR hβ) hV0
  have k3 : A * (r ^ (2 * a) * (Ka ^ 2 * Φr + KG ^ 2 * r ^ d) / lam ^ 2) ≤
      A / lam ^ 2 * (θ ^ (2 * a) * M ^ 2 * Φr + V * R ^ (-β) * r ^ β) := by
    calc _ = A / lam ^ 2 * (r ^ (2 * a) * Ka ^ 2 * Φr + r ^ (2 * a) * (KG ^ 2 * r ^ d)) := by ring
      _ ≤ _ := by gcongr
  refine h1.trans ((add_le_add le_rfl k3).trans_eq ?_)
  ring

/-- One step of the Campanato decay. If `Φ_r ≤ L V (r / R)^β` with `β ≤ d`, then the error term
`A r^{2α} (K_a² Φ_r + K_G² r^d) / λ²` of the comparison estimate is at most
`A (M² L + 1) V R^{-γ} r^γ / λ²` with `γ = 2α + β`, when `K_a R^α ≤ M` and `K_G² R^{d+2α} ≤ V`. -/
private theorem le_mul_add_mul_rpow_of_le_of_le_mul_rpow
    {A lam M Ka KG R V r q ψρ ψr Φr L a d β : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R) (hKa : 0 ≤ Ka) (hM : Ka * R ^ a ≤ M) (hV : KG ^ 2 * R ^ (d + 2 * a) ≤ V)
    (hV0 : 0 ≤ V) (hΦr0 : 0 ≤ Φr) (hΦr : Φr ≤ L * V * (r / R) ^ β) (hβ : β ≤ d)
    (h1 : ψρ ≤ A * q * ψr + A * (r ^ (2 * a) * (Ka ^ 2 * Φr + KG ^ 2 * r ^ d) / lam ^ 2)) :
    ψρ ≤ A * (q + 0) * ψr +
      A * (M ^ 2 * L + 1) * V * R ^ (-(2 * a + β)) / lam ^ 2 * r ^ (2 * a + β) := by
  have hq : (r / R) ^ (2 * a + β) = R ^ (-(2 * a + β)) * r ^ (2 * a + β) := by
    rw [Real.div_rpow hr.le hR.le, Real.rpow_neg hR.le]
    ring
  have hsplit : (r / R) ^ (2 * a) * (r / R) ^ β = (r / R) ^ (2 * a + β) := by
    rw [← Real.rpow_add (div_pos hr hR)]
  have k1 : r ^ (2 * a) * Ka ^ 2 * Φr ≤ M ^ 2 * L * V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β)) := by
    calc _ ≤ (r / R) ^ (2 * a) * M ^ 2 * (L * V * (r / R) ^ β) :=
          mul_le_mul (rpow_mul_sq_le hr hR hKa hM) hΦr hΦr0 (by positivity)
      _ = M ^ 2 * L * V * ((r / R) ^ (2 * a) * (r / R) ^ β) := by ring
      _ = _ := by rw [hsplit, hq]
  have k2 : r ^ (2 * a) * (KG ^ 2 * r ^ d) ≤ V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β)) := by
    refine (rpow_mul_mul_rpow_le hr hR hV).trans ?_
    rw [← hq]
    exact mul_le_mul_of_nonneg_left (div_rpow_le_div_rpow hr hrR (by linarith)) hV0
  have k3 : A * (r ^ (2 * a) * (Ka ^ 2 * Φr + KG ^ 2 * r ^ d) / lam ^ 2) ≤
      A / lam ^ 2 * (M ^ 2 * L * V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β)) +
        V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β))) := by
    calc _ = A / lam ^ 2 * (r ^ (2 * a) * Ka ^ 2 * Φr + r ^ (2 * a) * (KG ^ 2 * r ^ d)) := by ring
      _ ≤ _ := by gcongr
  refine h1.trans ((add_le_add le_rfl k3).trans_eq ?_)
  ring

/-- The square-integrable gradient is square integrable on every ball inside `Ω`. -/
private theorem integrableOn_norm_gradient_sq {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Omega 2) {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ}
    (hball : ball z t ⊆ Omega) : IntegrableOn (fun x => ‖W1p.gradient u x‖ ^ 2) (ball z t) :=
  ((Lp.memLp (W1p.gradient u)).mono_measure
    (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero

/-- The `L²` mass `∫_{B_t} ‖∇u‖²` of the gradient is nondecreasing in the radius. -/
private theorem monotoneOn_setIntegral_norm_gradient_sq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hball : ball z R ⊆ Omega) :
    MonotoneOn (fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2) (Ioc 0 R) :=
  fun _ _ t ht hst => setIntegral_mono_set
    (integrableOn_norm_gradient_sq u ((ball_subset_ball ht.2).trans hball))
    (ae_of_all _ fun _ => by positivity) (ball_subset_ball hst).eventuallyLE

/-- A radius `θ ∈ (0, 1]` with `θ^{2α} M² / λ² ≤ ε₀`. -/
private theorem exists_rpow_mul_sq_div_le {a lam M ε₀ : ℝ} (ha : 0 < a) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ^ (2 * a) * M ^ 2 / lam ^ 2 ≤ ε₀ := by
  obtain ⟨x, hx⟩ : ∃ x, x = ε₀ * lam ^ 2 / (M ^ 2 + 1) := ⟨_, rfl⟩
  have hx0 : 0 < x := hx ▸ by positivity
  refine ⟨min 1 (x ^ (2 * a)⁻¹), lt_min one_pos (Real.rpow_pos_of_pos hx0 _), min_le_left _ _, ?_⟩
  have hθx : (min 1 (x ^ (2 * a)⁻¹)) ^ (2 * a) ≤ x := by
    calc (min 1 (x ^ (2 * a)⁻¹)) ^ (2 * a) ≤ (x ^ (2 * a)⁻¹) ^ (2 * a) :=
          Real.rpow_le_rpow (by positivity) (min_le_right _ _) (by positivity)
      _ = x := Real.rpow_inv_rpow hx0.le (by positivity)
  have hM : x * M ^ 2 ≤ ε₀ * lam ^ 2 := by
    rw [hx, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε₀ (pow_pos hlam 2)]
  rw [div_le_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_right hθx (sq_nonneg M)).trans hM

/-- **Morrey decay of the gradient.** For `α > 0` there are `θ ∈ (0, 1]` and `C`, depending only
on `n`, `α`, `λ`, `Λ` and `M`, such that the following holds. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, let `ball z R ⊆ Ω`, let `a(z)` be uniformly
elliptic with constants `λ`, `Λ`, and let `a` and `G` be `α`-Hölder on `ball z R` with constants
`K_a`, `K_G`, where `K_a R^α ≤ M`. If `K_G² R^{n+1+2α} ≤ V` and `∫_{B_R} ‖∇u‖² ≤ V`, then
`∫_{B_ρ} ‖∇u‖² ≤ C V (ρ / R)^{n+1-α}` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sq_le_rpow {α : ℝ≥0} (hα : 0 < α)
    {lam Lam M : ℝ} (hlam : 0 < lam) :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (KG : ℝ) ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) ≤ V →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x‖ ^ 2 ≤ C * V * (ρ / R) ^ ((n : ℝ) + 1 - α) := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison n lam Lam
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (n : ℝ) + 1 - α := ⟨_, rfl⟩
  have hβ : β < (n : ℝ) + 1 := by linarith
  obtain ⟨ε₀, C₀, hε₀, hC₀, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA hβ hβ
  obtain ⟨θ, hθ, hθ1, hε⟩ := exists_rpow_mul_sq_div_le (M := M) hα' hlam hε₀
  refine ⟨θ, C₀ * (θ ^ (-β) + A / lam ^ 2), hθ, hθ1, by positivity, ?_⟩
  intro Omega u a G s z R V Ka KG h hz haK hGK hu hball hR hM hV hΦR ρ hρ hρθ
  rw [← hβdef]
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hV0 : 0 ≤ V := (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity).trans hΦR
  -- One step of the decay: `Φ(ρ) ≤ A ((ρ / r)^{n+1} + ε) Φ(r) + B r^β` for `ρ ≤ r ≤ θ R`.
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ θ * R →
      ∫ x in ball z ρ, ‖W1p.gradient u x‖ ^ 2 ≤
        A * ((ρ / r) ^ ((n : ℝ) + 1) + θ ^ (2 * (α : ℝ)) * M ^ 2 / lam ^ 2) *
            (∫ x in ball z r, ‖W1p.gradient u x‖ ^ 2) +
          A * V * R ^ (-β) / lam ^ 2 * r ^ β := by
    intro ρ r hρ hρr hrθ
    have hr : 0 < r := hρ.trans_le hρr
    have hrR : r ≤ R := hrθ.trans hθR
    obtain ⟨h1, -⟩ := hcomp h hz hα (haK.mono (ball_subset_ball hrR))
      (hGK.mono (ball_subset_ball hrR)) hu ((ball_subset_ball hrR).trans hball) hρ hρr
    exact le_mul_add_mul_rpow_of_le_of_mul_rpow_le hA hr hR hrθ hrR (by positivity) Ka.2 hM hV hV0
      (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) (by linarith) h1
  have hit' := hit (φ := fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2) (R := θ * R)
    (B := A * V * R ^ (-β) / lam ^ 2) (by positivity) hε
    (monotoneOn_setIntegral_norm_gradient_sq u ((ball_subset_ball hθR).trans hball))
    (fun t _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hstep ρ (θ * R)
    hρ hρθ le_rfl
  have hΦθR : ∫ x in ball z (θ * R), ‖W1p.gradient u x‖ ^ 2 ≤ V :=
    (monotoneOn_setIntegral_norm_gradient_sq u hball ⟨by positivity, hθR⟩ ⟨hR, le_rfl⟩ hθR).trans
      hΦR
  have hq : (ρ / R) ^ β = R ^ (-β) * ρ ^ β := by
    rw [Real.div_rpow hρ.le hR.le, Real.rpow_neg hR.le]
    ring
  refine hit'.trans ?_
  rw [div_mul_rpow_eq hρ.le hθ hR]
  have h1 := mul_le_mul_of_nonneg_left hΦθR (by positivity : (0 : ℝ) ≤ θ ^ (-β) * (ρ / R) ^ β)
  calc C₀ * (θ ^ (-β) * (ρ / R) ^ β * (∫ x in ball z (θ * R), ‖W1p.gradient u x‖ ^ 2) +
        A * V * R ^ (-β) / lam ^ 2 * ρ ^ β)
      ≤ C₀ * (θ ^ (-β) * (ρ / R) ^ β * V + A * V * R ^ (-β) / lam ^ 2 * ρ ^ β) := by gcongr
    _ = C₀ * (θ ^ (-β) + A / lam ^ 2) * V * (ρ / R) ^ β := by rw [hq]; ring

/-- The square mean oscillation of the gradient on `B_t` is at most its `L²` mass on `B_t`. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) :
    ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
      ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 := by
  have h := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
      measure_ball_lt_top.ne 0)
  simpa only [sub_zero] using h

/-- The square mean oscillation `∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` is nondecreasing in the radius,
since the average is the best constant in square mean. -/
private theorem monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hball : ball z R ⊆ Omega) :
    MonotoneOn
      (fun t => ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2)
      (Ioc 0 R) := fun r hr t ht hst => by
  have hr' := (ball_subset_ball hr.2).trans hball
  have ht' := (ball_subset_ball ht.2).trans hball
  exact (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hr' measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hr'
      measure_ball_lt_top.ne _)).trans
    (setIntegral_mono_set ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset ht'
      measure_ball_lt_top.ne _) (ae_of_all _ fun _ => by positivity)
      (ball_subset_ball hst).eventuallyLE)

/-- **Campanato decay of the gradient from a Morrey bound.** Let `α > 0`, `β ≤ n + 1` and
`2α + β < n + 3`, and let `θ ∈ (0, 1]` and `L ≥ 0`. There is `C`, depending only on `n`, `α`, `β`,
`λ`, `Λ`, `M`, `θ` and `L`, such that the following holds. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, let `ball z R ⊆ Ω`, let `a(z)` be uniformly
elliptic with constants `λ`, `Λ`, and let `a` and `G` be `α`-Hölder on `ball z R` with constants
`K_a`, `K_G`, where `K_a R^α ≤ M`. Suppose that `K_G² R^{n+1+2α} ≤ V`, `∫_{B_R} ‖∇u‖² ≤ V`, and
`∫_{B_t} ‖∇u‖² ≤ L V (t / R)^β` for `0 < t ≤ θ R`. Then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C V (ρ / R)^{2α+β}` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow {α : ℝ≥0} (hα : 0 < α)
    {β : ℝ} (hβ : β ≤ (n : ℝ) + 1) (hγ : 2 * (α : ℝ) + β < (n : ℝ) + 3) {lam Lam M θ L : ℝ}
    (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (KG : ℝ) ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) ≤ V →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      (∀ t, 0 < t → t ≤ θ * R → ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 ≤ L * V * (t / R) ^ β) →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
          C * V * (ρ / R) ^ (2 * (α : ℝ) + β) := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison n lam Lam
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = 2 * (α : ℝ) + β := ⟨_, rfl⟩
  rw [← hγdef] at hγ
  obtain ⟨ε₀, C₀, hε₀, hC₀, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA hγ hγ
  refine ⟨C₀ * (θ ^ (-γ) + A * (M ^ 2 * L + 1) / lam ^ 2), by positivity, ?_⟩
  intro Omega u a G s z R V Ka KG h hz haK hGK hu hball hR hM hV hΦR hΦ ρ hρ hρθ
  rw [← hγdef]
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hV0 : 0 ≤ V := (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity).trans hΦR
  -- One step of the decay: `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B r^γ` for `ρ ≤ r ≤ θ R`.
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ θ * R →
      ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
        A * ((ρ / r) ^ ((n : ℝ) + 3) + 0) *
            (∫ x in ball z r, ‖W1p.gradient u x - ⨍ y in ball z r, W1p.gradient u y‖ ^ 2) +
          A * (M ^ 2 * L + 1) * V * R ^ (-γ) / lam ^ 2 * r ^ γ := by
    intro ρ r hρ hρr hrθ
    have hr : 0 < r := hρ.trans_le hρr
    have hrR : r ≤ R := hrθ.trans hθR
    obtain ⟨-, h1⟩ := hcomp h hz hα (haK.mono (ball_subset_ball hrR))
      (hGK.mono (ball_subset_ball hrR)) hu ((ball_subset_ball hrR).trans hball) hρ hρr
    rw [hγdef]
    exact le_mul_add_mul_rpow_of_le_of_le_mul_rpow hA hr hR hrR Ka.2 hM hV hV0
      (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) (hΦ r hr hrθ) hβ h1
  have hit' := hit (φ := fun t =>
      ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2) (R := θ * R)
    (B := A * (M ^ 2 * L + 1) * V * R ^ (-γ) / lam ^ 2) (by positivity) hε₀.le
    (monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq u ((ball_subset_ball hθR).trans hball))
    (fun t _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hstep ρ (θ * R)
    hρ hρθ le_rfl
  have hψθR : ∫ x in ball z (θ * R),
      ‖W1p.gradient u x - ⨍ y in ball z (θ * R), W1p.gradient u y‖ ^ 2 ≤ V :=
    (setIntegral_norm_gradient_sub_setAverage_sq_le u ((ball_subset_ball hθR).trans hball)).trans
      ((monotoneOn_setIntegral_norm_gradient_sq u hball ⟨by positivity, hθR⟩ ⟨hR, le_rfl⟩
        hθR).trans hΦR)
  have hq : (ρ / R) ^ γ = R ^ (-γ) * ρ ^ γ := by
    rw [Real.div_rpow hρ.le hR.le, Real.rpow_neg hR.le]
    ring
  refine hit'.trans ?_
  rw [div_mul_rpow_eq hρ.le hθ hR]
  calc C₀ * (θ ^ (-γ) * (ρ / R) ^ γ *
          (∫ x in ball z (θ * R),
            ‖W1p.gradient u x - ⨍ y in ball z (θ * R), W1p.gradient u y‖ ^ 2) +
        A * (M ^ 2 * L + 1) * V * R ^ (-γ) / lam ^ 2 * ρ ^ γ)
      ≤ C₀ * (θ ^ (-γ) * (ρ / R) ^ γ * V +
        A * (M ^ 2 * L + 1) * V * R ^ (-γ) / lam ^ 2 * ρ ^ γ) := by gcongr
    _ = C₀ * (θ ^ (-γ) + A * (M ^ 2 * L + 1) / lam ^ 2) * V * (ρ / R) ^ γ := by rw [hq]; ring

/-- The gradient is integrable on `closedBall z t` whenever `ball z R ⊆ Ω` and `t ≤ R`; for
`t = R` because `closedBall z R` and `ball z R` differ by a null set. -/
private theorem integrableOn_closedBall_gradient {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Omega 2) {z : EuclideanSpace ℝ (Fin (n + 1))} {R t : ℝ}
    (hball : ball z R ⊆ Omega) (ht : t ≤ R) :
    IntegrableOn (W1p.gradient u) (closedBall z t) := by
  rcases ht.lt_or_eq with ht | rfl
  · exact (Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((closedBall_subset_ball ht).trans hball) measure_closedBall_lt_top.ne
  · exact ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball
      measure_ball_lt_top.ne).congr_set_ae (volume.addHaar_closedBall_ae_eq_ball z t)

/-- **Jensen's inequality for the mean oscillation.** The squared mean oscillation of `∇u` on
`closedBall z t`, times the volume of the ball, is at most the square mean oscillation
`∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`. -/
private theorem sq_setAverage_closedBall_norm_gradient_sub_mul_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) (ht : 0 < t) :
    (⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖) ^ 2 *
        volume.real (ball z t) ≤
      ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 := by
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball z t)]
  have hpos := measureReal_ball_pos volume z ht
  have hint := (Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball
    measure_ball_lt_top.ne
  have hJ := sq_setAverage_norm_le_setAverage_norm_sq (measure_ball_pos volume z ht).ne'
    measure_ball_lt_top.ne (hint.sub (integrableOn_const measure_ball_lt_top.ne))
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne
      (⨍ y in ball z t, W1p.gradient u y))
  have hav : ⨍ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 =
      (volume.real (ball z t))⁻¹ *
        ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
  simp only [Pi.sub_apply] at hJ
  rw [hav] at hJ
  calc _ ≤ _ := mul_le_mul_of_nonneg_right hJ hpos.le
    _ = _ := by field_simp

/-- The squared norm of the average of `∇u` over `closedBall z t`, times the volume of the ball,
is at most `∫_{B_t} ‖∇u‖²`. -/
private theorem sq_norm_setAverage_closedBall_gradient_mul_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) :
    ‖⨍ y in closedBall z t, W1p.gradient u y‖ ^ 2 * volume.real (ball z t) ≤
      ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 := by
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball z t)]
  have h := setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add
    measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
      measure_ball_lt_top.ne 0)
  simp only [sub_zero] at h
  rw [h, mul_comm]
  exact le_add_of_nonneg_left (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)

/-- **Mean oscillation from square mean oscillation.** If
`∫_{B_r} ‖∇u - (∇u)_{B_r}‖² ≤ C V (r / R)^{n+1} (r / R)^{2κ}`, then the mean oscillation of `∇u`
on `closedBall z r` is at most `√(C V / (ω R^{n+1})) R^{-κ} r^κ`, where `ω` is the volume of the
unit ball. -/
private theorem setAverage_closedBall_norm_gradient_sub_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r R C V κ : ℝ} (hball : ball z r ⊆ Omega) (hr : 0 < r)
    (hR : 0 < R)
    (hψ : ∫ x in ball z r, ‖W1p.gradient u x - ⨍ y in ball z r, W1p.gradient u y‖ ^ 2 ≤
      C * V * ((r / R) ^ (n + 1) * (r / R) ^ (2 * κ))) :
    ⨍ y in closedBall z r, ‖W1p.gradient u y - ⨍ w in closedBall z r, W1p.gradient u w‖ ≤
      √(C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1)))) *
        R ^ (-κ) * r ^ κ := by
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have h1 := (sq_setAverage_closedBall_norm_gradient_sub_mul_le u hball hr).trans hψ
  rw [measureReal_ball_eq_pow z hr] at h1
  have hsq : ((r / R) ^ κ) ^ 2 = (r / R) ^ (2 * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  have h2 : C * V * ((r / R) ^ (n + 1) * (r / R) ^ (2 * κ)) =
      C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1))) *
        ((r / R) ^ κ) ^ 2 *
        (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ (n + 1)) := by
    rw [hsq, div_pow]
    field_simp
  have h3 := le_of_mul_le_mul_right (h1.trans_eq h2) (by positivity)
  have h4 : (⨍ y in closedBall z r,
      ‖W1p.gradient u y - ⨍ w in closedBall z r, W1p.gradient u w‖) ≤
        √(C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1)))) *
          (r / R) ^ κ := by
    rw [← Real.sqrt_sq (average_nonneg fun _ => norm_nonneg _),
      ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (r / R) ^ κ), ← Real.sqrt_mul' _ (by positivity)]
    exact Real.sqrt_le_sqrt h3
  refine h4.trans_eq ?_
  rw [Real.div_rpow hr.le hR.le, Real.rpow_neg hR.le]
  ring

/-- **Bounded averages from Campanato decay.** Let `κ > 0` and `θ ∈ (0, 1]`. If
`ball z R ⊆ Ω`, `∫_{B_R} ‖∇u‖² ≤ V` and the square mean oscillation of `∇u` satisfies
`∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C₂ V (t / R)^{n+1+2κ}` for `0 < t ≤ θ R`, then for `0 < t ≤ θ R`
the averages of `∇u` over `closedBall z t` satisfy
`‖(∇u)_{z,t}‖² ≤ (2 θ^{-(n+1)} + 8 c² C₂) V / (ω R^{n+1})`, where `ω` is the volume of the unit
ball and `c = 2^{n+1} / (1 - 2^{-κ})` is the constant of Campanato's theorem. -/
private theorem sq_norm_setAverage_closedBall_gradient_le {κ θ C₂ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hC₂ : 0 ≤ C₂) {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume Omega 2} {z : EuclideanSpace ℝ (Fin (n + 1))} {R V : ℝ}
    (hball : ball z R ⊆ Omega) (hR : 0 < R) (hΦR : ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V)
    (hψ : ∀ t, 0 < t → t ≤ θ * R →
      ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
        C₂ * V * ((t / R) ^ (n + 1) * (t / R) ^ (2 * κ)))
    {t : ℝ} (ht : 0 < t) (htθ : t ≤ θ * R) :
    ‖⨍ y in closedBall z t, W1p.gradient u y‖ ^ 2 ≤
      (2 / θ ^ (n + 1) + 8 * (2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
        (1 - 2 ^ (-κ))) ^ 2 * C₂) *
        (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1))) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-κ)) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc : 0 ≤ c := hcdef ▸ div_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hκ))).le
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W =
      V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1)) := ⟨_, rfl⟩
  rw [← hW]
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hV0 : 0 ≤ V := (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity).trans hΦR
  have hW0 : 0 ≤ W := hW ▸ by positivity
  -- The mean oscillation on `closedBall z r` is at most `m r^κ`, `m = √(C₂ W) R^{-κ}`.
  have hosc : ∀ r, 0 < r → r ≤ θ * R →
      ⨍ y in closedBall z r, ‖W1p.gradient u y - ⨍ w in closedBall z r, W1p.gradient u w‖ ≤
        √(C₂ * W) * R ^ (-κ) * r ^ κ := fun r hr hrθ => hW ▸
    setAverage_closedBall_norm_gradient_sub_le u ((ball_subset_ball (hrθ.trans hθR)).trans hball)
      hr hR (hψ r hr hrθ)
  -- The average at radius `θ R` is controlled by `∫_{B_R} ‖∇u‖² ≤ V`.
  have ha₁ : ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ^ 2 ≤ W / θ ^ (n + 1) := by
    have h := (sq_norm_setAverage_closedBall_gradient_mul_le u
      ((ball_subset_ball hθR).trans hball)).trans
      ((monotoneOn_setIntegral_norm_gradient_sq u hball ⟨by positivity, hθR⟩ ⟨hR, le_rfl⟩
        hθR).trans hΦR)
    rw [measureReal_ball_eq_pow z (by positivity), mul_pow] at h
    rw [hW, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    linarith
  -- By Campanato's estimate, the averages over `closedBall z t` stay close to the average at
  -- radius `θ R`.
  have hat : ‖⨍ y in closedBall z t, W1p.gradient u y‖ ≤
      ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ + 2 * (c * √(C₂ * W)) := by
    have h := norm_setAverage_closedBall_sub_setAverage_closedBall_le hκ
      (integrableOn_closedBall_gradient u hball hθR) hosc ht htθ
    rw [← hcdef] at h
    have hRr : R ^ (-κ) * (θ * R) ^ κ ≤ 1 := by
      rw [Real.rpow_neg hR.le, inv_mul_le_one₀ (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hθR hκ.le
    have h' : 2 * c * (√(C₂ * W) * R ^ (-κ) * (θ * R) ^ κ) ≤ 2 * (c * √(C₂ * W)) := by
      have := mul_le_mul_of_nonneg_left hRr (by positivity : (0 : ℝ) ≤ 2 * c * √(C₂ * W))
      linarith
    have h4 := norm_le_norm_add_norm_sub' (⨍ y in closedBall z t, W1p.gradient u y)
      (⨍ y in closedBall z (θ * R), W1p.gradient u y)
    linarith
  have hsq : (c * √(C₂ * W)) ^ 2 = c ^ 2 * C₂ * W := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  calc ‖⨍ y in closedBall z t, W1p.gradient u y‖ ^ 2
      ≤ (‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ + 2 * (c * √(C₂ * W))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hat 2
    _ ≤ 2 * ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ^ 2 +
          2 * (2 * (c * √(C₂ * W))) ^ 2 := add_sq_le.trans_eq (by ring)
    _ ≤ 2 * (W / θ ^ (n + 1)) + 8 * (c ^ 2 * C₂ * W) := by nlinarith
    _ = (2 / θ ^ (n + 1) + 8 * c ^ 2 * C₂) * W := by ring

/-- **Morrey decay with the full exponent from Campanato decay.** Let `κ > 0` and `θ ∈ (0, 1]`.
There is `C₃`, depending only on `n`, `κ`, `θ` and `C₂`, such that the following holds. If
`ball z R ⊆ Ω`, `∫_{B_R} ‖∇u‖² ≤ V` and `∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C₂ V (t / R)^{n+1+2κ}` for
`0 < t ≤ θ R`, then `∫_{B_t} ‖∇u‖² ≤ C₃ V (t / R)^{n+1}` for `0 < t ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sq_le_pow {κ θ C₂ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hC₂ : 0 ≤ C₂) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2} {z : EuclideanSpace ℝ (Fin (n + 1))} {R V : ℝ},
      ball z R ⊆ Omega → 0 < R → ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      (∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
          C₂ * V * ((t / R) ^ (n + 1) * (t / R) ^ (2 * κ))) →
      ∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 ≤ C₃ * V * (t / R) ^ (n + 1) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 / θ ^ (n + 1) + 8 * (2 ^ finrank ℝ
      (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-κ))) ^ 2 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ by positivity
  refine ⟨C₂ + K, by positivity, ?_⟩
  intro Omega u z R V hball hR hΦR hψ t ht htθ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have htR : t ≤ R := htθ.trans hθR
  have hballt : ball z t ⊆ Omega := (ball_subset_ball htR).trans hball
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have ha := sq_norm_setAverage_closedBall_gradient_le hκ hθ hθ1 hC₂ hball hR hΦR hψ ht htθ
  rw [← hK] at ha
  -- Split `∫_{B_t} ‖∇u‖²` into the square mean oscillation and the squared average.
  have hpy := setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add
    measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hballt measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hballt
      measure_ball_lt_top.ne 0)
  have hcb : ⨍ y in ball z t, W1p.gradient u y = ⨍ y in closedBall z t, W1p.gradient u y := by
    rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball z t)]
  simp only [sub_zero] at hpy
  rw [hpy, measureReal_ball_eq_pow z ht]
  rw [← hcb] at ha
  have h1 := hψ t ht htθ
  have h2 : (t / R) ^ (2 * κ) ≤ 1 :=
    Real.rpow_le_one (by positivity) ((div_le_one hR).2 htR) (by positivity)
  have h3 : C₂ * V * ((t / R) ^ (n + 1) * (t / R) ^ (2 * κ)) ≤ C₂ * V * (t / R) ^ (n + 1) := by
    have hV0 : 0 ≤ V :=
      (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity).trans hΦR
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ C₂ * V * (t / R) ^ (n + 1))
    linarith
  have h4 : volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * t ^ (n + 1) *
      ‖⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤ K * V * (t / R) ^ (n + 1) := by
    calc _ ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * t ^ (n + 1) *
          (K * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
            R ^ (n + 1)))) := by gcongr
      _ = K * V * (t / R) ^ (n + 1) := by
          rw [div_pow]
          field_simp
  linarith

/-- `V (t / R)^{2α+n+1} = Q² t^{n+1} (t^α)²` for `V = (R^{(n+1)/2+α} Q)²`. -/
private theorem sq_rpow_mul_mul_div_rpow_eq {R t Q a : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 * (t / R) ^ (2 * a + ((n : ℝ) + 1)) =
      Q ^ 2 * (t ^ (n + 1) * (t ^ a) ^ 2) := by
  have e1 : (((n : ℝ) + 1) / 2 + a) * ((2 : ℕ) : ℝ) = 2 * a + ((n : ℝ) + 1) := by
    push_cast
    ring
  have e2 : t ^ (n + 1) * (t ^ a) ^ 2 = t ^ (2 * a + ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast t, ← Real.rpow_natCast (t ^ a), ← Real.rpow_mul ht.le,
      ← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  rw [mul_pow, ← Real.rpow_natCast (R ^ _), ← Real.rpow_mul hR.le, e1, e2,
    Real.div_rpow ht.le hR.le]
  field_simp

end Iteration


/-- The scaling of the final estimate. Let `Q = K_G + R^{-(n+1)/2-α} X` with `K_G, X ≥ 0`. Then
`V = (R^{(n+1)/2+α} Q)²` equals `R^{n+1} (R^α Q)²` and bounds both `K_G² R^{n+1+2α}` and `X²`. -/
private theorem sq_rpow_mul_eq_and_le {R KG X Q a : ℝ} (hR : 0 < R) (hKG : 0 ≤ KG) (hX : 0 ≤ X)
    (hQ : Q = KG + R ^ (-(((n : ℝ) + 1) / 2 + a)) * X) :
    (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 = R ^ (n + 1) * (R ^ a * Q) ^ 2 ∧
      KG ^ 2 * R ^ ((n : ℝ) + 1 + 2 * a) ≤ (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 ∧
      X ≤ R ^ (((n : ℝ) + 1) / 2 + a) * Q := by
  have hVR : (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 = R ^ (n + 1) * (R ^ a * Q) ^ 2 := by
    have h := sq_rpow_mul_mul_div_rpow_eq (n := n) (Q := Q) (a := a) hR hR
    rw [div_self hR.ne', Real.one_rpow, mul_one] at h
    rw [h]
    ring
  refine ⟨hVR, ?_, ?_⟩
  · have hRe : R ^ ((n : ℝ) + 1 + 2 * a) = R ^ (n + 1) * (R ^ a) ^ 2 := by
      rw [← Real.rpow_natCast R, ← Real.rpow_natCast (R ^ a), ← Real.rpow_mul hR.le,
        ← Real.rpow_add hR]
      push_cast
      ring_nf
    have hKQ : KG ≤ Q := hQ ▸ le_add_of_nonneg_right (by positivity)
    rw [hVR, hRe]
    calc KG ^ 2 * (R ^ (n + 1) * (R ^ a) ^ 2) ≤ Q ^ 2 * (R ^ (n + 1) * (R ^ a) ^ 2) := by gcongr
      _ = _ := by ring
  · have h1 : R ^ (-(((n : ℝ) + 1) / 2 + a)) * X ≤ Q := hQ ▸ le_add_of_nonneg_left hKG
    have h2 : X = R ^ (((n : ℝ) + 1) / 2 + a) * (R ^ (-(((n : ℝ) + 1) / 2 + a)) * X) := by
      rw [← mul_assoc, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [h2]
    gcongr

/-- If `∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C (R^{(n+1)/2+α} Q)² (t / R)^{n+1+2α}`, then the mean
oscillation of `∇u` on `closedBall z t` is at most `√(C / ω) Q t^α`, where `ω` is the volume of
the unit ball. -/
private theorem setAverage_closedBall_norm_gradient_sub_le_mul_rpow
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t R Q C a : ℝ} (hball : ball z t ⊆ Omega) (ht : 0 < t)
    (hR : 0 < R) (hQ : 0 ≤ Q)
    (hψ : ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
      C * (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 * (t / R) ^ (2 * a + ((n : ℝ) + 1))) :
    ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
      √(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q * t ^ a := by
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have h1 := (sq_setAverage_closedBall_norm_gradient_sub_mul_le u hball ht).trans hψ
  rw [measureReal_ball_eq_pow z ht, mul_assoc C, sq_rpow_mul_mul_div_rpow_eq hR ht] at h1
  have h2 : C * (Q ^ 2 * (t ^ (n + 1) * (t ^ a) ^ 2)) =
      C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * (Q * t ^ a) ^ 2 *
        (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * t ^ (n + 1)) := by
    field_simp
  have h3 := le_of_mul_le_mul_right (h1.trans_eq h2) (by positivity)
  rw [← Real.sqrt_sq (average_nonneg fun _ => norm_nonneg _), mul_assoc,
    ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Q * t ^ a), ← Real.sqrt_mul' _ (by positivity)]
  exact Real.sqrt_le_sqrt h3

/-- If `∫_{B_{θR}} ‖∇u‖² ≤ R^{n+1} (R^α Q)²`, then the average of `∇u` over `closedBall z (θ R)`
is at most `R^α Q / √(ω θ^{n+1})`, where `ω` is the volume of the unit ball. -/
private theorem norm_setAverage_closedBall_gradient_le_div
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {θ R Q a : ℝ} (hball : ball z (θ * R) ⊆ Omega)
    (hθ : 0 < θ) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hΦ : ∫ x in ball z (θ * R), ‖W1p.gradient u x‖ ^ 2 ≤ R ^ (n + 1) * (R ^ a * Q) ^ 2) :
    ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ≤
      R ^ a * Q / √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1)) := by
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have h := (sq_norm_setAverage_closedBall_gradient_mul_le u hball).trans hΦ
  rw [measureReal_ball_eq_pow z (by positivity), mul_pow] at h
  have h' : ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ^ 2 ≤
      (R ^ a * Q) ^ 2 / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
        θ ^ (n + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have hRn : 0 < R ^ (n + 1) := by positivity
    nlinarith
  rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul
    (sq_nonneg _), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ R ^ a * Q)]
  refine Real.sqrt_le_sqrt ?_
  rwa [← le_div_iff₀ (by positivity)]

/-- **Decay of the gradient at a centre.** Let `0 < α < 1`. There are `θ ∈ (0, 1]` and `C`,
depending only on `n`, `α`, `λ`, `Λ` and `M`, such that the following holds. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, let `ball z R ⊆ Ω`, let `a(z)` be uniformly
elliptic with constants `λ`, `Λ`, and let `a` and `G` be `α`-Hölder on `ball z R` with constants
`K_a`, `K_G`, where `K_a R^α ≤ M`. If `K_G² R^{n+1+2α} ≤ V` and `∫_{B_R} ‖∇u‖² ≤ V`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C V (ρ / R)^{n+1+2α}` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Lam M : ℝ} (hlam : 0 < lam) :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (KG : ℝ) ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) ≤ V →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
          C * V * (ρ / R) ^ (2 * (α : ℝ) + ((n : ℝ) + 1)) := by
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  -- Morrey decay with exponent `n + 1 - α`.
  obtain ⟨θ, C₁, hθ, hθ1, hC₁, hΦ1⟩ :=
    exists_setIntegral_norm_gradient_sq_le_rpow (n := n) hα (Lam := Lam) (M := M) hlam
  -- Campanato decay with exponent `n + 1 + α`.
  obtain ⟨C₂, hC₂, hψ2⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow (n := n) hα
    (β := (n : ℝ) + 1 - α) (by linarith) (by linarith) (Lam := Lam) (M := M) hlam hθ hθ1 hC₁
  -- Bounded averages, hence Morrey decay with exponent `n + 1`.
  obtain ⟨C₃, hC₃, hΦ3⟩ := exists_setIntegral_norm_gradient_sq_le_pow (n := n) (κ := α / 2)
    (by positivity) hθ hθ1 hC₂
  -- Campanato decay with exponent `n + 1 + 2α`.
  obtain ⟨C₄, hC₄, hψ4⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow (n := n) hα
    (β := (n : ℝ) + 1) le_rfl (by linarith) (Lam := Lam) (M := M) hlam hθ hθ1 hC₃
  refine ⟨θ, C₄, hθ, hθ1, hC₄, ?_⟩
  intro Omega u a G s z R V Ka KG h hz haK hGK hu hball hR hM hV hΦR
  have hΦ1z := hΦ1 h hz haK hGK hu hball hR hM hV hΦR
  have hψ2z := hψ2 h hz haK hGK hu hball hR hM hV hΦR hΦ1z
  have hΦ3z := hΦ3 hball hR hΦR fun t ht htθ => (hψ2z t ht htθ).trans_eq (by
    rw [← Real.rpow_natCast, ← Real.rpow_add (div_pos ht hR)]
    congr 2
    push_cast
    ring)
  exact hψ4 h hz haK hGK hu hball hR hM hV hΦR fun t ht htθ => (hΦ3z t ht htθ).trans_eq (by
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf)

/-- The constant of the final estimate:
`c M Q + (R^α Q / √(ω θ^{n+1})) (θ R)^{-α} = (c M + θ^{-α} / √(ω θ^{n+1})) Q`. -/
private theorem add_mul_div_sqrt_mul_rpow_eq {c M ω θ R Q a : ℝ} (hθ : 0 < θ) (hR : 0 < R) :
    c * (M * Q) + R ^ a * Q / √(ω * θ ^ (n + 1)) * (θ * R) ^ (-a) =
      (c * M + θ ^ (-a) / √(ω * θ ^ (n + 1))) * Q := by
  rw [Real.mul_rpow hθ.le hR.le, Real.rpow_neg hR.le]
  field_simp [(Real.rpow_pos_of_pos hR a).ne']

/-- **Interior Schauder estimate for divergence-form equations with Hölder coefficients.** Let
`0 < α < 1`. There is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `M`, such that the
following holds. Let `Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function
`φ`. Let `S` be a set whose open `R`-thickening lies in `Ω`, let `a` be uniformly elliptic with
constants `λ`, `Λ` at the points of `S`, and let `a` and `G` be `α`-Hölder on the `R`-thickening
of `S` with constants `K_a` and `K_G`, the oscillation of `a` measured in the operator norm of the
attached bilinear forms, where `K_a R^α ≤ M`. Then the precise representative of `∇u` is
`α`-Hölder on `S`, with constant `C (K_G + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The constant depends on the coefficients only through `λ`, `Λ` and the dimensionless bound `M`
on `R^α [a]_α`, so the estimate is invariant under dilations. The precise representative agrees
with `∇u` almost everywhere on `Ω` (`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`).
For `a = 1` this is `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`. -/
theorem exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {Ka KG : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn S a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  by_cases hlam : 0 < lam
  swap
  · refine ⟨0, le_rfl, ?_⟩
    intro Omega u a G Ka KG S R h
    exact absurd h.pos hlam
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨θ, C₀, hθ, hθ1, hC₀, hdec⟩ :=
    exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith (n := n) hα hα1
      (Lam := Lam) (M := M) hlam
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ measureReal_ball_pos volume _ one_pos
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(α : ℝ))) := ⟨_, rfl⟩
  have hc : 0 ≤ c := hcdef ▸ div_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα'))).le
  refine ⟨2 * 2 ^ (α : ℝ) * (c * √(C₀ / ω) + θ ^ (-(α : ℝ)) / √(ω * θ ^ (n + 1))),
    by positivity, ?_⟩
  intro Omega u a G Ka KG S R h haK hGK hM hu hR hRS
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (KG : ℝ) + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ :=
    ⟨_, rfl⟩
  rw [← hQ]
  have hQ0 : 0 ≤ Q := hQ ▸ by positivity
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hball : ∀ z ∈ S, ball z R ⊆ Omega := fun z hz => (ball_subset_thickening hz R).trans hRS
  -- `V = (R^{(n+1)/2+α} Q)²` bounds both `K_G² R^{n+1+2α}` and `∫_{B_R} ‖∇u‖²`.
  obtain ⟨hVR, hV1, hX⟩ := sq_rpow_mul_eq_and_le (n := n) hR KG.2 (norm_nonneg _) hQ
  have hV2 : ∀ z ∈ S, ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤
      (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 := fun z hz =>
    (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) (hball z hz)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hX 2)
  -- The mean oscillation of `∇u` on `closedBall z t` is at most `√(C₀ / ω) Q t^α`.
  have hosc : ∀ z ∈ S, ∀ t, 0 < t → t ≤ θ * R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        √(C₀ / ω) * Q * t ^ (α : ℝ) := fun z hz t ht htθ => hωdef ▸
    setAverage_closedBall_norm_gradient_sub_le_mul_rpow u
      ((ball_subset_ball (htθ.trans hθR)).trans (hball z hz)) ht hR hQ0
      (hdec h hz (haK.mono (ball_subset_thickening hz R)) (hGK.mono (ball_subset_thickening hz R))
        hu (hball z hz) hR hM hV1 (hV2 z hz) t ht htθ)
  -- The average of `∇u` over `closedBall z (θ R)` is at most `R^α Q / √(ω θ^{n+1})`.
  have havg : ∀ z ∈ S, ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ≤
      R ^ (α : ℝ) * Q / √(ω * θ ^ (n + 1)) := fun z hz => hωdef ▸
    norm_setAverage_closedBall_gradient_le_div u ((ball_subset_ball hθR).trans (hball z hz)) hθ hR
      hQ0 (hVR ▸ (monotoneOn_setIntegral_norm_gradient_sq u (hball z hz) ⟨by positivity, hθR⟩
        ⟨hR, le_rfl⟩ hθR).trans (hV2 z hz))
  have hH := TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le hα
    (ρ := θ * R) (by positivity) (fun z hz => integrableOn_closedBall_gradient u (hball z hz) hθR)
    hosc havg
  rwa [← hcdef, add_mul_div_sqrt_mul_rpow_eq hθ hR, ← mul_assoc] at hH

end PDE

end TauCeti
