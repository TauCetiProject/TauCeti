/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.Sobolev.W1p.GradientMeanOscillation
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.CampanatoIteration
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Schauder estimates for divergence-form equations with Hölder coefficients

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in an open set `Ω ⊆ ℝ^{n+1}`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, with a variable
coefficient matrix `a`, a vector field `G` and a scalar datum `f`. This file proves the interior
Schauder estimate: if the open `R`-thickening `S_R` of a set `S` lies in `Ω`, `a` is uniformly
elliptic with constants `λ`, `Λ` at the points of `S`, `a` and `G` are `α`-Hölder on `S_R` with
constants `K_a` and `K_G`, and `f ∈ L^q(S_R)` with `2 ≤ q ≤ ∞`, then for every `0 < β < 1` with
`β ≤ α` and `β ≤ 1 - (n + 1) / q` the precise representative of `∇u` is `β`-Hölder on `S` with
constant

`C (K_G R^{α-β} + R^{1-(n+1)/q-β} ‖f‖_{L^q(S_R)} + R^{-(n+1)/2-β} ‖∇u‖_{L²(Ω)})`,

where `C` depends only on `n`, `α`, `β`, `q`, `λ`, `Λ` and a bound `M ≥ R^α K_a`. The best
exponent below `1` is `β = min α (1 - (n + 1) / q)`: the field `G` costs nothing, while the scalar
datum costs `(n + 1) / q` of a derivative, and needs `q > n + 1`. Hölder continuity of the
coefficients is measured in the operator norm of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`. The constant is invariant under dilations, since `R^α K_a` is.
For `f = 0` the exponent is `β = α` for every `α < 1`. For the Laplacian, `a = 1`, `f = 0`, the
estimate is `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`.

## The argument

The proof is Campanato's, by comparison with the problem frozen at the centre of each ball. Fix a
centre `z ∈ S` and write `Φ(t) = ∫_{B_t} ‖∇u‖²` and `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` for
the balls `B_t = ball z t`. On `B_r` let `w` solve `-∂ᵢ(a(z)ⁱʲ ∂ⱼw) = 0` with the boundary values
of `u`. Its energy distance from `u` is `O(r^{2α} K_a² Φ(r) + D(r))` with the data term
`D(r) = r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r} f²`
(`TauCeti.PDE.UniformlyEllipticOn.exists_frozen_setIntegral_norm_gradient_sub_sq_le`), while
`Φ` and `ψ` decay for `w` with exponents `n + 1` and `n + 3`
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`).
By Hölder's inequality `∫_{B_r} f² ≤ |B_r|^{1-2/q} ‖f‖²_{L^q}`, so the data term decays like
`D(r) ≲ (r / R)^{n+1+2β}`. Transferring the decay of `w` to `u`
(`TauCeti.PDE.setIntegral_norm_gradient_sq_le_add_of_frozen` and
`TauCeti.PDE.setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen`) gives, for
`0 < ρ ≤ r`,

`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A (r^{2α} (K_a / λ)² Φ(r) + D(r))`,
`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A (r^{2α} (K_a / λ)² Φ(r) + D(r))`.

The coefficient oscillation `r^{2α} K_a²` is not small on `B_R` itself, only on `B_{θR}` for a
small `θ`, depending on `M`. There the two steps of Campanato's perturbation argument
(`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add` and
`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow`) turn the
two inequalities into decay estimates in four steps:

1. Morrey decay `Φ(t) ≲ (t / R)^{n+1-β}`, from the first inequality, where the coefficient term
   is a small perturbation.
2. Campanato decay `ψ(t) ≲ (t / R)^{n+1+β}`, from the second inequality and step 1, using
   `β ≤ α`.
3. Morrey decay `Φ(t) ≲ (t / R)^{n+1}`: by step 2 and Campanato's theorem the averages of `∇u`
   over the balls `B_t` stay bounded
   (`TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`).
4. Campanato decay `ψ(t) ≲ (t / R)^{n+1+2β}`, from the second inequality and step 3. This needs
   `β < 1`.

By Jensen's inequality, step 4 bounds the mean oscillation of `∇u` on balls of radius `t` by a
multiple of `t^β`, and the local form of Campanato's theorem
(`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`) gives the
Hölder estimate.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`:
  the interior Schauder estimate for `∇u` with a scalar datum `f ∈ L^q`.
* `exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`: its
  case `f = 0`, with exponent `α`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations with
  variable coefficients, by freezing the coefficients).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.32 (the estimate with a bounded scalar datum).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- **Comparison with the frozen problem on a ball.** There is `A`, depending only on `n`, `λ`
and `Λ`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly
on `Ω ⊆ ℝ^{n+1}`, let `ball x₀ r ⊆ Ω`, let `a(x₀)` be uniformly elliptic with constants `λ`, `Λ`,
let `a` and `G` be `α`-Hölder on `ball x₀ r` with constants `K_a` and `K_G`, and let
`f ∈ L²(B_r)`. Write `Φ(t) = ∫_{B_t} ‖∇u‖²` and `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`, and
`e = r^{2α} (K_a / λ)² Φ(r) + r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r} f²`. Then for `0 < ρ ≤ r`,
`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A e` and `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A e`. -/
private theorem exists_comparison (n : ℕ) (lam Lam : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {r ρ : ℝ} {α Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → x₀ ∈ s → 0 < α →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r) →
      HolderOnWith KG α G (ball x₀ r) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      MemLp f 2 (volume.restrict (ball x₀ r)) →
      ball x₀ r ⊆ Omega → 0 < ρ → ρ ≤ r →
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 1) * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 *
                (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
                (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
                  4 * r ^ 2 * ∫ x in ball x₀ r, f x ^ 2)) ∧
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 1 + 2) *
              (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 *
                (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
                (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
                  4 * r ^ 2 * ∫ x in ball x₀ r, f x ^ 2)) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  set D₀ : ℝ := 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)
  set D₁ : ℝ := 2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)
  have hD₀ : 0 ≤ D₀ := by positivity
  have hD₁ : 0 ≤ D₁ := by positivity
  refine ⟨3 * (1 + ω) * (4 * (D₀ + D₁) + 2) * (1 + (lam ^ 2)⁻¹), by positivity, ?_⟩
  intro Omega u a G f s x₀ r ρ α Ka KG h hx₀ hα haK hGK hu hf hball hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, he⟩ :=
    h.exists_frozen_setIntegral_norm_gradient_sub_sq_le hx₀ hα haK hGK hu hf hball hr
  -- The error term of the comparison, with `λ` taken out of the data.
  have hΦ0 : 0 ≤ ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hI0 : 0 ≤ ∫ x in ball x₀ r, f x ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have he' := rpow_mul_add_mul_div_sq_le (α := (α : ℝ)) (Ka := (Ka : ℝ)) (KG := (KG : ℝ))
    (lam := lam) hr.le hΦ0 (by positivity : (0 : ℝ) ≤ r ^ ((n : ℝ) + 1)) hI0
  have he0 : 0 ≤ r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 *
      (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
      (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball x₀ r, f x ^ 2) := by positivity
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
    exact le_mul_add_mul_of_le_of_le_mul hD₀ hD₁ (by positivity) hω (by positivity) he0
      (setIntegral_norm_gradient_sq_le_add_of_frozen h.pos (h.lower_bound hx₀) hAu hw0 hball hρ
        hρr) he he'
  · have hrp : (ρ / r) ^ ((n : ℝ) + 1 + 2) = (ρ / r) ^ (n + 1 + 2) := by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    rw [hrp, add_comm D₀ D₁]
    exact le_mul_add_mul_of_le_of_le_mul hD₁ hD₀ (by positivity) hω (by positivity) he0
      (setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen h.pos (h.lower_bound hx₀) hAu
        hw0 hball hρ hρr) he he'

end Comparison

section Iteration

/-- **Morrey decay of the gradient.** For `α > 0` and `γ > 0` there are `θ ∈ (0, 1]` and `C`,
depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that the following holds. Let `u ∈ H¹(Ω)`
solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `Ω ⊆ ℝ^{n+1}`, let `ball z R ⊆ Ω`, let `a(z)` be
uniformly elliptic with constants `λ`, `Λ`, let `a` and `G` be `α`-Hölder on `ball z R` with
constants `K_a`, `K_G`, where `K_a R^α ≤ M`, and let `f ∈ L²(B_R)`. If the data decay like
`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r} f² ≤ V (r / R)^{n+1+2γ}` for `0 < r ≤ R` and
`∫_{B_R} ‖∇u‖² ≤ V`, then `∫_{B_ρ} ‖∇u‖² ≤ C V (ρ / R)^{n+1-γ}` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sq_le_rpow {α : ℝ≥0} (hα : 0 < α) {γ : ℝ}
    (hγ : 0 < γ) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R)) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x‖ ^ 2 ≤ C * V * (ρ / R) ^ ((n : ℝ) + 1 - γ) := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison n lam Lam
  obtain ⟨θ, C, hθ, hθ1, hC, hit⟩ := exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add
    (d := (n : ℝ) + 1) (M := M / lam) hA (by exact_mod_cast hα) hγ
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro Omega u a G f s z R V Ka KG h hz haK hGK hu hf hball hR hM hD hΦR
  have hV0 : 0 ≤ V := (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity).trans hΦR
  -- The `L²` mass `∫_{B_t} ‖∇u‖²` is nondecreasing in the radius.
  have hmono : MonotoneOn (fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2) (Iic R) := by
    simpa only [inter_univ] using
      (Lp.memLp (W1p.gradient u)).monotoneOn_setIntegral_ball_inter_norm_sq (H := univ) hball
  exact hit (Φ := fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2)
    (D := fun r => r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ x in ball z r, f x ^ 2) hR (div_nonneg Ka.property h.pos.le)
    (by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hM h.pos.le)
    (hmono.mono Ioc_subset_Iic_self)
    (fun t _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hΦR
    (fun r hr hrR => (hD r hr hrR).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hR).2 hrR) (by linarith))
      hV0))
    fun ρ r hρ hρr hrR => (hcomp h hz hα (haK.mono (ball_subset_ball hrR))
      (hGK.mono (ball_subset_ball hrR)) hu
      (hf.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl))
      ((ball_subset_ball hrR).trans hball) hρ hρr).1

/-- **Campanato decay of the gradient from a Morrey bound.** Let `α > 0`, `θ ∈ (0, 1]` and
`L ≥ 0`, and let `τ < n + 3` with `τ ≤ 2α + β` and `τ ≤ n + 1 + 2γ`. There is `C`, depending only
on `n`, `α`, `τ`, `λ`, `Λ`, `M`, `θ` and `L`, such that the following holds. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `Ω ⊆ ℝ^{n+1}`, let `ball z R ⊆ Ω`, let `a(z)` be uniformly
elliptic with constants `λ`, `Λ`, let `a` and `G` be `α`-Hölder on `ball z R` with constants
`K_a`, `K_G`, where `K_a R^α ≤ M`, and let `f ∈ L²(B_R)`. Suppose that the data decay like
`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r} f² ≤ V (r / R)^{n+1+2γ}` for `0 < r ≤ R`, that
`∫_{B_R} ‖∇u‖² ≤ V`, and that `∫_{B_t} ‖∇u‖² ≤ L V (t / R)^β` for `0 < t ≤ θ R`. Then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C V (ρ / R)^τ` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow {α : ℝ≥0} (hα : 0 < α)
    {β γ τ : ℝ} (hτβ : τ ≤ 2 * (α : ℝ) + β) (hτγ : τ ≤ (n : ℝ) + 1 + 2 * γ)
    (hτ : τ < (n : ℝ) + 3) {lam Lam M θ L : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R)) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      (∀ t, 0 < t → t ≤ θ * R → ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 ≤ L * V * (t / R) ^ β) →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
          C * V * (ρ / R) ^ τ := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison n lam Lam
  obtain ⟨C, hC, hit⟩ :=
    exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow (α := α)
      (κ := (n : ℝ) + 1 + 2 * γ) (δ := (n : ℝ) + 1 + 2) (M := M / lam) hA hτβ hτγ (by linarith) hθ
      hθ1 hL
  refine ⟨C, hC, ?_⟩
  intro Omega u a G f s z R V Ka KG h hz haK hGK hu hf hball hR hM hD hΦR hΦ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  -- The `L²` mass `∫_{B_t} ‖∇u‖²` is nondecreasing in the radius.
  have hmono : MonotoneOn (fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2) (Iic R) := by
    simpa only [inter_univ] using
      (Lp.memLp (W1p.gradient u)).monotoneOn_setIntegral_ball_inter_norm_sq (H := univ) hball
  exact hit (φ := fun t =>
      ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2)
    (Φ := fun t => ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2)
    (D := fun r => r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ x in ball z r, f x ^ 2) hR (div_nonneg Ka.property h.pos.le)
    (by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hM h.pos.le)
    (W1p.monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq u
      ((ball_subset_ball hθR).trans hball))
    (fun t _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)
    ((W1p.setIntegral_norm_gradient_sub_setAverage_sq_le u
      ((ball_subset_ball hθR).trans hball)).trans
      ((hmono hθR le_rfl hθR).trans hΦR))
    (fun t _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hΦ
    (fun r hr hrθ => hD r hr (hrθ.trans hθR))
    fun ρ r hρ hρr hrθ => (hcomp h hz hα (haK.mono (ball_subset_ball (hrθ.trans hθR)))
      (hGK.mono (ball_subset_ball (hrθ.trans hθR))) hu
      (hf.mono_measure (Measure.restrict_mono (ball_subset_ball (hrθ.trans hθR)) le_rfl))
      ((ball_subset_ball (hrθ.trans hθR)).trans hball) hρ hρr).2

/-- **Morrey decay with the full exponent from Campanato decay.** Let `κ > 0` and `θ ∈ (0, 1]`.
There is `C₃`, depending only on `n`, `κ`, `θ` and `C₂`, such that the following holds. If
`ball z R ⊆ Ω`, `∫_{B_R} ‖∇u‖² ≤ V` and `∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C₂ V (t / R)^{n+1+2κ}` for
`0 < t ≤ θ R`, then `∫_{B_t} ‖∇u‖² ≤ C₃ V (t / R)^{n+1}` for `0 < t ≤ θ R`. This is the case
`Ω = univ` of `TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`: by
Campanato's estimate the averages of `∇u` over the balls stay bounded. -/
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
  obtain ⟨C₃, hC₃, h⟩ := exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (F := EuclideanSpace ℝ (Fin (n + 1))) hκ hθ hθ1 hC₂ one_pos
  refine ⟨C₃, hC₃, fun {Omega u z R V} hball hR hΦR hψ => ?_⟩
  simpa only [inter_univ, finrank_euclideanSpace_fin] using
    h (Ω := univ) (g := W1p.gradient u) (fun _ _ _ => by simp)
      ((Lp.memLp (W1p.gradient u)).mono_measure
        (Measure.restrict_mono (inter_subset_left.trans hball) le_rfl)) hR
      (by simpa only [inter_univ] using hΦR)
      (by simpa only [inter_univ, finrank_euclideanSpace_fin] using hψ)

end Iteration

/-- **Decay of the gradient at a centre.** Let `0 < γ < 1` with `γ ≤ α`. There are
`θ ∈ (0, 1]` and `C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that the following
holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `Ω ⊆ ℝ^{n+1}`, let
`ball z R ⊆ Ω`, let `a(z)` be uniformly elliptic with constants `λ`, `Λ`, let `a` and `G` be
`α`-Hölder on `ball z R` with constants `K_a`, `K_G`, where `K_a R^α ≤ M`, and let `f ∈ L²(B_R)`.
If the data decay like `r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r} f² ≤ V (r / R)^{n+1+2γ}` for
`0 < r ≤ R` and `∫_{B_R} ‖∇u‖² ≤ V`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C V (ρ / R)^{n+1+2γ}` for `0 < ρ ≤ θ R`. -/
theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith
    {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R)) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
          C * V * (ρ / R) ^ (2 * γ + ((n : ℝ) + 1)) := by
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  -- Morrey decay with exponent `n + 1 - γ`.
  obtain ⟨θ, C₁, hθ, hθ1, hC₁, hΦ1⟩ :=
    exists_setIntegral_norm_gradient_sq_le_rpow (n := n) hα hγ (Lam := Lam) (M := M)
  -- Campanato decay with exponent `n + 1 + γ`.
  obtain ⟨C₂, hC₂, hψ2⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow (n := n) hα
    (β := (n : ℝ) + 1 - γ) (γ := γ) (τ := (n : ℝ) + 1 + γ) (by linarith) (by linarith)
    (by linarith) (Lam := Lam) (M := M) hθ hθ1 hC₁
  -- Bounded averages, hence Morrey decay with exponent `n + 1`.
  obtain ⟨C₃, hC₃, hΦ3⟩ := exists_setIntegral_norm_gradient_sq_le_pow (n := n) (κ := γ / 2)
    (by positivity) hθ hθ1 hC₂
  -- Campanato decay with exponent `n + 1 + 2γ`.
  obtain ⟨C₄, hC₄, hψ4⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le_rpow (n := n) hα
    (β := (n : ℝ) + 1) (γ := γ) (τ := 2 * γ + ((n : ℝ) + 1)) (by linarith) (by linarith)
    (by linarith) (Lam := Lam) (M := M) hθ hθ1 hC₃
  refine ⟨θ, C₄, hθ, hθ1, hC₄, ?_⟩
  intro Omega u a G f s z R V Ka KG h hz haK hGK hu hf hball hR hM hD hΦR
  have hΦ1z := hΦ1 h hz haK hGK hu hf hball hR hM hD hΦR
  have hψ2z := hψ2 h hz haK hGK hu hf hball hR hM hD hΦR hΦ1z
  have hΦ3z := hΦ3 hball hR hΦR fun t ht htθ => (hψ2z t ht htθ).trans_eq (by
    rw [← Real.rpow_natCast, ← Real.rpow_add (div_pos ht hR)]
    congr 2
    push_cast
    ring)
  exact hψ4 h hz haK hGK hu hf hball hR hM hD hΦR fun t ht htθ => (hΦ3z t ht htθ).trans_eq (by
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf)

/-- **The data on a small ball.** Let `f ∈ L^q(T)` with `q ≥ 2`, let `β ≤ α` and
`β ≤ 1 - (n + 1) / q`, and let `Q` bound both `R^{α-β} K_G` and
`R^{1-(n+1)/q-β} ‖f‖_{L^q(T)}`. If `B(z, r) ⊆ T` with `0 < r ≤ R`, then by Hölder's inequality the
data term of the comparison estimate on `B(z, r)` decays with the exponent `n + 1 + 2β`:

`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B(z, r)} f² ≤ (1 + 4 ω^{1-2/q}) (R^{(n+1)/2+β} Q)² (r / R)^{n+1+2β}`,

where `ω` is the volume of the unit ball. -/
theorem rpow_mul_add_mul_setIntegral_sq_le {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {T : Set (EuclideanSpace ℝ (Fin (n + 1)))} {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hf : MemLp f q (volume.restrict T)) {α β KG Q R r : ℝ} (hβα : β ≤ α)
    (hβq : β ≤ 1 - ((n : ℝ) + 1) / q.toReal) (hKG : 0 ≤ KG) (hGQ : R ^ (α - β) * KG ≤ Q)
    (hfQ : R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * (eLpNorm f q (volume.restrict T)).toReal ≤ Q)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hr : 0 < r) (hrR : r ≤ R) (hsub : ball z r ⊆ T) :
    r ^ (2 * α) * (KG ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤
      (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^ (1 - 2 / q.toReal)) *
        (R ^ (((n : ℝ) + 1) / 2 + β) * Q) ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  set Kf := (eLpNorm f q (volume.restrict T)).toReal
  set X := R ^ (((n : ℝ) + 1) / 2 + β) * Q
  -- Hölder's inequality on `B_r`: `∫_{B_r} f² ≤ ‖f‖²_{L^q(T)} ω^{1-2/q} r^{(n+1)(1-2/q)}`.
  have h2 := hf.setIntegral_ball_norm_sq_le_eLpNorm_sq_mul_rpow hq hr hsub
  simp only [Real.norm_eq_abs, sq_abs, finrank_euclideanSpace_fin] at h2
  have hr2 : r ^ 2 * r ^ (((n + 1 : ℕ) : ℝ) * (1 - 2 / q.toReal)) =
      r ^ (2 * (1 - ((n : ℝ) + 1) / q.toReal)) * r ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hF : 4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤ 4 * ω ^ (1 - 2 / q.toReal) *
      (r ^ (2 * (1 - ((n : ℝ) + 1) / q.toReal)) * (Kf ^ 2 * r ^ ((n : ℝ) + 1))) :=
    calc 4 * r ^ 2 * ∫ x in ball z r, f x ^ 2
        ≤ 4 * r ^ 2 * (Kf ^ 2 *
          (ω ^ (1 - 2 / q.toReal) * r ^ (((n + 1 : ℕ) : ℝ) * (1 - 2 / q.toReal)))) := by gcongr
      _ = 4 * ω ^ (1 - 2 / q.toReal) *
          (Kf ^ 2 * (r ^ 2 * r ^ (((n + 1 : ℕ) : ℝ) * (1 - 2 / q.toReal)))) := by ring
      _ = _ := by rw [hr2]; ring
  -- Both data decay with the exponent `n + 1 + 2β`.
  have hG := Real.rpow_mul_mul_rpow_le_rpow_div_two_add_mul_sq_mul_rpow (d := (n : ℝ) + 1) hr hrR
    hβα hKG hGQ
  have hF' := Real.rpow_mul_mul_rpow_le_rpow_div_two_add_mul_sq_mul_rpow (d := (n : ℝ) + 1) hr
    hrR hβq ENNReal.toReal_nonneg hfQ
  calc _ ≤ X ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β) +
        4 * ω ^ (1 - 2 / q.toReal) * (X ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β)) :=
        add_le_add hG (hF.trans (mul_le_mul_of_nonneg_left hF' (by positivity)))
    _ = _ := by ring

/-- **Interior Schauder estimate for divergence-form equations with a scalar datum.** Let
`0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`.
There is a constant `C`, depending only on `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, such that the
following holds. Let `Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every
test function `φ`. Let `S` be a set whose open `R`-thickening `S_R` lies in `Ω`, let `a` be
uniformly elliptic with constants `λ`, `Λ` at the points of `S`, let `a` and `G` be `α`-Hölder on
`S_R` with constants `K_a` and `K_G`, the oscillation of `a` measured in the operator norm of the
attached bilinear forms, where `K_a R^α ≤ M`, and let `f ∈ L^q(S_R)`. Then the precise
representative of `∇u` is `β`-Hölder on `S`, with constant

`C (K_G R^{α-β} + R^{1-(n+1)/q-β} ‖f‖_{L^q(S_R)} + R^{-(n+1)/2-β} ‖∇u‖_{L²(Ω)})`.

The largest admissible exponent is `β = min α (1 - (n + 1) / q)` when this is less than `1`, which
needs `q > n + 1`: the datum `f` costs `(n + 1) / q` of a derivative. For finite `q` the
hypothesis `β < 1` follows from `β ≤ 1 - (n + 1) / q`, and `q ≥ 2` follows from `q > n + 1`
except in dimension one. A bounded datum, `q = ∞`, allows every `β < 1` with `β ≤ α`. Every term
of the constant scales like `[∇u]_β`, so the estimate is invariant under dilations. The precise
representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn S a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (thickening R S)) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (KG * R ^ ((α : ℝ) - β) +
            R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
              (eLpNorm f q (volume.restrict (thickening R S))).toReal +
            R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖)).toNNReal β
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  have hβ' : (0 : ℝ) < β := hβ
  obtain ⟨θ, C₀, hθ, hθ1, _, hdec⟩ :=
    exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith (n := n) (α := α) hβ'
      (by exact_mod_cast hβα) (by exact_mod_cast hβ1) (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ measureReal_ball_pos volume _ one_pos
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(β : ℝ))) := ⟨_, rfl⟩
  have hc : 0 ≤ c := hcdef ▸ div_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hβ'))).le
  -- The data enter the decay estimate through `V = c₀ (R^{(n+1)/2+β} Q)²`.
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = 1 + 4 * ω ^ (1 - 2 / q.toReal) := ⟨_, rfl⟩
  have hc₀ : 1 ≤ c₀ := hc₀def ▸ le_add_of_nonneg_right (by positivity)
  refine ⟨2 * 2 ^ (β : ℝ) * (c * √(C₀ * c₀ / ω) + θ ^ (-(β : ℝ)) / √(ω * θ ^ (n + 1))),
    by positivity, ?_⟩
  intro Omega u a G f Ka KG S R h haK hGK hM hf hu hR hRS
  obtain ⟨Kf, hKf⟩ : ∃ Kf, Kf = (eLpNorm f q (volume.restrict (thickening R S))).toReal :=
    ⟨_, rfl⟩
  rw [← hKf]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (KG : ℝ) * R ^ ((α : ℝ) - β) +
      R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf +
      R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖ := ⟨_, rfl⟩
  rw [← hQ]
  have hKf0 : 0 ≤ Kf := hKf ▸ ENNReal.toReal_nonneg
  have hRG : 0 ≤ (KG : ℝ) * R ^ ((α : ℝ) - β) := by positivity
  have hRf : 0 ≤ R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf := by positivity
  have hRu : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖ := by positivity
  have hQ0 : 0 ≤ Q := hQ ▸ by positivity
  have hGQ : R ^ ((α : ℝ) - β) * KG ≤ Q := by
    rw [hQ, mul_comm]
    linarith
  have hfQ : R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf ≤ Q := by
    rw [hQ]
    linarith
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hball : ∀ z ∈ S, ball z R ⊆ Omega := fun z hz => (ball_subset_thickening hz R).trans hRS
  set X := R ^ (((n : ℝ) + 1) / 2 + β) * Q with hX
  have hVR : X ^ 2 = R ^ (n + 1) * (R ^ (β : ℝ) * Q) ^ 2 := by
    rw [hX, Real.rpow_div_two_add_mul_sq Q hR]
    norm_cast
  have hXu : ‖W1p.gradient u‖ ≤ X := by
    rw [hX, hQ, mul_add, ← mul_assoc _ (R ^ _), ← Real.rpow_add hR, add_neg_cancel,
      Real.rpow_zero, one_mul]
    exact le_add_of_nonneg_left (by positivity)
  have hV2 : ∀ z ∈ S, ∫ x in ball z R, ‖W1p.gradient u x‖ ^ 2 ≤ X ^ 2 := fun z hz =>
    (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) (hball z hz)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hXu 2)
  -- The data decay with the exponent `n + 1 + 2β`.
  have hD : ∀ z ∈ S, ∀ r, 0 < r → r ≤ R →
      r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r, f x ^ 2 ≤
          c₀ * X ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β) := fun z hz r hr hrR => by
    rw [hc₀def, hωdef]
    exact rpow_mul_add_mul_setIntegral_sq_le hq hf (by exact_mod_cast hβα) hβq KG.property hGQ
      (hKf ▸ hfQ) hr hrR ((ball_subset_ball hrR).trans (ball_subset_thickening hz R))
  -- The mean oscillation of `∇u` on `closedBall z t` is at most `√(C₀ c₀ / ω) Q t^β`.
  have hosc : ∀ z ∈ S, ∀ t, 0 < t → t ≤ θ * R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        √(C₀ * c₀ / ω) * Q * t ^ (β : ℝ) := fun z hz t ht htθ => by
    have : IsFiniteMeasure (volume.restrict (ball z R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact hωdef ▸ W1p.setAverage_closedBall_norm_gradient_sub_le_mul_rpow u
      ((ball_subset_ball (htθ.trans hθR)).trans (hball z hz)) ht hR hQ0
      ((hdec h hz (haK.mono (ball_subset_thickening hz R)) (hGK.mono (ball_subset_thickening hz R))
        hu ((hf.mono_measure (Measure.restrict_mono (ball_subset_thickening hz R)
          le_rfl)).mono_exponent hq) (hball z hz) hR hM (hD z hz)
        ((hV2 z hz).trans (le_mul_of_one_le_left (sq_nonneg X) hc₀)) t ht htθ).trans_eq
        (by ring))
  -- The average of `∇u` over `closedBall z (θ R)` is at most `R^β Q / √(ω θ^{n+1})`.
  have havg : ∀ z ∈ S, ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ≤
      R ^ (β : ℝ) * Q / √(ω * θ ^ (n + 1)) := fun z hz => hωdef ▸
    W1p.norm_setAverage_closedBall_gradient_le_div u ((ball_subset_ball hθR).trans (hball z hz))
      hθ hR hQ0 (hVR ▸ le_trans (by
        simpa only [inter_univ] using
          (Lp.memLp (W1p.gradient u)).monotoneOn_setIntegral_ball_inter_norm_sq (H := univ)
            (hball z hz) hθR le_rfl hθR) (hV2 z hz))
  have hH := TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le hβ
    (ρ := θ * R) (by positivity)
    (fun z hz => W1p.integrableOn_closedBall_gradient u (hball z hz) hθR) hosc havg
  have hconst : c * (√(C₀ * c₀ / ω) * Q) +
      R ^ (β : ℝ) * Q / √(ω * θ ^ (n + 1)) * (θ * R) ^ (-(β : ℝ)) =
      (c * √(C₀ * c₀ / ω) + θ ^ (-(β : ℝ)) / √(ω * θ ^ (n + 1))) * Q := by
    rw [Real.mul_rpow hθ.le hR.le, Real.rpow_neg hR.le]
    field_simp [(Real.rpow_pos_of_pos hR (β : ℝ)).ne']
  rwa [← hcdef, hconst, ← mul_assoc] at hH

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
This is the case `f = 0`, `q = ∞`, `β = α` of
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`;
for `a = 1` it is `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`. -/
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
  -- The datum is `f = 0`, which lies in `L^∞`.
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
      (n := n) hα hα1 le_rfl le_top (by simpa using hα1.le) (lam := lam) (Lam := Lam) (M := M)
  refine ⟨C, hC, fun hell haK hGK hM hu hR hRS => ?_⟩
  have h' := h hell haK hGK hM (f := 0) MemLp.zero
    (fun φ => by rw [hu φ, Pi.zero_def]; simp only [zero_mul, integral_zero, add_zero]) hR hRS
  simpa only [sub_self, Real.rpow_zero, mul_one, eLpNorm_zero, ENNReal.toReal_zero, mul_zero,
    add_zero] using h'

end PDE

end TauCeti
