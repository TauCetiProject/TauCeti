/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
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
(`TauCeti.PDE.UniformlyEllipticOn.exists_frozen_setIntegral_norm_gradient_sub_sq_le`), while
`Φ` and `ψ` decay for `w` with exponents `n + 1` and `n + 3`
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`).
Transferring this decay to `u` (`TauCeti.PDE.setIntegral_norm_gradient_sq_le_add_of_frozen` and
`TauCeti.PDE.setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen`) gives, for
`0 < ρ ≤ r`,

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
    h.exists_frozen_setIntegral_norm_gradient_sub_sq_le hx₀ hα haK hGK hu hball hr
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
    mul_le_mul_of_nonneg_right ((Real.rpow_mul_sq_le hr hR hKa hM).trans
      (mul_le_mul_of_nonneg_right hrθR (sq_nonneg M))) hΦr
  have k2 : r ^ (2 * a) * (KG ^ 2 * r ^ d) ≤ V * R ^ (-β) * r ^ β := by
    have hq : (r / R) ^ β = R ^ (-β) * r ^ β :=
      Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR
    refine (Real.rpow_mul_mul_rpow_le hr hR hV).trans ?_
    rw [mul_assoc, ← hq]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR)
      ((div_le_one₀ hR).2 hrR) hβ) hV0
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
  have hq : (r / R) ^ (2 * a + β) = R ^ (-(2 * a + β)) * r ^ (2 * a + β) :=
    Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR
  have hsplit : (r / R) ^ (2 * a) * (r / R) ^ β = (r / R) ^ (2 * a + β) := by
    rw [← Real.rpow_add (div_pos hr hR)]
  have k1 : r ^ (2 * a) * Ka ^ 2 * Φr ≤ M ^ 2 * L * V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β)) := by
    calc _ ≤ (r / R) ^ (2 * a) * M ^ 2 * (L * V * (r / R) ^ β) :=
          mul_le_mul (Real.rpow_mul_sq_le hr hR hKa hM) hΦr hΦr0 (by positivity)
      _ = M ^ 2 * L * V * ((r / R) ^ (2 * a) * (r / R) ^ β) := by ring
      _ = _ := by rw [hsplit, hq]
  have k2 : r ^ (2 * a) * (KG ^ 2 * r ^ d) ≤ V * (R ^ (-(2 * a + β)) * r ^ (2 * a + β)) := by
    refine (Real.rpow_mul_mul_rpow_le hr hR hV).trans ?_
    rw [← hq]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR)
      ((div_le_one₀ hR).2 hrR) (by linarith)) hV0
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
  obtain ⟨θ, hθ, hθ1, hε⟩ := Real.exists_pos_le_one_mul_rpow_le (M ^ 2 / lam ^ 2)
    (by positivity : (0 : ℝ) < 2 * α) hε₀
  rw [mul_comm] at hε
  rw [← mul_div_assoc] at hε
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
  have hq : (ρ / R) ^ β = R ^ (-β) * ρ ^ β :=
    Real.div_rpow_eq_rpow_neg_mul_rpow hρ.le hR
  refine hit'.trans ?_
  rw [Real.div_mul_rpow_eq hρ.le hθ hR]
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
  have hq : (ρ / R) ^ γ = R ^ (-γ) * ρ ^ γ :=
    Real.div_rpow_eq_rpow_neg_mul_rpow hρ.le hR
  refine hit'.trans ?_
  rw [Real.div_mul_rpow_eq hρ.le hθ hR]
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
  rw [Measure.addHaar_real_ball_of_pos _ z hr, finrank_euclideanSpace_fin,
    mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))] at h1
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
  rw [Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR]
  ring

/-- **Bounded averages from Campanato decay.** Let `κ > 0` and `θ ∈ (0, 1]`. If
`ball z R ⊆ Ω`, `∫_{B_R} ‖∇u‖² ≤ V` and the square mean oscillation of `∇u` satisfies
`∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C₂ V (t / R)^{n+1+2κ}` for `0 < t ≤ θ R`, then for `0 < t ≤ θ R`
the averages of `∇u` over `closedBall z t` satisfy
`‖(∇u)_{z,t}‖² ≤ (2 θ^{-(n+1)} + 2 c² C₂) V / (ω R^{n+1})`, where `ω` is the volume of the unit
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
      (2 / θ ^ (n + 1) + 2 * (2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
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
    rw [Measure.addHaar_real_ball_of_pos _ z (by positivity), finrank_euclideanSpace_fin,
      mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), mul_pow] at h
    rw [hW, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    linarith
  -- By Campanato's estimate, the averages over `closedBall z t` stay close to the average at
  -- radius `θ R`.
  have hat : ‖⨍ y in closedBall z t, W1p.gradient u y‖ ≤
      ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ + c * √(C₂ * W) := by
    have h := norm_setAverage_closedBall_sub_setAverage_closedBall_le hκ
      (integrableOn_closedBall_gradient u hball hθR) hosc ht htθ le_rfl
    rw [← hcdef] at h
    have hRr : R ^ (-κ) * (θ * R) ^ κ ≤ 1 := by
      rw [Real.rpow_neg hR.le, inv_mul_le_one₀ (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hθR hκ.le
    have h' : c * (√(C₂ * W) * R ^ (-κ) * (θ * R) ^ κ) ≤ c * √(C₂ * W) := by
      have := mul_le_mul_of_nonneg_left hRr (by positivity : (0 : ℝ) ≤ c * √(C₂ * W))
      linarith
    have h4 := norm_le_norm_add_norm_sub' (⨍ y in closedBall z t, W1p.gradient u y)
      (⨍ y in closedBall z (θ * R), W1p.gradient u y)
    linarith
  have hsq : (c * √(C₂ * W)) ^ 2 = c ^ 2 * C₂ * W := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  calc ‖⨍ y in closedBall z t, W1p.gradient u y‖ ^ 2
      ≤ (‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ + c * √(C₂ * W)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hat 2
    _ ≤ 2 * ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ^ 2 +
          2 * (c * √(C₂ * W)) ^ 2 := add_sq_le.trans_eq (mul_add _ _ _)
    _ ≤ 2 * (W / θ ^ (n + 1)) + 2 * (c ^ 2 * C₂ * W) := by nlinarith
    _ = (2 / θ ^ (n + 1) + 2 * c ^ 2 * C₂) * W := by ring

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
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 / θ ^ (n + 1) + 2 * (2 ^ finrank ℝ
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
  rw [hpy, Measure.addHaar_real_ball_of_pos _ z ht, finrank_euclideanSpace_fin,
    mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))]
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

end Iteration

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
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  have hV : (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 = R ^ (n + 1) * (R ^ a * Q) ^ 2 := by
    rw [Real.rpow_div_two_add_mul_sq Q hR]
    norm_cast
  refine (setAverage_closedBall_norm_gradient_sub_le u hball ht hR (C := C) (κ := a)
    (V := (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2) (hψ.trans_eq ?_)).trans_eq ?_
  · rw [← Real.rpow_natCast (t / R) (n + 1), ← Real.rpow_add (div_pos ht hR)]
    congr 2
    push_cast
    ring
  · have hRa : R ^ a ≠ 0 := (Real.rpow_pos_of_pos hR a).ne'
    have hC : C * (R ^ (n + 1) * (R ^ a * Q) ^ 2 / (ω * R ^ (n + 1))) =
        C / ω * (R ^ a * Q) ^ 2 := by
      field_simp
    rw [hV, hC, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity), Real.rpow_neg hR.le]
    field_simp

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
  rw [Measure.addHaar_real_ball_of_pos _ z (by positivity), finrank_euclideanSpace_fin,
    mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), mul_pow] at h
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
  have hVR : (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 = R ^ (n + 1) * (R ^ (α : ℝ) * Q) ^ 2 := by
    rw [Real.rpow_div_two_add_mul_sq Q hR]
    norm_cast
  have hV1 : (KG : ℝ) ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) ≤ (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 :=
    Real.sq_mul_rpow_add_two_mul_le hR KG.2 (hQ ▸ le_add_of_nonneg_right (by positivity))
  have hX : ‖W1p.gradient u‖ ≤ R ^ (((n : ℝ) + 1) / 2 + α) * Q := by
    rw [hQ, mul_add, ← mul_assoc, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, one_mul]
    exact le_add_of_nonneg_left (by positivity)
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
  have hconst : c * (√(C₀ / ω) * Q) + R ^ (α : ℝ) * Q / √(ω * θ ^ (n + 1)) * (θ * R) ^ (-(α : ℝ)) =
      (c * √(C₀ / ω) + θ ^ (-(α : ℝ)) / √(ω * θ ^ (n + 1))) * Q := by
    rw [Real.mul_rpow hθ.le hR.le, Real.rpow_neg hR.le]
    field_simp [(Real.rpow_pos_of_pos hR (α : ℝ)).ne']
  rwa [← hcdef, hconst, ← mul_assoc] at hH

end PDE

end TauCeti
