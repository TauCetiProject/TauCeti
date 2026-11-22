/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HigherIntegrability
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.EnergyForm.Integrated.Symmetry
import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# Meyers' global `W^{1,p}` estimates for the Dirichlet problem

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ` with constants
`0 < λ ≤ Λ ≤ K λ`, and let `u ∈ H¹₀(Ω)` be the weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, `u = 0` on `∂Ω`,

that is `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, with `F ∈ L²(Ω; ℝⁿ)`. Suppose that the
complement of `Ω` has density at least `θ > 0` at its points up to a scale `r₀ > 0`:
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`, as for Lipschitz domains. This file
proves the two global estimates of Meyers' Theorem 1, for exponents near `2` on either side, with
`ε₀ > 0` and the constants depending only on `n`, `K` and `θ`.

* **Above `2`.** For `0 < ε ≤ ε₀`,

  `∫_Ω ‖∇u‖^(2+ε) ≤ C (|B_{r₀}|^(-ε/2) (∫_Ω (‖F‖/λ)²)^((2+ε)/2) + ∫_Ω (‖F‖/λ)^(2+ε))`

  (`TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`). Both sides scale in the
  same way under dilations of `Ω`. By Jensen's inequality this gives the norm bound

  `‖∇u‖_{L^{2+ε}(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{L^{2+ε}(Ω)} / λ`

  (`TauCeti.PDE.exists_eLpNorm_gradient_le_divergence`).
* **Below `2`.** For `0 < ε ≤ ε₀` and the conjugate exponent `p = (2+ε)/(1+ε) < 2`, on an open set
  of finite measure,

  `‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`

  (`TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`). The right-hand side only
  involves `‖F‖_{Lᵖ}`, a weaker norm than `‖F‖_{L²}`, so this is not a regularity statement but
  the a priori estimate behind the `W^{1,p}` theory of the Dirichlet problem for `p < 2`.

The local estimate up to the boundary
(`TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence`) bounds the
`(2+ε)`-mean of the gradient of the zero extension of `u` on every ball `B(y, r₀/2)` by its
`L²` mean and the `(2+ε)`-mean of `F` on `B(y, r₀)`. Integrating over all centres `y`
(`TauCeti.lintegral_rpow_le_of_forall_setLAverage_rpow_le`) turns it into a global bound that
still involves the `L²` norm of the gradient. The energy estimate `λ ‖∇u‖₂ ≤ ‖F‖₂`, from testing
the equation with `u`, removes it from the right-hand side.

The estimate below `2` follows by duality. For a bounded field `g` vanishing off a set of finite
measure, let `v ∈ H¹₀(Ω)` solve the adjoint problem `-∂ⱼ(aⁱʲ ∂ᵢv) = ∂ᵢgⁱ`, whose coefficient `aᵀ`
has the same ellipticity constants. Testing the two equations with each other gives
`∫ ⟪∇u, g⟫ = ∫ ⟪F, ∇v⟫`, which Hölder's inequality and the estimate above `2` for `v` bound by
`‖F‖_p ‖∇v‖_{2+ε} ≤ C' ‖F‖_p ‖g‖_{2+ε} / λ`. Such fields `g` norm `Lᵖ`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`).

## Main declarations

* `TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`: the global estimate above
  `2`.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_divergence`: its norm form, with the measure of `Ω` in
  place of the `L²` norm of `F`.
* `TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`: the global estimate below
  `2`.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorem 1.
* T. Kilpeläinen, P. Koskela, *Global integrability of the gradients of solutions to partial
  differential equations*, Nonlinear Anal. **23** (1994), 899–909.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- **Meyers' global estimate above `2`.** Let `n ≥ 1` be the dimension, let `K` bound the
ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`,
both depending only on `n`, `K` and `θ`, with the following property. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let
`u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. Suppose that the complement
of `Ω` has density at least `θ` at its points up to a scale `r₀ > 0`:
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`. Then

`∫_Ω ‖∇u‖^(2+ε) ≤ C (|B_{r₀}|^(-ε/2) (∫_Ω (‖F‖/λ)²)^((2+ε)/2) + ∫_Ω (‖F‖/λ)^(2+ε))`,

where `B_{r₀}` is a ball of radius `r₀`. No boundedness of `Ω` is assumed. -/
theorem exists_lintegral_enorm_gradient_rpow_le_divergence [Nonempty ι] (K : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
        {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ →
      ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((mu (ball 0 r₀))⁻¹ ^ (ε / 2) *
            (∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence
    (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u r₀} h hK ha hF hu hdens hr₀ => ?_⟩
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- The zero extensions of `‖∇u‖` and of `‖F‖ / λ`; their integrals are integrals over `Ω`.
  set g : EuclideanSpace ℝ ι → ℝ≥0∞ := fun x =>
    ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ
  set k : EuclideanSpace ℝ ι → ℝ≥0∞ := fun x =>
    ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam
  have hgΩ : ∀ r : ℝ, 0 < r → ∫⁻ x, g x ^ r ∂mu =
      ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ r ∂mu := fun r hr =>
    lintegral_enorm_rpow_eq_setLIntegral hOm .rfl hr
  have hkΩ : ∀ r : ℝ, 0 < r → ∫⁻ x, k x ^ r ∂mu =
      ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ r ∂mu := fun r hr => by
    simpa only [eNorm_eq_self] using lintegral_enorm_rpow_eq_setLIntegral hOm
      (g := k) (f := fun x => ‖F x‖ₑ / ENNReal.ofReal lam)
      (ae_of_all _ fun x => by
        by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) <;> simp [k, hx]) hr
  -- Meyers' estimates on the balls of radius `r₀` integrate to a global one.
  have hglob := lintegral_rpow_le_of_forall_setLAverage_rpow_le (μ := mu) (g := g) (k := k)
    ((aestronglyMeasurable_indicator_iff hOm).2
      (Lp.aestronglyMeasurable (W1p.gradient (u : W1p mu Omega 2)))).eNorm
    (((aestronglyMeasurable_indicator_iff hOm).2 hF.aestronglyMeasurable).eNorm.div_const _)
    two_pos (by linarith : (2 : ℝ) ≤ 2 + ε) hr₀ (C := C)
    fun y => hC h hK ha hF hu hdens le_rfl (x₀ := y)
  rw [show (2 + ε) / 2 - 1 = ε / 2 by ring, hgΩ (2 + ε) (by positivity), hgΩ 2 two_pos,
    hkΩ (2 + ε) (by positivity)] at hglob
  -- The energy estimate bounds the remaining `L²` norm of the gradient.
  refine hglob.trans ?_
  have hE := h.lintegral_enorm_gradient_sq_le_of_forall_energyFormH1_eq_divergence ha hF hu
  gcongr

/-- **Meyers' global estimate above `2`, in norm form.** Let `K` bound the ellipticity ratio and
let `θ > 0`. There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both depending only on
the dimension, `K` and `θ`, with the following property. Under the hypotheses of
`TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`,

`‖∇u‖_{L^{2+ε}(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{L^{2+ε}(Ω)} / λ`,

where `B_{r₀}` is a ball of radius `r₀`. The bound is finite when `Ω` has finite measure and
`F ∈ L^{2+ε}(Ω)`. -/
theorem exists_eLpNorm_gradient_le_divergence [Nonempty ι] (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
        {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ →
      eLpNorm (W1p.gradient (u : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) ≤
        (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ *
          eLpNorm F (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) / ENNReal.ofReal lam := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_lintegral_enorm_gradient_rpow_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u r₀} h hK ha hF hu hdens hr₀ => ?_⟩
  have hq : 0 < 2 + ε := by linarith
  -- Jensen's inequality bounds the `L²` term by the `L^{2+ε}` term and the measure of `Ω`.
  have hJ := rpow_lintegral_le_measure_univ_rpow_mul (μ := mu.restrict Omega)
    (u := fun x => (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ)) (r := (2 + ε) / 2) (by linarith)
  rw [Measure.restrict_apply_univ, show (2 + ε) / 2 - 1 = ε / 2 by ring] at hJ
  simp_rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((2 + ε) / 2) = 2 + ε by ring] at hJ
  have hint : ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ (2 + ε) ∂mu ≤
      C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2)) *
        ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu := by
    refine (hC h hK ha hF hu hdens hr₀).trans ((by gcongr : _ ≤ (C : ℝ≥0∞) *
      ((mu (ball 0 r₀))⁻¹ ^ (ε / 2) * (mu Omega ^ (ε / 2) *
        ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) +
          ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu)).trans_eq ?_)
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    ring
  -- Take `(2 + ε)`-th roots.
  have hF' : ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu =
      (eLpNorm F (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) / ENNReal.ofReal lam) ^ (2 + ε) := by
    have hpow := eLpNorm_rpow_eq_lintegral (by simpa using hq) ENNReal.ofReal_ne_top
      (hF.aestronglyMeasurable.eNorm.div_const (ENNReal.ofReal lam))
    rw [ENNReal.toReal_ofReal hq.le] at hpow
    rw [← hpow, eLpNorm_enorm_div_const (by simpa using hq) hF.aestronglyMeasurable]
  refine eLpNorm_le_of_lintegral_rpow_le (by simpa using hq) ENNReal.ofReal_ne_top
    (Lp.aestronglyMeasurable _) ?_
  rw [ENNReal.toReal_ofReal hq.le, mul_div_assoc, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    ← ENNReal.rpow_mul, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one, ← hF']
  exact hint

/-- **Meyers' global estimate below `2`.** Let `K` bound the ellipticity ratio and let `θ > 0`.
There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both depending only on the dimension,
`K` and `θ`, with the following property for the exponent `p = (2+ε)/(1+ε)`, the conjugate of
`2 + ε`. Let `Ω ⊆ ℝⁿ` be open of finite measure, and suppose that its complement has density at
least `θ` at its points up to a scale `r₀ > 0`: `θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and
`0 < r ≤ r₀`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, and let `u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`.
Then

`‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`,

where `B_{r₀}` is a ball of radius `r₀`. The exponents `p` fill `[(2+ε₀)/(1+ε₀), 2)`. -/
theorem exists_eLpNorm_gradient_conjExponent_le_divergence [Nonempty ι] (K : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
        {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ → mu Omega ≠ ∞ →
      eLpNorm (W1p.gradient (u : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε).conjExponent)
          (mu.restrict Omega) ≤
        (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ *
          eLpNorm F (ENNReal.ofReal (2 + ε).conjExponent) (mu.restrict Omega) /
            ENNReal.ofReal lam := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_eLpNorm_gradient_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u r₀} h hK ha hu hdens hr₀ hfin => ?_⟩
  have hpq := (Real.HolderConjugate.conjExponent (by linarith : 1 < 2 + ε)).symm
  have := ENNReal.holderConjugate_iff.2 hpq.inv_add_inv_ennreal
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  set D := (C : ℝ≥0∞) * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))
  -- Norm `∇u` in `Lᵖ` against bounded test fields `g`, which lie in `L²(Ω)`.
  refine (Lp.aestronglyMeasurable _).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ)
    (q' := ENNReal.ofReal (2 + ε)) ENNReal.ofReal_ne_top fun g s _ _ hg => ?_
  have hg2 : MemLp g 2 (mu.restrict Omega) := hg.mono_exponent le_top
  -- Test the equation of `u` with the solution `v` of the adjoint problem with datum `g`.
  obtain ⟨v, hv⟩ := h.transpose.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top
    (continuous_id.matrix_transpose.comp_aestronglyMeasurable ha) hfin hg2
  have hid : ∫ x in Omega, ⟪W1p.gradient (u : W1p mu Omega 2) x, g x⟫_ℝ ∂mu =
      ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
    have htr : energyFormH1 (fun x => (a x)ᵀ) 0 0 (v : W1p mu Omega 2)
        (u : W1p mu Omega 2) = energyFormH1 a 0 0 (u : W1p mu Omega 2) v := by
      rw [energyFormH1_def, energyFormH1_def, ← energyFormIntegral_def, ← energyFormIntegral_def]
      exact energyFormIntegral_zero_drift_transpose_apply
    simp_rw [real_inner_comm (g _) (W1p.gradient (u : W1p mu Omega 2) _)]
    rw [← neg_neg (∫ x in Omega, ⟪g x, _⟫_ℝ ∂mu), ← hv u, htr, hu v, neg_neg]
  -- Hölder's inequality and the estimate above `2` for `v`.
  have hvq : eLpNorm (W1p.gradient (v : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε))
      (mu.restrict Omega) ≤
        D ^ (2 + ε)⁻¹ * (eLpNorm g (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) /
          ENNReal.ofReal lam) := by
    simpa only [mul_div_assoc] using hC h.transpose hK
      (continuous_id.matrix_transpose.comp_aestronglyMeasurable ha) hg2 hv hdens hr₀
  rw [hid]
  refine (enorm_integral_inner_le (p := ENNReal.ofReal (2 + ε).conjExponent)
    (q := ENNReal.ofReal (2 + ε))).trans ((mul_le_mul_of_nonneg_left hvq zero_le).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

end PDE

end TauCeti
