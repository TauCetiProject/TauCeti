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
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.Analysis.Sobolev.Wkp.Exponent
import TauCeti.MeasureTheory.Function.Holder
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
proves the two global estimates of Meyers' Theorem 1, for exponents near `2` on either side, and
the existence of solutions in `W^{1,p}_0(Ω)` for data in `Lᵖ(Ω)` below `2`, with `ε₀ > 0` and the
constants depending only on `n`, `K` and `θ`.

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
* **Solutions for `Lᵖ` data below `2`.** In the same setting, for every `F ∈ Lᵖ(Ω; ℝⁿ)`, which need
  not be square integrable, the Dirichlet problem has a solution `u ∈ W^{1,p}_0(Ω)` in the sense
  that `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ W^{1,q}_0(Ω)`, `q = 2 + ε`, with the same bound
  (`TauCeti.PDE.exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_le_conjExponent`).
  Uniqueness in `W^{1,p}_0(Ω)` is not proved here.

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

The solutions for `Lᵖ` data are obtained by density. Simple fields `Gₖ → F` in `Lᵖ(Ω)` are square
integrable, since `Ω` has finite measure, and their solutions `uₖ ∈ H¹₀(Ω) ⊆ W^{1,p}_0(Ω)` satisfy
`‖∇(uₖ - uₗ)‖_p ≤ C' ‖Gₖ - Gₗ‖_p` by the estimate below `2`. By the Poincaré inequality on
`W^{1,p}_0(Ω)` (`TauCeti.W1p.exists_mem_w1p0Submodule_tendsto_of_cauchySeq_gradient`) they converge
in `W^{1,p}_0(Ω)`, and the equation passes to the limit since `a ∇v ∈ L^q` for `v ∈ W^{1,q}_0(Ω)`.

## Main declarations

* `TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`: the global estimate above
  `2`.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_divergence`: its norm form, with the measure of `Ω` in
  place of the `L²` norm of `F`.
* `TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`: the global estimate below
  `2`.
* `TauCeti.PDE.exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_le_conjExponent`:
  solutions in `W^{1,p}_0(Ω)` for data in `Lᵖ(Ω)` below `2`, with the estimate.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorem 1.
* T. Kilpeläinen, P. Koskela, *Global integrability of the gradients of solutions to partial
  differential equations*, Nonlinear Anal. **23** (1994), 899–909.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace Filter Topology
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

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- With no drift and no mass, the energy form of jet fields `U`, `V` is
`∫ ⟨a(x) U₂(x), V₂(x)⟩`, read through the matrix bilinear form. -/
private theorem energyFormIntegral_zero_zero_eq_integral {Omega : Set (EuclideanSpace ℝ ι)}
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (U V : EuclideanSpace ℝ ι → ℝ × EuclideanSpace ℝ ι) :
    energyFormIntegral (mu.restrict Omega) a 0 0 U V =
      ∫ x in Omega, matrixBilinearForm (a x) (V x).2 (U x).2 ∂mu := by
  rw [energyFormIntegral_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [energyIntegrand_apply, driftForm_apply, massForm_apply]

/-- For a fixed `v ∈ W^{1,q}(Ω)`, the energy form `w ↦ a(w, v)` with no drift and no mass is
continuous on `W^{1,p}(Ω)` for Hölder conjugate `p` and `q`. -/
private theorem tendsto_energyFormIntegral_jetField
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (v : W1p mu Omega q)
    {W : ℕ → W1p mu Omega p} {w : W1p mu Omega p} (hW : Tendsto W atTop (𝓝 w)) :
    Tendsto (fun n => energyFormIntegral (mu.restrict Omega) a 0 0 (jetField (W n)) (jetField v))
      atTop (𝓝 (energyFormIntegral (mu.restrict Omega) a 0 0 (jetField w) (jetField v))) := by
  -- The field `x ↦ ⟨a(x) ·, ∇v(x)⟩` of linear functionals lies in `L^q(Ω)`.
  set G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x)
  have hG : MemLp G q (mu.restrict Omega) := by
    refine (Lp.memLp (W1p.gradient v)).of_le_mul (c := Lam)
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).prodMk
          (Lp.aestronglyMeasurable _))) ?_
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    exact ((matrixBilinearForm (a x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (h.opNorm_matrixBilinearForm_le hx) (norm_nonneg _))
  -- Integration against it is a continuous linear functional of the gradient.
  set L := (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ)).lpPairing
    (mu.restrict Omega) q p (hG.toLp G)
  have hL : ∀ u : W1p mu Omega p, L (W1p.gradientL u) =
      energyFormIntegral (mu.restrict Omega) a 0 0 (jetField u) (jetField v) := fun u => by
    rw [energyFormIntegral_zero_zero_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with x hx
    simp only [ContinuousLinearMap.id_apply, hx, W1p.gradientL_apply, jetField_apply, G]
  simp_rw [← hL]
  exact ((L.continuous.comp (W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).continuous).tendsto
    w).comp hW

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- If `Gₙ → F` in `Lᵖ(Ω)` at the rate `1 / (n + 1)`, then `∫ ⟪Gₙ, g⟫ → ∫ ⟪F, g⟫` for every
`g ∈ L^q(Ω)`, `q` the conjugate exponent. -/
private theorem tendsto_integral_inner_of_eLpNorm_sub_lt {Omega : Set (EuclideanSpace ℝ ι)}
    {p q : ℝ≥0∞} [p.HolderConjugate q]
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {G : ℕ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F p (mu.restrict Omega))
    (hG : ∀ n, MemLp (G n) p (mu.restrict Omega)) (hg : MemLp g q (mu.restrict Omega))
    (hGF : ∀ n : ℕ, eLpNorm (F - G n) p (mu.restrict Omega) < ((n : ℝ≥0∞) + 1)⁻¹) :
    Tendsto (fun n => ∫ x in Omega, ⟪G n x, g x⟫_ℝ ∂mu) atTop
      (𝓝 (∫ x in Omega, ⟪F x, g x⟫_ℝ ∂mu)) := by
  set c := (eLpNorm g q (mu.restrict Omega)).toReal
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const c))
  rw [← integral_sub ((hG n).integrable_inner_of_holderConjugate hg)
    (hF.integrable_inner_of_holderConjugate hg)]
  have hsub : ∀ x, ⟪G n x, g x⟫_ℝ - ⟪F x, g x⟫_ℝ = ⟪(G n - F) x, g x⟫_ℝ := fun x => by
    rw [Pi.sub_apply, inner_sub_left]
  simp_rw [hsub]
  have hle := enorm_integral_inner_le (𝕜 := ℝ) (μ := mu.restrict Omega) (p := p) (q := q)
    (u := G n - F) (v := g)
  rw [eLpNorm_sub_comm] at hle
  calc ‖∫ x in Omega, ⟪(G n - F) x, g x⟫_ℝ ∂mu‖
      ≤ (eLpNorm (F - G n) p (mu.restrict Omega) * eLpNorm g q (mu.restrict Omega)).toReal := by
        rw [← toReal_eNorm]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top
          ((hF.sub (hG n)).eLpNorm_ne_top) hg.eLpNorm_ne_top) hle
    _ ≤ ((n : ℝ) + 1)⁻¹ * c := by
        rw [ENNReal.toReal_mul]
        gcongr
        refine (ENNReal.toReal_mono (by simp) (hGF n).le).trans_eq ?_
        rw [ENNReal.toReal_inv]
        norm_cast

/-- The difference of two weak solutions in `H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢGⁱ` with data
`G₁, G₂ ∈ L²(Ω; ℝⁿ)` is the weak solution with datum `G₁ - G₂`. -/
private theorem forall_energyFormH1_sub_eq_divergence {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {G₁ G₂ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hG₁ : MemLp G₁ 2 (mu.restrict Omega))
    (hG₂ : MemLp G₂ 2 (mu.restrict Omega)) {u₁ u₂ : W1p0 mu Omega 2}
    (hu₁ : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u₁ : W1p mu Omega 2) (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪G₁ x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hu₂ : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u₂ : W1p mu Omega 2) (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪G₂ x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (v : W1p0 mu Omega 2) :
    energyFormH1 a 0 0 ((u₁ - u₂ : W1p0 mu Omega 2) : W1p mu Omega 2) (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪(G₁ - G₂) x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) := by
    simpa using memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  rw [Submodule.coe_sub, energyFormH1_sub_left (b := 0) (c := 0) hcoeff, hu₁ v, hu₂ v,
    neg_sub_neg, ← integral_sub (hG₂.integrable_inner_of_holderConjugate (Lp.memLp _))
      (hG₁.integrable_inner_of_holderConjugate (Lp.memLp _)), ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, inner_sub_left, neg_sub]

omit [DecidableEq ι] in
/-- A weak solution in `H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢGⁱ`, read in `W^{1,p}_0(Ω)` for `p ≤ 2`,
satisfies the equation against every `v ∈ W^{1,q}_0(Ω)` with `q ≥ 2`. -/
private theorem energyFormIntegral_jetField_ofExponentLEL_eq_divergence
    {Omega : Opens (EuclideanSpace ℝ ι)} [IsFiniteMeasure (mu.restrict (Omega : Set _))]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp2 : p ≤ 2) (h2q : 2 ≤ q)
    {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪G x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (v : W1p0 mu Omega q) :
    energyFormIntegral (mu.restrict Omega) a 0 0
        (jetField (W1p.ofExponentLEL hp2 (u : W1p mu Omega 2))) (jetField (v : W1p mu Omega q)) =
      -∫ x in Omega, ⟪G x, W1p.gradient (v : W1p mu Omega q) x⟫_ℝ ∂mu := by
  have huv := hu ⟨_, W1p.ofExponentLE_mem_w1p0Submodule h2q v.property⟩
  have hjv : jetField (W1p.ofExponentLE h2q (v : W1p mu Omega q)) =
      jetField (v : W1p mu Omega q) := funext fun x => by
    simp only [jetField_apply, W1p.coeFn_value_ofExponentLE, W1p.coeFn_gradient_ofExponentLE]
  have hju : jetField (W1p.ofExponentLEL hp2 (u : W1p mu Omega 2)) =
      jetField (u : W1p mu Omega 2) := funext fun x => by
    simp only [jetField_apply, W1p.ofExponentLEL_apply, W1p.coeFn_value_ofExponentLE,
      W1p.coeFn_gradient_ofExponentLE]
  rw [energyFormH1_def, ← energyFormIntegral_def, W1p.coeFn_gradient_ofExponentLE] at huv
  rw [hju, ← hjv]
  exact huv

omit [Fintype ι] [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- A sequence in a normed group with `‖fₙ - fₘ‖ ≤ D (1 / (n + 1) + 1 / (m + 1))`, `D < ∞`, is a
Cauchy sequence. -/
private theorem cauchySeq_of_enorm_sub_le {V : Type*} [SeminormedAddCommGroup V] {f : ℕ → V}
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (h : ∀ n m : ℕ, ‖f n - f m‖ₑ ≤ D * (((n : ℝ≥0∞) + 1)⁻¹ + ((m : ℝ≥0∞) + 1)⁻¹)) :
    CauchySeq f := by
  have hinv0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => D.toReal * (((N : ℝ) + 1)⁻¹ + ((N : ℝ) + 1)⁻¹))
    (fun n m N hn hm => ?_) (by simpa using (hinv0.add hinv0).const_mul D.toReal)
  rw [dist_eq_norm, ← toReal_eNorm]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hD (by simp)) (h n m)).trans ?_
  have hinv : ∀ k : ℕ, (((k : ℝ≥0∞) + 1)⁻¹).toReal = ((k : ℝ) + 1)⁻¹ := fun k => by
    rw [ENNReal.toReal_inv]
    norm_cast
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), hinv, hinv]
  gcongr

omit [DecidableEq ι] in
/-- If `wₙ → w` in `W^{1,p}(Ω)` and `‖∇wₙ‖_{Lᵖ} ≤ D (e + 1 / (n + 1))` with `D, e < ∞`, then
`‖∇w‖_{Lᵖ} ≤ D e`. -/
private theorem eLpNorm_gradient_le_of_tendsto {Omega : Opens (EuclideanSpace ℝ ι)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {W : ℕ → W1p mu Omega p} {w : W1p mu Omega p}
    (hW : Tendsto W atTop (𝓝 w)) {D e : ℝ≥0∞} (hD : D ≠ ∞) (he : e ≠ ∞)
    (h : ∀ n : ℕ, eLpNorm (W1p.gradient (W n)) p (mu.restrict Omega) ≤
      D * (e + ((n : ℝ≥0∞) + 1)⁻¹)) :
    eLpNorm (W1p.gradient w) p (mu.restrict Omega) ≤ D * e := by
  have hinv0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hgrad : Tendsto (fun n => ‖W1p.gradient (W n)‖) atTop (𝓝 ‖W1p.gradient w‖) := by
    simpa only [Function.comp_def, W1p.gradientL_apply] using
      (((W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).continuous.tendsto w).comp hW).norm
  have hle : ∀ n : ℕ, ‖W1p.gradient (W n)‖ ≤ D.toReal * (e.toReal + ((n : ℝ) + 1)⁻¹) := fun n => by
    rw [Lp.norm_def]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hD (ENNReal.add_ne_top.2 ⟨he, by simp⟩))
      (h n)).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_add he (by simp), ENNReal.toReal_inv]
    norm_cast
  have hlim := le_of_tendsto_of_tendsto' hgrad ((tendsto_const_nhds.add hinv0).const_mul D.toReal)
    hle
  rw [add_zero] at hlim
  rw [← Lp.eNorm_def, ← ofReal_norm, ← ENNReal.ofReal_toReal hD, ← ENNReal.ofReal_toReal he,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hlim

/-- **Extension of an `Lᵖ` estimate from square integrable data.** Let `p ≤ 2 ≤ q` be conjugate
exponents and let `Ω` have finite measure. If every weak solution in `H¹₀(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢGⁱ` with `G ∈ L²(Ω; ℝⁿ)` satisfies `‖∇u‖_{Lᵖ} ≤ D ‖G‖_{Lᵖ}`, then for every
`F ∈ Lᵖ(Ω; ℝⁿ)` there is `u ∈ W^{1,p}_0(Ω)` with `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ W^{1,q}_0(Ω)` and `‖∇u‖_{Lᵖ} ≤ D ‖F‖_{Lᵖ}`: the limit of the solutions for simple data
`Gₙ → F`. -/
private theorem exists_forall_energyFormIntegral_eq_divergence_of_eLpNorm_gradient_le
    [Nonempty ι] {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp2 : p ≤ 2) (h2q : 2 ≤ q)
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hfin : mu Omega ≠ ∞) {D : ℝ≥0∞}
    (hD : D ≠ ∞)
    (hest : ∀ {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2},
      MemLp G 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪G x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      eLpNorm (W1p.gradient (u : W1p mu Omega 2)) p (mu.restrict Omega) ≤
        D * eLpNorm G p (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F p (mu.restrict Omega)) :
    ∃ u : W1p0 mu Omega p,
      (∀ v : W1p0 mu Omega q, energyFormIntegral (mu.restrict Omega) a 0 0
          (jetField (u : W1p mu Omega p)) (jetField (v : W1p mu Omega q)) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega q) x⟫_ℝ ∂mu) ∧
      eLpNorm (W1p.gradient (u : W1p mu Omega p)) p (mu.restrict Omega) ≤
        D * eLpNorm F p (mu.restrict Omega) := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  have hp_top : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp2
  -- Approximate `F` in `Lᵖ(Ω)` by simple, hence square integrable, data `Gₙ`, solve the Dirichlet
  -- problem for them in `H¹₀(Ω)`, and read the solutions `Wₙ` in `W^{1,p}_0(Ω)`.
  choose G hGF hGp using fun n : ℕ => hF.exists_simpleFunc_eLpNorm_sub_lt hp_top
    (ε := ((n : ℝ≥0∞) + 1)⁻¹) (by simp)
  have hG2 : ∀ n, MemLp (G n) 2 (mu.restrict Omega) := fun n =>
    (G n).memLp_of_isFiniteMeasure 2 _
  choose U hU using fun n => h.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top ha hfin
    (hG2 n)
  set W : ℕ → W1p mu Omega p := fun n => W1p.ofExponentLEL hp2 (U n : W1p mu Omega 2)
  have hWgrad : ∀ u : W1p mu Omega 2, eLpNorm (W1p.gradient (W1p.ofExponentLEL hp2 u)) p
      (mu.restrict Omega) = eLpNorm (W1p.gradient u) p (mu.restrict Omega) := fun u => by
    rw [W1p.ofExponentLEL_apply, W1p.coeFn_gradient_ofExponentLE]
  -- The gradients of the `Wₙ` are Cauchy in `Lᵖ(Ω)`, so the `Wₙ` converge in `W^{1,p}_0(Ω)`.
  have hcau : CauchySeq fun n => W1p.gradient (W n) := by
    refine cauchySeq_of_enorm_sub_le hD fun n m => ?_
    have hGnm : eLpNorm (⇑(G n) - ⇑(G m)) p (mu.restrict Omega) ≤
        ((n : ℝ≥0∞) + 1)⁻¹ + ((m : ℝ≥0∞) + 1)⁻¹ := by
      rw [← sub_sub_sub_cancel_left _ _ F, add_comm]
      exact (eLpNorm_sub_le Fact.out).trans (add_le_add (hGF m).le (hGF n).le)
    rw [← W1p.gradient_sub, ← map_sub, ← Submodule.coe_sub, Lp.eNorm_def, hWgrad]
    exact (hest ((hG2 n).sub (hG2 m)) (forall_energyFormH1_sub_eq_divergence h ha (hG2 n) (hG2 m)
      (hU n) (hU m))).trans (by gcongr)
  obtain ⟨w, hwmem, hw⟩ := W1p.exists_mem_w1p0Submodule_tendsto_of_cauchySeq_gradient hp_top hfin
    (fun n => by simpa only [W, W1p.ofExponentLEL_apply] using
      W1p.ofExponentLE_mem_w1p0Submodule hp2 (U n).property) hcau
  refine ⟨⟨w, hwmem⟩, fun v => ?_, ?_⟩
  · -- The equation holds for each `Wₙ` with datum `Gₙ`; pass to the limit on both sides.
    refine tendsto_nhds_unique ?_ ((tendsto_integral_inner_of_eLpNorm_sub_lt hF hGp
      (Lp.memLp _) hGF).neg)
    simpa only [W, energyFormIntegral_jetField_ofExponentLEL_eq_divergence hp2 h2q (hU _) v] using
      tendsto_energyFormIntegral_jetField h ha (v : W1p mu Omega q) hw
  · -- Pass the bound `‖∇Wₙ‖ ≤ D ‖Gₙ‖ ≤ D (‖F‖ + 1 / (n + 1))` to the limit.
    refine eLpNorm_gradient_le_of_tendsto hw hD hF.eLpNorm_ne_top fun n => ?_
    rw [hWgrad]
    refine (hest (hG2 n) (hU n)).trans (mul_le_mul_right ?_ D)
    rw [← sub_sub_cancel F (G n)]
    exact (eLpNorm_sub_le Fact.out).trans (add_le_add le_rfl (hGF n).le)

/-- **Meyers' `W^{1,p}` solutions of the Dirichlet problem below `2`.** Let `K` bound the
ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both
depending only on the dimension, `K` and `θ`, with the following property for the exponent
`p = (2+ε)/(1+ε)` and its conjugate `q = 2 + ε`. Let `Ω ⊆ ℝⁿ` be open of finite measure, and suppose
that its complement has density at least `θ` at its points up to a scale `r₀ > 0`:
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, and let `F ∈ Lᵖ(Ω; ℝⁿ)`, which need not be square
integrable. Then the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, `u = 0` on `∂Ω` has a solution
`u ∈ W^{1,p}_0(Ω)`, in the sense that `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ W^{1,q}_0(Ω)`, with

`‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`,

where `B_{r₀}` is a ball of radius `r₀`. -/
theorem exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_le_conjExponent [Nonempty ι]
    (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], p = ENNReal.ofReal (2 + ε).conjExponent →
      q = ENNReal.ofReal (2 + ε) →
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F p (mu.restrict Omega) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ → mu Omega ≠ ∞ →
      ∃ u : W1p0 mu Omega p,
        (∀ v : W1p0 mu Omega q, energyFormIntegral (mu.restrict Omega) a 0 0
            (jetField (u : W1p mu Omega p)) (jetField (v : W1p mu Omega q)) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega q) x⟫_ℝ ∂mu) ∧
        eLpNorm (W1p.gradient (u : W1p mu Omega p)) p (mu.restrict Omega) ≤
          (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ *
            eLpNorm F p (mu.restrict Omega) / ENNReal.ofReal lam := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_eLpNorm_gradient_conjExponent_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {p q} _ _ hp hq {Omega a lam Lam F r₀} h hK ha hF hdens hr₀ hfin => ?_⟩
  subst hp hq
  have := ENNReal.holderConjugate_iff.2
    (Real.HolderConjugate.conjExponent (by linarith : 1 < 2 + ε)).symm.inv_add_inv_ennreal
  have hp2 : ENNReal.ofReal (2 + ε).conjExponent ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat 2]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.conjExponent, div_le_iff₀ (by linarith)]
    linarith
  have h2q : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 + ε) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- The constant of Meyers' estimate below `2` is finite.
  have hD : (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ /
      ENNReal.ofReal lam ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.div_ne_top hfin
          (measure_ball_pos mu 0 hr₀).ne')⟩))) (ENNReal.ofReal_pos.2 h.pos).ne'
  obtain ⟨u, hu, hle⟩ := exists_forall_energyFormIntegral_eq_divergence_of_eLpNorm_gradient_le
    hp2 h2q h ha hfin hD
    (fun _ hu => (hC h hK ha hu hdens hr₀ hfin).trans_eq (ENNReal.mul_div_right_comm ..)) hF
  exact ⟨u, hu, hle.trans_eq (ENNReal.mul_div_right_comm ..).symm⟩

end PDE

end TauCeti
