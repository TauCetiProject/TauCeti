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
import TauCeti.Data.ENNReal.Holder
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
  of finite measure, every weak solution `u ∈ W^{1,p}_0(Ω)` satisfies

  `‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`

  (`TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`). Here `u` solves the
  equation in the sense `∫_Ω ⟪∇v, a ∇u⟫ = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)` with
  `∇v ∈ L^{2+ε}(Ω)`, a class of test functions containing `C_c^∞(Ω)`; the `H¹₀(Ω)` solutions of
  the problem with `F ∈ L²(Ω)` are among these solutions. The right-hand side only involves
  `‖F‖_{Lᵖ}`, a weaker norm than `‖F‖_{L²}`, so this is not a regularity statement but the a priori
  estimate of the `W^{1,p}` theory of the Dirichlet problem for `p < 2`.
* **Existence below `2`, and uniqueness in this solution class.** For the same exponents and
  every `F ∈ Lᵖ(Ω; ℝⁿ)` the problem has exactly one weak solution `u ∈ W^{1,p}_0(Ω)` in the sense
  above (`TauCeti.PDE.exists_existsUnique_forall_setIntegral_matrixBilinearForm_eq_divergence`).
  Approximating `F` in `Lᵖ(Ω)` by simple functions, which lie in `L²(Ω)`, the `H¹₀(Ω)` solutions
  form a Cauchy sequence in `W^{1,p}_0(Ω)` by the estimate below `2` and the Poincaré inequality,
  and their limit solves the problem; uniqueness is the estimate applied to the difference of two
  solutions. As the test functions include `C_c^∞(Ω)`, the solution is also a weak solution in the
  usual sense. Uniqueness among all solutions tested only against `C_c^∞(Ω)` is not proved here:
  it would need every `v ∈ H¹₀(Ω)` with `∇v ∈ L^{2+ε}(Ω)` to lie in `W^{1,2+ε}_0(Ω)`. For exponents
  far below `2` uniqueness fails in general, by Serrin's pathological solutions, so the range near
  `2` is essential.
* **Solutions with the estimate.** For every `0 < ε ≤ ε₀` of the estimate below `2` and every
  `F ∈ Lᵖ(Ω; ℝⁿ)`, which need not be square integrable, the problem has a solution
  `u ∈ W^{1,p}_0(Ω)` with `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ W^{1,q}_0(Ω)`, `q = 2 + ε`,
  obeying the same bound:
  `TauCeti.PDE.exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_gradient_conjExponent_le`.

The local estimate up to the boundary
(`TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence`) bounds the
`(2+ε)`-mean of the gradient of the zero extension of `u` on every ball `B(y, r₀/2)` by its
`L²` mean and the `(2+ε)`-mean of `F` on `B(y, r₀)`. Integrating over all centres `y`
(`TauCeti.lintegral_rpow_le_of_forall_setLAverage_rpow_le`) turns it into a global bound that
still involves the `L²` norm of the gradient. The energy estimate `λ ‖∇u‖₂ ≤ ‖F‖₂`, from testing
the equation with `u`, removes it from the right-hand side.

The estimate below `2` follows by duality. For a bounded field `g` vanishing off a set of finite
measure, let `v ∈ H¹₀(Ω)` solve the adjoint problem `-∂ⱼ(aⁱʲ ∂ᵢv) = ∂ᵢgⁱ`, whose coefficient `aᵀ`
has the same ellipticity constants. By the estimate above `2`, `∇v ∈ L^{2+ε}(Ω)`, so `v` is an
admissible test function for `u`, and the equation of `v` extends by density from `C_c^∞(Ω)` to
test functions in `W^{1,p}_0(Ω)`. Testing the two equations with each other gives
`∫ ⟪∇u, g⟫ = ∫ ⟪F, ∇v⟫`, which Hölder's inequality and the estimate above `2` for `v` bound by
`‖F‖_p ‖∇v‖_{2+ε} ≤ C' ‖F‖_p ‖g‖_{2+ε} / λ`. Such fields `g` norm `Lᵖ`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`).

The solutions with the estimate are obtained by density. Simple fields `Gₖ → F` in `Lᵖ(Ω)` are
square integrable, since `Ω` has finite measure, and their solutions
`uₖ ∈ H¹₀(Ω) ⊆ W^{1,p}_0(Ω)` satisfy `‖∇(uₖ - uₗ)‖_p ≤ C' ‖Gₖ - Gₗ‖_p` by the estimate
below `2`. By the Poincaré inequality on
`W^{1,p}_0(Ω)` (`TauCeti.W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top`) they
converge in `W^{1,p}_0(Ω)` (`TauCeti.W1p.exists_mem_w1p0Submodule_tendsto_of_cauchySeq_gradient`),
and the equation passes to the limit since `aᵀ ∇v ∈ L^q` for `v ∈ W^{1,q}_0(Ω)`.
This density argument holds for any such estimate on square integrable data and is
`TauCeti.PDE.exists_forall_energyFormIntegral_eq_divergence_of_eLpNorm_gradient_le`.

## Main declarations

* `TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`: the global estimate above
  `2`.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_divergence`: its norm form, with the measure of `Ω` in
  place of the `L²` norm of `F`.
* `TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`: the global estimate below
  `2`, for weak solutions in `W^{1,p}_0(Ω)`.
* `TauCeti.PDE.exists_existsUnique_forall_setIntegral_matrixBilinearForm_eq_divergence`: existence
  of a weak solution in `W^{1,p}_0(Ω)` below `2`, unique among the solutions tested against every
  `v ∈ H¹₀(Ω)` with `∇v ∈ L^{2+ε}(Ω)`.
* `TauCeti.PDE.exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_gradient_conjExponent_le`:
  solutions in `W^{1,p}_0(Ω)` for data in `Lᵖ(Ω)` below `2`, with the estimate.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorem 1.
* T. Kilpeläinen, P. Koskela, *Global integrability of the gradients of solutions to partial
  differential equations*, Nonlinear Anal. **23** (1994), 899–909.
* J. Serrin, *Pathological solutions of elliptic differential equations*, Ann. Scuola Norm. Sup.
  Pisa **18** (1964), 385–387.
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

/-! ### Weak solutions in `W^{1,p}_0(Ω)` below the exponent `2` -/

section BelowTwo

/-- `u ∈ W^{1,p}_0(Ω)` is a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` tested against every
`v ∈ H¹₀(Ω)` with `∇v ∈ L^q(Ω)`: `∫_Ω ⟪∇v, a ∇u⟫ = -∫_Ω ⟪F, ∇v⟫`. -/
private def IsWeakSolution {p : ℝ≥0∞} [Fact (1 ≤ p)] {Omega : Opens (EuclideanSpace ℝ ι)}
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (q : ℝ≥0∞) (u : W1p0 mu Omega p) : Prop :=
  ∀ v : W1p0 mu Omega 2, MemLp (W1p.gradient (v : W1p mu Omega 2)) q (mu.restrict Omega) →
    ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x)
      (W1p.gradient (u : W1p mu Omega p) x) ∂mu =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu

/-- The field `x ↦ (a x)ᵀ (ξ x)`, defined through the Riesz isomorphism by
`⟪flux a ξ x, η⟫ = ⟪ξ x, a x η⟫`: its pairing with a gradient is the integrand of the weak form. -/
private noncomputable def flux (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (ξ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (matrixBilinearForm (a x) (ξ x))

omit [DecidableEq ι] in
private theorem inner_flux (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (ξ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x η : EuclideanSpace ℝ ι) :
    ⟪flux a ξ x, η⟫_ℝ = matrixBilinearForm (a x) (ξ x) η :=
  InnerProductSpace.toDual_symm_apply

omit [mu.IsAddHaarMeasure] in
/-- For a uniformly elliptic `a`, the flux of an `Lʳ` field is an `Lʳ` field. -/
private theorem memLp_flux {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {ξ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {r : ℝ≥0∞}
    (hξ : MemLp ξ r (mu.restrict Omega)) : MemLp (flux a ξ) r (mu.restrict Omega) := by
  have hcont : Continuous fun z : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) ×
      EuclideanSpace ℝ ι => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (z.1 z.2) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (continuous_fst.clm_apply continuous_snd)
  refine hξ.of_le_mul (c := Lam) (hcont.comp_aestronglyMeasurable
    ((continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).prodMk
      hξ.aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [flux, LinearIsometryEquiv.norm_map]
  exact (matrixBilinearForm (a x)).le_of_opNorm_le (h.opNorm_matrixBilinearForm_le hx) (ξ x)

omit [DecidableEq ι] in
/-- Pairing the flux of `ξ` with the gradient is integrating the weak-form integrand. -/
private theorem innerLpCLM_flux_comp_gradientL_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [q.HolderConjugate p] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {ξ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hG : MemLp (flux a ξ) q (mu.restrict Omega)) (w : W1p mu Omega p) :
    ((hG.innerLpCLM ℝ).comp W1p.gradientL) w =
      ∫ x in Omega, matrixBilinearForm (a x) (ξ x) (W1p.gradient w x) ∂mu := by
  simp only [ContinuousLinearMap.comp_apply, MemLp.innerLpCLM_apply, W1p.gradientL_apply,
    inner_flux]

/-- **Testing with a `W^{1,p}_0` function.** Let `v ∈ H¹₀(Ω)` solve the adjoint problem
`-∂ⱼ(aⁱʲ ∂ᵢv) = ∂ᵢgⁱ` with `g ∈ L^q(Ω)`, and suppose `∇v ∈ L^q(Ω)`. Then its equation also holds
against every `u ∈ W^{1,p}_0(Ω)`, `p` the conjugate exponent of `q`: both sides are continuous on
`W^{1,p}(Ω)` and agree on the test functions. -/
private theorem setIntegral_matrixBilinearForm_eq_of_forall_energyFormH1_eq
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate q] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hg : MemLp g q (mu.restrict Omega))
    {v : W1p0 mu Omega 2} (hvq : MemLp (W1p.gradient (v : W1p mu Omega 2)) q (mu.restrict Omega))
    (hv : ∀ w : W1p0 mu Omega 2, energyFormH1 (fun x => (a x)ᵀ) 0 0 (v : W1p mu Omega 2)
      (w : W1p mu Omega 2) = -∫ x in Omega, ⟪g x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (u : W1p0 mu Omega p) :
    ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x)
        (W1p.gradient (u : W1p mu Omega p) x) ∂mu =
      -∫ x in Omega, ⟪g x, W1p.gradient (u : W1p mu Omega p) x⟫_ℝ ∂mu := by
  have hG := memLp_flux h ha hvq
  let Φ := (hG.innerLpCLM ℝ (q' := p)).comp W1p.gradientL
  let Ψ := -((hg.innerLpCLM ℝ (q' := p)).comp W1p.gradientL)
  have hΨ (w : W1p mu Omega p) :
      Ψ w = -∫ x in Omega, ⟪g x, W1p.gradient w x⟫_ℝ ∂mu := by
    simp only [Ψ, neg_apply, ContinuousLinearMap.comp_apply,
      MemLp.innerLpCLM_apply, W1p.gradientL_apply]
  have hsub := w1p0Submodule_subset_of_isClosed (s := {w | Φ w = Ψ w})
    (isClosed_eq Φ.continuous Ψ.continuous) fun φ => by
      -- On a test function, this is the equation of `v` tested with `φ ∈ H¹₀(Ω)`.
      have hφ := hv ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (p := 2) φ⟩
      rw [energyFormH1_zero_zero_eq_setIntegral] at hφ
      simp only [W1p.gradient_ofTestFunctionₗ, matrixBilinearForm_transpose_apply] at hφ
      simp only [Set.mem_ofPred_eq, Φ, innerLpCLM_flux_comp_gradientL_apply, hΨ,
        W1p.gradient_ofTestFunctionₗ]
      have h2 := gradientTestFunctionLp_apply_ae (mu := mu) 2 φ
      have hp := gradientTestFunctionLp_apply_ae (mu := mu) p φ
      have e (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ) :
          ∫ x in Omega, f x (gradientTestFunctionLp (mu := mu) p φ x) ∂mu =
            ∫ x in Omega, f x (gradientTestFunctionLp (mu := mu) 2 φ x) ∂mu :=
        integral_congr_ae ((h2.and hp).mono fun x hx => by simp only [hx.1, hx.2])
      refine (e fun x ξ => matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x) ξ).trans
        (hφ.trans ?_)
      exact congrArg Neg.neg (e fun x ξ => ⟪g x, ξ⟫_ℝ).symm
  have hu := hsub u.property
  rwa [Set.mem_ofPred_eq, innerLpCLM_flux_comp_gradientL_apply, hΨ] at hu

/-- The weak formulation in `W^{1,p}_0(Ω)` is linear: if `u₁` and `u₂` solve it with data
`F₁, F₂ ∈ Lᵖ(Ω)`, then `u₁ - u₂` solves it with datum `F₁ - F₂`. -/
private theorem forall_setIntegral_matrixBilinearForm_sub {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [p.HolderConjugate q] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {F₁ F₂ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF₁ : MemLp F₁ p (mu.restrict Omega))
    (hF₂ : MemLp F₂ p (mu.restrict Omega)) {u₁ u₂ : W1p0 mu Omega p}
    (hu₁ : IsWeakSolution a F₁ q u₁) (hu₂ : IsWeakSolution a F₂ q u₂) :
    IsWeakSolution a (F₁ - F₂) q (u₁ - u₂) := by
  intro v hvq
  have hG := memLp_flux h ha hvq
  have hlin := ((hG.innerLpCLM ℝ (q' := p)).comp W1p.gradientL).map_sub (u₁ : W1p mu Omega p) u₂
  rw [← Submodule.coe_sub] at hlin
  simp only [innerLpCLM_flux_comp_gradientL_apply] at hlin
  simp only [Pi.sub_apply, inner_sub_left]
  rw [hlin, hu₁ v hvq, hu₂ v hvq, integral_sub (hF₁.integrable_inner_of_holderConjugate hvq)
    (hF₂.integrable_inner_of_holderConjugate hvq)]
  ring

omit [DecidableEq ι] in
/-- The constant of Meyers' estimates is finite on a set of finite measure. -/
private theorem coe_mul_one_add_div_rpow_ne_top (C : ℝ≥0) {Omega : Opens (EuclideanSpace ℝ ι)}
    (hfin : mu Omega ≠ ∞) {r₀ ε : ℝ} (hr₀ : 0 < r₀) (hε : 0 ≤ ε) :
    (C : ℝ≥0∞) * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2)) ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.div_ne_top hfin (measure_ball_pos mu 0 hr₀).ne')⟩)

/-- For `g ∈ L²(Ω)` and `p ≤ 2`, the `H¹₀(Ω)` solution of the Dirichlet problem with datum `g`
is a weak solution in `W^{1,p}_0(Ω)`: it solves the equation against all of `H¹₀(Ω)`, so against
the test functions `v` with `∇v ∈ L^q(Ω)` for every `q`. -/
private theorem exists_forall_setIntegral_matrixBilinearForm_eq_of_memLp_two [Nonempty ι]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p ≤ 2) {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hfin : mu Omega ≠ ∞)
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hg : MemLp g 2 (mu.restrict Omega)) :
    ∃ u : W1p0 mu Omega p, ∀ q, IsWeakSolution a g q u := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  obtain ⟨w, hw⟩ := h.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top ha hfin hg
  refine ⟨W1p0.ofExponentLEL hp2 w, fun _ v _ => ?_⟩
  rw [W1p0.coe_ofExponentLEL, W1p.coeFn_gradient_ofExponentLE, ← hw v,
    energyFormH1_zero_zero_eq_setIntegral]

/-- Uniqueness of weak solutions in `W^{1,p}_0(Ω)` from a stability bound
`‖w‖_{W^{1,p}} ≤ M ‖F'‖_{Lᵖ}` for the solutions `w` with data `F'`. -/
private theorem eq_of_forall_setIntegral_matrixBilinearForm_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [p.HolderConjugate q] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {M : ℝ≥0∞}
    (hstab : ∀ (F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (w : W1p0 mu Omega p),
      IsWeakSolution a F' q w → ‖(w : W1p mu Omega p)‖ₑ ≤ M * eLpNorm F' p (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F p (mu.restrict Omega))
    {u₁ u₂ : W1p0 mu Omega p} (hu₁ : IsWeakSolution a F q u₁) (hu₂ : IsWeakSolution a F q u₂) :
    u₁ = u₂ := by
  have hd := hstab (F - F) (u₁ - u₂) (forall_setIntegral_matrixBilinearForm_sub h ha hF hF hu₁ hu₂)
  rw [sub_self, eLpNorm_zero, mul_zero] at hd
  have h0 : ((u₁ - u₂ : W1p0 mu Omega p) : W1p mu Omega p) = 0 := W1p.ext
    (by rw [W1p.value_zero]; exact eNorm_eq_zero.1 (nonpos_iff_eq_zero.1
      ((W1p.enorm_value_le _).trans hd)))
    (by rw [W1p.gradient_zero]; exact eNorm_eq_zero.1 (nonpos_iff_eq_zero.1
      ((W1p.enorm_gradient_le _).trans hd)))
  rwa [Submodule.coe_eq_zero, sub_eq_zero] at h0

open Filter Topology in
/-- **Passing to the limit in the weak formulation.** If `uₙ → u` in `W^{1,p}_0(Ω)`, `gₙ → F` in
`Lᵖ(Ω)`, and each `uₙ` is a weak solution with datum `gₙ`, then `u` is a weak solution with
datum `F`: both sides of the equation are continuous in the solution and in the datum. -/
private theorem forall_setIntegral_matrixBilinearForm_eq_of_tendsto {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [p.HolderConjugate q] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {g : ℕ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hgp : ∀ n, MemLp (g n) p (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F p (mu.restrict Omega))
    (hgF : Tendsto (fun n => eLpNorm (F - g n) p (mu.restrict Omega)) atTop (𝓝 0))
    {u : ℕ → W1p0 mu Omega p} {u₀ : W1p0 mu Omega p} (hu₀ : Tendsto u atTop (𝓝 u₀))
    (hu : ∀ n, IsWeakSolution a (g n) q (u n)) : IsWeakSolution a F q u₀ := by
  intro v hvq
  -- The left side is continuous in the solution.
  have hG := memLp_flux h ha hvq
  let Φ := ((hG.innerLpCLM ℝ (q' := p)).comp W1p.gradientL).comp
    (w1p0Submodule mu Omega p).toSubmodule.subtypeL
  have hΦ (w : W1p0 mu Omega p) : Φ w = ∫ x in Omega, matrixBilinearForm (a x)
      (W1p.gradient (v : W1p mu Omega 2) x) (W1p.gradient (w : W1p mu Omega p) x) ∂mu := by
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      innerLpCLM_flux_comp_gradientL_apply]
  -- The right side is continuous in the datum, as the pairing with `∇v ∈ L^q`.
  have hconv : Tendsto (fun n => (hgp n).toLp (g n)) atTop (𝓝 (hF.toLp F)) := by
    refine tendsto_iff_edist_tendsto_0.2 ?_
    simpa only [Lp.edist_toLp_toLp, eLpNorm_sub_comm] using hgF
  have hpair (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hf : MemLp f p (mu.restrict Omega)) :
      hvq.innerLpCLM ℝ (hf.toLp f) =
        ∫ x in Omega, ⟪f x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
    rw [MemLp.innerLpCLM_apply]
    refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
    dsimp only
    rw [hx, real_inner_comm]
  have hlim := (((hvq.innerLpCLM ℝ (q' := p)).continuous.tendsto _).comp hconv).neg
  simp only [Function.comp_def, hpair] at hlim
  rw [← hΦ]
  refine tendsto_nhds_unique ((Φ.continuous.tendsto u₀).comp hu₀) ?_
  simpa only [Function.comp_def, hΦ, hu _ v hvq] using hlim

open Filter Topology in
/-- Existence of weak solutions in `W^{1,p}_0(Ω)`, `p ≤ 2`, from a stability bound
`‖w‖_{W^{1,p}} ≤ M ‖F'‖_{Lᵖ}`. Approximate `F` in `Lᵖ(Ω)` by simple functions `gₙ`, which lie in
`L²(Ω)`; their `H¹₀(Ω)` solutions form a Cauchy sequence in `W^{1,p}_0(Ω)` by the stability bound,
and the equation passes to the limit. -/
private theorem exists_forall_setIntegral_matrixBilinearForm_eq_of_stability [Nonempty ι]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : p ≠ ∞) (hp2 : p ≤ 2)
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hfin : mu Omega ≠ ∞) {M : ℝ≥0∞}
    (hM : M ≠ ∞)
    (hstab : ∀ (F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (w : W1p0 mu Omega p),
      IsWeakSolution a F' q w → ‖(w : W1p mu Omega p)‖ₑ ≤ M * eLpNorm F' p (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F p (mu.restrict Omega)) :
    ∃ u : W1p0 mu Omega p, IsWeakSolution a F q u := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  choose g hgF hgp using fun n : ℕ =>
    hF.exists_simpleFunc_eLpNorm_sub_lt hp (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose u hu using fun n : ℕ => exists_forall_setIntegral_matrixBilinearForm_eq_of_memLp_two
    hp2 h ha hfin ((g n).memLp_of_isFiniteMeasure 2 _)
  have hgF' (n N : ℕ) (hn : N ≤ n) :
      eLpNorm (F - ⇑(g n)) p (mu.restrict Omega) ≤ (N : ℝ≥0∞)⁻¹ :=
    (hgF n).le.trans (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hn))
  -- The solutions `uₙ` form a Cauchy sequence.
  have hcauchy : CauchySeq u := by
    refine EMetric.cauchySeq_iff_le_tendsto_0.2 ⟨fun N => M * ((N : ℝ≥0∞)⁻¹ + (N : ℝ≥0∞)⁻¹),
      fun n m N hn hm => ?_, ?_⟩
    · have hd := hstab _ (u n - u m) (forall_setIntegral_matrixBilinearForm_sub h ha (hgp n)
        (hgp m) (hu n q) (hu m q))
      rw [eDist_eq_eNorm_sub]
      refine hd.trans ?_
      dsimp only
      gcongr
      have hsub : ⇑(g n) - ⇑(g m) = (F - ⇑(g m)) - (F - ⇑(g n)) := by abel
      rw [hsub]
      refine (eLpNorm_sub_le Fact.out).trans ?_
      rw [add_comm]
      exact add_le_add (hgF' n N hn) (hgF' m N hm)
    · simpa using ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_inv_nat_nhds_zero.add ENNReal.tendsto_inv_nat_nhds_zero) (Or.inr hM)
  obtain ⟨u₀, hu₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨u₀, forall_setIntegral_matrixBilinearForm_eq_of_tendsto h ha hgp hF
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) fun n => (hgF n).le) hu₀
    fun n => hu n q⟩

end BelowTwo

/-- **Meyers' global estimate below `2`.** Let `K` bound the ellipticity ratio and let `θ > 0`.
There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both depending only on the dimension,
`K` and `θ`, with the following property for the exponent `p = (2+ε)/(1+ε)`, the conjugate of
`2 + ε`. Let `Ω ⊆ ℝⁿ` be open of finite measure, and suppose that its complement has density at
least `θ` at its points up to a scale `r₀ > 0`: `θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and
`0 < r ≤ r₀`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, and let `u ∈ W^{1,p}_0(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, `u = 0` on `∂Ω`: `∫_Ω ⟪∇v, a ∇u⟫ = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)` with `∇v ∈ L^{2+ε}(Ω)`. Then

`‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`,

where `B_{r₀}` is a ball of radius `r₀`. The exponents `p` fill `[(2+ε₀)/(1+ε₀), 2)`. The test
functions include `C_c^∞(Ω)`, and every `u ∈ H¹₀(Ω)` solving the equation against all of `H¹₀(Ω)`
is such a solution (`TauCeti.W1p0.ofExponentLEL`). -/
theorem exists_eLpNorm_gradient_conjExponent_le_divergence [Nonempty ι] (K : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate (ENNReal.ofReal (2 + ε))]
        {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega p}
        {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        MemLp (W1p.gradient (v : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) →
        ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x)
          (W1p.gradient (u : W1p mu Omega p) x) ∂mu =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ → mu Omega ≠ ∞ →
      eLpNorm (W1p.gradient (u : W1p mu Omega p)) p (mu.restrict Omega) ≤
        (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ *
          eLpNorm F p (mu.restrict Omega) / ENNReal.ofReal lam := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_eLpNorm_gradient_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {p _ _ Omega a lam Lam F u r₀} h hK ha hu hdens hr₀ hfin => ?_⟩
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  have hha : AEStronglyMeasurable (fun x => (a x)ᵀ) (mu.restrict Omega) :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable ha
  set D := (C : ℝ≥0∞) * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))
  have hD : D ≠ ∞ := coe_mul_one_add_div_rpow_ne_top C hfin hr₀ hε.le
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 + ε) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Norm `∇u` in `Lᵖ` against bounded test fields `g`, which lie in `L²(Ω)` and `L^{2+ε}(Ω)`.
  refine (Lp.aestronglyMeasurable _).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ)
    (q' := ENNReal.ofReal (2 + ε)) ((ENNReal.HolderConjugate.ne_top_iff_ne_one p _).2
      (ENNReal.one_lt_two.trans_le h2).ne') fun g s _ _ hg => ?_
  have hg2 : MemLp g 2 (mu.restrict Omega) := hg.mono_exponent le_top
  have hgq : MemLp g (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) := hg.mono_exponent le_top
  -- Test the equation of `u` with the solution `v` of the adjoint problem with datum `g`, whose
  -- gradient lies in `L^{2+ε}` by the estimate above `2`.
  obtain ⟨v, hv⟩ :=
    h.transpose.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top hha hfin hg2
  have hvq : eLpNorm (W1p.gradient (v : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε))
      (mu.restrict Omega) ≤
        D ^ (2 + ε)⁻¹ * (eLpNorm g (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) /
          ENNReal.ofReal lam) := by
    simpa only [mul_div_assoc] using hC h.transpose hK hha hg2 hv hdens hr₀
  have hvQ : MemLp (W1p.gradient (v : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε))
      (mu.restrict Omega) :=
    hvq.trans_lt (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hD)
      (ENNReal.div_lt_top hgq.eLpNorm_ne_top (ENNReal.ofReal_pos.2 h.pos).ne'))
  have hid : ∫ x in Omega, ⟪W1p.gradient (u : W1p mu Omega p) x, g x⟫_ℝ ∂mu =
      ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
    have hvu := setIntegral_matrixBilinearForm_eq_of_forall_energyFormH1_eq h ha hgq hvQ hv u
    rw [hu v hvQ, neg_inj] at hvu
    simp_rw [real_inner_comm (g _) (W1p.gradient (u : W1p mu Omega p) _)]
    exact hvu.symm
  -- Hölder's inequality and the estimate above `2` for `v`.
  rw [hid]
  refine (enorm_integral_inner_le (p := p) (q := ENNReal.ofReal (2 + ε))).trans
    ((mul_le_mul_of_nonneg_left hvq zero_le).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

/-- **Existence, and uniqueness in a solution class, for the Dirichlet problem in `W^{1,p}_0`
below the exponent `2`.** Let `K` bound
the ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, depending only on the dimension, `K`
and `θ`, with the following property for every `0 < ε ≤ ε₀` and the conjugate exponent
`p = (2+ε)/(1+ε)` of `2 + ε`. Let `Ω ⊆ ℝⁿ` be open of finite measure, and suppose that its
complement has density at least `θ` at its points up to a scale `r₀ > 0`, as for Lipschitz
domains. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`. Then for every `F ∈ Lᵖ(Ω; ℝⁿ)` the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, `u = 0` on `∂Ω`

has exactly one solution `u ∈ W^{1,p}_0(Ω)` in the following sense: `∫_Ω ⟪∇v, a ∇u⟫ = -∫_Ω ⟪F, ∇v⟫`
for every `v ∈ H¹₀(Ω)` with `∇v ∈ L^{2+ε}(Ω)`. These test functions include `C_c^∞(Ω)`, so `u` is
also a weak solution in the usual sense, tested against `C_c^∞(Ω)`. Uniqueness is proved only
within the solution class above, which is built to contain the adjoint solutions of the duality
argument. Uniqueness among all solutions tested only against `C_c^∞(Ω)` would also need every
`v ∈ H¹₀(Ω)` with `∇v ∈ L^{2+ε}(Ω)` to lie in `W^{1,2+ε}_0(Ω)`, which is not proved here.

When `ε` is also below the threshold of
`TauCeti.PDE.exists_eLpNorm_gradient_conjExponent_le_divergence`, the gradient of `u` obeys that
theorem's bound.

For `F ∈ L²(Ω)` the `H¹₀(Ω)` solution, included by `TauCeti.W1p0.ofExponentLEL`, is a weak solution
in this sense, hence it is the solution. For `F` only in `Lᵖ(Ω)` there is in general no solution
in `H¹₀(Ω)`. Uniqueness is a property of exponents near `2`: far below `2` it fails in general, by
Serrin's pathological solutions. -/
theorem exists_existsUnique_forall_setIntegral_matrixBilinearForm_eq_divergence [Nonempty ι]
    (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate (ENNReal.ofReal (2 + ε))]
        {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F p (mu.restrict Omega) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ → mu Omega ≠ ∞ →
      ∃! u : W1p0 mu Omega p, ∀ v : W1p0 mu Omega 2,
        MemLp (W1p.gradient (v : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) →
        ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x)
          (W1p.gradient (u : W1p mu Omega p) x) ∂mu =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_eLpNorm_gradient_conjExponent_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  intro p _ _ Omega a lam Lam F r₀ h hK ha hF hdens hr₀ hfin
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 + ε) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp : p ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p _).2
    (ENNReal.one_lt_two.trans_le h2).ne'
  have hp2 : p ≤ 2 := ENNReal.HolderConjugate.le_two h2
  obtain ⟨P, hPw⟩ :=
    W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top (mu := mu) hp hfin
  -- Meyers' estimate and the Poincaré inequality bound every solution by its datum.
  set D := (C : ℝ≥0∞) * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))
  have hMtop : (P : ℝ≥0∞) * (D ^ (2 + ε)⁻¹ / ENNReal.ofReal lam) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) (coe_mul_one_add_div_rpow_ne_top C hfin hr₀ hε.le))
      (ENNReal.ofReal_pos.2 h.pos).ne')
  have hstab (F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (w : W1p0 mu Omega p)
      (hw : IsWeakSolution a F' (ENNReal.ofReal (2 + ε)) w) :
      ‖(w : W1p mu Omega p)‖ₑ ≤
        P * (D ^ (2 + ε)⁻¹ / ENNReal.ofReal lam) * eLpNorm F' p (mu.restrict Omega) := by
    refine (hPw w w.property).trans ?_
    rw [Lp.eNorm_def, mul_assoc]
    gcongr
    refine (hC h hK ha hw hdens hr₀ hfin).trans_eq ?_
    simp only [D, div_eq_mul_inv]
    ring
  obtain ⟨u, hu⟩ :=
    exists_forall_setIntegral_matrixBilinearForm_eq_of_stability hp hp2 h ha hfin hMtop hstab hF
  exact ⟨u, hu, fun w hw => eq_of_forall_setIntegral_matrixBilinearForm_eq h ha hstab hF hw hu⟩

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
theorem exists_forall_energyFormIntegral_eq_divergence_and_eLpNorm_gradient_conjExponent_le
    [Nonempty ι] (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
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
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hfin
  have := ENNReal.holderConjugate_iff.2
    (Real.HolderConjugate.conjExponent (by linarith : 1 < 2 + ε)).symm.inv_add_inv_ennreal
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 + ε) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp2 : ENNReal.ofReal (2 + ε).conjExponent ≤ 2 := ENNReal.HolderConjugate.le_two h2
  have hD : (C * (1 + (mu Omega / mu (ball 0 r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ /
      ENNReal.ofReal lam ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (coe_mul_one_add_div_rpow_ne_top C hfin hr₀ hε.le)) (ENNReal.ofReal_pos.2 h.pos).ne'
  -- An `H¹₀(Ω)` solution, read in `W^{1,p}_0(Ω)`, obeys Meyers' estimate below `2`.
  obtain ⟨u, hu, hle⟩ := exists_forall_energyFormIntegral_eq_divergence_of_eLpNorm_gradient_le
    (q := ENNReal.ofReal (2 + ε)) hp2 h ha hfin hD (fun {G w} _ hw => by
      have hest := hC (u := W1p0.ofExponentLEL hp2 w) h hK ha (fun v _ => by
        rw [W1p0.coe_ofExponentLEL, W1p.coeFn_gradient_ofExponentLE, ← hw v,
          energyFormH1_zero_zero_eq_setIntegral]) hdens hr₀ hfin
      rw [W1p0.coe_ofExponentLEL, W1p.coeFn_gradient_ofExponentLE] at hest
      exact hest.trans_eq (ENNReal.mul_div_right_comm ..)) hF
  exact ⟨u, hu, hle.trans_eq (ENNReal.mul_div_right_comm ..).symm⟩

end PDE

end TauCeti
