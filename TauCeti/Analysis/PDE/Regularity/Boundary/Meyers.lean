/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HigherIntegrability
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

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
* **Below `2`.** For `0 < ε ≤ ε₀` and the conjugate exponent `p = (2+ε)/(1+ε) < 2`, on a bounded
  open set,

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

/-- The energy estimate for the Dirichlet problem with a divergence datum,
`∫_Ω ‖∇u‖² ≤ ∫_Ω (‖F‖/λ)²`, from testing the equation with the solution itself. -/
private theorem lintegral_enorm_gradient_sq_le {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hF : MemLp F 2 (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) :
    ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ) ∂mu := by
  set g := W1p.gradient (u : W1p mu Omega 2)
  have hlam := h.pos
  have hE := h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (b := 0) (c := 0)
    (gamma := 0) ha aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp)
    (fun _ _ => le_rfl) (u : W1p mu Omega 2)
  rw [hu u] at hE
  have hpair : ∫ x in Omega, ⟪F x, g x⟫_ℝ ∂mu = ⟪hF.toLp F, g⟫_ℝ := by
    rw [L2.inner_def]
    exact integral_congr_ae (hF.coeFn_toLp.mono fun x hx => by simp only [hx])
  -- `λ ‖∇u‖₂² ≤ -∫ ⟪F, ∇u⟫ ≤ ‖F‖₂ ‖∇u‖₂`.
  have hle : lam * ‖g‖ ≤ ‖hF.toLp F‖ := by
    rcases (norm_nonneg g).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · refine le_of_mul_le_mul_right ?_ hpos
      calc lam * ‖g‖ * ‖g‖ = lam * ‖g‖ ^ 2 := by ring
        _ ≤ -⟪hF.toLp F, g⟫_ℝ := by rw [← hpair]; exact hE
        _ ≤ ‖hF.toLp F‖ * ‖g‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hsq : ∀ {f : EuclideanSpace ℝ ι → ℝ≥0∞}, AEMeasurable f (mu.restrict Omega) →
      ∫⁻ x in Omega, f x ^ (2 : ℝ) ∂mu = eLpNorm f 2 (mu.restrict Omega) ^ (2 : ℝ) :=
    fun hf => by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hf.aestronglyMeasurable, ← ENNReal.rpow_mul]
      simp
  have hmeasF := hF.aestronglyMeasurable.eNorm.div_const (ENNReal.ofReal lam)
  rw [hsq (Lp.aestronglyMeasurable g).eNorm, hsq hmeasF]
  gcongr
  -- Both `L²` norms are those of `g` and of `F / λ`.
  rw [eLpNorm_eNorm _ (Lp.aestronglyMeasurable g), ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g),
    ← Lp.norm_def]
  calc ENNReal.ofReal ‖g‖ ≤ ENNReal.ofReal (‖hF.toLp F‖ / lam) :=
        ENNReal.ofReal_le_ofReal ((le_div_iff₀ hlam).2 (by linarith))
    _ = eLpNorm (fun x => ‖F x‖ₑ / ENNReal.ofReal lam) 2 (mu.restrict Omega) := by
        rw [ENNReal.ofReal_div_of_pos hlam, Lp.norm_toLp,
          ENNReal.ofReal_toReal hF.eLpNorm_ne_top, div_eq_mul_inv]
        simp_rw [div_eq_mul_inv, mul_comm _ (ENNReal.ofReal lam)⁻¹]
        rw [eLpNorm_const_mul_ennreal_of_pos (by norm_num), eLpNorm_eNorm _ hF.aestronglyMeasurable]

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
      ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ r ∂mu := fun r hr => by
    rw [← lintegral_indicator hOm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) <;>
      simp [g, hx, ENNReal.zero_rpow_of_pos hr]
  have hkΩ : ∀ r : ℝ, 0 < r → ∫⁻ x, k x ^ r ∂mu =
      ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ r ∂mu := fun r hr => by
    rw [← lintegral_indicator hOm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) <;>
      simp [k, hx, ENNReal.zero_rpow_of_pos hr]
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
  have hE := lintegral_enorm_gradient_sq_le h ha hF hu
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
  have hlam := h.pos
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
  have hroot : ∀ {f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι},
      AEStronglyMeasurable f (mu.restrict Omega) → ∀ c : ℝ, 0 < c →
        (∫⁻ x in Omega, (‖f x‖ₑ / ENNReal.ofReal c) ^ (2 + ε) ∂mu) ^ (2 + ε)⁻¹ =
          eLpNorm f (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) / ENNReal.ofReal c :=
    fun {f} hf c hc => by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hf,
        ENNReal.toReal_ofReal hq.le, one_div]
      simp_rw [ENNReal.div_rpow_of_nonneg _ _ hq.le, div_eq_mul_inv]
      rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 hc) ENNReal.ofReal_ne_top).ne'),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.inv_rpow, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]
  rw [← div_one (eLpNorm _ _ _), ← ENNReal.ofReal_one, ← hroot (Lp.aestronglyMeasurable _) 1
    one_pos, mul_div_assoc, ← hroot hF.aestronglyMeasurable lam hlam,
    ← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le)]
  simp_rw [ENNReal.ofReal_one, div_one]
  exact ENNReal.rpow_le_rpow hint (inv_nonneg.2 hq.le)

section Dual

variable {n : ℕ}

/-- The adjoint problem `-∂ⱼ(aⁱʲ ∂ᵢv) = ∂ᵢHⁱ`, `v = 0` on `∂Ω`, has a weak solution
`v ∈ H¹₀(Ω)` on a bounded open set, for every `H ∈ L²(Ω; ℝⁿ)`. -/
private theorem exists_forall_energyFormH1_transpose_eq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hH : MemLp H 2 (volume.restrict Omega)) :
    ∃ v : W1p0 volume Omega 2, ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => (a x)ᵀ) 0 0 (v : W1p volume Omega 2) (w : W1p volume Omega 2) =
        -∫ x in Omega, ⟪H x, W1p.gradient (w : W1p volume Omega 2) x⟫_ℝ := by
  obtain ⟨R, -, hball⟩ := hb.subset_ball_lt 0 0
  obtain ⟨v, ⟨hv0, hv⟩, -⟩ :=
    h.transpose.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) (beta := 0) (gamma := 0)
      (continuous_id.matrix_transpose.comp_aestronglyMeasurable ha) aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl)
      hball (by simpa using h.pos) (divergenceForcing (hH.toLp H)) 0
  refine ⟨⟨v, by simpa using hv0⟩, fun w => ?_⟩
  rw [Subtype.coe_mk, hv w, divergenceForcing_apply_eq_neg_setIntegral]
  exact congrArg Neg.neg (integral_congr_ae (hH.coeFn_toLp.mono fun x hx => by simp only [hx]))

/-- **Meyers' global estimate below `2`.** Let `K` bound the ellipticity ratio and let `θ > 0`.
There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both depending only on the dimension,
`K` and `θ`, with the following property for the exponent `p = (2+ε)/(1+ε)`, the conjugate of
`2 + ε`. Let `Ω ⊆ ℝⁿ` be bounded and open, and suppose that its complement has density at least
`θ` at its points up to a scale `r₀ > 0`: `θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and
`0 < r ≤ r₀`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, and let `u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`.
Then

`‖∇u‖_{Lᵖ(Ω)} ≤ (C (1 + (|Ω| / |B_{r₀}|)^(ε/2)))^(1/(2+ε)) ‖F‖_{Lᵖ(Ω)} / λ`,

where `B_{r₀}` is a ball of radius `r₀`. The exponents `p` fill `[(2+ε₀)/(1+ε₀), 2)`. -/
theorem exists_eLpNorm_gradient_conjExponent_le_divergence (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {u : W1p0 volume Omega 2} {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam →
      Lam ≤ K * lam → AEStronglyMeasurable a (volume.restrict Omega) →
      (∀ v : W1p0 volume Omega 2,
        energyFormH1 a 0 0 (u : W1p volume Omega 2) (v : W1p volume Omega 2) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫_ℝ) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∀ r, 0 < r → r ≤ r₀ →
        θ * volume.real (ball z r) ≤
          volume.real (ball z r \ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) →
      0 < r₀ → Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
      eLpNorm (W1p.gradient (u : W1p volume Omega 2)) (ENNReal.ofReal (2 + ε).conjExponent)
          (volume.restrict Omega) ≤
        (C * (1 + (volume (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) /
            volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) r₀)) ^ (ε / 2))) ^ (2 + ε)⁻¹ *
          eLpNorm F (ENNReal.ofReal (2 + ε).conjExponent) (volume.restrict Omega) /
            ENNReal.ofReal lam := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_eLpNorm_gradient_le_divergence
    (mu := volume) (ι := Fin (n + 1)) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u r₀} h hK ha hu hdens hr₀ hb => ?_⟩
  have hpq := (Real.HolderConjugate.conjExponent (by linarith : 1 < 2 + ε)).symm
  have := ENNReal.holderConjugate_iff.2 hpq.inv_add_inv_ennreal
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  set D := (C : ℝ≥0∞) * (1 + (volume (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) /
    volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) r₀)) ^ (ε / 2))
  -- Norm `∇u` in `Lᵖ` against bounded test fields `g`, which lie in `L²(Ω)`.
  refine (Lp.aestronglyMeasurable _).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ)
    (q' := ENNReal.ofReal (2 + ε)) ENNReal.ofReal_ne_top fun g s _ _ hg => ?_
  have hg2 : MemLp g 2 (volume.restrict Omega) := hg.mono_exponent le_top
  -- Test the equation of `u` with the solution `v` of the adjoint problem with datum `g`.
  obtain ⟨v, hv⟩ := exists_forall_energyFormH1_transpose_eq h ha hb hg2
  have hid : ∫ x in Omega, ⟪W1p.gradient (u : W1p volume Omega 2) x, g x⟫_ℝ =
      ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫_ℝ := by
    have htr : energyFormH1 (fun x => (a x)ᵀ) 0 0 (v : W1p volume Omega 2)
        (u : W1p volume Omega 2) = energyFormH1 a 0 0 (u : W1p volume Omega 2) v := by
      rw [energyFormH1_def, energyFormH1_def]
      exact integral_congr_ae (ae_of_all _ fun x =>
        energyIntegrand_zero_drift_transpose_apply (a x) 0 _ _)
    simp_rw [real_inner_comm (g _) (W1p.gradient (u : W1p volume Omega 2) _)]
    rw [← neg_neg (∫ x in Omega, ⟪g x, _⟫_ℝ), ← hv u, htr, hu v, neg_neg]
  -- Hölder's inequality and the estimate above `2` for `v`.
  have hvq : eLpNorm (W1p.gradient (v : W1p volume Omega 2)) (ENNReal.ofReal (2 + ε))
      (volume.restrict Omega) ≤
        D ^ (2 + ε)⁻¹ * (eLpNorm g (ENNReal.ofReal (2 + ε)) (volume.restrict Omega) /
          ENNReal.ofReal lam) := by
    simpa only [mul_div_assoc] using hC h.transpose hK
      (continuous_id.matrix_transpose.comp_aestronglyMeasurable ha) hg2 hv hdens hr₀
  rw [hid]
  refine (enorm_integral_inner_le (p := ENNReal.ofReal (2 + ε).conjExponent)
    (q := ENNReal.ofReal (2 + ε))).trans ((mul_le_mul_of_nonneg_left hvq zero_le).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

end Dual

end PDE

end TauCeti
