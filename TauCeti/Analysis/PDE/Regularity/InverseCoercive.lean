/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.InverseCoercive
public import TauCeti.Analysis.PDE.Regularity.Harnack
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.PDE.Regularity.HigherIntegrability
import TauCeti.MeasureTheory.Measure.Restrict.Chain

/-!
# De Giorgi–Nash–Moser and Meyers under inverse-coercive ellipticity

Let `a` be a measurable coefficient field on an open set of `ℝⁿ` which is uniformly elliptic in
the almost-everywhere inverse-coercive sense (`TauCeti.PDE.IsUniformlyEllipticAE`): for almost
every `x` and every `ξ`, `ξ · a(x)ξ ≥ λ‖ξ‖²` and `ξ · a(x)⁻¹ξ ≥ Λ⁻¹‖ξ‖²`, with no symmetry. This
is the ellipticity hypothesis of the divergence-form theory. This file proves the interior
regularity theorems under it, in every dimension: the De Giorgi–Nash–Moser estimates for weak
solutions, subsolutions and supersolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, quantitative in a local norm
of `u`, Meyers' estimate for weak solutions of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, quantitative in an
average of `‖∇u‖²` and a datum term in `‖F‖ / λ`, and De Giorgi's estimates for weak solutions
of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`. The constants depend only on an upper bound for the ellipticity
ratio `Λ / λ`, the dimension and the normalization of the Haar measure, and in addition on the
exponent `s` for the weak Harnack inequality, on `ε` for Meyers' estimate and on the exponents of
the data for the equation with a right-hand side.

* **Local boundedness (De Giorgi).** A weak subsolution satisfies, above every level `k`,
  `u ≤ k + D R^(-n/2) ‖(u - k)⁺‖_{L²(B(x₀, R))}` on `B(x₀, R/2)`
  (`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_isUniformlyEllipticAE`),
  and a weak solution satisfies `|u| ≤ D R^(-n/2) ‖u‖_{L²(B(x₀, R))}` there
  (`TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral_of_isUniformlyEllipticAE`).
* **De Giorgi's theorem.** A weak solution `u ∈ H¹(B(x₀, 2r))` has a precise representative
  which is `α`-Hölder on `B(x₀, r)` with constant `C r^(-α) r^(-n/2) ‖u‖_{L²(B(x₀, 2r))}`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isUniformlyEllipticAE`).
* **Moser's weak Harnack inequality.** A nonnegative weak supersolution satisfies
  `(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`, for every `s > 0` with
  `(n - 2) s < n`
  (`TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_isUniformlyEllipticAE`).
* **Moser's Harnack inequality.** A nonnegative weak solution `u ∈ H¹(B(x₀, 4r))` satisfies
  `u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`
  (`TauCeti.PDE.exists_ae_ae_value_le_mul_value_of_isUniformlyEllipticAE`).
* **Meyers' higher integrability.** A weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` satisfies
  `⨍_{B(x₀, R/2)} ‖∇u‖^(2+ε) ≤ C ((⨍_{B(x₀, R)} ‖∇u‖²)^((2+ε)/2) + ⨍_{B(x₀, R)} (‖F‖/λ)^(2+ε))`
  for small `ε > 0`
  (`TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence_of_isUniformlyEllipticAE`),
  so `∇u ∈ L^{2+ε}_loc` when `F ∈ L^{2+ε}_loc`
  (`TauCeti.PDE.exists_memLp_gradient_ball_divergence_of_isUniformlyEllipticAE`).

For the equation with a right-hand side, `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with `f ∈ Lʳ`, `r > 1`,
`r > n/2`, and `F ∈ L^q`, `q > 2`, `q > n`, the file also proves local boundedness and De
Giorgi's Hölder estimate on every set whose closed `R`-thickening lies in `Ω`, with constants
depending only on `Λ / λ`, `n`, `r`, `q` and the normalization of the Haar measure, and with the
data entering through `‖f‖_{Lʳ} / λ` and `‖F‖_{L^q} / λ` with their Morrey gains `2 - n/r` and
`1 - n/q`. These are, in the namespace `TauCeti.PDE`,
`exists_ae_abs_value_le_mul_add_of_memLp_add_divergence_of_isUniformlyEllipticAE` and
`exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence_of_isUniformlyEllipticAE`.
Either datum may be zero.

All of them reduce to the theorems for the pointwise operator-bound predicate
(`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`,
`TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`,
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`,
`TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value`,
`TauCeti.PDE.exists_ae_ae_value_le_mul_value` and
`TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence`, and with a right-hand side
`TauCeti.PDE.exists_ae_abs_value_le_mul_add_of_memLp_add_divergence` and
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence`). Dividing `a` by
`λ` does not change the weak solutions, subsolutions and supersolutions, and normalizes the
constants to `(1, Λ / λ)`; changing `a` on a null set gives a field satisfying the operator bound
with the same constants everywhere
(`TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq`). For Meyers'
estimate the divergence datum becomes `F / λ`, which is why `‖F‖ / λ` appears on the right;
with a right-hand side both data are divided by `λ`
(`TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq_add_divergence`).
The homogeneous Hölder estimate is applied with the thickening radius `r / 2`. The Harnack
inequality on `B(x₀, r)` is assembled from the inequality on balls of radius `ρ = r / (8 √n)`
centred in `closedBall x₀ r`: finitely many such balls cover `closedBall x₀ r`, and each is
joined to `B(x₀, ρ)` by a chain of `⌈8 √n⌉ + 2` balls centred on a segment, consecutive balls
overlapping (`TauCeti.ae_ae_le_pow_mul_of_forall_mem_closedBall`). The number of balls in a chain
depends only on the dimension, so the constant does too.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorem 2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.18, 8.20, 8.22 and 8.24.
-/

public section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- **Local boundedness of weak subsolutions (De Giorgi).** Fix a bound `ratio` for the
ellipticity ratio. In every dimension `n ≥ 1` there is `D > 0`, depending only on `ratio`, the
dimension and the normalization of the additive Haar measure `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` in the inverse-coercive sense with constants
`λ, Λ`, `Λ ≤ ratio · λ`, not necessarily symmetric, and let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Then for every
level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^(-n/2) (∫_{B(x₀, R)} ((u - k)⁺)²)^(1/2)` almost everywhere on `B(x₀, R/2)`. -/
theorem exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_isUniformlyEllipticAE
    [Nonempty ι] (ratio : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ ratio * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := 1) (Lam := ratio)
  refine ⟨D, hD, fun {lam Lam Omega a u k x₀ R} h hratio ha hu hR hball => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_nonpos hratio ha hu
  exact hbound h' ha' hu' hR hball

/-- **Local boundedness of weak solutions (De Giorgi).** Fix a bound `ratio` for the ellipticity
ratio. In every dimension `n ≥ 1` there is `D > 0`, depending only on `ratio`, the dimension and
the normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` in the inverse-coercive sense with constants `λ, Λ`,
`Λ ≤ ratio · λ`, not necessarily symmetric, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`. Then for every ball
`B(x₀, R) ⊆ Ω`,

`|u| ≤ D R^(-n/2) ‖u‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`. -/
theorem exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral_of_isUniformlyEllipticAE
    [Nonempty ι] (ratio : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ ratio * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := 1) (Lam := ratio)
  refine ⟨D, hD, fun {lam Lam Omega a u x₀ R} h hratio ha hu hR hball => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq_zero hratio ha hu
  exact hbound h' ha' hu' hR hball

/-- **De Giorgi's theorem on a ball.** Fix a bound `ratio` for the ellipticity ratio. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `ratio`, the dimension `n` and the normalization of
the additive Haar measure `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `B(x₀, 2r)` in the inverse-coercive sense with constants `λ, Λ`,
`Λ ≤ ratio · λ`, not necessarily symmetric, and let `u ∈ H¹(B(x₀, 2r))` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(B(x₀, 2r))`. Then the precise
representative of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) r^(-n/2) ‖u‖_{L²(B(x₀, 2r))}`.

The precise representative agrees with `u` almost everywhere
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The estimate is invariant under `u ↦ M u`, under
`a ↦ t a` for `t > 0`, and under translations and dilations of the ball. -/
theorem exists_holderOnWith_preciseRepresentative_of_isUniformlyEllipticAE (ratio : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {u : W1p mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2},
        IsUniformlyEllipticAE mu (ball x₀ (2 * r)) a lam Lam → Lam ≤ ratio * lam →
        AEStronglyMeasurable a (mu.restrict (ball x₀ (2 * r))) →
        (∀ v : W1p0 mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2,
          energyFormH1 a 0 0 u (v : W1p mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2) = 0) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (r ^ (-(Fintype.card ι : ℝ) / 2) *
            √(∫ y in ball x₀ (2 * r), W1p.value u y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu (W1p.value u)) (ball x₀ r) := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := 1) (Lam := ratio)
  refine ⟨α, C * 2 ^ ((α : ℝ) + Fintype.card ι / 2), hα, hα1, by positivity, ?_⟩
  intro lam Lam x₀ r a u h hratio ha hu
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ (2 * r), isOpen_ball⟩) hratio ha hu
  -- The closed `r / 2`-thickening of `B(x₀, r)` lies in `B(x₀, 2r)`.
  have hthick : cthickening (r / 2) (ball x₀ r) ⊆ ball x₀ (2 * r) :=
    (cthickening_subset_of_subset _ ball_subset_closedBall).trans
      ((cthickening_closedBall (by positivity) hr.le x₀).trans_subset
        (closedBall_subset_ball (by linarith)))
  have key := hhol (Omega := ⟨ball x₀ (2 * r), isOpen_ball⟩) (K := ball x₀ r) h' ha' hu'
    (half_pos hr) hthick
  -- Rescale the constant from the radius `r / 2` to the radius `r`.
  have hconst : ∀ S : ℝ, C * 2 ^ ((α : ℝ) + Fintype.card ι / 2) * r ^ (-(α : ℝ)) *
      (r ^ (-(Fintype.card ι : ℝ) / 2) * S) =
      C * (r / 2) ^ (-(α : ℝ)) * ((r / 2) ^ (-(Fintype.card ι : ℝ) / 2) * S) := fun S => by
    simp only [Real.div_rpow hr.le zero_le_two, Real.rpow_add two_pos, neg_div,
      Real.rpow_neg zero_le_two]
    field_simp
  rw [hconst]
  exact key

/-- **Moser's weak Harnack inequality.** Fix a bound `ratio` for the ellipticity ratio and an
exponent `s > 0` with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3` and `s` arbitrary
when `n ≤ 2`. In every dimension `n ≥ 1` there is `C > 0`, depending only on `ratio`, `s`, the
dimension and the normalization of the additive Haar measure `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` in the inverse-coercive sense with constants
`λ, Λ`, `Λ ≤ ratio · λ`, not necessarily symmetric, and let `u ∈ H¹(Ω)` be a nonnegative weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Then on every ball with `B(x₀, 8√n r) ⊆ Ω`, `u^s` is integrable on `B(x₀, r)` and

`(⨍_{B(x₀, r)} u^s)^(1/s) ≤ C u(x)` for almost every `x ∈ B(x₀, r)`. -/
theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_isUniformlyEllipticAE [Nonempty ι]
    (ratio : ℝ) {s : ℝ} (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ ratio * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu ∧ ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨C, hC, hweak⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value (mu := mu)
    (lam := 1) (Lam := ratio) hs hsn
  refine ⟨C, hC, fun {lam Lam Omega a u x₀ r} h hratio ha hu hu0 hball => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_nonneg hratio ha hu
  exact hweak h' ha' hu' hu0 hball

/-- **Moser's Harnack inequality on a ball.** Fix a bound `ratio` for the ellipticity ratio.
There is `C > 0`, depending only on `ratio`, the dimension `n` and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `B(x₀, 4r)` in the inverse-coercive sense with constants `λ, Λ`, `Λ ≤ ratio · λ`, not
necessarily symmetric, and let `u ∈ H¹(B(x₀, 4r))` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`
with `u ≥ 0` almost everywhere. Then

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. -/
theorem exists_ae_ae_value_le_mul_value_of_isUniformlyEllipticAE (ratio : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {u : W1p mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2},
        IsUniformlyEllipticAE mu (ball x₀ (4 * r)) a lam Lam → Lam ≤ ratio * lam →
        AEStronglyMeasurable a (mu.restrict (ball x₀ (4 * r))) →
        (∀ v : W1p0 mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2,
          energyFormH1 a 0 0 u (v : W1p mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2) = 0) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (4 * r)), 0 ≤ W1p.value u x) →
        ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
          W1p.value u y ≤ C * W1p.value u x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero the space is a single point.
    refine ⟨1, one_pos, fun {lam Lam x₀ r a u} _ _ _ _ hu0 => ?_⟩
    rcases le_or_gt r 0 with hr | hr
    · simp [ball_eq_empty.2 hr]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hu0]
      with x _
    filter_upwards with y
    rw [Subsingleton.elim y x, one_mul]
  obtain ⟨C₀, hC₀, hH⟩ := exists_ae_ae_value_le_mul_value (mu := mu) (lam := 1) (Lam := ratio)
  -- Chains of `m + 1` balls of radius `ρ = r / (8 √n)` join `x₀` to every point of
  -- `closedBall x₀ r`.
  set m : ℕ := ⌈8 * √(Fintype.card ι : ℝ)⌉₊ + 1
  refine ⟨C₀ ^ (2 * m + 2), by positivity, ?_⟩
  intro lam Lam x₀ r a u h hratio ha hu hu0
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ (4 * r), isOpen_ball⟩) hratio ha hu
  have : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hρ : 0 < r / (8 * √(Fintype.card ι : ℝ)) := by positivity
  refine ae_ae_le_pow_mul_of_forall_mem_closedBall hC₀.le hρ ?_ fun z hz => ?_
  · -- `r < m ρ` since `m > 8 √n`.
    have h8 : 8 * √(Fintype.card ι : ℝ) < m :=
      (Nat.le_ceil _).trans_lt (by simp only [m]; push_cast; linarith)
    rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
    nlinarith
  -- Moser's Harnack inequality on `B(z, ρ)`, since `B(z, 16 √n ρ) = B(z, 2r) ⊆ B(x₀, 4r)`.
  refine hH (Omega := ⟨ball x₀ (4 * r), isOpen_ball⟩) h' ha' hu' hu0 (ball_subset_ball' ?_)
  rw [mem_closedBall] at hz
  have : 16 * √(Fintype.card ι : ℝ) * (r / (8 * √(Fintype.card ι : ℝ))) = 2 * r := by
    field_simp; ring
  linarith

/-- **Meyers' higher integrability estimate.** Fix a bound `ratio` for the ellipticity ratio. In
every dimension `n ≥ 1` there is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, depending
only on `ratio`, `ε`, the dimension and the normalization of the additive Haar measure `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` in the
inverse-coercive sense with constants `λ, Λ`, `Λ ≤ ratio · λ`, not necessarily symmetric, let
`F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is
`a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. Then for every ball `B(x₀, R) ⊆ Ω`,

`⨍_{B(x₀, R/2)} ‖∇u‖^(2+ε) ≤ C ((⨍_{B(x₀, R)} ‖∇u‖²)^((2+ε)/2) + ⨍_{B(x₀, R)} (‖F‖/λ)^(2+ε))`.

The averages are extended-valued. -/
theorem exists_setLAverage_enorm_gradient_rpow_le_divergence_of_isUniformlyEllipticAE
    [Nonempty ι] (ratio : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
        {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ ratio * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍⁻ x in ball x₀ (R / 2), ‖W1p.gradient u x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((⨍⁻ x in ball x₀ R, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ⨍⁻ x in ball x₀ R, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_setLAverage_enorm_gradient_rpow_le_divergence (mu := mu) ratio
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u x₀ R} h hratio ha hF hu hball => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ :=
    h.exists_uniformlyEllipticOn_energyFormH1_eq_divergence hratio ha hu
  have key := hC h' (le_of_eq (mul_one ratio).symm) ha' (hF.const_smul lam⁻¹) hu' hball
  -- The datum `λ⁻¹ F` of the normalized equation has `‖λ⁻¹ F‖ / 1 = ‖F‖ / λ`.
  have hF' : ∀ x, ‖(lam⁻¹ • F) x‖ₑ / ENNReal.ofReal 1 = ‖F x‖ₑ / ENNReal.ofReal lam := fun x => by
    simp [eNorm_smul, Real.eNorm_eq_ofReal (inv_nonneg.2 h.pos.le),
      ENNReal.ofReal_inv_of_pos h.pos, div_eq_mul_inv, mul_comm]
  simpa only [hF'] using key

/-- **Meyers' theorem: higher integrability of the gradient.** Fix a bound `ratio` for the
ellipticity ratio. In every dimension `n ≥ 1` there is `ε₀ > 0`, depending only on `ratio` and
the dimension, such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` in the inverse-coercive sense with constants `λ, Λ`, `Λ ≤ ratio · λ`, not necessarily
symmetric, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`. If `B(x₀, R) ⊆ Ω`, `0 < ε ≤ ε₀` and `F` lies in `L^{2+ε}(B(x₀, R))`, then `∇u`
lies in `L^{2+ε}(B(x₀, R/2))`. -/
theorem exists_memLp_gradient_ball_divergence_of_isUniformlyEllipticAE [Nonempty ι]
    (ratio : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
        {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ ratio * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp F (ENNReal.ofReal (2 + ε)) (mu.restrict (ball x₀ R)) →
      MemLp (W1p.gradient u) (ENNReal.ofReal (2 + ε)) (mu.restrict (ball x₀ (R / 2))) := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_memLp_gradient_ball_divergence (mu := mu) ratio
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  intro Omega a lam Lam F u x₀ R h hratio ha hF hu hball hFp
  obtain ⟨a', h', ha', hu'⟩ :=
    h.exists_uniformlyEllipticOn_energyFormH1_eq_divergence hratio ha hu
  exact hM ε hε hεle h' (le_of_eq (mul_one ratio).symm) ha' (hF.const_smul lam⁻¹) hu' hball
    (hFp.const_smul lam⁻¹)

/-! ### A right-hand side `f + ∂ᵢFⁱ` -/

/-- **Local boundedness with a right-hand side under inverse-coercive ellipticity.** Let `n ≥ 1`
be the dimension, let `r > 1` with `r > n/2`, let `q > 2` with `q > n`, and fix a bound `ratio`
for the ellipticity ratio. There is `D > 0`, depending only on `ratio`, `n`, `r`, `q` and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic
on `Ω` in the inverse-coercive sense with constants `λ, Λ`, `Λ ≤ ratio · λ`, not necessarily
symmetric, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with
`f ∈ Lʳ(B(x₀, R))` and `F ∈ L^q(B(x₀, R); ℝⁿ)`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on
`B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + (R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} +
  R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))}) / λ)`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp_add_divergence_of_isUniformlyEllipticAE
    [Nonempty ι] {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) (ratio : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      Lam ≤ ratio * lam → AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) → MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam) := by
  obtain ⟨D, hD, hbound⟩ := exists_ae_abs_value_le_mul_add_of_memLp_add_divergence (mu := mu)
    (lam := 1) (Lam := ratio) hr hrn hq hqn
  refine ⟨D, hD, fun {lam Lam Omega a f F u x₀ R} h hratio ha hf hF hu hR hball => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ :=
    h.exists_uniformlyEllipticOn_energyFormH1_eq_add_divergence hratio ha hu
  refine (hbound h' ha' (hf.const_smul lam⁻¹) (hF.const_smul lam⁻¹) hu' hR hball).mono
    fun x hx => hx.trans_eq ?_
  -- The normalized data `λ⁻¹ f` and `λ⁻¹ F` have norms `‖f‖ / λ` and `‖F‖ / λ`.
  simp only [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_eNorm, norm_inv,
    Real.norm_of_nonneg h.pos.le]
  ring

/-- **De Giorgi's theorem with a right-hand side under inverse-coercive ellipticity.** Let
`n ≥ 1` be the dimension, let `r > 1` with `r > n/2`, let `q > 2` with `q > n`, and fix a bound
`ratio` for the ellipticity ratio. There are `α ∈ (0, 1]` and `C > 0`, depending only on `ratio`,
`n`, `r`, `q` and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `a` be measurable and uniformly elliptic on `Ω` in the inverse-coercive sense with
constants `λ, Λ`, `Λ ≤ ratio · λ`, not necessarily symmetric, let `f ∈ Lʳ(Ω)` and
`F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is
`a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. If the closed `R`-thickening of a set
`K` lies in `Ω`, then the precise representative of `u` is Hölder continuous on `K` with exponent
`α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + (R^(2 - n/r) ‖f‖_{Lʳ(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)}) / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The estimate is invariant under `a ↦ t a` together
with `(f, F) ↦ t (f, F)` for `t > 0`. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence_of_isUniformlyEllipticAE
    [Nonempty ι] {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) (ratio : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {lam Lam : ℝ}
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      Lam ≤ ratio * lam → AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
              R ^ (1 - (Fintype.card ι : ℝ) / q) *
                (eLpNorm F q (mu.restrict Omega)).toReal) / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence (mu := mu) (lam := 1)
      (Lam := ratio) hr hrn hq hqn
  refine ⟨α, C, hα, hα1, hC, fun {lam Lam Omega a f F u K R} h hratio ha hf hF hu hR hRK => ?_⟩
  obtain ⟨a', h', ha', hu'⟩ :=
    h.exists_uniformlyEllipticOn_energyFormH1_eq_add_divergence hratio ha hu
  have key := hhol h' ha' (hf.const_smul lam⁻¹) (hF.const_smul lam⁻¹) hu' hR hRK
  -- The normalized data `λ⁻¹ f` and `λ⁻¹ F` have norms `‖f‖ / λ` and `‖F‖ / λ`.
  simp only [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_eNorm, norm_inv,
    Real.norm_of_nonneg h.pos.le, div_one] at key
  exact key.mono_const (Real.toNNReal_le_toNNReal (le_of_eq (by ring)))

end TauCeti.PDE
