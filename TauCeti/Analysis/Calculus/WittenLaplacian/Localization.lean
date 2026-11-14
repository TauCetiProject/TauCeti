/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Calculus.WittenLaplacian.Basic
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.Support

/-!
# Localization of the Witten Laplacian on Euclidean space

This file proves the two estimates with which the spectrum of the Witten Laplacian
`Δ_t = d_t d_t^* + d_t^* d_t` of a function `f` on `ℝ^ι` is localized near the critical points of
`f` as `t → ∞`. Forms are written, as in `TauCeti.Analysis.Calculus.WittenLaplacian.Basic`, as
functions `φ : (ι → ℝ) → Finset ι → ℝ` giving the coefficients of `dx^s`, paired pointwise by
`⟨φ, ψ⟩ = ∑ s, φ s * ψ s`, and integrated against Lebesgue measure.

**The IMS localization formula.** By Witten's frame formula
`TauCeti.euclideanWittenLaplacian_apply`, `Δ_t` is the coefficientwise Laplacian `Δ = -∑ᵢ ∂ᵢ²`
plus an endomorphism of the fibre at each point. Only `Δ` fails to commute with multiplication by
a function `J`, so
`Δ_t (J φ) = J Δ_t φ - 2 ∑ᵢ ∂ᵢJ ∂ᵢφ + (ΔJ) φ`
(`TauCeti.euclideanWittenLaplacian_smul_apply`). If `∑ₐ Jₐ² = 1` near a point, the first-order
terms cancel after summing `Jₐ Δ_t (Jₐ φ)` over `a`, and

`∑ₐ Jₐ Δ_t (Jₐ φ) = Δ_t φ + (∑ₐ |∇Jₐ|²) φ`

(`TauCeti.sum_smul_euclideanWittenLaplacian_smul_apply`). Integrated against `φ`, this splits the
quadratic form of `Δ_t` along a partition of unity, at the cost of the bounded potential
`∑ₐ |∇Jₐ|²`, which does not depend on `t`
(`TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`).

**The lower bound away from the critical points.** The fibre endomorphism of the frame formula
is `t² |df|² + t ∑_{i,j} Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆`, and each `⁅εᵢ, ιⱼ⁆` has quadratic form bounded by
`1` (`Module.Basis.abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le`). As the
quadratic form of `Δ` is the nonnegative Dirichlet energy on compactly supported forms
(`TauCeti.integral_sum_neg_fderiv_fderiv_apply_mul_eq_integral_sum_sq`), for every compactly
supported `C²` form `φ`

`∫ (t² |df|² - |t| ∑_{i,j} |∂ᵢ∂ⱼf|) |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`

(`TauCeti.integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`), integrating the
pointwise bound
`TauCeti.sum_sum_neg_fderiv_fderiv_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul`.
Where `|df|² ≥ c` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` on the support of `φ`, the quadratic form of `Δ_t` is
therefore at least `t² c - |t| h` times `∫ |φ|²`, which grows quadratically in `t` as soon as
`c > 0` (`TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`).

In the integrated statements only `φ` has to be `C²` everywhere; `f` and the `Jₐ` need only be
`C²` at the points of the support of `φ`.

These are the two inputs of Witten's localization argument: for a partition of unity with one
function supported away from the critical points and one near each critical point, they compare
the low-lying spectrum of `Δ_t` with the harmonic-oscillator models at the critical points, which
are computed in `TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic`. That spectral comparison
itself is not carried out here.

## Main results

* `TauCeti.euclideanWittenLaplacian_smul_apply`: the Leibniz rule for `Δ_t (J φ)`.
* `TauCeti.sum_smul_euclideanWittenLaplacian_smul_apply`: the pointwise IMS localization formula.
* `TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`: the IMS localization formula for the
  quadratic form of `Δ_t`.
* `TauCeti.sum_sum_neg_fderiv_fderiv_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul`: the
  pointwise lower bound for `⟨Δ_t φ, φ⟩`.
* `TauCeti.integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul` and
  `TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`: lower bounds for the
  quadratic form of `Δ_t` by the potential `t² |df|² - |t| |Hess f|`.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 3 (the IMS localization formula) and Chapter 11
  (its application to the Witten Laplacian).
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340.
-/

public section

open Filter MeasureTheory Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### The Leibniz rule and the IMS formula -/

/-- **The Witten Laplacian of a product with a function.** For `f`, `J` and a form `φ` that are
`C²` at `x`,

`Δ_t (J φ) = J Δ_t φ - 2 ∑ᵢ ∂ᵢJ ∂ᵢφ - (∑ᵢ ∂ᵢ²J) φ`

at `x`: only the second-order part `-∑ᵢ ∂ᵢ²` of `Δ_t` fails to commute with `J`. -/
theorem euclideanWittenLaplacian_smul_apply {f J : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x) (hJ : ContDiffAt ℝ 2 J x) (hφ : ContDiffAt ℝ 2 φ x)
    (t : ℝ) :
    euclideanWittenLaplacian f t (J • φ) x =
      J x • euclideanWittenLaplacian f t φ x -
        (2 : ℝ) • ∑ i, fderiv ℝ J x (Pi.single i 1) • fderiv ℝ φ x (Pi.single i 1) -
          (∑ i, fderiv ℝ (fderiv ℝ J) x (Pi.single i 1) (Pi.single i 1)) • φ x := by
  rw [euclideanWittenLaplacian_apply hf (hJ.smul hφ), euclideanWittenLaplacian_apply hf hφ,
    Pi.smul_apply']
  -- The second-order part, one direction at a time.
  have h₁ : ∀ i : ι,
      -fderiv ℝ (fderiv ℝ (J • φ)) x (Pi.single i 1) (Pi.single i 1) +
          (t ^ 2 * fderiv ℝ f x (Pi.single i 1) ^ 2) • (J x • φ x) =
        J x • (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) +
            (t ^ 2 * fderiv ℝ f x (Pi.single i 1) ^ 2) • φ x) -
          (2 : ℝ) • (fderiv ℝ J x (Pi.single i 1) • fderiv ℝ φ x (Pi.single i 1)) -
            fderiv ℝ (fderiv ℝ J) x (Pi.single i 1) (Pi.single i 1) • φ x := fun i ↦ by
    rw [fderiv_fderiv_smul_apply hJ hφ]
    module
  -- The zeroth-order part commutes with `J`.
  have h₂ : t • ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
        ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
          (J x • φ x) =
      J x • t • ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
        ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
          (φ x) := by
    simp only [map_smul, Finset.smul_sum, smul_comm (J x)]
  rw [Finset.sum_congr rfl fun i _ ↦ h₁ i, h₂, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul, smul_add]
  abel

/-- **The IMS localization formula.** Let `(Jₐ)_{a ∈ A}` be functions that are `C²` at `x` with
`∑ₐ Jₐ² = 1` near `x`. Then for `f` and a form `φ` that are `C²` at `x`,

`∑ₐ Jₐ Δ_t (Jₐ φ) = Δ_t φ + (∑ₐ |∇Jₐ|²) φ`

at `x`. The localization error `∑ₐ |∇Jₐ|²` does not depend on `t`. -/
theorem sum_smul_euclideanWittenLaplacian_smul_apply {α : Type*} {A : Finset α}
    {J : α → (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hJ : ∀ a ∈ A, ContDiffAt ℝ 2 (J a) x) (hφ : ContDiffAt ℝ 2 φ x)
    (hJA : (fun y ↦ ∑ a ∈ A, J a y ^ 2) =ᶠ[𝓝 x] fun _ ↦ 1) (t : ℝ) :
    ∑ a ∈ A, J a x • euclideanWittenLaplacian f t (J a • φ) x =
      euclideanWittenLaplacian f t φ x +
        (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) • φ x := by
  have h₀ : ∑ a ∈ A, J a x ^ 2 = 1 := hJA.eq_of_nhds
  have h₁ := fun i : ι ↦ sum_mul_fderiv_apply_eq_zero_of_sum_sq_eventuallyEq_const
    (fun a ha ↦ (hJ a ha).differentiableAt (by norm_num)) hJA (Pi.single i 1)
  have h₂ := fun i : ι ↦
    sum_mul_fderiv_fderiv_apply_add_fderiv_apply_mul_eq_zero_of_sum_sq_eventuallyEq_const hJ hJA
      (Pi.single i 1) (Pi.single i 1)
  -- Each summand, written with scalar coefficients in front of `Δ_t φ`, `∂ᵢφ` and `φ`.
  have hterm : ∀ a ∈ A, J a x • euclideanWittenLaplacian f t (J a • φ) x =
      J a x ^ 2 • euclideanWittenLaplacian f t φ x +
        ∑ i, (-2 * (J a x * fderiv ℝ (J a) x (Pi.single i 1))) • fderiv ℝ φ x (Pi.single i 1) +
          (-∑ i, J a x * fderiv ℝ (fderiv ℝ (J a)) x (Pi.single i 1) (Pi.single i 1)) • φ x := by
    intro a ha
    have hS : ∑ i, (-2 * (J a x * fderiv ℝ (J a) x (Pi.single i 1))) •
        fderiv ℝ φ x (Pi.single i 1) = (-2 * J a x) •
          ∑ i, fderiv ℝ (J a) x (Pi.single i 1) • fderiv ℝ φ x (Pi.single i 1) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by module
    rw [euclideanWittenLaplacian_smul_apply hf (hJ a ha) hφ, hS, ← Finset.mul_sum]
    module
  -- The three groups of terms, summed over `a`.
  have hA : ∑ a ∈ A, J a x ^ 2 • euclideanWittenLaplacian f t φ x =
      euclideanWittenLaplacian f t φ x := by
    rw [← Finset.sum_smul, h₀, one_smul]
  have hB : ∑ a ∈ A, ∑ i, (-2 * (J a x * fderiv ℝ (J a) x (Pi.single i 1))) •
      fderiv ℝ φ x (Pi.single i 1) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [← Finset.sum_smul, ← Finset.mul_sum, h₁, mul_zero,
      zero_smul]
  have hC : ∑ a ∈ A, (-∑ i, J a x * fderiv ℝ (fderiv ℝ (J a)) x (Pi.single i 1) (Pi.single i 1)) •
      φ x = (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) • φ x := by
    -- The scalar identity `∑ₐ -∑ᵢ Jₐ ∂ᵢ²Jₐ = ∑ₐ ∑ᵢ (∂ᵢJₐ)²`, summed from `h₂` over `i`.
    have h : ∑ a ∈ A, -∑ i, J a x * fderiv ℝ (fderiv ℝ (J a)) x (Pi.single i 1) (Pi.single i 1) =
        ∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2 := by
      have h₂' : ∑ i, ∑ a ∈ A,
          (J a x * fderiv ℝ (fderiv ℝ (J a)) x (Pi.single i 1) (Pi.single i 1) +
            fderiv ℝ (J a) x (Pi.single i 1) * fderiv ℝ (J a) x (Pi.single i 1)) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ h₂ i
      rw [Finset.sum_comm] at h₂'
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, sq] at h₂' ⊢
      linarith
    rw [← Finset.sum_smul, h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC,
    add_zero]

/-! ### The IMS formula for the quadratic form -/

/-- **The IMS localization formula for the quadratic form of the Witten Laplacian.** Let `φ` be a
compactly supported `C²` form, and let `f` and a finite family of functions `(Jₐ)_{a ∈ A}` be `C²`
at every point of the support of `φ`, with `∑ₐ Jₐ² = 1` wherever `φ` does not vanish. Then

`∫ ⟨Δ_t φ, φ⟩ = ∑ₐ ∫ ⟨Δ_t (Jₐ φ), Jₐ φ⟩ - ∫ (∑ₐ |∇Jₐ|²) |φ|²`. -/
theorem integral_sum_euclideanWittenLaplacian_mul_eq {α : Type*} {A : Finset α}
    {J : α → (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hJ : ∀ a ∈ A, ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 (J a) x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJA : ∀ x, φ x ≠ 0 → ∑ a ∈ A, J a x ^ 2 = 1) (t : ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ a ∈ A, (∫ x, ∑ s, euclideanWittenLaplacian f t (J a • φ) x s * (J a • φ) x s) -
        ∫ x, (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
  -- The IMS formula, paired with `φ` at each point.
  have hpt : ∀ x, ∑ a ∈ A, ∑ s, euclideanWittenLaplacian f t (J a • φ) x s * (J a • φ) x s =
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s +
        (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    have hxs : x ∈ tsupport φ := subset_tsupport φ hx
    have hJA' : (fun y ↦ ∑ a ∈ A, J a y ^ 2) =ᶠ[𝓝 x] fun _ ↦ 1 :=
      (hφ.continuous.continuousAt.eventually_ne hx).mono hJA
    have h := congrArg (fun ψ : Finset ι → ℝ ↦ ∑ s, ψ s * φ x s)
      (sum_smul_euclideanWittenLaplacian_smul_apply (hf x hxs) (fun a ha ↦ hJ a ha x hxs)
        hφ.contDiffAt hJA' t)
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    calc _ = ∑ s, (∑ a ∈ A, J a x * euclideanWittenLaplacian f t (J a • φ) x s) * φ x s := by
          rw [Finset.sum_comm]
          simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
      _ = _ := h
      _ = _ := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, sq, mul_assoc]
  have hint : ∀ a ∈ A, Integrable fun x ↦
      ∑ s, euclideanWittenLaplacian f t (J a • φ) x s * (J a • φ) x s := by
    intro a ha
    have hJc : ContinuousOn (J a) (tsupport φ) := fun x hx ↦
      (hJ a ha x hx).continuousAt.continuousWithinAt
    exact Continuous.integrable_sum_mul_of_continuousOn
      (hφ.continuous.smul_of_continuousOn_of_tsupport_subset subset_rfl hJc) hφc.smul_left
      (tsupport_smul_subset_right (J a) φ) fun x hx ↦
        (continuousAt_euclideanWittenLaplacian (hf x hx) ((hJ a ha x hx).smul hφ.contDiffAt)
          t).continuousWithinAt
  have hP : Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_euclideanWittenLaplacian (hf x hx) hφ.contDiffAt t).continuousWithinAt
  have hQ : Integrable fun x ↦
      (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 :=
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl fun x hx ↦
      ContinuousAt.continuousWithinAt <| tendsto_finsetSum _ fun a ha ↦
        tendsto_finsetSum _ fun i _ ↦
          (((hJ a ha x hx).continuousAt_fderiv two_ne_zero).clm_apply continuousAt_const).pow 2
  rw [← integral_finsetSum A hint, integral_congr_ae (Eventually.of_forall hpt), integral_add hP hQ,
    add_sub_cancel_right]

/-! ### The lower bound away from the critical points -/

omit [LinearOrder ι] in
/-- The potential `t² |df|² - |t| ∑_{i,j} |∂ᵢ∂ⱼf|` of a function `f` that is `C²` at `x` is
continuous at `x`. -/
private theorem continuousAt_mul_sum_fderiv_apply_sq_sub_mul_sum_sum_abs_fderiv_fderiv_apply
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x) (t : ℝ) :
    ContinuousAt (fun y ↦ t ^ 2 * ∑ i, fderiv ℝ f y (Pi.single i 1) ^ 2 -
      |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single j 1)|) x := by
  have hf₁ := hf.continuousAt_fderiv two_ne_zero
  have hf₂ := hf.continuousAt_fderiv_fderiv le_rfl
  exact (continuousAt_const.mul (tendsto_finsetSum _ fun i _ ↦
    (hf₁.clm_apply continuousAt_const).pow 2)).sub
      (continuousAt_const.mul (tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
        ((hf₂.clm_apply continuousAt_const).clm_apply continuousAt_const).abs))

/-- **The pointwise lower bound for the pairing of the Witten Laplacian with a form.** For `f` and
a form `φ` that are `C²` at `x`,

`∑ᵢ ⟨-∂ᵢ²φ, φ⟩ + (t² |df|² - |t| ∑_{i,j} |∂ᵢ∂ⱼf|) |φ|² ≤ ⟨Δ_t φ, φ⟩`

at `x`. By Witten's frame formula, `⟨Δ_t φ, φ⟩` is `∑ᵢ ⟨-∂ᵢ²φ, φ⟩ + t² |df|² |φ|²` plus `t` times
`⟨∑_{i,j} ∂ᵢ∂ⱼf ⁅εᵢ, ιⱼ⁆ φ, φ⟩`, and the last pairing is bounded by `(∑_{i,j} |∂ᵢ∂ⱼf|) |φ|²`. -/
theorem sum_sum_neg_fderiv_fderiv_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ x) (t : ℝ) :
    ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        (t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
          |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|) *
            ∑ s, φ x s ^ 2 ≤
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  set HT := ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
    ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s *
      φ x s
  have hdecomp : ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        (t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 + t * HT := by
    rw [euclideanWittenLaplacian_apply hf hφ]
    simp only [HT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.neg_apply,
      smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, neg_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset ι)))
      (t := (Finset.univ : Finset ι))]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring
    · exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ by ring
  have hHT :=
    (Pi.basisFun ℝ ι).abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) (φ x)
  have htHT : -(t * HT) ≤ |t| * ((∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|) * ∑ s, φ x s ^ 2) :=
    calc -(t * HT) ≤ |t * HT| := neg_le_abs _
      _ = |t| * |HT| := abs_mul t HT
      _ ≤ _ := mul_le_mul_of_nonneg_left hHT (abs_nonneg t)
  rw [hdecomp]
  linarith

/-- **A lower bound for the quadratic form of the Witten Laplacian.** For a compactly supported
`C²` form `φ` on `ℝ^ι` and a function `f` that is `C²` at every point of the support of `φ`,

`∫ (t² |df|² - |t| ∑_{i,j} |∂ᵢ∂ⱼf|) |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`,

with `|df|² = ∑ᵢ (∂ᵢf)²` and `|φ|² = ∑ s, φ s ²`. The potential on the left is the fibre part of
Witten's frame formula, bounded below using `|⟨⁅εᵢ, ιⱼ⁆ v, v⟩| ≤ |v|²`; the coefficientwise
Laplacian contributes the nonnegative Dirichlet energy `∑ᵢ ∫ |∂ᵢφ|²`. -/
theorem integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul {f : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    ∫ x, (t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
        |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|) *
          ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hφ₂ : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  -- The second-order part of the pairing, `K = ∑ᵢ ⟨-∂ᵢ²φ, φ⟩`, and the potential `V`.
  set K : (ι → ℝ) → ℝ := fun x ↦
    ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s
  set V : (ι → ℝ) → ℝ := fun x ↦ t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
    |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|
  -- The Dirichlet energy is nonnegative: `∫ K = ∑ᵢ ∫ |∂ᵢφ|² ≥ 0`.
  have hKint : ∀ i ∈ (Finset.univ : Finset ι), Integrable fun x ↦
      ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s := fun i _ ↦
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc (Set.subset_univ _)
      ((hφ₂.clm_apply continuous_const).clm_apply continuous_const).neg.continuousOn
  have hKi : Integrable K := integrable_finsetSum _ hKint
  have hK : 0 ≤ ∫ x, K x := by
    rw [integral_finsetSum _ hKint]
    refine Finset.sum_nonneg fun i _ ↦ ?_
    rw [integral_sum_neg_fderiv_fderiv_apply_mul_eq_integral_sum_sq hφ hφc]
    exact integral_nonneg fun x ↦ Finset.sum_nonneg fun s _ ↦ sq_nonneg _
  -- Pointwise, the pairing is at least `K + V |φ|²`; off the support of `φ` both sides vanish.
  have hpt : ∀ x, K x + V x * ∑ s, φ x s ^ 2 ≤
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact sum_sum_neg_fderiv_fderiv_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
        (hf x hx) hφ.contDiffAt t
    · simp [K, image_eq_zero_of_notMem_tsupport hx]
  have hV : Integrable fun x ↦ V x * ∑ s, φ x s ^ 2 :=
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_mul_sum_fderiv_apply_sq_sub_mul_sum_sum_abs_fderiv_fderiv_apply (hf x hx)
        t).continuousWithinAt
  have hP : Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_euclideanWittenLaplacian (hf x hx) hφ.contDiffAt t).continuousWithinAt
  calc ∫ x, V x * ∑ s, φ x s ^ 2 ≤ (∫ x, K x) + ∫ x, V x * ∑ s, φ x s ^ 2 :=
        le_add_of_nonneg_left hK
    _ = ∫ x, (K x + V x * ∑ s, φ x s ^ 2) := (integral_add hKi hV).symm
    _ ≤ _ := integral_mono (hKi.add hV) hP hpt

/-- **The Witten Laplacian is large away from the critical points.** Let `φ` be a compactly
supported `C²` form and `f` a function that is `C²` at every point of the support of `φ`. If
`|df|² ≥ c` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` wherever `φ` does not vanish, then

`(t² c - |t| h) ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`.

When `c > 0` the constant grows like `t²`, so forms supported away from the critical points of `f`
do not contribute to the low-lying spectrum of `Δ_t` for large `t`. -/
theorem mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul {f : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) {c h : ℝ}
    (hc : ∀ x, φ x ≠ 0 → c ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) (t : ℝ) :
    (t ^ 2 * c - |t| * h) * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  refine le_trans ?_ (integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul hf hφ hφc t)
  rw [← integral_const_mul]
  refine integral_mono ?_ ?_ fun x ↦ ?_
  · exact hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl continuousOn_const
  · exact hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_mul_sum_fderiv_apply_sq_sub_mul_sum_sum_abs_fderiv_fderiv_apply (hf x hx)
        t).continuousWithinAt
  by_cases hx : φ x = 0
  · simp [hx]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun s _ ↦ sq_nonneg _)
  have := hc x hx
  have := hh x hx
  gcongr

end TauCeti
