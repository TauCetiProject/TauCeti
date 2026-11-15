/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Calculus.WittenLaplacian.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
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

For a single compactly supported cutoff `J` and a form `φ` that need not have compact support, an
integration by parts of the first-order term gives instead

`∫ ⟨Δ_t (J φ), J φ⟩ = ∫ J² ⟨Δ_t φ, φ⟩ + ∫ |∇J|² |φ|²`

(`TauCeti.integral_sum_euclideanWittenLaplacian_smul_mul_eq`). Applied to an eigenform `φ`, such as
a Gaussian ground state of the harmonic-oscillator model, it computes the energy of the cut-off form
`J φ` exactly.

Since `Δ_t` is local (`TauCeti.euclideanWittenLaplacian_eventuallyEq`), its quadratic form has no
cross terms between forms with disjoint supports
(`TauCeti.integral_sum_euclideanWittenLaplacian_sum_mul_sum_eq`). So a bound
`∫ ⟨Δ_t φₐ, φₐ⟩ ≤ l ∫ |φₐ|²` for each of finitely many such forms persists on their span
(`TauCeti.integral_sum_euclideanWittenLaplacian_sum_smul_mul_le`). This is how quasimodes localized
at different critical points combine.

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
* `TauCeti.integral_sum_euclideanWittenLaplacian_smul_mul_eq`: the localization formula for a single
  cutoff applied to a form without compact support.
* `TauCeti.integral_sum_euclideanWittenLaplacian_sum_mul_sum_eq` and
  `TauCeti.integral_sum_euclideanWittenLaplacian_sum_smul_mul_le`: the quadratic form of `Δ_t`
  splits over forms with disjoint supports, so a common bound on their Rayleigh quotients holds on
  their span.
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

omit [LinearOrder ι] in
/-- The scalar identity behind the localization formula for a single cutoff: the pairing of
`J L - 2 ∑ᵢ gᵢ Dᵢ - (∑ᵢ hᵢ) φ` with `J φ` is `J² ⟨L, φ⟩ + (∑ᵢ gᵢ²) |φ|²` minus the sum over `i` of
the derivatives `(gᵢ² + J hᵢ) |φ|² + J gᵢ ∑ₛ 2 φₛ Dᵢₛ` of `J gᵢ |φ|²`. -/
private theorem sum_sub_mul_mul_eq (J : ℝ) (L φ : Finset ι → ℝ) (g h : ι → ℝ)
    (D : ι → Finset ι → ℝ) :
    ∑ s, (J * L s - 2 * ∑ i, g i * D i s - (∑ i, h i) * φ s) * (J * φ s) =
      J ^ 2 * ∑ s, L s * φ s + (∑ i, g i ^ 2) * ∑ s, φ s ^ 2 -
        ∑ i, ((g i ^ 2 + J * h i) * (∑ s, φ s ^ 2) + J * g i * ∑ s, 2 * φ s * D i s) := by
  have e₁ : ∑ s, (∑ i, g i * D i s) * (J * φ s) = J * ∑ i, g i * ∑ s, φ s * D i s := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring
  have e₂ : ∀ i, (g i ^ 2 + J * h i) * (∑ s, φ s ^ 2) + J * g i * ∑ s, 2 * φ s * D i s =
      g i ^ 2 * (∑ s, φ s ^ 2) + J * (∑ s, φ s ^ 2) * h i + 2 * J * (g i * ∑ s, φ s * D i s) :=
    fun i ↦ by
      rw [show ∑ s, 2 * φ s * D i s = 2 * ∑ s, φ s * D i s from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ by ring]
      ring
  calc _ = ∑ s, (J ^ 2 * (L s * φ s) - 2 * ((∑ i, g i * D i s) * (J * φ s)) -
          J * (∑ i, h i) * φ s ^ 2) := Finset.sum_congr rfl fun s _ ↦ by ring
    _ = J ^ 2 * ∑ s, L s * φ s - 2 * ∑ s, (∑ i, g i * D i s) * (J * φ s) -
          J * (∑ i, h i) * ∑ s, φ s ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ = _ := by
        rw [e₁, Finset.sum_congr rfl fun i _ ↦ e₂ i, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

omit [LinearOrder ι] in
/-- The derivative of `y ↦ J y ∂_v J y |φ y|²` in the direction `v`. -/
private theorem fderiv_mul_fderiv_apply_mul_sum_sq_apply {J : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ} (hJ : ContDiffAt ℝ 2 J x)
    (hφ : DifferentiableAt ℝ φ x) (v : ι → ℝ) :
    fderiv ℝ (fun y ↦ J y * fderiv ℝ J y v * ∑ s, φ y s ^ 2) x v =
      (fderiv ℝ J x v ^ 2 + J x * fderiv ℝ (fderiv ℝ J) x v v) * ∑ s, φ x s ^ 2 +
        J x * fderiv ℝ J x v * ∑ s, 2 * φ x s * fderiv ℝ φ x v s := by
  have hJ₁ : HasFDerivAt J (fderiv ℝ J x) x := (hJ.differentiableAt (by norm_num)).hasFDerivAt
  have hJ₂ : HasFDerivAt (fun y ↦ fderiv ℝ J y v) ((fderiv ℝ (fderiv ℝ J) x).flip v) x := by
    have h := ((hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    simpa using h
  have hq : HasFDerivAt (fun y ↦ ∑ s, φ y s ^ 2)
      (∑ s, (2 * φ x s) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp
        (fderiv ℝ φ x)) x := by
    refine HasFDerivAt.fun_sum fun s _ ↦ ?_
    have hs : HasFDerivAt (fun y ↦ φ y s)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp (fderiv ℝ φ x)) x :=
      (hasFDerivAt_apply (𝕜 := ℝ) s (φ x)).comp x hφ.hasFDerivAt
    refine (hs.pow 2).congr_fderiv ?_
    ext w
    simp
  rw [((hJ₁.fun_mul hJ₂).fun_mul hq).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  ring

/-- **The localization formula for a single cutoff.** Let `J` be a compactly supported `C²`
function, `φ` a `C²` form that need not have compact support, and `f` a function that is `C²` at
every point of the support of `J`. Then

`∫ ⟨Δ_t (J φ), J φ⟩ = ∫ J² ⟨Δ_t φ, φ⟩ + ∫ |∇J|² |φ|²`.

The localization error `∫ |∇J|² |φ|²` does not depend on `t`. When `φ` is an eigenform of `Δ_t`
it measures how far the cut-off form `J φ` is from being one. -/
theorem integral_sum_euclideanWittenLaplacian_smul_mul_eq {f J : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport J, ContDiffAt ℝ 2 f x)
    (hJ : ContDiff ℝ 2 J) (hJc : HasCompactSupport J) (hφ : ContDiff ℝ 2 φ) (t : ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t (J • φ) x s * (J • φ) x s =
      (∫ x, J x ^ 2 * ∑ s, euclideanWittenLaplacian f t φ x s * φ x s) +
        ∫ x, (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
  -- The divergence terms `∂ᵢ (J ∂ᵢJ |φ|²)`, whose integrals vanish.
  set u : ι → (ι → ℝ) → ℝ := fun i y ↦ J y * fderiv ℝ J y (Pi.single i 1) * ∑ s, φ y s ^ 2
  have hu : ∀ i, ContDiff ℝ 1 (u i) := fun i ↦
    ((hJ.of_le (by norm_num)).mul ((hJ.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const)).mul (ContDiff.sum fun s _ ↦
        ((contDiff_pi.1 hφ s).of_le (by norm_num)).pow 2)
  have huc : ∀ i, HasCompactSupport (u i) := fun i ↦
    (hJc.mul_right (f' := fun y ↦ fderiv ℝ J y (Pi.single i 1))).mul_right
  have hpt : ∀ x, ∑ s, euclideanWittenLaplacian f t (J • φ) x s * (J • φ) x s =
      J x ^ 2 * ∑ s, euclideanWittenLaplacian f t φ x s * φ x s +
        (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 -
          ∑ i, fderiv ℝ (u i) x (Pi.single i 1) := by
    intro x
    by_cases hx : x ∈ tsupport J
    · simp only [u, fderiv_mul_fderiv_apply_mul_sum_sq_apply hJ.contDiffAt
        (hφ.differentiable (by norm_num) x),
        euclideanWittenLaplacian_smul_apply (hf x hx) hJ.contDiffAt hφ.contDiffAt t,
        Pi.smul_apply', Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact sum_sub_mul_mul_eq _ _ _ _ _ _
    · have hu0 : ∀ i, fderiv ℝ (u i) x = 0 := fun i ↦ fderiv_of_notMem_tsupport ℝ fun h ↦ hx <|
        (tsupport_mul_subset_left.trans tsupport_mul_subset_left) h
      simp [image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx, hu0]
  have hA : Integrable fun x ↦ J x ^ 2 * ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
    have h := (hJ.continuous.smul (hJ.continuous.smul hφ.continuous))
      |>.integrable_sum_mul_of_continuousOn (μ := volume) (s := Finset.univ)
        (g := euclideanWittenLaplacian f t φ) hJc.smul_right
      (by exact tsupport_smul_subset_left J (J • φ)) fun x hx ↦
        (continuousAt_euclideanWittenLaplacian (hf x hx) hφ.contDiffAt t).continuousWithinAt
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hB : Integrable fun x ↦ (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
    refine Continuous.integrable_of_hasCompactSupport ((continuous_finsetSum _ fun i _ ↦
      ((hJ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).mul
        (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp hφ.continuous).pow 2))
      (hJc.mono' fun x hx ↦ ?_)
    by_contra h
    exact hx (by simp [fderiv_of_notMem_tsupport ℝ h])
  have hD : ∀ i, Integrable fun x ↦ fderiv ℝ (u i) x (Pi.single i 1) := fun i ↦
    integrable_fderiv_apply_of_hasCompactSupport (hu i) (huc i) _
  have hAB : Integrable fun x ↦ J x ^ 2 * ∑ s, euclideanWittenLaplacian f t φ x s * φ x s +
      (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := hA.add hB
  have hDs : Integrable fun x ↦ ∑ i, fderiv ℝ (u i) x (Pi.single i 1) :=
    integrable_finsetSum _ fun i _ ↦ hD i
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub hAB hDs,
    integral_finsetSum _ fun i _ ↦ hD i, integral_add hA hB]
  simp [integral_fderiv_apply_eq_zero_of_hasCompactSupport (hu _) (huc _)]

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


/-! ### Forms with disjoint supports -/

/-- **The quadratic form of `Δ_t` on forms with disjoint supports.** For a finite family of
compactly supported `C²` forms `φₐ` with pairwise disjoint supports, and `f` that is `C²` at every
point of these supports, `∫ ⟨Δ_t (∑ₐ φₐ), ∑ₐ φₐ⟩ = ∑ₐ ∫ ⟨Δ_t φₐ, φₐ⟩`: as `Δ_t` is local, the
cross terms vanish. -/
theorem integral_sum_euclideanWittenLaplacian_sum_mul_sum_eq {α : Type*} {A : Finset α}
    {f : (ι → ℝ) → ℝ} {φ : α → (ι → ℝ) → Finset ι → ℝ}
    (hf : ∀ a ∈ A, ∀ x ∈ tsupport (φ a), ContDiffAt ℝ 2 f x) (hφ : ∀ a ∈ A, ContDiff ℝ 2 (φ a))
    (hφc : ∀ a ∈ A, HasCompactSupport (φ a))
    (hdisj : (A : Set α).PairwiseDisjoint fun a ↦ tsupport (φ a)) (t : ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t (∑ a ∈ A, φ a) x s * (∑ a ∈ A, φ a) x s =
      ∑ a ∈ A, ∫ x, ∑ s, euclideanWittenLaplacian f t (φ a) x s * φ a x s := by
  have hpt : ∀ x, ∑ s, euclideanWittenLaplacian f t (∑ a ∈ A, φ a) x s * (∑ a ∈ A, φ a) x s =
      ∑ a ∈ A, ∑ s, euclideanWittenLaplacian f t (φ a) x s * φ a x s := by
    intro x
    by_cases h : ∃ a ∈ A, x ∈ tsupport (φ a)
    · obtain ⟨a, ha, hx⟩ := h
      have hsum := Finset.sum_eventuallyEq_of_pairwiseDisjoint_tsupport hdisj ha hx
      rw [(euclideanWittenLaplacian_eventuallyEq (EventuallyEq.refl _ f) hsum t).eq_of_nhds,
        hsum.eq_of_nhds, Finset.sum_eq_single_of_mem a ha fun b hb hba ↦ ?_]
      have hxb : x ∉ tsupport (φ b) := fun hxb ↦
        Set.disjoint_left.1 (hdisj ha hb (Ne.symm hba)) hx hxb
      simp [image_eq_zero_of_notMem_tsupport hxb]
    · simp only [not_exists, not_and] at h
      have h0 : ∀ a ∈ A, φ a x = 0 := fun a ha ↦ image_eq_zero_of_notMem_tsupport (h a ha)
      have hx0 : (∑ a ∈ A, φ a) x = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero h0
      rw [hx0, Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun s _ ↦ by simp [h0 a ha]]
      simp
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun a ha ↦ ?_]
  exact (hφ a ha).continuous.integrable_sum_mul_of_continuousOn (hφc a ha) subset_rfl fun x hx ↦
    (continuousAt_euclideanWittenLaplacian (hf a ha x hx) (hφ a ha).contDiffAt t).continuousWithinAt

omit [LinearOrder ι] in
/-- The squared length of a sum of forms with pairwise disjoint supports is the sum of their
squared lengths, pointwise. -/
private theorem sum_sum_apply_sq_eq_of_pairwiseDisjoint {α : Type*} {A : Finset α}
    {φ : α → (ι → ℝ) → Finset ι → ℝ} (hdisj : (A : Set α).PairwiseDisjoint fun a ↦ tsupport (φ a))
    (x : ι → ℝ) :
    ∑ s, (∑ a ∈ A, φ a) x s ^ 2 = ∑ a ∈ A, ∑ s, φ a x s ^ 2 := by
  by_cases h : ∃ a ∈ A, x ∈ tsupport (φ a)
  · obtain ⟨a, ha, hx⟩ := h
    rw [(Finset.sum_eventuallyEq_of_pairwiseDisjoint_tsupport hdisj ha hx).eq_of_nhds,
      Finset.sum_eq_single_of_mem a ha fun b hb hba ↦ ?_]
    have hxb : x ∉ tsupport (φ b) := fun hxb ↦
      Set.disjoint_left.1 (hdisj ha hb (Ne.symm hba)) hx hxb
    simp [image_eq_zero_of_notMem_tsupport hxb]
  · simp only [not_exists, not_and] at h
    have h0 : ∀ a ∈ A, φ a x = 0 := fun a ha ↦ image_eq_zero_of_notMem_tsupport (h a ha)
    have hx0 : (∑ a ∈ A, φ a) x = 0 := by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero h0
    rw [hx0, Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun s _ ↦ by simp [h0 a ha]]
    simp

/-- **Rayleigh quotients on the span of forms with disjoint supports.** Let `φₐ` be finitely many
compactly supported `C²` forms with pairwise disjoint supports, and `f` a function that is `C²` at
every point of these supports, such that each `φₐ` has Rayleigh quotient at most `l`:
`∫ ⟨Δ_t φₐ, φₐ⟩ ≤ l ∫ |φₐ|²`. Then every linear combination `ψ = ∑ₐ wₐ φₐ` satisfies
`∫ ⟨Δ_t ψ, ψ⟩ ≤ l ∫ |ψ|²`. -/
theorem integral_sum_euclideanWittenLaplacian_sum_smul_mul_le {α : Type*} {A : Finset α}
    {f : (ι → ℝ) → ℝ} {φ : α → (ι → ℝ) → Finset ι → ℝ}
    (hf : ∀ a ∈ A, ∀ x ∈ tsupport (φ a), ContDiffAt ℝ 2 f x) (hφ : ∀ a ∈ A, ContDiff ℝ 2 (φ a))
    (hφc : ∀ a ∈ A, HasCompactSupport (φ a))
    (hdisj : (A : Set α).PairwiseDisjoint fun a ↦ tsupport (φ a)) {t l : ℝ}
    (hl : ∀ a ∈ A, ∫ x, ∑ s, euclideanWittenLaplacian f t (φ a) x s * φ a x s ≤
      l * ∫ x, ∑ s, φ a x s ^ 2) (w : α → ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t (∑ a ∈ A, w a • φ a) x s *
        (∑ a ∈ A, w a • φ a) x s ≤
      l * ∫ x, ∑ s, (∑ a ∈ A, w a • φ a) x s ^ 2 := by
  have hdisj' : (A : Set α).PairwiseDisjoint fun a ↦ tsupport (w a • φ a) :=
    hdisj.mono fun a ↦ tsupport_smul_subset_right (fun _ ↦ w a) (φ a)
  have hsq : ∀ a ∈ A, Integrable fun x ↦ ∑ s, φ a x s ^ 2 := fun a ha ↦
    (hφ a ha).continuous.integrable_mul_sum_sq_of_continuousOn (h := fun _ ↦ (1 : ℝ)) (hφc a ha)
      subset_rfl continuousOn_const |>.congr (Eventually.of_forall fun x ↦ one_mul _)
  rw [integral_sum_euclideanWittenLaplacian_sum_mul_sum_eq (φ := fun a ↦ w a • φ a)
      (fun a ha x hx ↦ hf a ha x (tsupport_smul_subset_right (fun _ ↦ w a) (φ a) hx))
      (fun a ha ↦ (hφ a ha).const_smul (w a)) (fun a ha ↦ (hφc a ha).smul_left) hdisj' t,
    integral_congr_ae (Eventually.of_forall (sum_sum_apply_sq_eq_of_pairwiseDisjoint hdisj')),
    integral_finsetSum _ fun a ha ↦ (hsq a ha).const_mul (w a ^ 2) |>.congr
      (Eventually.of_forall fun x ↦ by simp [Finset.mul_sum, mul_pow]), Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha ↦ ?_
  have e₁ : ∫ x, ∑ s, euclideanWittenLaplacian f t (w a • φ a) x s * (w a • φ a) x s =
      w a ^ 2 * ∫ x, ∑ s, euclideanWittenLaplacian f t (φ a) x s * φ a x s := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [euclideanWittenLaplacian_const_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have e₂ : ∫ x, ∑ s, (w a • φ a) x s ^ 2 = w a ^ 2 * ∫ x, ∑ s, φ a x s ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
  rw [e₁, e₂, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hl a ha) (sq_nonneg _)

end TauCeti
