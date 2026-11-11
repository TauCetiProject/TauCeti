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

(`TauCeti.integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`). Where `|df|² ≥ c`
and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` on the support of `φ`, the quadratic form of `Δ_t` is therefore at least
`t² c - |t| h` times `∫ |φ|²`, which grows quadratically in `t` as soon as `c > 0`
(`TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`).

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
    euclideanWittenLaplacian f t (fun y ↦ J y • φ y) x =
      J x • euclideanWittenLaplacian f t φ x -
        (2 : ℝ) • ∑ i, fderiv ℝ J x (Pi.single i 1) • fderiv ℝ φ x (Pi.single i 1) -
          (∑ i, fderiv ℝ (fderiv ℝ J) x (Pi.single i 1) (Pi.single i 1)) • φ x := by
  have hJφ : ContDiffAt ℝ 2 (fun y ↦ J y • φ y) x := hJ.smul hφ
  rw [euclideanWittenLaplacian_apply hf hJφ, euclideanWittenLaplacian_apply hf hφ]
  beta_reduce
  -- The second-order part, one direction at a time.
  have h₁ : ∀ i : ι,
      -fderiv ℝ (fderiv ℝ fun y ↦ J y • φ y) x (Pi.single i 1) (Pi.single i 1) +
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
    ∑ a ∈ A, J a x • euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x =
      euclideanWittenLaplacian f t φ x +
        (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) • φ x := by
  have h₀ : ∑ a ∈ A, J a x ^ 2 = 1 := hJA.eq_of_nhds
  have h₁ := fun i : ι ↦
    (sum_mul_fderiv_eq_zero_of_sum_sq_eventuallyEq_one hJ hJA (Pi.single i 1)).1
  have h₂ := fun i : ι ↦
    (sum_mul_fderiv_eq_zero_of_sum_sq_eventuallyEq_one hJ hJA (Pi.single i 1)).2
  -- Each summand, written with scalar coefficients in front of `Δ_t φ`, `∂ᵢφ` and `φ`.
  have hterm : ∀ a ∈ A, J a x • euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x =
      J a x ^ 2 • euclideanWittenLaplacian f t φ x +
        ∑ i, (-2 * (J a x * fderiv ℝ (J a) x (Pi.single i 1))) • fderiv ℝ φ x (Pi.single i 1) +
          (-∑ i, J a x * fderiv ℝ (fderiv ℝ (J a)) x (Pi.single i 1) (Pi.single i 1)) • φ x := by
    intro a ha
    rw [euclideanWittenLaplacian_smul_apply hf (hJ a ha) hφ]
    simp only [smul_sub, smul_smul, Finset.smul_sum, neg_smul, Finset.sum_smul, sq]
    rw [sub_sub, sub_eq_add_neg, neg_add, add_assoc, ← Finset.sum_neg_distrib]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by module
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
    rw [← Finset.sum_smul, Finset.sum_neg_distrib, Finset.sum_comm, ← Finset.sum_neg_distrib,
      Finset.sum_comm (s := A)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := h₂ i
    rw [Finset.sum_add_distrib] at h
    linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC,
    add_zero]

/-! ### The IMS formula for the quadratic form -/

/-- **The IMS localization formula for the quadratic form of the Witten Laplacian.** Let `φ` be a
compactly supported `C²` form, `f` a `C²` function, and `(Jₐ)_{a ∈ A}` a finite family of `C²`
functions with `∑ₐ Jₐ² = 1` near every point where `φ` does not vanish. Then

`∫ ⟨Δ_t φ, φ⟩ = ∑ₐ ∫ ⟨Δ_t (Jₐ φ), Jₐ φ⟩ - ∫ (∑ₐ |∇Jₐ|²) |φ|²`. -/
theorem integral_sum_euclideanWittenLaplacian_mul_eq {α : Type*} {A : Finset α}
    {J : α → (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    (hf : ContDiff ℝ 2 f) (hJ : ∀ a ∈ A, ContDiff ℝ 2 (J a)) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (hJA : ∀ x, φ x ≠ 0 → (fun y ↦ ∑ a ∈ A, J a y ^ 2) =ᶠ[𝓝 x] fun _ ↦ 1) (t : ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ a ∈ A, (∫ x, ∑ s, euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x s *
          (J a x • φ x) s) -
        ∫ x, (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
  -- The IMS formula, paired with `φ` at each point.
  have hpt : ∀ x, ∑ a ∈ A, ∑ s, euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x s *
      (J a x • φ x) s = ∑ s, euclideanWittenLaplacian f t φ x s * φ x s +
        (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    have h := congrArg (fun ψ : Finset ι → ℝ ↦ ∑ s, ψ s * φ x s)
      (sum_smul_euclideanWittenLaplacian_smul_apply hf.contDiffAt
        (fun a ha ↦ (hJ a ha).contDiffAt) hφ.contDiffAt (hJA x hx) t)
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    calc _ = ∑ s, (∑ a ∈ A, J a x * euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x s) *
          φ x s := by
          rw [Finset.sum_comm]
          simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
      _ = _ := h
      _ = _ := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, sq, mul_assoc]
  have hcont : ∀ a ∈ A, Continuous fun x ↦ fderiv ℝ (J a) x :=
    fun a ha ↦ (hJ a ha).continuous_fderiv (by norm_num)
  have hint : ∀ a ∈ A, Integrable fun x ↦
      ∑ s, euclideanWittenLaplacian f t (fun y ↦ J a y • φ y) x s * (J a x • φ x) s := by
    intro a ha
    exact (continuous_euclideanWittenLaplacian hf ((hJ a ha).smul hφ) t
      ).integrable_sum_mul_of_hasCompactSupport ((hJ a ha).continuous.smul hφ.continuous)
        (HasCompactSupport.smul_left (f := J a) hφc)
  have hP : Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
    (continuous_euclideanWittenLaplacian hf hφ t).integrable_sum_mul_of_hasCompactSupport
      hφ.continuous hφc
  have hQ : Integrable fun x ↦
      (∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 :=
    (continuous_finsetSum _ fun a ha ↦ continuous_finsetSum _ fun i _ ↦
      ((hcont a ha).clm_apply continuous_const).pow 2).integrable_mul_sum_sq_of_hasCompactSupport
        hφ.continuous hφc
  rw [← integral_finsetSum A hint, integral_congr_ae (Eventually.of_forall hpt), integral_add hP hQ,
    add_sub_cancel_right]

/-! ### The lower bound away from the critical points -/

/-- **A lower bound for the quadratic form of the Witten Laplacian.** For a `C²` function `f` and
a compactly supported `C²` form `φ` on `ℝ^ι`,

`∫ (t² |df|² - |t| ∑_{i,j} |∂ᵢ∂ⱼf|) |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`,

with `|df|² = ∑ᵢ (∂ᵢf)²` and `|φ|² = ∑ s, φ s ²`. The potential on the left is the fibre part of
Witten's frame formula, bounded below using `|⟨⁅εᵢ, ιⱼ⁆ v, v⟩| ≤ |v|²`; the coefficientwise
Laplacian contributes the nonnegative Dirichlet energy `∑ᵢ ∫ |∂ᵢφ|²`. -/
theorem integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul {f : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (t : ℝ) :
    ∫ x, (t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
        |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|) *
          ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hφ₂ : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hf₁ : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hf₂ : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  -- The second-order part of the pairing, `K = ∑ᵢ ⟨-∂ᵢ²φ, φ⟩`, and the potential `V`.
  set K : (ι → ℝ) → ℝ := fun x ↦
    ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s
  set V : (ι → ℝ) → ℝ := fun x ↦ t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
    |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|
  -- The Dirichlet energy is nonnegative: `∫ K = ∑ᵢ ∫ |∂ᵢφ|² ≥ 0`.
  have hKint : ∀ i ∈ (Finset.univ : Finset ι), Integrable fun x ↦
      ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s := fun i _ ↦
    ((hφ₂.clm_apply continuous_const).clm_apply continuous_const).neg
      |>.integrable_sum_mul_of_hasCompactSupport hφ.continuous hφc
  have hKi : Integrable K := integrable_finsetSum _ hKint
  have hK : 0 ≤ ∫ x, K x := by
    rw [integral_finsetSum _ hKint]
    refine Finset.sum_nonneg fun i _ ↦ ?_
    rw [integral_sum_neg_fderiv_fderiv_apply_mul_eq_integral_sum_sq hφ hφc]
    exact integral_nonneg fun x ↦ Finset.sum_nonneg fun s _ ↦ sq_nonneg _
  -- Pointwise, the pairing is `K` plus `t² |df|² |φ|²` plus `t` times the Hessian term `HT`,
  -- and `|HT| ≤ (∑ᵢⱼ |∂ᵢ∂ⱼf|) |φ|²`.
  have hpt : ∀ x, K x + V x * ∑ s, φ x s ^ 2 ≤
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
    intro x
    set HT := ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
      ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s *
        φ x s
    have hdecomp : ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
        K x + (t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 + t * HT := by
      rw [euclideanWittenLaplacian_apply hf.contDiffAt hφ.contDiffAt]
      simp only [K, HT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.neg_apply,
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
    simp only [V]
    linarith
  have hV : Integrable fun x ↦ V x * ∑ s, φ x s ^ 2 :=
    Continuous.integrable_mul_sum_sq_of_hasCompactSupport ((continuous_const.mul
      (continuous_finsetSum _ fun i _ ↦ (hf₁.clm_apply continuous_const).pow 2)).sub
        (continuous_const.mul (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
          ((hf₂.clm_apply continuous_const).clm_apply continuous_const).abs)))
      hφ.continuous hφc
  have hP : Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
    (continuous_euclideanWittenLaplacian hf hφ t).integrable_sum_mul_of_hasCompactSupport
      hφ.continuous hφc
  calc ∫ x, V x * ∑ s, φ x s ^ 2 ≤ (∫ x, K x) + ∫ x, V x * ∑ s, φ x s ^ 2 :=
        le_add_of_nonneg_left hK
    _ = ∫ x, (K x + V x * ∑ s, φ x s ^ 2) := (integral_add hKi hV).symm
    _ ≤ _ := integral_mono (hKi.add hV) hP hpt

/-- **The Witten Laplacian is large away from the critical points.** Let `f` be `C²` and `φ` a
compactly supported `C²` form. If `|df|² ≥ c` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` wherever `φ` does not
vanish, then

`(t² c - |t| h) ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`.

When `c > 0` the constant grows like `t²`, so forms supported away from the critical points of `f`
do not contribute to the low-lying spectrum of `Δ_t` for large `t`. -/
theorem mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul {f : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) {c h : ℝ}
    (hc : ∀ x, φ x ≠ 0 → c ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) (t : ℝ) :
    (t ^ 2 * c - |t| * h) * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  refine le_trans ?_ (integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul hf hφ hφc t)
  rw [← integral_const_mul]
  have hf₁ : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hf₂ : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  refine integral_mono ?_ ?_ fun x ↦ ?_
  · exact continuous_const.integrable_mul_sum_sq_of_hasCompactSupport hφ.continuous hφc
  · exact Continuous.integrable_mul_sum_sq_of_hasCompactSupport ((continuous_const.mul
      (continuous_finsetSum _ fun i _ ↦ (hf₁.clm_apply continuous_const).pow 2)).sub
        (continuous_const.mul (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
          ((hf₂.clm_apply continuous_const).clm_apply continuous_const).abs)))
      hφ.continuous hφc
  by_cases hx : φ x = 0
  · simp [hx]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun s _ ↦ sq_nonneg _)
  have := hc x hx
  have := hh x hx
  gcongr

end TauCeti
