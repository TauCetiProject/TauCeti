/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Calculus.WittenLaplacian.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
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

**Comparing two functions.** By the same frame formula, the Witten Laplacians of two functions `f`
and `g` differ by the fibre endomorphism `t² (|df|² - |dg|²) + t ∑_{i,j} (∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg) ⁅εᵢ, ιⱼ⁆`.
So wherever `|dg|² ≤ |df|²` and `∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg| ≤ e` on the support of a form `φ`,

`∫ ⟨Δ_t^g φ, φ⟩ - |t| e ‖φ‖² ≤ ∫ ⟨Δ_t^f φ, φ⟩`

(`integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul`).
This compares `Δ_t` near a critical point with the harmonic oscillator of a quadratic model that
agrees with `f` only up to its Taylor remainder.

In the integrated statements only `φ` has to be `C²` everywhere; `f` and the `Jₐ` need only be
`C²` at the points of the support of `φ`.

These are the two inputs of Witten's localization argument: for a partition of unity with one
function supported away from the critical points and one near each critical point, they compare
the low-lying spectrum of `Δ_t` with the harmonic-oscillator models at the critical points, which
are computed in `TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic`. That spectral comparison
itself is not carried out here.

**Forms with disjoint supports.** As `Δ_t` is a local operator, it does not mix forms with disjoint
supports: the pointwise energy of a combination `∑ⱼ cⱼ vⱼ` of such forms is `∑ⱼ cⱼ²` times the
pointwise energies of the `vⱼ`
(`TauCeti.sum_euclideanWittenLaplacian_sum_smul_mul_of_notMem_tsupport`). So if the quadratic form
of `Δ_t` is at most `ε` times the squared norm on each of finitely many linearly independent such
forms, it is so on their span
(`TauCeti.exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le`). This is how
quasimodes at different critical points combine into a low-energy space.

## Main results

* `TauCeti.euclideanWittenLaplacian_smul_apply`: the Leibniz rule for `Δ_t (J φ)`.
* `TauCeti.sum_smul_euclideanWittenLaplacian_smul_apply`: the pointwise IMS localization formula.
* `TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`: the IMS localization formula for the
  quadratic form of `Δ_t`.
* `TauCeti.sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul` and
  `TauCeti.sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`: lower bounds for the
  localized pieces give a lower bound for the quadratic form of `Δ_t`;
  `TauCeti.sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`
  is the uniform bound for a partition of unity `J₀, (J p)_{p ∈ P}` at a finite set of points.
* `TauCeti.sum_sum_neg_fderiv_fderiv_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul`: the
  pointwise lower bound for `⟨Δ_t φ, φ⟩`.
* `TauCeti.integral_mul_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul` and
  `TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`: lower bounds for the
  quadratic form of `Δ_t` by the potential `t² |df|² - |t| |Hess f|`, and
  `TauCeti.mul_mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul_of_add_le_mul`:
  the bound `t κ ‖φ‖²` once `κ + h ≤ t c`.
* `TauCeti.sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul`
  and
  `integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul`:
  comparison of the Witten Laplacians of two functions, pointwise and integrated.
* `TauCeti.sum_euclideanWittenLaplacian_sum_smul_mul_of_notMem_tsupport`: `Δ_t` does not mix forms
  with disjoint supports.
* `TauCeti.exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le`: an upper bound
  for the quadratic form of `Δ_t` on forms with disjoint supports extends to their span.

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
open scoped ContDiff

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

/-- **The lower bound of IMS localization.** Under the hypotheses of
`TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`, suppose that `∑ₐ |∇Jₐ|² ≤ K` wherever `φ`
does not vanish, and that the quadratic form of `Δ_t` at each localized piece `Jₐ φ` is at least
`Bₐ`. Then `∑ₐ Bₐ - K ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`. -/
theorem sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul {α : Type*}
    {A : Finset α} {J : α → (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hJ : ∀ a ∈ A, ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 (J a) x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJA : ∀ x, φ x ≠ 0 → ∑ a ∈ A, J a x ^ 2 = 1) {K : ℝ}
    (hK : ∀ x, φ x ≠ 0 → ∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2 ≤ K) {t : ℝ}
    {B : α → ℝ}
    (hB : ∀ a ∈ A, B a ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t (J a • φ) x s * (J a • φ) x s) :
    ∑ a ∈ A, B a - K * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  rw [integral_sum_euclideanWittenLaplacian_mul_eq hf hJ hφ hφc hJA t]
  refine sub_le_sub (Finset.sum_le_sum hB) ?_
  -- The localization error is at most `K ∫ |φ|²`.
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ ?_)
    (hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl continuousOn_const)
    (Eventually.of_forall fun x ↦ ?_)
  · positivity
  · by_cases hx : φ x = 0
    · simp [hx]
    exact mul_le_mul_of_nonneg_right (hK x hx) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- A form of degree `m` has no component at a multi-index `S` of another cardinality, so omitting
that component does not change its pointwise squared norm. -/
theorem sum_erase_sq_eq_sum_sq_of_card_ne {φ : (ι → ℝ) → Finset ι → ℝ} {m : ℕ}
    (hφ : ∀ x s, φ x s ≠ 0 → s.card = m) {S : Finset ι} (hS : S.card ≠ m) (x : ι → ℝ) :
    ∑ s ∈ Finset.univ.erase S, φ x s ^ 2 = ∑ s, φ x s ^ 2 :=
  Finset.sum_erase _ (by rw [not_imp_comm.1 (hφ x S) hS, sq, mul_zero])

/-- **A uniform lower bound from IMS localization.** Under the hypotheses of
`TauCeti.sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`, if the quadratic form
of `Δ_t` at every localized piece `Jₐ φ` is at least `κ` times its squared norm, then
`(κ - K) ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`: the squared norms of the pieces add up to that of `φ`. -/
theorem sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul {α : Type*}
    {A : Finset α} {J : α → (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hJ : ∀ a ∈ A, ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 (J a) x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJA : ∀ x, φ x ≠ 0 → ∑ a ∈ A, J a x ^ 2 = 1) {K : ℝ}
    (hK : ∀ x, φ x ≠ 0 → ∑ a ∈ A, ∑ i, fderiv ℝ (J a) x (Pi.single i 1) ^ 2 ≤ K) {t κ : ℝ}
    (hκ : ∀ a ∈ A, κ * ∫ x, ∑ s, (J a • φ) x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J a • φ) x s * (J a • φ) x s) :
    (κ - K) * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have key := sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul hf hJ hφ hφc hJA
    hK hκ
  -- The squared norms of the pieces `Jₐ φ` add up to `∫ |φ|²`.
  have hsq : ∀ a x, ∑ s, (J a • φ) x s ^ 2 = J a x ^ 2 * ∑ s, φ x s ^ 2 := fun a x ↦ by
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hint : ∀ a ∈ A, Integrable fun x ↦ J a x ^ 2 * ∑ s, φ x s ^ 2 := fun a ha ↦
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl fun x hx ↦
      ((hJ a ha x hx).continuousAt.pow 2).continuousWithinAt
  have hN : ∑ a ∈ A, ∫ x, J a x ^ 2 * ∑ s, φ x s ^ 2 = ∫ x, ∑ s, φ x s ^ 2 := by
    rw [← integral_finsetSum _ hint]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : φ x = 0
    · simp [hx]
    simp only [← Finset.sum_mul, hJA x hx, one_mul]
  simp only [hsq, ← Finset.mul_sum, hN] at key
  linarith

/-- **A uniform lower bound from IMS localization at a finite set of points.** Let `J₀` and `J p`
(`p ∈ P`) be `C²` on the support of `φ`, with `J₀² + ∑ₚ (J p)² = 1` and
`∑ᵢ (∂ᵢJ₀)² + ∑ₚ ∑ᵢ (∂ᵢ J p)² ≤ K` wherever `φ` does not vanish. If the quadratic form of `Δ_t` at
`J₀ φ` and at every `J p φ` is at least `κ` times its squared norm, then
`(κ - K) ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`. This is
`TauCeti.sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul` for the partition of unity
indexed by `P.insertNone`, with `none` for `J₀`. -/
theorem sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {P : Finset (ι → ℝ)} {J₀ : (ι → ℝ) → ℝ}
    {J : (ι → ℝ) → (ι → ℝ) → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hJ₀ : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 J₀ x)
    (hJ : ∀ p ∈ P, ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 (J p) x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJ1 : ∀ x, φ x ≠ 0 → J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1)
    {K : ℝ} (hK : ∀ x, φ x ≠ 0 → ∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2 ≤ K) {t κ : ℝ}
    (h₀ : κ * ∫ x, ∑ s, (J₀ • φ) x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J₀ • φ) x s * (J₀ • φ) x s)
    (hκ : ∀ p ∈ P, κ * ∫ x, ∑ s, (J p • φ) x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J p • φ) x s * (J p • φ) x s) :
    (κ - K) * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
  sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul (A := P.insertNone)
    (J := fun o ↦ o.elim J₀ J) hf
    (by rintro (_ | p) hp; exacts [hJ₀, hJ p (Finset.some_mem_insertNone.1 hp)]) hφ hφc
    (fun x hx ↦ by simpa [Finset.sum_insertNone] using hJ1 x hx)
    (fun x hx ↦ by simpa [Finset.sum_insertNone] using hK x hx)
    (by rintro (_ | p) hp; exacts [h₀, hκ p (Finset.some_mem_insertNone.1 hp)])

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
  rw [sum_euclideanWittenLaplacian_apply_mul hf hφ]
  set HT := ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
    ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s *
      φ x s
  have hHT :=
    (Pi.basisFun ℝ ι).abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) (φ x)
  have htHT : -(t * HT) ≤ |t| * ((∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|) * ∑ s, φ x s ^ 2) :=
    calc -(t * HT) ≤ |t * HT| := neg_le_abs _
      _ = |t| * |HT| := abs_mul t HT
      _ ≤ _ := mul_le_mul_of_nonneg_left hHT (abs_nonneg t)
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
  -- The second-order part of the pairing, `K = ∑ᵢ ⟨-∂ᵢ²φ, φ⟩`, and the potential `V`.
  set K : (ι → ℝ) → ℝ := fun x ↦
    ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s
  set V : (ι → ℝ) → ℝ := fun x ↦ t ^ 2 * ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 -
    |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|
  -- The Dirichlet energy is nonnegative: `∫ K = ∑ᵢ ∫ |∂ᵢφ|² ≥ 0`.
  have hKint : ∀ i ∈ (Finset.univ : Finset ι), Integrable fun x ↦
      ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s := fun i _ ↦
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc (Set.subset_univ _)
      (hφ.continuous_fderiv_fderiv_apply le_rfl _ _).neg.continuousOn
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

/-- **The Witten Laplacian is large away from the critical points, for large `t`.** Under the
hypotheses of `TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`, if
`t ≥ 0` and `κ + h ≤ t c`, then `t κ ∫ |φ|² ≤ ∫ ⟨Δ_t φ, φ⟩`. -/
theorem mul_mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul_of_add_le_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) {c h : ℝ}
    (hc : ∀ x, φ x ≠ 0 → c ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) {t κ : ℝ}
    (ht : 0 ≤ t) (htc : κ + h ≤ t * c) :
    t * κ * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have h₀ := mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul hf hφ hφc hc hh t
  rw [abs_of_nonneg ht] at h₀
  have hcoef : t * κ ≤ t ^ 2 * c - t * h := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef
    (integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).trans h₀

/-! ### Comparing the Witten Laplacians of two functions -/

/-- **Comparison of the Witten Laplacians of two functions, pointwise.** For functions `f`, `g` and
a form `φ` that are `C²` at `x`,

`⟨Δ_t^g φ, φ⟩ + (t² (|df|² - |dg|²) - |t| ∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg|) |φ|² ≤ ⟨Δ_t^f φ, φ⟩`

at `x`: by Witten's frame formula the two pairings differ by `t² (|df|² - |dg|²) |φ|²` and `t`
times the pairing of `φ` with `∑_{i,j} (∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg) ⁅εᵢ, ιⱼ⁆ φ`. -/
theorem sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
    {f g : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (hφ : ContDiffAt ℝ 2 φ x) (t : ℝ) :
    ∑ s, euclideanWittenLaplacian g t φ x s * φ x s +
        (t ^ 2 * (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 - ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2) -
          |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
            fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)|) * ∑ s, φ x s ^ 2 ≤
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  rw [sum_euclideanWittenLaplacian_apply_mul hf hφ, sum_euclideanWittenLaplacian_apply_mul hg hφ]
  -- The Hessian terms differ by the pairing with the commutators weighted by the difference of
  -- the Hessians, which is bounded by `(∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg|) |φ|²`.
  have hb :=
    (Pi.basisFun ℝ ι).abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)) (φ x)
  simp only [sub_smul, Finset.sum_sub_distrib, Pi.sub_apply, sub_mul] at hb
  have ht := (neg_le_abs _).trans ((abs_mul t _).trans_le (mul_le_mul_of_nonneg_left hb
    (abs_nonneg t)))
  linarith

/-- **Comparison of the Witten Laplacians of two functions.** Let `φ` be a compactly supported
`C²` form and `f`, `g` functions that are `C²` at every point of the support of `φ`. If, wherever
`φ` does not vanish, `|dg|² ≤ |df|²` and `∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg| ≤ e`, then

`∫ ⟨Δ_t^g φ, φ⟩ - |t| e ∫ |φ|² ≤ ∫ ⟨Δ_t^f φ, φ⟩`. -/
theorem integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul
    {f g : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hg : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 g x) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hdf : ∀ x, φ x ≠ 0 →
      ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {e : ℝ} (he : ∀ x, φ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)| ≤ e) (t : ℝ) :
    (∫ x, ∑ s, euclideanWittenLaplacian g t φ x s * φ x s) - |t| * e * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hint : ∀ u : (ι → ℝ) → ℝ, (∀ x ∈ tsupport φ, ContDiffAt ℝ 2 u x) →
      Integrable fun x ↦ ∑ s, euclideanWittenLaplacian u t φ x s * φ x s := fun u hu ↦
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_euclideanWittenLaplacian (hu x hx) hφ.contDiffAt t).continuousWithinAt
  have hN : Integrable fun x ↦ |t| * e * ∑ s, φ x s ^ 2 :=
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl continuousOn_const
  calc _ = ∫ x, (∑ s, euclideanWittenLaplacian g t φ x s * φ x s -
        |t| * e * ∑ s, φ x s ^ 2) := by
          rw [integral_sub (hint g hg) hN, integral_const_mul]
    _ ≤ _ := integral_mono ((hint g hg).sub hN) (hint f hf) fun x ↦ ?_
  by_cases hx : φ x = 0
  · simp [hx]
  have hxs := subset_tsupport φ hx
  have h := sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
    (hf x hxs) (hg x hxs) hφ.contDiffAt t
  have h₁ := mul_nonneg (sq_nonneg t) (sub_nonneg.2 (hdf x hx))
  have h₂ := mul_le_mul_of_nonneg_left (he x hx) (abs_nonneg t)
  have h₃ : 0 ≤ ∑ s, φ x s ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only
  nlinarith

/-! ### Forms with disjoint supports -/

section Disjoint

variable {κ : Type*} [Fintype κ] {v : κ → (ι → ℝ) → Finset ι → ℝ}

/-- **The Witten Laplacian does not mix forms with disjoint supports.** If `x` lies in the
topological support of at most one of the forms `v j`, the pointwise energy of `∑ⱼ cⱼ vⱼ` at `x`
is `∑ⱼ cⱼ²` times the pointwise energies of the `v j`, since `Δ_t` is a local operator. -/
theorem sum_euclideanWittenLaplacian_sum_smul_mul_of_notMem_tsupport (f : (ι → ℝ) → ℝ) (t : ℝ)
    (c : κ → ℝ) {x : ι → ℝ} (hv : ∀ i j, i ≠ j → x ∈ tsupport (v i) → x ∉ tsupport (v j)) :
    ∑ s, euclideanWittenLaplacian f t (∑ j, c j • v j) x s * (∑ j, c j • v j) x s =
      ∑ j, c j ^ 2 * ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s :=
  apply_sum_smul_eq_sum_sq_mul_of_notMem_tsupport
    (fun φ ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s) (fun a φ ↦ by
      simp only [euclideanWittenLaplacian_const_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ ↦ by ring)
    (fun φ ψ h ↦ by
      rw [((EventuallyEq.refl _ f).euclideanWittenLaplacian h t).eq_of_nhds, h.eq_of_nhds])
    c hv

/-- **The span of forms with disjoint supports.** Let `v j` be linearly independent smooth
compactly supported forms of degree `m` with pairwise disjoint supports, on each of which the
quadratic form of `Δ_t` is at most `ε` times the squared norm. Then their span has dimension the
number of the `v j`, and on every element of it the quadratic form is at most `ε` times the
squared norm. -/
theorem exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le
    {f : (ι → ℝ) → ℝ} {t ε : ℝ} {m : ℕ}
    (hli : LinearIndependent ℝ v) (hvC : ∀ j, ContDiff ℝ ∞ (v j))
    (hvc : ∀ j, HasCompactSupport (v j)) (hvm : ∀ j x s, v j x s ≠ 0 → s.card = m)
    (hdisj : ∀ x i j, i ≠ j → x ∈ tsupport (v i) → x ∉ tsupport (v j))
    (hE : ∀ j, Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s)
    (hq : ∀ j, ∫ x, ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s ≤
      ε * ∫ x, ∑ s, v j x s ^ 2) :
    ∃ V : Submodule ℝ ((ι → ℝ) → Finset ι → ℝ), Module.finrank ℝ V = Fintype.card κ ∧
      ∀ φ ∈ V, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
        ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ ε * ∫ x, ∑ s, φ x s ^ 2 := by
  refine ⟨Submodule.span ℝ (Set.range v), finrank_span_eq_card hli, fun φ hφ ↦ ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (∑ j, c j • v j) = fun x ↦ ∑ j, c j • v j x := by
      ext x
      simp [Finset.sum_apply]
    rw [h]
    exact ContDiff.sum fun j _ ↦ (hvC j).const_smul (c j)
  · exact Finset.sum_induction _ HasCompactSupport (fun _ _ h₁ h₂ ↦ h₁.add h₂)
      HasCompactSupport.zero fun j _ ↦ (hvc j).mono (Function.support_const_smul_subset _ _)
  · intro x s hxs
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hxs
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxs
    exact hvm j x s (right_ne_zero_of_mul hj)
  -- At each point at most one `v j` is nonzero, so the squared norm splits like the energy.
  have hsq : ∀ x, ∑ s, (∑ j, c j • v j) x s ^ 2 = ∑ j, c j ^ 2 * ∑ s, v j x s ^ 2 := fun x ↦
    apply_sum_smul_eq_sum_sq_mul_of_notMem_tsupport
      (fun φ : (ι → ℝ) → Finset ι → ℝ ↦ ∑ s, φ x s ^ 2)
      (fun a φ ↦ by simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum])
      (fun φ ψ h ↦ by rw [h.eq_of_nhds]) c (hdisj x)
  have hN : ∀ j, Integrable fun x ↦ c j ^ 2 * ∑ s, v j x s ^ 2 := fun j ↦
    (hvC j).continuous.integrable_mul_sum_sq_of_continuousOn (hvc j) subset_rfl
      continuousOn_const
  rw [integral_congr_ae (Eventually.of_forall fun x ↦
      sum_euclideanWittenLaplacian_sum_smul_mul_of_notMem_tsupport f t c (hdisj x)),
    integral_congr_ae (Eventually.of_forall hsq),
    integral_finsetSum _ fun j _ ↦ (hE j).const_mul _, integral_finsetSum _ fun j _ ↦ hN j,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hq j) (sq_nonneg _)

end Disjoint

end TauCeti
