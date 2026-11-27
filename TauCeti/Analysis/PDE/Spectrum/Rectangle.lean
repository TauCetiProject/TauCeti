/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Box
public import TauCeti.Analysis.PDE.Spectrum.CompleteFamily
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Fourier.SineCosineSeries
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# The mixed eigenvalues of `-Δ` on a rectangle with one Dirichlet side

On the rectangle `Ω = (a₀, b₀) × (a₁, b₁)` of the Euclidean plane (`TauCeti.PDE.boxDomain a b`
with `a b : Fin 2 → ℝ`), take the left side `Γ = {a₀} × (a₁, b₁)` as Dirichlet part. The weak
mixed eigenvalue problem asks for a nonzero `u ∈ H¹_Γ(Ω)`, the space
`TauCeti.W1pVanishingOn` of Sobolev functions vanishing on `Γ`, with

`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(Ω)`.

It imposes `u = 0` on `Γ` and, through the test space, the natural Neumann condition `∂_ν u = 0`
on the other three sides. The problem separates: the eigenvalues are exactly the numbers

`κ = ((2m + 1) π / (2 (b₀ - a₀)))² + (l π / (b₁ - a₁))²`, `m, l ≥ 0`,

with eigenfunctions `sin ((2m + 1) π (x₀ - a₀) / (2 (b₀ - a₀))) cos (l π (x₁ - a₁) / (b₁ - a₁))`,
a quarter-wave sine (Dirichlet at `a₀`, Neumann at `b₀`) times a Neumann cosine.

* Each mode lies in `H¹_Γ(Ω)`: it is the restriction of a function in `H¹₀` of the larger
  rectangle `(a₀, 2b₀ - a₀) × (a₁ - 1, b₁ + 1)` after a cutoff in `x₁`, and that rectangle misses
  `Γ`.
* Each mode is a weak eigenfunction. Against a generator `φ` of `H¹_Γ(Ω)`, a test function whose
  support misses the closed left side, Green's formula on the rectangle, Mathlib's planar
  divergence theorem `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` applied to the flux
  `φ ∇u`, leaves only boundary terms, and each vanishes: `φ` on the left side, the normal
  derivative of the mode on the other three. The identity is closed in `v`, so it extends to all
  of `H¹_Γ(Ω)`.
* The modes are complete in `L²(Ω)`: by Fubini, the coefficients of a function orthogonal to all
  of them are orthogonal to every cosine in `x₁` and vanish, and then its slices are orthogonal to
  every quarter-wave sine in `x₀` (`TauCeti.ae_eq_zero_of_forall_setIntegral_mul_cos_eq_zero`,
  `TauCeti.ae_eq_zero_of_forall_setIntegral_mul_sin_two_mul_add_one_eq_zero` and the slice step
  `TauCeti.ae_eq_zero_prod_of_forall_integral_mul_eq_zero`).
* As the form is symmetric, an eigenfunction for any other `κ` is orthogonal to every mode, hence
  zero (`TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`); and an
  eigenfunction for the least eigenvalue `(π / (2 (b₀ - a₀)))²`, which only the mode `m = l = 0`
  attains, is a multiple of it.

On the unit square with `Γ = {0} × (0, 1)` the least eigenvalue is `π² / 4`, attained only by
`sin (π x₀ / 2)`, and the next one is `5 π² / 4 = (π / 2)² + π²`, from `sin (π x₀ / 2) cos (π x₁)`,
not the second quarter-wave sine with eigenvalue `9 π² / 4`. Counted with multiplicity these are
the first two mixed eigenvalues.

## Main declarations

* `TauCeti.PDE.exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq`: the separated modes are
  weak mixed eigenfunctions.
* `TauCeti.PDE.eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero`: they are complete in
  `L²(Ω)`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left`: the weak mixed
  eigenvalues of `-Δ` on the rectangle with Dirichlet part `Γ`.
* `TauCeti.PDE.exists_value_ae_eq_mul_sin_of_forall_inner_gradient_eq_boxDomain_left`: the least
  of them is simple.
* `TauCeti.PDE.isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left` and
  `TauCeti.PDE.isLeast_inter_Ioi_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left`: on the
  unit square the two least mixed eigenvalues are `π² / 4` and `5 π² / 4`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.5.1 (eigenvalues by separation of
  variables).
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5 (mixed boundary conditions).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a mixed condition in one dimension) and §9.8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open InnerProductSpace _root_.MeasureTheory Set TopologicalSpace Filter
open scoped Real InnerProductSpace Gradient Topology ContDiff Interval Distributions

variable {a b : Fin 2 → ℝ}

/-! ### Integrals over a rectangle -/

/-- The gradient pairing of a separated function `s (x 0) k (x 1)` with `φ` in coordinates. -/
private theorem inner_gradient_mul_eq {s s' k k' : ℝ → ℝ} (hs : ∀ t, HasDerivAt s (s' t) t)
    (hk : ∀ t, HasDerivAt k (k' t) t) (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪∇ (fun y : EuclideanSpace ℝ (Fin 2) => s (y 0) * k (y 1)) x, ∇ φ x⟫_ℝ =
      s' (x 0) * k (x 1) * fderiv ℝ φ x (EuclideanSpace.single 0 1) +
        s (x 0) * k' (x 1) * fderiv ℝ φ x (EuclideanSpace.single 1 1) := by
  have hG : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => s (y 0) * k (y 1))
      (s (x 0) • (k' (x 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) +
        k (x 1) • (s' (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))) x := by
    have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => s (y 0))
        (s' (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) x :=
      (hs (x 0)).comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => k (y 1))
        (k' (x 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) x :=
      (hk (x 1)).comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
    exact h0.mul h1
  simp only [PiLp.inner_apply, Fin.sum_univ_two, gradient_apply_eq_fderiv_apply_single,
    hG.fderiv, RCLike.inner_apply (𝕜 := ℝ), conj_trivial]
  simp only [add_apply, smul_apply, PiLp.proj_apply,
    ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true, PiLp.single_eq_of_ne, PiLp.single_eq_same,
    smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
  ring

/-- The divergence of the flux `φ ∇(s (x 0) k (x 1))` of a separated mode, read on `ℝ × ℝ`: for
`s'' = -c s` and `k'' = -d k` it is `∇(s (x 0) k (x 1)) · ∇φ - (c + d) s (x 0) k (x 1) φ`. -/
private theorem fderiv_flux_add_fderiv_flux {s s' k k' : ℝ → ℝ} {c d : ℝ}
    (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, HasDerivAt s' (-c * s t) t)
    (hk : ∀ t, HasDerivAt k (k' t) t) (hk' : ∀ t, HasDerivAt k' (-d * k t) t)
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : ContDiff ℝ 1 φ) (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => φ (euclideanPlaneCLEquivProd.symm p) * (s' p.1 * k p.2)) p (1, 0) +
        fderiv ℝ (fun p : ℝ × ℝ => φ (euclideanPlaneCLEquivProd.symm p) * (s p.1 * k' p.2)) p
          (0, 1) =
      s' p.1 * k p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 0 1) +
        s p.1 * k' p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 1 1) -
        (c + d) * (s p.1 * k p.2 * φ (euclideanPlaneCLEquivProd.symm p)) := by
  have hφL : HasFDerivAt (fun q => φ (euclideanPlaneCLEquivProd.symm q))
      ((fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p)).comp
        (euclideanPlaneCLEquivProd.symm : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2))) p :=
    ((hφ.differentiable one_ne_zero) (euclideanPlaneCLEquivProd.symm p)).hasFDerivAt.comp p
      euclideanPlaneCLEquivProd.symm.hasFDerivAt
  have hfd : HasFDerivAt (fun p : ℝ × ℝ => φ (euclideanPlaneCLEquivProd.symm p) * (s' p.1 * k p.2))
      _ p :=
    hφL.mul (((hs' p.1).comp_hasFDerivAt p (hasFDerivAt_fst)).mul
      ((hk p.2).comp_hasFDerivAt p (hasFDerivAt_snd)))
  have hgd : HasFDerivAt (fun p : ℝ × ℝ => φ (euclideanPlaneCLEquivProd.symm p) * (s p.1 * k' p.2))
      _ p :=
    hφL.mul (((hs p.1).comp_hasFDerivAt p (hasFDerivAt_fst)).mul
      ((hk' p.2).comp_hasFDerivAt p (hasFDerivAt_snd)))
  rw [hfd.fderiv, hgd.fderiv]
  simp only [euclideanPlaneCLEquivProd_symm_apply, Function.comp_apply, smul_add, add_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, smul_eq_mul, mul_zero, mul_one,
    zero_add, add_zero, EuclideanSpace.toLp_one_zero, EuclideanSpace.toLp_zero_one]
  ring

/-- The two parts of Green's formula for a separated mode, the divergence of the flux
`φ ∇(s (x 0) k (x 1))` in coordinates and the product `(c + d) s (x 0) k (x 1) φ`, are
continuous. -/
private theorem continuous_flux_divergence_and_continuous_mul {s s' k k' : ℝ → ℝ} (c d : ℝ)
    (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : Continuous s') (hk : ∀ t, HasDerivAt k (k' t) t)
    (hk' : Continuous k') {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
      s' (x 0) * k (x 1) * fderiv ℝ φ x (EuclideanSpace.single 0 1) +
        s (x 0) * k' (x 1) * fderiv ℝ φ x (EuclideanSpace.single 1 1) -
        (c + d) * (s (x 0) * k (x 1) * φ x)) ∧
      Continuous fun x : EuclideanSpace ℝ (Fin 2) => (c + d) * (s (x 0) * k (x 1) * φ x) := by
  have hsc : Continuous s := continuous_iff_continuousAt.2 fun t => (hs t).continuousAt
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have (v : EuclideanSpace ℝ (Fin 2)) : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have := hφ.continuous
  have : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 := PiLp.continuous_apply 2 _ 0
  have : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 := PiLp.continuous_apply 2 _ 1
  exact ⟨by fun_prop, by fun_prop⟩

/-- **The divergence theorem for the flux of a separated mode.** Let `s'' = -c s` and
`k'' = -d k` on the line, and let `φ` be of class `C¹` on the plane. If the flux of the vector field
`φ ∇(s (x 0) k (x 1))` through each side of the rectangle `∏ᵢ (aᵢ, bᵢ)` vanishes, then its
divergence `∇(s (x 0) k (x 1)) · ∇φ - (c + d) s (x 0) k (x 1) φ` has integral zero over the
rectangle. -/
private theorem setIntegral_flux_divergence_eq_zero (hab : ∀ i, a i ≤ b i)
    {s s' k k' : ℝ → ℝ} {c d : ℝ}
    (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, HasDerivAt s' (-c * s t) t)
    (hk : ∀ t, HasDerivAt k (k' t) t) (hk' : ∀ t, HasDerivAt k' (-d * k t) t)
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hleft : ∀ t ∈ [[a 1, b 1]], φ (WithLp.toLp 2 ![a 0, t]) * s' (a 0) = 0)
    (hright : ∀ t ∈ [[a 1, b 1]], φ (WithLp.toLp 2 ![b 0, t]) * s' (b 0) = 0)
    (hbot : ∀ t ∈ [[a 0, b 0]], φ (WithLp.toLp 2 ![t, a 1]) * k' (a 1) = 0)
    (htop : ∀ t ∈ [[a 0, b 0]], φ (WithLp.toLp 2 ![t, b 1]) * k' (b 1) = 0) :
    ∫ x in boxDomain a b, (s' (x 0) * k (x 1) * fderiv ℝ φ x (EuclideanSpace.single 0 1) +
      s (x 0) * k' (x 1) * fderiv ℝ φ x (EuclideanSpace.single 1 1) -
      (c + d) * (s (x 0) * k (x 1) * φ x)) = 0 := by
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hsd : Differentiable ℝ s := fun t => (hs t).differentiableAt
  have hs'd : Differentiable ℝ s' := fun t => (hs' t).differentiableAt
  have hkd : Differentiable ℝ k := fun t => (hk t).differentiableAt
  have hk'd : Differentiable ℝ k' := fun t => (hk' t).differentiableAt
  have hsc := hsd.continuous
  have hs'c := hs'd.continuous
  have hkc := hkd.continuous
  have hk'c := hk'd.continuous
  rw [setIntegral_boxDomain_eq_intervalIntegral hab
    (continuous_flux_divergence_and_continuous_mul c d hs hs'c hk hk'c hφ).1]
  -- The two components `φ s' k` and `φ s k'` of the flux, read on `ℝ × ℝ`.
  set f : ℝ × ℝ → ℝ := fun p => φ (euclideanPlaneCLEquivProd.symm p) * (s' p.1 * k p.2)
  set g : ℝ × ℝ → ℝ := fun p => φ (euclideanPlaneCLEquivProd.symm p) * (s p.1 * k' p.2)
  have hdiv (p : ℝ × ℝ) : fderiv ℝ f p (1, 0) + fderiv ℝ g p (0, 1) =
      s' p.1 * k p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 0 1) +
        s p.1 * k' p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 1 1) -
        (c + d) * (s p.1 * k p.2 * φ (euclideanPlaneCLEquivProd.symm p)) :=
    fderiv_flux_add_fderiv_flux hs hs' hk hk' hφ p
  have := euclideanPlaneCLEquivProd.symm.differentiable
  have (v : EuclideanSpace ℝ (Fin 2)) : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have := hφ.continuous
  have hdivc : Continuous fun p : ℝ × ℝ =>
      s' p.1 * k p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 0 1) +
        s p.1 * k' p.2 * fderiv ℝ φ (euclideanPlaneCLEquivProd.symm p) (EuclideanSpace.single 1 1) -
        (c + d) * (s p.1 * k p.2 * φ (euclideanPlaneCLEquivProd.symm p)) := by
    fun_prop
  have hi : IntegrableOn (fun p => fderiv ℝ f p (1, 0) + fderiv ℝ g p (0, 1))
      ([[a 0, b 0]] ×ˢ [[a 1, b 1]]) := by
    simp_rw [hdiv]
    exact hdivc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hgreen := integral2_divergence_prod_of_hasFDerivAt f g (fun p => fderiv ℝ f p)
    (fun p => fderiv ℝ g p) (a 0) (a 1) (b 0) (b 1) (by fun_prop) (by fun_prop)
    (fun p _ => (by fun_prop : DifferentiableAt ℝ f p).hasFDerivAt)
    (fun p _ => (by fun_prop : DifferentiableAt ℝ g p).hasFDerivAt) hi
  -- Each boundary integral vanishes.
  have hz {F : ℝ → ℝ} {u v : ℝ} (h : ∀ t ∈ [[u, v]], F t = 0) : ∫ t in u..v, F t = 0 :=
    intervalIntegral.integral_zero_ae (ae_of_all _ fun t ht => h t (uIoc_subset_uIcc ht))
  rw [hz (F := fun t => g (t, b 1)) fun t ht => by
      simp only [g, euclideanPlaneCLEquivProd_symm_apply]; linear_combination s t * htop t ht,
    hz (F := fun t => g (t, a 1)) fun t ht => by
      simp only [g, euclideanPlaneCLEquivProd_symm_apply]; linear_combination s t * hbot t ht,
    hz (F := fun t => f (b 0, t)) fun t ht => by
      simp only [f, euclideanPlaneCLEquivProd_symm_apply]; linear_combination k t * hright t ht,
    hz (F := fun t => f (a 0, t)) fun t ht => by
      simp only [f, euclideanPlaneCLEquivProd_symm_apply]; linear_combination k t * hleft t ht]
    at hgreen
  simp_rw [hdiv, euclideanPlaneCLEquivProd_symm_apply] at hgreen
  simpa using hgreen

/-- **Green's formula for a separated mode on a rectangle.** Let `s'' = -c s` and `k'' = -d k` on
the line, and let `φ` be of class `C¹` on the plane. If the flux of `s (x 0) k (x 1)` through
each side of the rectangle `∏ᵢ (aᵢ, bᵢ)` vanishes against `φ`, then
`∫ ∇(s (x 0) k (x 1)) · ∇φ = (c + d) ∫ s (x 0) k (x 1) φ` over the rectangle. -/
private theorem setIntegral_inner_gradient_mul_eq (hab : ∀ i, a i ≤ b i)
    {s s' k k' : ℝ → ℝ} {c d : ℝ}
    (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, HasDerivAt s' (-c * s t) t)
    (hk : ∀ t, HasDerivAt k (k' t) t) (hk' : ∀ t, HasDerivAt k' (-d * k t) t)
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hleft : ∀ t ∈ [[a 1, b 1]], φ (WithLp.toLp 2 ![a 0, t]) * s' (a 0) = 0)
    (hright : ∀ t ∈ [[a 1, b 1]], φ (WithLp.toLp 2 ![b 0, t]) * s' (b 0) = 0)
    (hbot : ∀ t ∈ [[a 0, b 0]], φ (WithLp.toLp 2 ![t, a 1]) * k' (a 1) = 0)
    (htop : ∀ t ∈ [[a 0, b 0]], φ (WithLp.toLp 2 ![t, b 1]) * k' (b 1) = 0) :
    ∫ x in boxDomain a b,
        ⟪∇ (fun y : EuclideanSpace ℝ (Fin 2) => s (y 0) * k (y 1)) x, ∇ φ x⟫_ℝ =
      (c + d) * ∫ x in boxDomain a b, s (x 0) * k (x 1) * φ x := by
  have hc := continuous_flux_divergence_and_continuous_mul c d hs
    (continuous_iff_continuousAt.2 fun t => (hs' t).continuousAt) hk
    (continuous_iff_continuousAt.2 fun t => (hk' t).continuousAt) hφ
  have hint {F : EuclideanSpace ℝ (Fin 2) → ℝ} (hF : Continuous F) :
      IntegrableOn F (boxDomain a b) :=
    (hF.continuousOn.integrableOn_compact (isBounded_boxDomain a b).isCompact_closure).mono_set
      subset_closure
  -- Write the gradient pairing as the divergence of the flux plus `(c + d) s k φ`.
  rw [integral_congr_ae (g := fun x =>
      (s' (x 0) * k (x 1) * fderiv ℝ φ x (EuclideanSpace.single 0 1) +
        s (x 0) * k' (x 1) * fderiv ℝ φ x (EuclideanSpace.single 1 1) -
        (c + d) * (s (x 0) * k (x 1) * φ x)) + (c + d) * (s (x 0) * k (x 1) * φ x))
      (ae_of_all _ fun x => by simp only [inner_gradient_mul_eq hs hk φ]; ring),
    integral_add (hint hc.1) (hint hc.2), integral_const_mul,
    setIntegral_flux_divergence_eq_zero hab hs hs' hk hk' hφ hleft hright hbot htop, zero_add]

/-! ### The separated modes with one Dirichlet side -/

/-- **The separated modes lie in `H¹_Γ` of the rectangle.** With `Γ` the left side
`{a₀} × (a₁, b₁)`, the function `sin (c (x₀ - a₀)) cos (d (x₁ - a₁))`, where
`c = (2m + 1) π / (2 (b₀ - a₀))`, is the value of an element of `H¹_Γ` of the rectangle. It is
the restriction of a function in `H¹₀` of the larger rectangle `(a₀, 2b₀ - a₀) × (a₁ - 1, b₁ + 1)`,
cut off in the second variable, which misses `Γ`. -/
private theorem exists_mem_w1pVanishingOnSubmodule_value_ae_eq (hab : ∀ i, a i < b i) (m : ℕ)
    (d : ℝ) :
    ∃ u : W1p volume (boxDomain a b) 2,
      u ∈ w1pVanishingOnSubmodule volume (boxDomain a b) 2
        {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)} ∧
      W1p.value u =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
        fun x => Real.sin ((2 * m + 1) * π / (2 * (b 0 - a 0)) * (x 0 - a 0)) *
          Real.cos (d * (x 1 - a 1)) := by
  set c : ℝ := (2 * m + 1) * π / (2 * (b 0 - a 0)) with hc
  have hba0 : 0 < b 0 - a 0 := sub_pos.2 (hab 0)
  -- A cutoff in `x₁`, equal to one on `[a₁, b₁]` and supported in `(a₁ - 1, b₁ + 1)`.
  obtain ⟨χ, hχc, -, hχ1, -, hχU⟩ := isCompact_Icc.exists_contDiff_cutoff isOpen_Ioo
    (Icc_subset_Ioo (sub_one_lt (a 1)) (lt_add_one (b 1)))
  set a' : Fin 2 → ℝ := ![a 0, a 1 - 1] with ha'
  set b' : Fin 2 → ℝ := ![2 * b 0 - a 0, b 1 + 1] with hb'
  set W : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => Real.sin (c * (x 0 - a 0)) * (Real.cos (d * (x 1 - a 1)) * χ (x 1)) with hW
  have hWc : ContDiff ℝ ∞ W := by
    have : ContDiff ℝ ∞ (WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) :=
      PiLp.contDiff_ofLp
    simp only [hW]
    fun_prop
  have hle : boxDomain a b ≤ boxDomain a' b' := fun x hx => mem_boxDomain.2 fun i => by
    have h := mem_boxDomain.1 hx i
    fin_cases i <;> simp [ha', hb'] at h ⊢ <;> constructor <;> linarith [h.1, h.2]
  have hΓ : Disjoint {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}
      (boxDomain a' b' : Set (EuclideanSpace ℝ (Fin 2))) :=
    disjoint_left.2 fun x hx hx' => by simpa [ha', hx.1] using (mem_boxDomain.1 hx' 0).1
  have hW0 : ∀ x ∈ frontier (boxDomain a' b' : Set (EuclideanSpace ℝ (Fin 2))), W x = 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_eq_endpoint_of_mem_frontier_boxDomain hx
    fin_cases i
    · -- On the vertical sides the sine factor vanishes.
      have hsin : Real.sin (c * (x 0 - a 0)) = 0 := by
        rcases hi with hi | hi <;>
          simp only [ha', hb', Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
        · simp [hi]
        · rw [hi, show c * (2 * b 0 - a 0 - a 0) = (2 * m + 1 : ℕ) * π by
            rw [hc]; push_cast; field_simp; ring]
          exact Real.sin_nat_mul_pi _
      simp [hW, hsin]
    · -- On the horizontal sides the cutoff vanishes.
      have hχ : χ (x 1) = 0 := by
        rcases hi with hi | hi <;> simp only [ha', hb', Fin.mk_one, Fin.isValue,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi <;> rw [hi] <;>
          exact image_eq_zero_of_notMem_tsupport fun h => by simpa using hχU h
      simp [hW, hχ]
  obtain ⟨U, hU0, hUv⟩ := W1p.exists_mem_w1p0Submodule_value_ae_eq_of_contDiff (mu := volume)
    (p := 2) (by simp) (isBounded_boxDomain a' b') (hWc.of_le (by simp)) hW0
  refine ⟨W1p.restrictL hle U, W1p.restrictL_mem_w1pVanishingOnSubmodule hle hΓ hU0, ?_⟩
  filter_upwards [W1p.value_restrictL_ae hle U,
    ae_restrict_of_ae_restrict_of_subset hle hUv,
    ae_restrict_mem (boxDomain a b).isOpen.measurableSet] with x h1 h2 hx
  -- On the rectangle the cutoff is one.
  have hx1 := mem_boxDomain.1 hx 1
  simp only [h1, h2, hW]
  rw [show χ (x 1) = 1 from interior_subset (hχ1 (Ioo_subset_Icc_self hx1)), mul_one]

/-- The closed left side `{a₀} × [a₁, b₁]` lies in the closure of the open left side. -/
private theorem toLp_mem_closure_left (hab : ∀ i, a i < b i) {t : ℝ} (ht : t ∈ Icc (a 1) (b 1)) :
    (WithLp.toLp 2 ![a 0, t] : EuclideanSpace ℝ (Fin 2)) ∈
      closure {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)} := by
  have he : Continuous fun t : ℝ => (WithLp.toLp 2 ![a 0, t] : EuclideanSpace ℝ (Fin 2)) := by
    have : Continuous fun t : ℝ => euclideanPlaneCLEquivProd.symm (a 0, t) :=
      euclideanPlaneCLEquivProd.symm.continuous.comp
        (continuous_const.prodMk continuous_id)
    simpa [euclideanPlaneCLEquivProd_symm_apply] using this
  refine closure_mono ?_ (image_closure_subset_closure_image he
    ⟨t, by rwa [closure_Ioo (hab 1).ne], rfl⟩)
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨by simp, by simpa using hs⟩

/-- A separated mode `sin (c (x₀ - a₀)) cos (d (x₁ - a₁))` with `c = (2m + 1) π / (2 (b₀ - a₀))`
and `sin (d (b₁ - a₁)) = 0` satisfies the weak eigenvalue identity against every generator of
`H¹_Γ`, `Γ = {a₀} × (a₁, b₁)`: the generator vanishes on the closed left side, and the normal
derivative of the mode vanishes on the other three sides. -/
private theorem inner_gradient_restrictL_ofTestFunctionₗ_eq (hab : ∀ i, a i < b i) (m : ℕ)
    {d : ℝ} (hd : Real.sin (d * (b 1 - a 1)) = 0) {u : W1p volume (boxDomain a b) 2}
    (hval : W1p.value u =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
      fun x => Real.sin ((2 * m + 1) * π / (2 * (b 0 - a 0)) * (x 0 - a 0)) *
        Real.cos (d * (x 1 - a 1)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin 2))), ℝ))
    (hφ : Disjoint (tsupport φ) (closure {x : EuclideanSpace ℝ (Fin 2) |
      x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)})) :
    ⟪W1p.gradient u, W1p.gradient (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ =
      (((2 * m + 1) * π / (2 * (b 0 - a 0))) ^ 2 + d ^ 2) *
        ⟪W1p.value u, W1p.value (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ := by
  set c : ℝ := (2 * m + 1) * π / (2 * (b 0 - a 0)) with hc
  have hs' (t : ℝ) : HasDerivAt (fun t => c * Real.cos (c * (t - a 0)))
      (-c ^ 2 * Real.sin (c * (t - a 0))) t := by
    convert (hasDerivAt_cos_mul_sub c (a 0) t).const_mul c using 1
    ring
  have hk' (t : ℝ) : HasDerivAt (fun t => -d * Real.sin (d * (t - a 1)))
      (-d ^ 2 * Real.cos (d * (t - a 1))) t := by
    convert (hasDerivAt_sin_mul_sub d (a 1) t).const_mul (-d) using 1
    ring
  have hGl : LocallyLipschitzOn (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))
      fun x => Real.sin (c * (x 0 - a 0)) * Real.cos (d * (x 1 - a 1)) := by
    have : ContDiff ℝ 1 (WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) :=
      PiLp.contDiff_ofLp
    exact (by fun_prop : ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin 2) =>
      Real.sin (c * (x 0 - a 0)) * Real.cos (d * (x 1 - a 1))).locallyLipschitz.locallyLipschitzOn
  have hgrad : ⟪W1p.gradient u, W1p.gradient (W1p.restrictL le_top
      (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ = ∫ x in boxDomain a b, ⟪∇ (fun x :
        EuclideanSpace ℝ (Fin 2) => Real.sin (c * (x 0 - a 0)) * Real.cos (d * (x 1 - a 1))) x,
        ∇ φ x⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_ae_eq_of_locallyLipschitzOn u hval hGl,
      W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2) le_top φ] with x h1 h2
    rw [h1, h2]
  have hvalue : ⟪W1p.value u, W1p.value (W1p.restrictL le_top
      (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ = ∫ x in boxDomain a b,
        Real.sin (c * (x 0 - a 0)) * Real.cos (d * (x 1 - a 1)) * φ x := by
    rw [W1p.inner_value_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hval, W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
      le_top φ] with x h1 h2
    rw [h1, h2]
  rw [hgrad, hvalue]
  -- The flux through each side vanishes.
  have hcb : Real.cos (c * (b 0 - a 0)) = 0 := by
    have hba0 := (sub_pos.2 (hab 0)).ne'
    rw [show c * (b 0 - a 0) = m * π + π / 2 by rw [hc]; field_simp,
      Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  exact setIntegral_inner_gradient_mul_eq (fun i => (hab i).le)
    (hasDerivAt_sin_mul_sub c (a 0)) hs' (hasDerivAt_cos_mul_sub d (a 1)) hk'
    (φ.contDiff.of_le (by exact_mod_cast le_top))
    (fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hφ.notMem_of_mem_left h
        (toLp_mem_closure_left hab (uIcc_of_le (hab 1).le ▸ ht)), zero_mul])
    (fun t _ => by rw [hcb, mul_zero, mul_zero])
    (fun t _ => by simp)
    (fun t _ => by rw [hd, mul_zero, mul_zero])

/-- **The separated modes are weak mixed eigenfunctions of `-Δ` on a rectangle with one Dirichlet
side.** On the rectangle `(a₀, b₀) × (a₁, b₁)` with the Dirichlet part `Γ = {a₀} × (a₁, b₁)`, for
all `m, l : ℕ` the function

`x ↦ sin ((2m + 1) π (x₀ - a₀) / (2 (b₀ - a₀))) cos (l π (x₁ - a₁) / (b₁ - a₁))`

is the value of some `u ∈ H¹_Γ`, with

`∫ ∇u · ∇v = (((2m + 1) π / (2 (b₀ - a₀)))² + (l π / (b₁ - a₁))²) ∫ u v` for every `v ∈ H¹_Γ`. -/
theorem exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq (hab : ∀ i, a i < b i)
    (m l : ℕ) :
    ∃ u : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
      W1p.value (u : W1p volume (boxDomain a b) 2)
          =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
        (fun x => Real.sin ((2 * m + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
          Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) ∧
      ∀ v : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
        ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
            W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
          (((2 * m + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (l * π / (b 1 - a 1)) ^ 2) *
            ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
              W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ := by
  set d : ℝ := l * π / (b 1 - a 1) with hd
  have hdb : Real.sin (d * (b 1 - a 1)) = 0 := by
    have hba1 := (sub_pos.2 (hab 1)).ne'
    rw [show d * (b 1 - a 1) = l * π by rw [hd]; field_simp]
    exact Real.sin_nat_mul_pi l
  obtain ⟨u, hu, hval⟩ := exists_mem_w1pVanishingOnSubmodule_value_ae_eq hab m d
  refine ⟨⟨u, hu⟩, hval.trans (Filter.EventuallyEq.of_eq (funext fun x => by rw [hd]; ring_nf)),
    fun v => ?_⟩
  -- The identity is a closed condition on `v`, so it suffices to test the generators.
  refine w1pVanishingOnSubmodule_subset_of_isClosed (s := {v | ⟪W1p.gradient u,
      W1p.gradient v⟫_ℝ = (((2 * m + 1) * π / (2 * (b 0 - a 0))) ^ 2 + d ^ 2) *
        ⟪W1p.value u, W1p.value v⟫_ℝ})
    (isClosed_eq (continuous_const.inner (W1p.gradientL.continuous.congr W1p.gradientL_apply))
      (continuous_const.mul (continuous_const.inner
        (W1p.valueL.continuous.congr W1p.valueL_apply))))
    (fun φ hφ => inner_gradient_restrictL_ofTestFunctionₗ_eq hab m hdb hval φ hφ) v.property

/-! ### Completeness of the separated modes -/

/-- **The separated modes are complete in `L²` of the rectangle.** An element of `L²` of the
rectangle `(a₀, b₀) × (a₁, b₁)` orthogonal to every mode
`x ↦ sin ((2m + 1) π (x₀ - a₀) / (2 (b₀ - a₀))) cos (l π (x₁ - a₁) / (b₁ - a₁))`, `m, l ≥ 0`, is
zero: its coefficients in the first variable are orthogonal to every cosine, so they vanish, and
then its slices are orthogonal to every quarter-wave sine. No relation between `a` and `b` is
assumed: an empty side makes the rectangle empty. -/
theorem eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero
    (f : Lp ℝ 2 (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))))
    (h : ∀ m l : ℕ, ∫ x in boxDomain a b, f x *
      (Real.sin ((2 * m + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) = 0) :
    f = 0 := by
  set S : ℕ → ℝ → ℝ := fun m t => Real.sin ((2 * m + 1) * π * (t - a 0) / (2 * (b 0 - a 0)))
  set C : ℕ → ℝ → ℝ := fun l t => Real.cos (l * π * (t - a 1) / (b 1 - a 1))
  set μ : Measure ℝ := volume.restrict (Ioo (a 0) (b 0))
  set ν : Measure ℝ := volume.restrict (Ioo (a 1) (b 1))
  have : IsFiniteMeasure (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isFiniteMeasure_restrict.2 (isBounded_boxDomain a b).measure_lt_top.ne
  have hfi : Integrable f (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))) :=
    (Lp.memLp f).integrable one_le_two
  -- Read `f` on `ℝ × ℝ`, with the product of the restricted Lebesgue measures.
  have hE : MeasurePreserving euclideanPlaneEquivProd
      (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))) (μ.prod ν) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod,
      ← preimage_euclideanPlaneEquivProd_Ioo_prod_Ioo]
    exact measurePreserving_euclideanPlaneEquivProd.restrict_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo)
  have hE' := hE.symm euclideanPlaneEquivProd
  set G : ℝ × ℝ → ℝ := fun p => f (euclideanPlaneEquivProd.symm p)
  have hG : Integrable G (μ.prod ν) :=
    (hE'.integrable_comp_emb euclideanPlaneEquivProd.symm.measurableEmbedding).2 hfi
  have hbdd {F : ℕ → ℝ → ℝ} (hF : ∀ k t, |F k t| ≤ 1) (k : ℕ) (t : ℝ) : ‖F k t‖ ≤ 1 := by
    simpa using hF k t
  have hS1 : ∀ m t, |S m t| ≤ 1 := fun _ _ => Real.abs_sin_le_one _
  have hC1 : ∀ l t, |C l t| ≤ 1 := fun _ _ => Real.abs_cos_le_one _
  have hGS (m : ℕ) : Integrable (fun p : ℝ × ℝ => G p * S m p.1) (μ.prod ν) :=
    hG.mul_bdd (by fun_prop) (ae_of_all _ fun p => hbdd hS1 m p.1)
  -- The coefficients of `G` against the quarter-wave sines are orthogonal to every cosine.
  have hcoef (m : ℕ) : (fun y => ∫ t, G (t, y) * S m t ∂μ) =ᵐ[ν] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_mul_cos_eq_zero (hGS m).integral_prod_right
      fun l => ?_
    have hint : Integrable (fun p : ℝ × ℝ => G p * S m p.1 * C l p.2) (μ.prod ν) :=
      (hGS m).mul_bdd (by fun_prop) (ae_of_all _ fun p => hbdd hC1 l p.2)
    simp_rw [← integral_mul_const]
    rw [← integral_prod_symm _ hint, ← h m l, ← hE'.integral_comp']
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [G, S, C, mul_assoc]
  have hG0 : G =ᵐ[μ.prod ν] 0 := ae_eq_zero_prod_of_forall_integral_mul_eq_zero
    (fun g hg h0 => ae_eq_zero_of_forall_setIntegral_mul_sin_two_mul_add_one_eq_zero hg h0) hG
    hcoef
  refine Lp.ext ?_
  have hGE : G ∘ euclideanPlaneEquivProd = f := funext fun x => by
    simp only [G, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [← hGE]
  exact (hE.quasiMeasurePreserving.ae_eq_comp hG0).trans (Lp.coeFn_zero _ _ _).symm

/-! ### The mixed eigenvalues -/

/-- The value of a mode is not zero: at the point with `x₀ - a₀ = (b₀ - a₀) / (2m + 1)` and
`x₁ - a₁ = (b₁ - a₁) / (2 (l + 1))` both factors are positive. -/
private theorem value_ne_zero_of_value_ae_eq_sin_mul_cos (hab : ∀ i, a i < b i) (m l : ℕ)
    {u : W1p volume (boxDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
      fun x => Real.sin ((2 * m + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) :
    W1p.value u ≠ 0 := by
  intro h0
  have hba0 : 0 < b 0 - a 0 := sub_pos.2 (hab 0)
  have hba1 : 0 < b 1 - a 1 := sub_pos.2 (hab 1)
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
      Real.sin ((2 * m + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1)) := by
    have : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 := PiLp.continuous_apply 2 _ 0
    have : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 1 := PiLp.continuous_apply 2 _ 1
    fun_prop
  have hzero : EqOn (fun x : EuclideanSpace ℝ (Fin 2) =>
      Real.sin ((2 * m + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) 0 (boxDomain a b) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (boxDomain a b).isOpen
      hcont.continuousOn continuousOn_const
    filter_upwards [hu, Lp.coeFn_zero ℝ 2
      (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2))))] with x h1 h2
    rw [← h1, h0, h2]
  -- At `x₀ - a₀ = (b₀ - a₀) / (4m + 2)` and `x₁ - a₁ = (b₁ - a₁) / (2l + 2)` the mode is
  -- `sin (π / 4) cos (l π / (2l + 2)) > 0`.
  have hm : (0 : ℝ) < 2 * (2 * m + 1) := by positivity
  have hl : (0 : ℝ) < 2 * (l + 1) := by positivity
  have hx : (WithLp.toLp 2 ![a 0 + (b 0 - a 0) / (2 * (2 * m + 1)),
      a 1 + (b 1 - a 1) / (2 * (l + 1))] : EuclideanSpace ℝ (Fin 2)) ∈ boxDomain a b := by
    refine mem_boxDomain.2 fun i => ?_
    fin_cases i
    · have : (b 0 - a 0) / (2 * (2 * m + 1)) < b 0 - a 0 :=
        div_lt_self hba0 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      simp only [mem_Ioo, Fin.zero_eta, Matrix.cons_val_zero]
      constructor <;> linarith [div_pos hba0 hm]
    · have : (b 1 - a 1) / (2 * (l + 1)) < b 1 - a 1 :=
        div_lt_self hba1 (by linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
      simp only [mem_Ioo, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      constructor <;> linarith [div_pos hba1 hl]
  have h := hzero hx
  simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  rw [show (2 * m + 1) * π * (a 0 + (b 0 - a 0) / (2 * (2 * m + 1)) - a 0) /
      (2 * (b 0 - a 0)) = π / 4 by field_simp; ring,
    show l * π * (a 1 + (b 1 - a 1) / (2 * (l + 1)) - a 1) / (b 1 - a 1) =
      l / (2 * (l + 1)) * π by field_simp; ring] at h
  refine (mul_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)).ne' h
  · have : 0 ≤ l / (2 * (l + 1)) * π := by positivity
    linarith [Real.pi_pos]
  · have : (l : ℝ) / (2 * (l + 1)) < 1 / 2 := by
      rw [div_lt_iff₀ hl]
      linarith
    nlinarith [Real.pi_pos]

/-- **The weak mixed eigenvalues of `-Δ` on a rectangle with one Dirichlet side.** On the
rectangle `(a₀, b₀) × (a₁, b₁)` with the Dirichlet part `Γ = {a₀} × (a₁, b₁)`, the problem
`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ` has a nonzero solution `u ∈ H¹_Γ`, imposing `u = 0` on
`Γ` and the natural Neumann condition on the other three sides, exactly when

`κ = ((2m + 1) π / (2 (b₀ - a₀)))² + (l π / (b₁ - a₁))²` for some `m, l ≥ 0`.

The form `∫ ∇u · ∇v` is symmetric, so an eigenfunction for any other `κ` is orthogonal in `L²` to
every separated mode, and it vanishes by completeness of the modes. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left (hab : ∀ i, a i < b i)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
      u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
        ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
            W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
            W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ) ↔
      ∃ m l : ℕ, kappa = ((2 * m + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (l * π / (b 1 - a 1)) ^ 2 := by
  choose w hwv hw using exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq hab
  rw [exists_ne_zero_forall_inner_gradient_eq_iff_of_complete
    (fun (ml : ℕ × ℕ) (x : EuclideanSpace ℝ (Fin 2)) =>
      Real.sin ((2 * ml.1 + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (ml.2 * π * (x 1 - a 1) / (b 1 - a 1)))
    (fun ml => w ml.1 ml.2) (fun ml => hwv ml.1 ml.2)
    (fun ml => value_ne_zero_of_value_ae_eq_sin_mul_cos hab ml.1 ml.2 (hwv ml.1 ml.2))
    (fun ml => hw ml.1 ml.2)
    (fun f hf => eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero f fun m l => hf (m, l)),
    Prod.exists]

/-- **The least mixed eigenvalue of the rectangle is simple.** With the Dirichlet part
`Γ = {a₀} × (a₁, b₁)`, every weak mixed eigenfunction `u ∈ H¹_Γ` with the eigenvalue
`(π / (2 (b₀ - a₀)))²` is a multiple of `sin (π (x₀ - a₀) / (2 (b₀ - a₀)))`. Every other separated
mode has a larger eigenvalue, so `u` minus its projection on the first mode is orthogonal to all of
them. -/
theorem exists_value_ae_eq_mul_sin_of_forall_inner_gradient_eq_boxDomain_left
    (hab : ∀ i, a i < b i)
    {u : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}}
    (hu : ∀ v : W1pVanishingOn volume (boxDomain a b) 2 {x | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
      ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
          W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
        (π / (2 * (b 0 - a 0))) ^ 2 * ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
          W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ) :
    ∃ r : ℝ, W1p.value (u : W1p volume (boxDomain a b) 2)
        =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
      fun x => r * Real.sin (π * (x 0 - a 0) / (2 * (b 0 - a 0))) := by
  choose w hwv hw using exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq hab
  set e := W1p.value (w 0 0 : W1p volume (boxDomain a b) 2)
  set f := W1p.value (u : W1p volume (boxDomain a b) 2)
  have he : e ≠ 0 := value_ne_zero_of_value_ae_eq_sin_mul_cos hab 0 0 (hwv 0 0)
  have hκ0 : ((2 * ((0 : ℕ) : ℝ) + 1) * π / (2 * (b 0 - a 0))) ^ 2 +
      ((0 : ℕ) * π / (b 1 - a 1)) ^ 2 = (π / (2 * (b 0 - a 0))) ^ 2 := by
    push_cast
    ring
  -- Every other mode has a larger eigenvalue.
  have hne (m l : ℕ) (hml : (m, l) ≠ (0, 0)) : (π / (2 * (b 0 - a 0))) ^ 2 ≠
      ((2 * m + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (l * π / (b 1 - a 1)) ^ 2 := by
    set c := π / (2 * (b 0 - a 0)) with hc_def
    have hc : 0 < c := div_pos Real.pi_pos (by linarith [hab 0])
    rw [show (2 * (m : ℝ) + 1) * π / (2 * (b 0 - a 0)) = (2 * m + 1) * c by rw [hc_def]; ring,
      mul_pow]
    have : 0 ≤ (l * π / (b 1 - a 1)) ^ 2 := sq_nonneg _
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have hl : l ≠ 0 := fun h => hml (by rw [h])
      have : 0 < (l * π / (b 1 - a 1)) ^ 2 := by
        have : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
        have := div_pos (mul_pos this Real.pi_pos) (sub_pos.2 (hab 1))
        positivity
      push_cast
      intro h
      linarith
    · have hm1 : (3 : ℝ) ≤ 2 * m + 1 := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
      have h9 : 9 ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
      intro h
      nlinarith [mul_pos hc hc]
  set r := ⟪f, e⟫_ℝ / ⟪e, e⟫_ℝ
  refine ⟨r, ?_⟩
  have hfe : f - r • e = 0 := by
    refine eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero _ fun m l => ?_
    rw [W1p.setIntegral_mul_eq_inner_value_of_ae_eq (hwv m l), inner_sub_left,
      real_inner_smul_left]
    by_cases hml : (m, l) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hml
      rw [div_mul_cancel₀ _ (inner_self_ne_zero.2 he), sub_self]
    · have h1 := inner_value_eq_zero_of_forall_inner_gradient_eq (hne m l hml) hu (hw m l)
      have h2 := inner_value_eq_zero_of_forall_inner_gradient_eq
        (hκ0 ▸ hne m l hml) (hw 0 0) (hw m l)
      simp only [f, e] at h1 h2 ⊢
      rw [h1, h2, mul_zero, sub_zero]
  rw [sub_eq_zero.1 hfe]
  filter_upwards [Lp.coeFn_smul r e, hwv 0 0] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  simp

/-! ### The unit square -/

/-- The weak mixed eigenvalues of `-Δ` on the unit square with the Dirichlet part `{0} × (0, 1)`
are the numbers `((2m + 1) π / 2)² + (l π)²`. -/
private theorem setOf_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left :
    {kappa | ∃ u : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2
        {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2 {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1},
        ⟪W1p.gradient (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.gradient (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.value (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ} =
      {kappa | ∃ m l : ℕ, kappa = ((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2} := by
  ext kappa
  have h := exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left
    (a := (0 : Fin 2 → ℝ)) (b := 1) (fun _ => zero_lt_one) (kappa := kappa)
  simp only [Pi.zero_apply, Pi.one_apply, sub_zero, mul_one, div_one] at h
  exact h

/-- **The least mixed eigenvalue of the unit square with one Dirichlet side** is `π² / 4`, with
eigenfunction `sin (π x₀ / 2)`. It lies strictly between the least Neumann eigenvalue `0` and the
least Dirichlet eigenvalue `2 π²`. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left :
    IsLeast {kappa | ∃ u : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2
        {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2 {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1},
        ⟪W1p.gradient (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.gradient (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.value (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ}
      (π ^ 2 / 4) := by
  rw [setOf_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left]
  refine ⟨⟨0, 0, by ring⟩, ?_⟩
  rintro _ ⟨m, l, rfl⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := Real.pi_pos
  nlinarith [sq_nonneg (l * π), mul_nonneg hm (sq_nonneg π), mul_nonneg (mul_nonneg hm hm)
    (sq_nonneg π)]

/-- **The second mixed eigenvalue of the unit square with one Dirichlet side** is `5 π² / 4`,
with eigenfunction `sin (π x₀ / 2) cos (π x₁)`: the least mixed eigenvalue above `π² / 4` comes
from the first cosine in the Neumann direction, not from the second quarter-wave sine, whose
eigenvalue is `9 π² / 4`. -/
theorem isLeast_inter_Ioi_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left :
    IsLeast ({kappa | ∃ u : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2
        {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain (ι := Fin 2) 0 1) 2 {x | x 0 = 0 ∧ x 1 ∈ Ioo 0 1},
        ⟪W1p.gradient (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.gradient (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain (ι := Fin 2) 0 1) 2),
            W1p.value (v : W1p volume (boxDomain (ι := Fin 2) 0 1) 2)⟫_ℝ} ∩ Ioi (π ^ 2 / 4))
      (5 * π ^ 2 / 4) := by
  rw [setOf_exists_ne_zero_forall_inner_gradient_eq_unitSquare_left]
  have hπ := Real.pi_pos
  refine ⟨⟨⟨0, 1, by ring⟩, by rw [mem_Ioi]; nlinarith⟩, ?_⟩
  rintro _ ⟨⟨m, l, rfl⟩, hlt⟩
  rw [mem_Ioi] at hlt
  -- Either `m ≥ 1`, or `m = 0` and then `l ≥ 1` since the eigenvalue exceeds `π² / 4`.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · have h0 : ((2 * ((0 : ℕ) : ℝ) + 1) * π / 2) ^ 2 + (((0 : ℕ) : ℝ) * π) ^ 2 = π ^ 2 / 4 := by
        push_cast
        ring
      exact absurd (h0 ▸ hlt) (lt_irrefl _)
    · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
      push_cast
      nlinarith [mul_le_mul hl1 hl1 zero_le_one (by linarith), sq_nonneg π]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [sq_nonneg (l * π), mul_le_mul hm1 hm1 zero_le_one (by linarith), sq_nonneg π]

end PDE

end TauCeti
