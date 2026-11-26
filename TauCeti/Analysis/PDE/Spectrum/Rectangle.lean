/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Box
public import TauCeti.Analysis.PDE.Spectrum.Mixed
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Fourier.SineCosineSeries
import TauCeti.Analysis.PDE.Spectrum.CompleteFamily
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# The mixed spectrum of `-Δ` on a rectangle with one Dirichlet side

On the rectangle `R = (a 0, b 0) × (a 1, b 1)` of the Euclidean plane (`TauCeti.PDE.boxDomain` on
`Fin 2`), take the Dirichlet condition on the left side `Γ = {a 0} × (a 1, b 1)` and the Neumann
condition on the other three sides. The weak eigenvalue problem is posed on the space
`H¹_Γ(R)` of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`):
`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ(R)`. The test functions are free on the other sides,
which is how they impose the Neumann condition. Separation of variables solves the problem
completely. With `L₀ = b 0 - a 0` and `L₁ = b 1 - a 1`, the eigenfunctions are the products

`sin ((2k + 1) π (x 0 - a 0) / (2 L₀)) cos (l π (x 1 - a 1) / L₁)`, `k, l ≥ 0`,

of the quarter-wave sines of `(a 0, b 0)`, which vanish at `a 0` and have zero derivative at
`b 0`, and the cosines of `(a 1, b 1)`. Their eigenvalues are
`((2k + 1) π / (2 L₀))² + (l π / L₁)²`, and there are no others.

* **The modes are eigenfunctions.** Each mode lies in `H¹_Γ(R)`. On a larger rectangle,
  doubled across the right side and widened vertically, a version of the mode cut off in the
  vertical direction vanishes on the frontier, so it lies in `H¹₀` there; its restriction to `R`
  vanishes on `Γ`, which misses the larger rectangle. Against a generator `φ` of `H¹_Γ(R)`, the
  divergence theorem for `φ ∇u` on the closed rectangle gives `∫ ∇u · ∇φ = κ ∫ u φ`. The boundary
  term vanishes on every side: on the left side `φ` vanishes, and on the other three the normal
  derivative of the mode does. The identity is closed in `v`, so it holds on all of `H¹_Γ(R)`.
* **The modes are complete.** For an element of `L²(R)` orthogonal to every mode, the coefficient
  of each quarter-wave sine in the first variable is orthogonal to every cosine in the second, so
  it vanishes; then almost every slice is orthogonal to every quarter-wave sine
  (`TauCeti.ae_eq_zero_prod_of_forall_integral_mul_eq_zero`).
* **No other eigenvalues.** The form `∫ ∇u · ∇v` is symmetric, so an eigenfunction for a `κ`
  outside the list would be orthogonal to every mode, hence zero
  (`TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_of_complete`).

The least eigenvalue is `(π / (2 L₀))²`, of `sin (π (x 0 - a 0) / (2 L₀))`. On the unit square it
is `π² / 4`, and the next one is `5 π² / 4 = (π / 2)² + π²`, not `9 π² / 4 = (3 π / 2)²`.

## Main declarations

* `TauCeti.PDE.exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq_boxDomain`: the separated
  modes are weak mixed eigenfunctions.
* `TauCeti.PDE.eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero_boxDomain`: the separated
  modes are complete in `L²(R)`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left`: the weak mixed
  eigenvalues are exactly the numbers `((2k + 1) π / (2 L₀))² + (l π / L₁)²`.
* `TauCeti.PDE.isLeast_exists_ne_zero_forall_inner_gradient_eq_boxDomain_left`: the least one is
  `(π / (2 L₀))²`.
* `TauCeti.PDE.isLeast_exists_ne_zero_forall_inner_gradient_eq_boxDomain_zero_one_left`: on the
  unit square the two least eigenvalues are `π² / 4` and `5 π² / 4`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1 (eigenvalues and
  separation of variables).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a Dirichlet condition at one endpoint) and Section 9.8.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Real Set TopologicalSpace
open scoped Gradient Distributions ContDiff

namespace TauCeti.PDE

/-- **Integration by parts against a separated mode on a rectangle.** Let `g₀'' = -κ₀ g₀` and
`g₁'' = -κ₁ g₁` on the line, and let `ψ` be a `C¹` function on the plane vanishing on the left
side of the rectangle `[a, b]`. If `g₀'` vanishes at `b.1` and `g₁'` at `a.2` and `b.2`, then
`∫ ∇(g₀ ⊗ g₁) · ∇ψ = (κ₀ + κ₁) ∫ (g₀ ⊗ g₁) ψ` over the rectangle: by the divergence theorem the
boundary term is the integral of `ψ ∂_ν (g₀ ⊗ g₁)` over the sides, which vanishes on each side. -/
private theorem setIntegral_Icc_mul_fderiv_add_eq {g₀ g₀' g₁ g₁' : ℝ → ℝ} {κ₀ κ₁ : ℝ}
    (h₀ : ∀ t, HasDerivAt g₀ (g₀' t) t) (h₀' : ∀ t, HasDerivAt g₀' (-κ₀ * g₀ t) t)
    (h₁ : ∀ t, HasDerivAt g₁ (g₁' t) t) (h₁' : ∀ t, HasDerivAt g₁' (-κ₁ * g₁ t) t)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a b : ℝ × ℝ} (hab : a ≤ b)
    (hb₀ : g₀' b.1 = 0) (ha₁ : g₁' a.2 = 0) (hb₁ : g₁' b.2 = 0)
    (hψa : ∀ y ∈ Icc a.2 b.2, ψ (a.1, y) = 0) :
    ∫ p in Icc a b, (g₀' p.1 * g₁ p.2 * fderiv ℝ ψ p (1, 0) +
        g₀ p.1 * g₁' p.2 * fderiv ℝ ψ p (0, 1)) =
      (κ₀ + κ₁) * ∫ p in Icc a b, g₀ p.1 * g₁ p.2 * ψ p := by
  have hc₀ : Continuous g₀ := continuous_iff_continuousAt.2 fun t => (h₀ t).continuousAt
  have hc₀' : Continuous g₀' := continuous_iff_continuousAt.2 fun t => (h₀' t).continuousAt
  have hc₁ : Continuous g₁ := continuous_iff_continuousAt.2 fun t => (h₁ t).continuousAt
  have hc₁' : Continuous g₁' := continuous_iff_continuousAt.2 fun t => (h₁' t).continuousAt
  have hψd (p : ℝ × ℝ) : HasFDerivAt ψ (fderiv ℝ ψ p) p :=
    (hψ.differentiable one_ne_zero p).hasFDerivAt
  have := hψ.continuous_fderiv one_ne_zero
  -- The two components `ψ ∂ₓ(g₀ ⊗ g₁)` and `ψ ∂_y(g₀ ⊗ g₁)` of the vector field.
  set f : ℝ × ℝ → ℝ := fun p => ψ p * (g₀' p.1 * g₁ p.2) with hf_def
  set g : ℝ × ℝ → ℝ := fun p => ψ p * (g₀ p.1 * g₁' p.2) with hg_def
  have hf (p : ℝ × ℝ) : HasFDerivAt f _ p :=
    (hψd p).mul (((h₀' p.1).hasFDerivAt.comp p hasFDerivAt_fst).mul
      ((h₁ p.2).hasFDerivAt.comp p hasFDerivAt_snd))
  have hg (p : ℝ × ℝ) : HasFDerivAt g _ p :=
    (hψd p).mul (((h₀ p.1).hasFDerivAt.comp p hasFDerivAt_fst).mul
      ((h₁' p.2).hasFDerivAt.comp p hasFDerivAt_snd))
  have hψc := hψ.continuous
  -- The divergence of `(f, g)` is the integrand minus `(κ₀ + κ₁) g₀ g₁ ψ`.
  set E : ℝ × ℝ → ℝ := fun p => g₀' p.1 * g₁ p.2 * fderiv ℝ ψ p (1, 0) +
      g₀ p.1 * g₁' p.2 * fderiv ℝ ψ p (0, 1) - (κ₀ + κ₁) * (g₀ p.1 * g₁ p.2 * ψ p) with hE
  have hint {F : ℝ × ℝ → ℝ} (hF : Continuous F) : IntegrableOn F (Icc a b) :=
    hF.continuousOn.integrableOn_compact isCompact_Icc
  have hEi : IntegrableOn E (Icc a b) := hint (by fun_prop)
  -- The pointwise divergence identity, proved once from `hf` and `hg`.
  have hdivE (p : ℝ × ℝ) : fderiv ℝ f p (1, 0) + fderiv ℝ g p (0, 1) = E p := by
    rw [(hf p).fderiv, (hg p).fderiv]
    simp only [hE, Function.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g (fderiv ℝ f) (fderiv ℝ g)
    a b hab (by fun_prop) (by fun_prop) (fun p _ => (hf p).differentiableAt.hasFDerivAt)
    (fun p _ => (hg p).differentiableAt.hasFDerivAt)
    (hEi.congr_fun (fun p _ => (hdivE p).symm) measurableSet_Icc)
  rw [setIntegral_congr_fun measurableSet_Icc fun p _ => hdivE p] at hdiv
  -- Every side contributes nothing.
  have hside : ∫ y in a.2..b.2, f (a.1, y) = 0 := by
    refine (intervalIntegral.integral_congr fun y hy => ?_).trans intervalIntegral.integral_zero
    rw [uIcc_of_le hab.2] at hy
    simp [hf_def, hψa y hy]
  simp only [hf_def, hg_def, hb₀, ha₁, hb₁, mul_zero, zero_mul, intervalIntegral.integral_zero,
    sub_zero, zero_add] at hdiv hside
  -- So the divergence `E` integrates to zero.
  have hE0 : ∫ p in Icc a b, E p = 0 := by rwa [hside, sub_zero] at hdiv
  rw [integral_sub (hint (by fun_prop)) (hint (by fun_prop)), integral_const_mul] at hE0
  linarith

/-! ### The rectangle in coordinates -/

/-- The rectangle `boxDomain a b` in the coordinates of `ℝ × ℝ`. -/
private theorem preimage_euclideanPlaneEquivProd_symm_boxDomain (a b : Fin 2 → ℝ) :
    euclideanPlaneEquivProd.symm ⁻¹' (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2))) =
      Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1) := by
  ext p
  simp [Fin.forall_fin_two]

/-- An integral over the rectangle `boxDomain a b` of the plane is an integral over the closed
rectangle `[a 0, b 0] × [a 1, b 1]` of `ℝ × ℝ`. -/
private theorem setIntegral_boxDomain_eq (a b : Fin 2 → ℝ) (F : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∫ x in boxDomain a b, F x =
      ∫ p in Icc (a 0, a 1) (b 0, b 1), F (euclideanPlaneEquivProdL.symm p) := by
  rw [coe_euclideanPlaneEquivProdL_symm, ← measurePreserving_euclideanPlaneEquivProd.symm
    |>.setIntegral_preimage_emb euclideanPlaneEquivProd.symm.measurableEmbedding,
    preimage_euclideanPlaneEquivProd_symm_boxDomain, ← Icc_prod_Icc, Measure.volume_eq_prod]
  exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

/-- In the coordinates of `ℝ × ℝ`, the restriction of the Lebesgue measure to the rectangle is the
product of its restrictions to `(a 0, b 0]` and `(a 1, b 1]`. -/
private theorem measurePreserving_euclideanPlaneEquivProd_symm_restrict (a b : Fin 2 → ℝ) :
    MeasurePreserving euclideanPlaneEquivProd.symm
      ((volume.restrict (Ioc (a 0) (b 0))).prod (volume.restrict (Ioc (a 1) (b 1))))
      (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))) := by
  have h := measurePreserving_euclideanPlaneEquivProd.symm.restrict_preimage
    (boxDomain a b).isOpen.measurableSet
  rw [preimage_euclideanPlaneEquivProd_symm_boxDomain, Measure.volume_eq_prod,
    Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Ioc Ioo_ae_eq_Ioc),
    ← Measure.prod_restrict] at h
  exact h

/-- The gradient pairing of a separated function `g₀ (x 0) g₁ (x 1)` with a `C¹` function `φ`, in
the coordinates of `ℝ × ℝ`. -/
private theorem inner_gradient_euclideanPlaneEquivProdL_symm {g₀ g₀' g₁ g₁' : ℝ → ℝ}
    (h₀ : ∀ t, HasDerivAt g₀ (g₀' t) t) (h₁ : ∀ t, HasDerivAt g₁ (g₁' t) t)
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (p : ℝ × ℝ) :
    ⟪∇ (fun x : EuclideanSpace ℝ (Fin 2) => g₀ (x 0) * g₁ (x 1)) (euclideanPlaneEquivProdL.symm p),
        ∇ φ (euclideanPlaneEquivProdL.symm p)⟫_ℝ =
      g₀' p.1 * g₁ p.2 * fderiv ℝ (φ ∘ euclideanPlaneEquivProdL.symm) p (1, 0) +
        g₀ p.1 * g₁' p.2 * fderiv ℝ (φ ∘ euclideanPlaneEquivProdL.symm) p (0, 1) := by
  set z := euclideanPlaneEquivProdL.symm p
  have hG : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => g₀ (x 0) * g₁ (x 1))
      (g₀ (z 0) • (g₁' (z 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) +
        g₁ (z 1) • (g₀' (z 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))) z := by
    refine (((h₀ (z 0)).comp_hasFDerivAt z
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt).mul ((h₁ (z 1)).comp_hasFDerivAt z
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => ?_)
    simp
  simp only [euclideanPlaneEquivProdL.symm.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, euclideanPlaneEquivProdL_symm_one_zero,
    euclideanPlaneEquivProdL_symm_zero_one]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [gradient_apply_eq_fderiv_apply_single, hG.fderiv, star_trivial]
  simp only [z, euclideanPlaneEquivProdL_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_apply, smul_apply,
    PiLp.proj_apply, PiLp.single_eq_same, ne_eq, one_ne_zero,
    zero_ne_one, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul]
  ring

/-- The points `(a 0, y)`, `y ∈ [a 1, b 1]`, lie in the closure of the left side
`{a 0} × (a 1, b 1)` of the rectangle. -/
private theorem euclideanPlaneEquivProdL_symm_mem_closure_leftSide {a b : Fin 2 → ℝ}
    (hab : a 1 < b 1) {y : ℝ} (hy : y ∈ Icc (a 1) (b 1)) :
    euclideanPlaneEquivProdL.symm (a 0, y) ∈
      closure {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)} := by
  have himage : euclideanPlaneEquivProdL.symm '' ({a 0} ×ˢ Ioo (a 1) (b 1)) ⊆
      {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)} := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨by simpa using hq1, by simpa using hq2⟩
  refine closure_mono himage
    (image_closure_subset_closure_image euclideanPlaneEquivProdL.symm.continuous ?_)
  refine ⟨(a 0, y), ?_, rfl⟩
  rw [closure_prod_eq, closure_singleton, closure_Ioo hab.ne]
  exact ⟨rfl, hy⟩

/-- **A separated mode is a weak mixed eigenfunction on the rectangle.** Let `g₀'' = -κ₀ g₀` and
`g₁'' = -κ₁ g₁` on the line, with `g₀'(b 0) = 0` and `g₁'(a 1) = g₁'(b 1) = 0`, and let
`u ∈ H¹` of the rectangle have value `g₀ (x 0) g₁ (x 1)`. Then `∫ ∇u · ∇v = (κ₀ + κ₁) ∫ u v` for
every `v` vanishing on the left side: for the generators of that space this is the integration by
parts `setIntegral_Icc_mul_fderiv_add_eq`, and the identity is closed in `v`. -/
private theorem inner_gradient_eq_of_mem_w1pVanishingOnSubmodule {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) {g₀ g₀' g₁ g₁' : ℝ → ℝ} {κ₀ κ₁ : ℝ}
    (h₀ : ∀ t, HasDerivAt g₀ (g₀' t) t) (h₀' : ∀ t, HasDerivAt g₀' (-κ₀ * g₀ t) t)
    (h₁ : ∀ t, HasDerivAt g₁ (g₁' t) t) (h₁' : ∀ t, HasDerivAt g₁' (-κ₁ * g₁ t) t)
    (hb₀ : g₀' (b 0) = 0) (ha₁ : g₁' (a 1) = 0) (hb₁ : g₁' (b 1) = 0)
    {u : W1p volume (boxDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
      fun x => g₀ (x 0) * g₁ (x 1))
    {v : W1p volume (boxDomain a b) 2}
    (hv : v ∈ w1pVanishingOnSubmodule volume (boxDomain a b) 2
      {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}) :
    ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = (κ₀ + κ₁) * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => g₀ (x 0) * g₁ (x 1) with hG
  -- A function with `g'' = -κ g` is `C¹`.
  have hC1 {g g' : ℝ → ℝ} {κ : ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
      (hg' : ∀ t, HasDerivAt g' (-κ * g t) t) : ContDiff ℝ 1 g :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hg t).differentiableAt, (funext fun t => (hg t).deriv :
      deriv g = g') ▸ continuous_iff_continuousAt.2 fun t => (hg' t).continuousAt⟩
  have hGc : ContDiff ℝ 1 G :=
    ((hC1 h₀ h₀').comp (contDiff_piLp_apply 2)).mul ((hC1 h₁ h₁').comp (contDiff_piLp_apply 2))
  have hgrad := W1p.gradient_ae_eq_of_locallyLipschitzOn u hu
    hGc.locallyLipschitz.locallyLipschitzOn
  refine inner_gradient_eq_mul_inner_value_of_mem_w1pVanishingOnSubmodule (fun φ hφ => ?_) hv
  have hgφ := W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
    (le_top : boxDomain a b ≤ ⊤) φ
  have hvφ := W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
    (le_top : boxDomain a b ≤ ⊤) φ
  -- Both pairings are integrals over the closed rectangle of `ℝ × ℝ`.
  have hψ : ContDiff ℝ 1 ((φ : EuclideanSpace ℝ (Fin 2) → ℝ) ∘ euclideanPlaneEquivProdL.symm) :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).comp euclideanPlaneEquivProdL.symm.contDiff
  have e1 : ⟪W1p.gradient u, W1p.gradient (W1p.restrictL le_top
      (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ =
        ∫ x in boxDomain a b, ⟪∇ G x, ∇ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) x⟫_ℝ := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hgrad, hgφ] with x h1 h2; rw [h1, h2])
  have e2 : ⟪W1p.value u, W1p.value (W1p.restrictL le_top
      (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ = ∫ x in boxDomain a b, G x * φ x := by
    rw [W1p.inner_value_eq_setIntegral]
    exact integral_congr_ae (by filter_upwards [hu, hvφ] with x h1 h2; rw [h1, h2])
  rw [e1, e2, setIntegral_boxDomain_eq, setIntegral_boxDomain_eq]
  simp_rw [hG, inner_gradient_euclideanPlaneEquivProdL_symm h₀ h₁]
  -- The coordinates of `euclideanPlaneEquivProdL.symm p` are those of `p`.
  have hp (p : ℝ × ℝ) : euclideanPlaneEquivProdL.symm p 0 = p.1 ∧
      euclideanPlaneEquivProdL.symm p 1 = p.2 := by
    simp
  simp only [hp]
  refine setIntegral_Icc_mul_fderiv_add_eq h₀ h₀' h₁ h₁' hψ
    (Prod.mk_le_mk.2 ⟨(hab 0).le, (hab 1).le⟩) hb₀ ha₁ hb₁ fun y hy => ?_
  exact image_eq_zero_of_notMem_tsupport (f := (φ : EuclideanSpace ℝ (Fin 2) → ℝ))
    (x := euclideanPlaneEquivProdL.symm (a 0, y)) fun h =>
      hφ.notMem_of_mem_left h (euclideanPlaneEquivProdL_symm_mem_closure_leftSide (hab 1) hy)

/-- The quarter-wave sine `sin ((2k + 1) π (x 0 - a 0) / (2 (b 0 - a 0)))`, times any function
`χ (x 1)` vanishing at `a 1 - 1` and `b 1 + 1`, vanishes on the frontier of the rectangle
`(a 0, 2 b 0 - a 0) × (a 1 - 1, b 1 + 1)`: the sine vanishes at both vertical sides. -/
private theorem sin_mul_eq_zero_of_mem_frontier_boxDomain {a b : Fin 2 → ℝ} (hab : a 0 < b 0)
    (k : ℕ) {χ : ℝ → ℝ} (hχa : χ (a 1 - 1) = 0) (hχb : χ (b 1 + 1) = 0)
    {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ frontier (boxDomain ![a 0, a 1 - 1] ![2 * b 0 - a 0, b 1 + 1] :
      Set (EuclideanSpace ℝ (Fin 2)))) :
    Real.sin ((2 * k + 1) * π / (2 * (b 0 - a 0)) * (x 0 - a 0)) * χ (x 1) = 0 := by
  have hend := exists_eq_endpoint_of_mem_frontier_boxDomain hx
  rw [Fin.exists_fin_two] at hend
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hend
  rcases hend with (hi | hi) | (hi | hi)
  · simp [hi]
  · have : (2 * k + 1) * π / (2 * (b 0 - a 0)) * (x 0 - a 0) = ((2 * k + 1 : ℕ) : ℝ) * π := by
      rw [hi]
      field_simp [(sub_pos.2 hab).ne']
      push_cast
      ring
    rw [this, Real.sin_nat_mul_pi, zero_mul]
  · simp [hi, hχa]
  · simp [hi, hχb]

/-- `sin ((2k + 1) π (x 0 - a 0) / (2 (b 0 - a 0))) cos (d (x 1 - a 1))` is the value of an element
of `H¹` of the rectangle `boxDomain a b` that vanishes on its left side. It is the restriction of an
element of `H¹₀` of a larger rectangle, doubled to the right and widened vertically, on which the
mode is cut off in the vertical direction. -/
private theorem exists_mem_w1pVanishingOnSubmodule_value_ae_eq_sin_mul_cos {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) (k : ℕ) (d : ℝ) :
    ∃ u : W1p volume (boxDomain a b) 2,
      u ∈ w1pVanishingOnSubmodule volume (boxDomain a b) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)} ∧
      W1p.value u =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
        fun x => Real.sin ((2 * k + 1) * π / (2 * (b 0 - a 0)) * (x 0 - a 0)) *
          Real.cos (d * (x 1 - a 1)) := by
  set c : ℝ := (2 * k + 1) * π / (2 * (b 0 - a 0)) with hc
  have h1 := sub_pos.2 (hab 1)
  -- The vertical cut-off `χ`, equal to one on `[a 1, b 1]` and to zero off `(a 1 - 1, b 1 + 1)`.
  let χ : ContDiffBump ((a 1 + b 1) / 2) :=
    ⟨(b 1 - a 1) / 2, (b 1 - a 1) / 2 + 1, by linarith, by linarith⟩
  have hχ (t : ℝ) (ht : (b 1 - a 1) / 2 + 1 = |t - (a 1 + b 1) / 2|) : χ t = 0 :=
    χ.zero_of_le_dist (by rw [Real.dist_eq]; exact ht.le)
  set W : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => Real.sin (c * (x 0 - a 0)) * (Real.cos (d * (x 1 - a 1)) * χ (x 1)) with hW_def
  have hW : ContDiff ℝ 2 W :=
    (Real.contDiff_sin.comp (contDiff_const.mul ((contDiff_piLp_apply 2).sub contDiff_const))).mul
      ((Real.contDiff_cos.comp (contDiff_const.mul ((contDiff_piLp_apply 2).sub
        contDiff_const))).mul (χ.contDiff.comp (contDiff_piLp_apply 2)))
  set a' : Fin 2 → ℝ := ![a 0, a 1 - 1]
  set b' : Fin 2 → ℝ := ![2 * b 0 - a 0, b 1 + 1]
  have hle : boxDomain a b ≤ boxDomain a' b' := fun x hx => by
    have := mem_boxDomain.1 hx
    refine mem_boxDomain.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · exact ⟨(this 0).1, (this 0).2.trans (by simp [b']; linarith [hab 0])⟩
    · exact ⟨by simp [a']; linarith [(this 1).1], (this 1).2.trans (by simp [b'])⟩
  have hΓ : Disjoint {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}
      (boxDomain a' b' : Set (EuclideanSpace ℝ (Fin 2))) :=
    disjoint_left.2 fun x hx hx' => ((mem_boxDomain.1 hx' 0).1.trans_eq' (by simp [a'])).ne' hx.1
  obtain ⟨u₀, hu₀⟩ := exists_w1p0_value_ae_eq_of_contDiff (mu := volume)
    (isBounded_boxDomain a' b') hW fun x hx => by
      have := sin_mul_eq_zero_of_mem_frontier_boxDomain (hab 0) k
        (χ := fun t => Real.cos (d * (t - a 1)) * χ t)
        (by simp only [hχ (a 1 - 1) (by rw [abs_of_nonpos (by linarith)]; ring), mul_zero])
        (by simp only [hχ (b 1 + 1) (by rw [abs_of_nonneg (by linarith)]; ring), mul_zero]) hx
      simpa [hW_def, hc] using this
  refine ⟨W1p.restrictL hle (u₀ : W1p volume (boxDomain a' b') 2),
    W1p.restrictL_mem_w1pVanishingOnSubmodule hle hΓ u₀.property, ?_⟩
  -- On the rectangle the cut-off is one.
  filter_upwards [W1p.value_restrictL_ae hle (u₀ : W1p volume (boxDomain a' b') 2),
    ae_restrict_of_ae_restrict_of_subset hle hu₀,
    ae_restrict_mem (boxDomain a b).isOpen.measurableSet] with x h1 h2 hx
  have hx1 := mem_boxDomain.1 hx 1
  have hχ1 : χ (x 1) = 1 := χ.one_of_mem_closedBall <| by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    simp only [χ]
    constructor <;> linarith [hx1.1, hx1.2]
  rw [h1, h2, hW_def]
  simp only [hχ1, mul_one]

/-- **The separated modes are weak mixed eigenfunctions of `-Δ` on a rectangle**, with a Dirichlet
condition on the left side `Γ = {a 0} × (a 1, b 1)` and a Neumann condition on the other three
sides. For all `k l : ℕ` the function

`x ↦ sin ((2k + 1) π (x 0 - a 0) / (2 (b 0 - a 0))) cos (l π (x 1 - a 1) / (b 1 - a 1))`

is the value of some `u ∈ H¹_Γ` of the rectangle with

`∫ ∇u · ∇v = (((2k + 1) π / (2 (b 0 - a 0)))² + (l π / (b 1 - a 1))²) ∫ u v`

for every `v ∈ H¹_Γ`. -/
theorem exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq_boxDomain {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) (k l : ℕ) :
    ∃ u : W1pVanishingOn volume (boxDomain a b) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
      W1p.value (u : W1p volume (boxDomain a b) 2)
          =ᵐ[volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))]
        (fun x => Real.sin ((2 * k + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
          Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) ∧
      ∀ v : W1pVanishingOn volume (boxDomain a b) 2
          {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
        ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
            W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
          (((2 * k + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (l * π / (b 1 - a 1)) ^ 2) *
            ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
              W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ := by
  set c₀ : ℝ := (2 * k + 1) * π / (2 * (b 0 - a 0)) with hc₀
  set c₁ : ℝ := l * π / (b 1 - a 1) with hc₁
  have h0 := (sub_pos.2 (hab 0)).ne'
  have h1 := (sub_pos.2 (hab 1)).ne'
  obtain ⟨u, hu, hval⟩ := exists_mem_w1pVanishingOnSubmodule_value_ae_eq_sin_mul_cos hab k c₁
  refine ⟨⟨u, hu⟩, hval.trans (Filter.EventuallyEq.of_eq (funext fun x => ?_)), fun v => ?_⟩
  · rw [hc₁]
    ring_nf
  refine inner_gradient_eq_of_mem_w1pVanishingOnSubmodule hab (κ₀ := c₀ ^ 2) (κ₁ := c₁ ^ 2)
    (g₀' := fun t => c₀ * Real.cos (c₀ * (t - a 0)))
    (g₁' := fun t => -c₁ * Real.sin (c₁ * (t - a 1)))
    (hasDerivAt_sin_mul_sub c₀ (a 0))
    (fun t => by convert (hasDerivAt_cos_mul_sub c₀ (a 0) t).const_mul c₀ using 1; ring)
    (hasDerivAt_cos_mul_sub c₁ (a 1))
    (fun t => by convert (hasDerivAt_sin_mul_sub c₁ (a 1) t).const_mul (-c₁) using 1; ring)
    ?_ (by simp) ?_ hval v.property
  · -- `c₀ (b 0 - a 0) = k π + π / 2`, where the cosine vanishes.
    rw [show c₀ * (b 0 - a 0) = k * π + π / 2 by rw [hc₀]; field_simp,
      Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero]
  · rw [show c₁ * (b 1 - a 1) = l * π by rw [hc₁]; field_simp, Real.sin_nat_mul_pi, mul_zero]

/-- **Completeness of the separated mixed modes on a rectangle.** An element of `L²` of the
rectangle `boxDomain a b` orthogonal to every

`x ↦ sin ((2k + 1) π (x 0 - a 0) / (2 (b 0 - a 0))) cos (l π (x 1 - a 1) / (b 1 - a 1))`,

`k l : ℕ`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero_boxDomain {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i)
    (f : Lp ℝ 2 (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))))
    (h : ∀ k l : ℕ, ∫ x in boxDomain a b, f x *
      (Real.sin ((2 * k + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1))) = 0) :
    f = 0 := by
  set μ₀ := volume.restrict (Ioc (a 0) (b 0))
  set μ₁ := volume.restrict (Ioc (a 1) (b 1))
  set e := euclideanPlaneEquivProd.symm
  have hmp := measurePreserving_euclideanPlaneEquivProd_symm_restrict a b
  have : IsFiniteMeasure (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isFiniteMeasure_restrict.2 (isBounded_boxDomain a b).measure_lt_top.ne
  set s : ℕ → ℝ → ℝ := fun k t => Real.sin ((2 * k + 1) * π * (t - a 0) / (2 * (b 0 - a 0)))
  set c : ℕ → ℝ → ℝ := fun l t => Real.cos (l * π * (t - a 1) / (b 1 - a 1))
  set F : ℝ × ℝ → ℝ := (f : EuclideanSpace ℝ (Fin 2) → ℝ) ∘ e
  have hF : Integrable F (μ₀.prod μ₁) :=
    (hmp.integrable_comp_emb e.measurableEmbedding).2 ((Lp.memLp f).integrable one_le_two)
  have hFs (k : ℕ) : Integrable (fun p : ℝ × ℝ => F p * s k p.1) (μ₀.prod μ₁) :=
    hF.mul_bdd (by fun_prop) (ae_of_all _ fun p => by simpa using Real.abs_sin_le_one _)
  -- For each `k` the coefficient in the first variable is orthogonal to every cosine, so it
  -- vanishes; then every slice is orthogonal to every quarter-wave sine.
  have hH (k : ℕ) : (fun y => ∫ t, F (t, y) * s k t ∂μ₀) =ᵐ[μ₁] 0 := by
    refine ae_eq_zero_of_forall_integral_mul_cos_eq_zero (hFs k).integral_prod_right fun l => ?_
    have hint : Integrable (fun p : ℝ × ℝ => F p * s k p.1 * c l p.2) (μ₀.prod μ₁) :=
      (hFs k).mul_bdd (by fun_prop) (ae_of_all _ fun p => by simpa using Real.abs_cos_le_one _)
    rw [intervalIntegral.integral_of_le (hab 1).le]
    simp_rw [← integral_mul_const]
    rw [← integral_prod_symm _ hint, ← h k l, ← hmp.integral_comp e.measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [F, s, c, Function.comp_apply]
    simp [e, mul_assoc]
  have hF0 : F =ᵐ[μ₀.prod μ₁] 0 :=
    ae_eq_zero_prod_of_forall_integral_mul_eq_zero (fun g hg hgs =>
      ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero hg fun k => by
        rw [intervalIntegral.integral_of_le (hab 0).le]
        exact hgs k) hF hH
  have hfe : F ∘ e.symm = f := funext fun x => by simp [F]
  refine Lp.ext (?_ : (f : EuclideanSpace ℝ (Fin 2) → ℝ) =ᵐ[_] _)
  rw [← hfe]
  exact ((hmp.symm e).quasiMeasurePreserving.ae_eq_comp hF0).trans
    (Lp.coeFn_zero ℝ 2 _).symm

/-- Each separated mixed mode is nonzero somewhere in the rectangle: near the corner `a`, where the
sine factor is `sin (π / 4)` and the argument of the cosine factor lies in `[0, π / 4)`. -/
private theorem exists_mem_boxDomain_sin_mul_cos_ne_zero {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    (k l : ℕ) :
    ∃ x ∈ (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2))),
      Real.sin ((2 * k + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (l * π * (x 1 - a 1) / (b 1 - a 1)) ≠ 0 := by
  have h0 := sub_pos.2 (hab 0)
  have h1 := sub_pos.2 (hab 1)
  have hl : (0 : ℝ) < l + 1 := by positivity
  refine ⟨euclideanPlaneEquivProdL.symm
    (a 0 + (b 0 - a 0) / (2 * (2 * k + 1)), a 1 + (b 1 - a 1) / (4 * (l + 1))), ?_, ?_⟩
  · have hk' : (b 0 - a 0) / (2 * (2 * k + 1)) < b 0 - a 0 :=
      div_lt_self h0 (by nlinarith)
    have hl' : (b 1 - a 1) / (4 * (l + 1)) < b 1 - a 1 := div_lt_self h1 (by nlinarith)
    have hk0 : 0 < (b 0 - a 0) / (2 * (2 * k + 1)) := by positivity
    have hl0 : 0 < (b 1 - a 1) / (4 * (l + 1)) := by positivity
    simp only [SetLike.mem_coe, mem_boxDomain, Fin.forall_fin_two,
      euclideanPlaneEquivProdL_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · simp only [euclideanPlaneEquivProdL_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [show (2 * k + 1) * π * (a 0 + (b 0 - a 0) / (2 * (2 * k + 1)) - a 0) /
        (2 * (b 0 - a 0)) = π / 4 by field_simp; ring,
      show l * π * (a 1 + (b 1 - a 1) / (4 * (l + 1)) - a 1) / (b 1 - a 1) =
        l / (l + 1) * (π / 4) by field_simp; ring]
    have hfrac : (l : ℝ) / (l + 1) ≤ 1 := (div_le_one hl).2 (by linarith)
    have hfrac0 : 0 ≤ (l : ℝ) / (l + 1) := by positivity
    refine mul_ne_zero (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith [Real.pi_pos])).ne' (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup

/-- **The weak mixed eigenvalues of `-Δ` on a rectangle with one Dirichlet side.** On the rectangle
`(a 0, b 0) × (a 1, b 1)`, with a Dirichlet condition on the left side
`Γ = {a 0} × (a 1, b 1)` and a Neumann condition on the other three sides, the problem
`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ` has a nonzero solution `u ∈ H¹_Γ` exactly when

`κ = ((2k + 1) π / (2 (b 0 - a 0)))² + (l π / (b 1 - a 1))²` for some `k l : ℕ`. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume (boxDomain a b) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain a b) 2
          {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
        ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
            W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
            W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ) ↔
      ∃ k l : ℕ, kappa = ((2 * k + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (l * π / (b 1 - a 1)) ^ 2 := by
  choose w hwv hw using exists_value_ae_eq_sin_mul_cos_and_inner_gradient_eq_boxDomain hab
  refine (exists_ne_zero_forall_inner_gradient_eq_iff_of_complete
    (kappas := fun kl : ℕ × ℕ =>
      ((2 * kl.1 + 1) * π / (2 * (b 0 - a 0))) ^ 2 + (kl.2 * π / (b 1 - a 1)) ^ 2)
    (fun (kl : ℕ × ℕ) (x : EuclideanSpace ℝ (Fin 2)) =>
      Real.sin ((2 * kl.1 + 1) * π * (x 0 - a 0) / (2 * (b 0 - a 0))) *
      Real.cos (kl.2 * π * (x 1 - a 1) / (b 1 - a 1)))
    (fun kl => w kl.1 kl.2) (fun kl => hwv kl.1 kl.2) (fun kl hval => ?_) (fun kl => hw kl.1 kl.2)
    fun f hf => eq_zero_of_forall_setIntegral_mul_sin_mul_cos_eq_zero_boxDomain hab f
      fun k l => hf (k, l)).trans Prod.exists
  -- The mode is continuous and nonzero somewhere in the open rectangle, so its value is nonzero.
  obtain ⟨x, hx, hne⟩ := exists_mem_boxDomain_sin_mul_cos_ne_zero hab kl.1 kl.2
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Real.sin ((2 * kl.1 + 1) * π * (y 0 - a 0) / (2 * (b 0 - a 0))) *
        Real.cos (kl.2 * π * (y 1 - a 1) / (b 1 - a 1)) := by fun_prop
  refine hne (Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (boxDomain a b).isOpen
    hc.continuousOn continuousOn_const hx)
  filter_upwards [hwv kl.1 kl.2, Lp.coeFn_zero ℝ 2
    (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ (Fin 2))))] with y h1 h2
  rw [← h1, hval, h2, Pi.zero_apply]

/-- **The first mixed eigenvalue of a rectangle with one Dirichlet side** is
`(π / (2 (b 0 - a 0)))²`, the case `k = l = 0`, with eigenfunction
`sin (π (x 0 - a 0) / (2 (b 0 - a 0)))`. It depends only on the width `b 0 - a 0` in the direction
normal to the Dirichlet side. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_boxDomain_left {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) :
    IsLeast {kappa | ∃ u : W1pVanishingOn volume (boxDomain a b) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain a b) 2
          {x : EuclideanSpace ℝ (Fin 2) | x 0 = a 0 ∧ x 1 ∈ Ioo (a 1) (b 1)},
        ⟪W1p.gradient (u : W1p volume (boxDomain a b) 2),
            W1p.gradient (v : W1p volume (boxDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain a b) 2),
            W1p.value (v : W1p volume (boxDomain a b) 2)⟫_ℝ}
      ((π / (2 * (b 0 - a 0))) ^ 2) := by
  refine ⟨(exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left hab).2 ⟨0, 0, by simp⟩,
    fun kappa hkappa => ?_⟩
  obtain ⟨k, l, rfl⟩ := (exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left hab).1 hkappa
  have h0 := sub_pos.2 (hab 0)
  have hk : π / (2 * (b 0 - a 0)) ≤ (2 * k + 1) * π / (2 * (b 0 - a 0)) := by
    gcongr
    nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have := pow_le_pow_left₀ (by positivity) hk 2
  nlinarith [sq_nonneg (l * π / (b 1 - a 1))]

/-- **The mixed eigenvalues of the unit square with one Dirichlet side.** On `(0, 1)²` with a
Dirichlet condition on the side `{0} × (0, 1)` and a Neumann condition on the other three sides, the
least weak mixed eigenvalue is `π² / 4`, with eigenfunction `sin (π x / 2)`, and the least one
above it is `5 π² / 4 = (π / 2)² + π²`, with eigenfunction `sin (π x / 2) cos (π y)`. It lies below
`9 π² / 4`, the second eigenvalue `(3 π / 2)²` of the interval `(0, 1)` with a Dirichlet condition
at `0`: the Neumann direction contributes an eigenvalue before the Dirichlet one does. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_boxDomain_zero_one_left :
    IsLeast {kappa | ∃ u : W1pVanishingOn volume (boxDomain (0 : Fin 2 → ℝ) 1) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ x 1 ∈ Ioo 0 1}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain (0 : Fin 2 → ℝ) 1) 2
          {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ x 1 ∈ Ioo 0 1},
        ⟪W1p.gradient (u : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2),
            W1p.gradient (v : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2),
            W1p.value (v : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2)⟫_ℝ} (π ^ 2 / 4) ∧
    IsLeast {kappa | (∃ u : W1pVanishingOn volume (boxDomain (0 : Fin 2 → ℝ) 1) 2
        {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ x 1 ∈ Ioo 0 1}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (boxDomain (0 : Fin 2 → ℝ) 1) 2
          {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ x 1 ∈ Ioo 0 1},
        ⟪W1p.gradient (u : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2),
            W1p.gradient (v : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2),
            W1p.value (v : W1p volume (boxDomain (0 : Fin 2 → ℝ) 1) 2)⟫_ℝ) ∧ π ^ 2 / 4 < kappa}
      (5 * π ^ 2 / 4) := by
  have hab : ∀ i, (0 : Fin 2 → ℝ) i < (1 : Fin 2 → ℝ) i := fun _ => zero_lt_one
  have hπ := Real.pi_pos
  -- On the unit square the eigenvalues are `((2k + 1) π / 2)² + (l π)²`.
  have hiff (kappa : ℝ) := exists_ne_zero_forall_inner_gradient_eq_iff_boxDomain_left hab
    (kappa := kappa)
  simp only [Pi.zero_apply, Pi.one_apply, sub_zero, mul_one, div_one] at hiff
  have h5 : π ^ 2 / 4 < 5 * π ^ 2 / 4 := by nlinarith
  have hsin (k : ℕ) : (π / 2) ^ 2 ≤ ((2 * k + 1) * π / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) 2
  refine ⟨⟨(hiff _).2 ⟨0, 0, by push_cast; ring⟩, fun kappa hkappa => ?_⟩,
    ⟨⟨(hiff _).2 ⟨0, 1, by push_cast; ring⟩, h5⟩, fun kappa hk => ?_⟩⟩
  · obtain ⟨k, l, rfl⟩ := (hiff kappa).1 hkappa
    nlinarith [hsin k, sq_nonneg (l * π)]
  obtain ⟨hkappa, hlt⟩ := hk
  obtain ⟨k, l, rfl⟩ := (hiff kappa).1 hkappa
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.cast_zero] at hlt
      nlinarith
    · have hk3 : (3 * π / 2) ^ 2 ≤ ((2 * k + 1) * π / 2) ^ 2 := by
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      nlinarith
  · have hl1 : π ^ 2 ≤ (l * π) ^ 2 := by
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      exact pow_le_pow_left₀ hπ.le (by nlinarith) 2
    nlinarith [hsin k]

end TauCeti.PDE
