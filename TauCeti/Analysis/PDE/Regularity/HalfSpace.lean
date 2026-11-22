/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.W1p.TangentialDerivative
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# `H²` regularity and the global `H²` estimate up to the boundary of a half-space

Let `Ω = {x | c < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, let `a` be a coefficient field that is
uniformly elliptic and bounded on `Ω` and Lipschitz there, and let `u ∈ H¹₀(Ω)` be the weak
solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`.

This file proves that `u ∈ H²(Ω)`: every second weak derivative of `u` exists and lies in
`L²(Ω)`, globally on `Ω` and not only on compactly contained subsets, with the global estimate

`‖∂_w ∂_y u‖_{L²(Ω)} ≤ C ‖y‖ ‖w‖ (‖f‖_{L²(Ω)} + K ‖∇u‖_{L²(Ω)}) / λ`, `C = (n + 2)² (1 + Λ / λ)`,

where `λ ≤ Λ` are the ellipticity constants, `K` is the Lipschitz constant of `a` and `n` is the
dimension. The proof uses only that every translation parallel to the hyperplane `⟪x, ν⟫ = 0`
maps `Ω` into itself, so it also covers slabs and the whole space.

This is the model of global `H²` regularity: flattening the boundary of a `C²` domain turns the
equation in each chart into one on a half-space with Lipschitz coefficients.

The file also takes the first step of higher regularity up to the boundary. When the
coefficients are smooth on a convex such domain, with Lipschitz first derivatives, and `f` has a
weak derivative in `L²(Ω)` along a direction `τ` parallel to the hyperplane, the derivative
`∂_τ u` again has zero boundary values and solves a Dirichlet problem with forcing in `L²(Ω)`, so
the `H²` result applies to it: the third derivatives of `u` with at least one tangential direction
lie in `L²(Ω)`.

## The argument

The proof is the classical one (Evans, §6.3.2, Theorem 4).

* **Tangential directions.** Translations parallel to `∂Ω` map `Ω` onto itself, so the
  difference quotients of `u` in such a direction stay in `H¹₀(Ω)` and are admissible test
  functions. The difference-quotient argument then bounds `∂_τ ∇u` in `L²(Ω)` for every tangential
  `τ`
  (`UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo`).
  Since weak derivatives commute, this gives every second derivative except `∂_ν ∂_ν u`.
* **The normal direction.** Write `Pz = z - (⟪z, ν⟫ / ‖ν‖²) ν` for the projection onto the
  hyperplane and `ν' = ν / ‖ν‖²`. Against a test function `φ`, splitting
  `∇φ = ⟪∇φ, ν⟫ ν' + ∑ᵢ ⟪∇φ, P eᵢ⟫ eᵢ` turns the equation into
  `∫ (∂_ν φ) W + ∑ᵢⱼ ∫ (∂_{P eᵢ} φ) aⁱʲ ∂ⱼu = ∫ f φ`, where `W = ∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu`. By the Leibniz
  rule for Lipschitz factors (`TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`) each `aⁱʲ ∂ⱼu`
  has an `L²` weak derivative in the tangential direction `P eᵢ`, so `W` has an `L²` weak
  derivative in the direction `ν`. Now `W - ∑ⱼ ⟪ν', a eⱼ⟫ ∂_{P eⱼ}u = ⟪ν', a ν'⟫ ∂_ν u`, and
  ellipticity gives `⟪ν', a ν'⟫ ≥ λ ‖ν'‖² > 0`. Multiplying by the Lipschitz function
  `⟪ν', a ν'⟫⁻¹` shows that `∂_ν ∂_ν u` exists in `L²(Ω)`.
* **Tangential derivatives.** Since `u ∈ H²(Ω)`, the difference quotients of `u` along a tangential
  `τ` converge to `∂_τ u` in `H¹(Ω)`, so `∂_τ u ∈ H¹₀(Ω)`
  (`TauCeti.W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn`). Differentiating the equation
  (`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn`) shows that it
  solves `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = ∂_τ f + ∑ᵢⱼ (∂ᵢ∂_τaⁱʲ ∂ⱼu + ∂_τaⁱʲ ∂ᵢ∂ⱼu)`, whose right side lies
  in `L²(Ω)` because the first two derivatives of the coefficients are bounded on `Ω`.

Every step comes with a bound. The Leibniz rule for a bounded Lipschitz factor bounds the
derivative of a product (`TauCeti.HasWeakLineDerivOn.exists_norm_le_lipschitzOnWith_smul`), and
for a unit normal the reciprocal `⟪ν, a ν⟫⁻¹` is bounded by `λ⁻¹` and `K / λ²`-Lipschitz. The
tangential bounds then control `∂_ν ∂_ν u`, and a general pair of directions splits into normal
and tangential parts.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo`: on a
  domain mapped into itself by the translations parallel to a hyperplane, every first derivative
  of the solution has an `L²(Ω)` weak derivative in every direction, with the global estimate.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`: on such a domain the solution
  lies in `W^{2,2}(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_halfSpace` and
  `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace`: the case of a half-space.
* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo`
  and its half-space case
  `UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_halfSpace`: a
  tangential derivative of the solution lies in `H¹₀(Ω)` and solves a Dirichlet problem with
  `L²` forcing.
* `UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_mapsTo` and
  its half-space case
  `UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_halfSpace`,
  both in `TauCeti.PDE`: the third derivatives of the solution with a tangential direction lie in
  `L²(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorems 4 and 5.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace Matrix NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι}

omit [DecidableEq ι] in
/-- Splitting the gradient of a test function `φ` along `ν` and the subspace orthogonal to `ν`
(with `P` the orthogonal projection onto `(ℝ ∙ ν)ᗮ`) turns the energy form `a(u, φ)` into the
sum of the normal term `∫ (∂_ν φ) ∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu` and the tangential terms
`∑ᵢⱼ ∫ (∂_{P eᵢ} φ) aⁱʲ ∂ⱼu`. -/
private theorem setIntegral_energyFormH1_split
    {U : W1p mu Omega 2} {f : Lp ℝ 2 (mu.restrict Omega)}
    (hloc : ∀ p j, LocallyIntegrableOn (fun x => matrixBilinearForm (a x) p
      (EuclideanSpace.basisFun ι ℝ j) •
        ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) Omega mu)
    (hU : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    (φ : 𝓓(Omega, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ∑ j, matrixBilinearForm (a x) ((‖ν‖ ^ 2)⁻¹ • ν) (EuclideanSpace.basisFun ι ℝ j) •
        ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ ∂mu +
      ∑ i, ∑ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x
        ((ℝ ∙ ν)ᗮ.starProjection (EuclideanSpace.basisFun ι ℝ i)) •
        (matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i)
          (EuclideanSpace.basisFun ι ℝ j) •
          ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) ∂mu =
      ∫ x in Omega, f x * φ x ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  set P := (ℝ ∙ ν)ᗮ.starProjection
  have hφ : Differentiable ℝ (φ : EuclideanSpace ℝ ι → ℝ) := φ.contDiff.differentiable (by simp)
  have hW := locallyIntegrableOn_finsetSum Finset.univ fun j _ => hloc ν' j
  have hI : ∀ (v p : EuclideanSpace ℝ ι) j, Integrable (fun x =>
      lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x v •
        (matrixBilinearForm (a x) p (b j) • ⟪W1p.gradient U x, b j⟫_ℝ)) mu :=
    fun v p j => integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc p j) φ v
  have hIW : Integrable (fun x => lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ∑ j, matrixBilinearForm (a x) ν' (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) mu :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn hW φ ν
  have hpt : ∫ x in Omega, matrixBilinearForm (a x)
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient U x) ∂mu =
      ∫ x in Omega, (lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
        ∑ j, matrixBilinearForm (a x) ν' (b j) • ⟪W1p.gradient U x, b j⟫_ℝ +
        ∑ i, ∑ j, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
          (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ)) ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx,
      b.bilin_eq_inner_mul_sum_add_sum_sum (matrixBilinearForm (a x)) ν]
    simp only [inner_gradient_left, (hφ x).lineDeriv_eq_fderiv, smul_eq_mul, Finset.mul_sum,
      ν', P]
  rw [← hU φ, energyFormH1_zero_zero_eq_setIntegral, hpt,
    integral_add hIW.integrableOn (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hI (P (b i)) (b i) j).integrableOn),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hI (P (b i)) (b i) j).integrableOn,
    setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ ν]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hI (P (b i)) (b i) j).integrableOn]
  exact Finset.sum_congr rfl fun j _ =>
    (setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ (P (b i))).symm

omit [DecidableEq ι] in
/-- **The equation gives a normal derivative.** Let `u ∈ H¹(Ω)` satisfy `a(u, φ) = ∫_Ω f φ` for
every test function `φ`, where `a` is the energy form of a coefficient field continuous on `Ω`.
Let `ν' = ν / ‖ν‖²` and let `P` be the orthogonal projection onto the subspace `(ℝ ∙ ν)ᗮ`
orthogonal to `ν`. If each product `aⁱʲ ∂ⱼu` has a weak derivative `Gᵢⱼ` in the tangential
direction `P eᵢ`, then `∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu` has the weak derivative `-(f + ∑ᵢⱼ Gᵢⱼ)` in the
direction `ν`. -/
private theorem hasWeakLineDerivOn_sum_smul_inner_gradient
    (ha : ∀ p q, ContinuousOn (fun x => matrixBilinearForm (a x) p q) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {U : W1p mu Omega 2}
    (hU : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    {G : ι → ι → EuclideanSpace ℝ ι → ℝ}
    (hG : ∀ i j, HasWeakLineDerivOn mu Omega
      (fun x => matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i)
          (EuclideanSpace.basisFun ι ℝ j) • ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
      (G i j) ((ℝ ∙ ν)ᗮ.starProjection (EuclideanSpace.basisFun ι ℝ i))) :
    HasWeakLineDerivOn mu Omega (fun x => ∑ j, matrixBilinearForm (a x) ((‖ν‖ ^ 2)⁻¹ • ν)
        (EuclideanSpace.basisFun ι ℝ j) • ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
      (fun x => -(f x + ∑ i, ∑ j, G i j x)) ν := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  set P := (ℝ ∙ ν)ᗮ.starProjection
  have hΩ : IsLocallyClosed (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.isLocallyClosed
  have hloc : ∀ p j, LocallyIntegrableOn (fun x => matrixBilinearForm (a x) p (b j) •
      ⟪W1p.gradient U x, b j⟫_ℝ) Omega mu := fun p j => by
    have h := ((W1p.hasWeakFDerivOn U).hasWeakLineDerivOn (b j)).locallyIntegrableOn_deriv
    simp only [innerSL_apply_apply] at h
    exact h.continuousOn_smul hΩ (ha p (b j))
  have hW := locallyIntegrableOn_finsetSum Finset.univ fun j _ => hloc ν' j
  have hGloc : LocallyIntegrableOn (fun x => ∑ i, ∑ j, G i j x) Omega mu :=
    locallyIntegrableOn_finsetSum Finset.univ fun i _ =>
      locallyIntegrableOn_finsetSum Finset.univ fun j _ => (hG i j).locallyIntegrableOn_deriv
  have hfloc : LocallyIntegrableOn (f : EuclideanSpace ℝ ι → ℝ) Omega mu :=
    Lp.locallyIntegrableOn f (by norm_num)
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hW, (hfloc.add hGloc).neg,
    fun φ => ?_⟩
  -- The weak equation, with the gradient of `φ` split along `ν` and `(ℝ ∙ ν)ᗮ`.
  have heq := setIntegral_energyFormH1_split (ν := ν) hloc hU φ
  -- Each tangential term moves its derivative onto the coefficient product.
  have htan : ∀ i j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
      (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) ∂mu =
        -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x ∂mu := fun i j =>
    (hG i j).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hIG : ∀ i j, Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x) mu :=
    fun i j => φ.integrable_smul (hG i j).locallyIntegrableOn_deriv
  have hR := TestFunction.neg_integral_smul_neg_add_eq φ hfloc hIG
  rw [hR, ← heq]
  simp only [b, P] at htan ⊢
  simp only [htan, Finset.sum_neg_distrib]
  ring

/-- **A coefficient times a first derivative, with a bound.** Let `a` be uniformly elliptic and
bounded on `Ω` with upper constant `Λ`, with `x ↦ a(x)` `K`-Lipschitz on `Ω` as a bilinear form.
If `∂_z u` has a weak derivative of `L²(Ω)` norm at most `C` in the direction `v`, then so does
`⟪p, a q⟫ ∂_z u`, with norm at most `Λ ‖p‖ ‖q‖ C + K ‖p‖ ‖q‖ ‖v‖ ‖z‖ ‖∇u‖`. -/
private theorem exists_norm_le_hasWeakLineDerivOn_matrixBilinearForm_smul
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) {U : W1p mu Omega 2}
    (p q : EuclideanSpace ℝ ι) {z v : EuclideanSpace ℝ ι} {C : ℝ}
    {G₀ : Lp ℝ 2 (mu.restrict Omega)} (hG₀n : ‖G₀‖ ≤ C)
    (hG₀ : HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, z⟫_ℝ) G₀ v) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ Lam * ‖p‖ * ‖q‖ * C + K * ‖p‖ * ‖q‖ * ‖v‖ * (‖z‖ * ‖W1p.gradient U‖) ∧
        HasWeakLineDerivOn mu Omega
          (fun x => matrixBilinearForm (a x) p q • ⟪W1p.gradient U x, z⟫_ℝ) G v := by
  obtain ⟨G, hGn, hG⟩ := hG₀.exists_norm_le_lipschitzOnWith_smul
    (lipschitzOnWith_matrixBilinearForm_apply_apply hK p q)
    (fun _ hx => ha.norm_point_matrixBilinearForm_le hx p q)
    ((Lp.memLp (W1p.gradient U)).inner_const z) (Lp.memLp G₀)
  refine ⟨G, hGn.trans ?_, hG⟩
  rw [← Lp.norm_def]
  push_cast
  have hc : 0 ≤ Lam * ‖p‖ * ‖q‖ :=
    mul_nonneg (mul_nonneg ha.upper_nonneg (norm_nonneg p)) (norm_nonneg q)
  have hK' : 0 ≤ (K : ℝ) * ‖p‖ * ‖q‖ * ‖v‖ := by positivity
  have hz : (eLpNorm (fun x => ⟪W1p.gradient U x, z⟫_ℝ) 2 (mu.restrict Omega)).toReal ≤
      ‖z‖ * ‖W1p.gradient U‖ := by
    simpa [Lp.norm_def] using ENNReal.toReal_mono (by finiteness)
      (eLpNorm_inner_const_le (𝕜 := ℝ) (μ := mu.restrict Omega) (W1p.gradient U) z 2)
  exact add_le_add (mul_le_mul_of_nonneg_left hG₀n hc) (mul_le_mul_of_nonneg_left hz hK')

/-- **Dividing by the normal coefficient.** Let `‖e‖ = 1` and let `a` be uniformly elliptic and
bounded on `Ω` with constants `λ` and `Λ`, with `x ↦ a(x)` `K`-Lipschitz on `Ω` as a bilinear
form. If `⟪e, a e⟫ ∂_e u` has the weak derivative `R ∈ L²(Ω)` in the direction `e`, then `∂_e u`
has a weak derivative in the direction `e` of `L²(Ω)` norm at most
`‖R‖ / λ + Λ K ‖∇u‖ / λ²`. -/
private theorem exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_matrixBilinearForm_mul
    {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) {U : W1p mu Omega 2}
    {R : Lp ℝ 2 (mu.restrict Omega)}
    (hR : HasWeakLineDerivOn mu Omega
      (fun x => matrixBilinearForm (a x) e e * ⟪W1p.gradient U x, e⟫_ℝ) R e) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ ‖R‖ / lam + Lam * (K * ‖W1p.gradient U‖) / lam ^ 2 ∧
        HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, e⟫_ℝ) G e := by
  have hlam := ha.pos
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hβL := lipschitzOnWith_matrixBilinearForm_apply_apply hK e e
  have hβb : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖matrixBilinearForm (a x) e e‖ ≤ Lam :=
    fun x hx => (ha.norm_point_matrixBilinearForm_le hx e e).trans_eq (by rw [he, mul_one, mul_one])
  have hQm : MemLp (fun x => matrixBilinearForm (a x) e e * ⟪W1p.gradient U x, e⟫_ℝ) 2
      (mu.restrict Omega) :=
    (memLp_top_of_bound (hβL.continuousOn.aestronglyMeasurable hΩm) Lam
      ((ae_restrict_mem hΩm).mono hβb)).mul ((Lp.memLp (W1p.gradient U)).inner_const e)
  have hQn : (eLpNorm (fun x => matrixBilinearForm (a x) e e * ⟪W1p.gradient U x, e⟫_ℝ) 2
      (mu.restrict Omega)).toReal ≤ Lam * ‖W1p.gradient U‖ := by
    rw [← Lp.norm_toLp _ hQm]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hQm.coeFn_toLp, ae_restrict_mem hΩm] with x hx hxΩ
    rw [hx, norm_mul]
    exact mul_le_mul (hβb x hxΩ) ((norm_inner_le_norm _ _).trans_eq (by rw [he, mul_one]))
      (norm_nonneg _) ha.upper_nonneg
  -- Ellipticity: the reciprocal of `⟪e, a e⟫` is bounded by `λ⁻¹` and `K / λ²`-Lipschitz on `Ω`.
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; exact one_ne_zero)
  have hrb : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖(matrixBilinearForm (a x) e e)⁻¹‖ ≤ lam⁻¹ := fun x hx =>
    (norm_inv_matrixBilinearForm_self_le ha hx e).trans_eq (by rw [he, one_pow, mul_one])
  -- Multiplying by `⟪e, a e⟫⁻¹` gives the normal second derivative.
  obtain ⟨G, hGn, hG⟩ := hR.exists_norm_le_lipschitzOnWith_smul
    (lipschitzOnWith_inv_matrixBilinearForm_self ha hK he0) hrb hQm (Lp.memLp R)
  refine ⟨G, hGn.trans ?_, hG.congr_ae ?_⟩
  · have hcoe : ((K * ‖e‖₊ * ‖e‖₊ / (lam * ‖e‖ ^ 2).toNNReal ^ 2 : ℝ≥0) : ℝ) =
        K / lam ^ 2 := by
      push_cast
      rw [Real.coe_toNNReal _ (by positivity), he, one_pow, mul_one, mul_one, mul_one]
    rw [← Lp.norm_def, hcoe, he, mul_one]
    calc lam⁻¹ * ‖R‖ + K / lam ^ 2 * (eLpNorm (fun x => matrixBilinearForm (a x) e e *
          ⟪W1p.gradient U x, e⟫_ℝ) 2 (mu.restrict Omega)).toReal
        ≤ lam⁻¹ * ‖R‖ + K / lam ^ 2 * (Lam * ‖W1p.gradient U‖) := by gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem hΩm] with x hx
    have hne : matrixBilinearForm (a x) e e ≠ 0 := (hlam.trans_le (by
      simpa only [matrixBilinearForm_self, he, one_pow, mul_one] using ha.lower_bound hx e)).ne'
    simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The combination `-(f + ∑ᵢ ∑ⱼ Gᵢⱼ) - ∑ⱼ Tⱼ` of elements of `L²(Ω)` with `‖Gᵢⱼ‖ ≤ D` and
`‖Tⱼ‖ ≤ D` has norm at most `‖f‖ + n (n + 1) D`, and is represented by the pointwise
combination. -/
private theorem exists_norm_le_ae_eq_neg_add_sum_sub_sum (f : Lp ℝ 2 (mu.restrict Omega))
    (G : ι → ι → Lp ℝ 2 (mu.restrict Omega)) (T : ι → Lp ℝ 2 (mu.restrict Omega)) {D : ℝ}
    (hG : ∀ i j, ‖G i j‖ ≤ D) (hT : ∀ j, ‖T j‖ ≤ D) :
    ∃ R : Lp ℝ 2 (mu.restrict Omega),
      ‖R‖ ≤ ‖f‖ + Fintype.card ι * (Fintype.card ι + 1) * D ∧
        (R : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega]
          fun x => -(f x + ∑ i, ∑ j, G i j x) - ∑ j, T j x := by
  refine ⟨-(f + ∑ i, ∑ j, G i j) - ∑ j, T j, ?_, ?_⟩
  · have hs1 : ‖∑ i, ∑ j, G i j‖ ≤ Fintype.card ι * Fintype.card ι * D :=
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => hG i j)).trans_eq (by simp [mul_assoc])
    have hs2 : ‖∑ j, T j‖ ≤ Fintype.card ι * D :=
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun j _ => hT j).trans_eq (by simp)
    calc ‖-(f + ∑ i, ∑ j, G i j) - ∑ j, T j‖ ≤ ‖f + ∑ i, ∑ j, G i j‖ + ‖∑ j, T j‖ := by
          rw [← norm_neg (f + _)]
          exact norm_sub_le _ _
      _ ≤ ‖f‖ + Fintype.card ι * Fintype.card ι * D + Fintype.card ι * D := by
          linarith [norm_add_le f (∑ i, ∑ j, G i j)]
      _ = _ := by ring
  · have hGs : ∀ i, (⇑(∑ j, G i j) : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega]
        fun x => ∑ j, G i j x := fun i => Lp.coeFn_fun_finsetSum _ _
    filter_upwards [Lp.coeFn_sub (-(f + ∑ i, ∑ j, G i j)) (∑ j, T j),
      Lp.coeFn_neg (f + ∑ i, ∑ j, G i j), Lp.coeFn_add f (∑ i, ∑ j, G i j),
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => ∑ j, G i j),
      Lp.coeFn_fun_finsetSum Finset.univ T, ae_all_iff.2 hGs] with x h1 h2 h3 h4 h5 h6
    simp only [h1, Pi.sub_apply, h2, Pi.neg_apply, h3, Pi.add_apply, h4, h5, h6]

/-- **The normal second derivative, with a bound.** Let `‖e‖ = 1`, let `a` be uniformly elliptic
and bounded on `Ω` with constants `λ` and `Λ`, with `x ↦ a(x)` `K`-Lipschitz on `Ω` as a bilinear
form, and let `u ∈ H¹(Ω)` satisfy `a(u, φ) = ∫_Ω f φ` for every test function `φ`. Suppose that
for all `y` and every `τ` orthogonal to `e`, the derivative `∂_y u` has a weak derivative in the
direction `τ` of `L²(Ω)` norm at most `‖y‖ ‖τ‖ M`. Then `∂_e u` has a weak derivative in the
direction `e` of `L²(Ω)` norm at most

`(‖f‖ + n (n + 1) (Λ M + K ‖∇u‖)) / λ + Λ K ‖∇u‖ / λ²`,

where `n` is the dimension. -/
private theorem exists_norm_le_hasWeakLineDerivOn_inner_gradient_normal
    {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {U : W1p mu Omega 2}
    (hU : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    {M : ℝ} (hM : 0 ≤ M)
    (htan : ∀ y τ, ⟪τ, e⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * ‖τ‖ * M ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G τ) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ (‖f‖ + Fintype.card ι * (Fintype.card ι + 1) *
          (Lam * M + K * ‖W1p.gradient U‖)) / lam + Lam * (K * ‖W1p.gradient U‖) / lam ^ 2 ∧
        HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, e⟫_ℝ) G e := by
  set b := EuclideanSpace.basisFun ι ℝ
  -- `P` is the orthogonal projection onto `(ℝ ∙ e)ᗮ`.
  set P := (ℝ ∙ e)ᗮ.starProjection
  set D : ℝ := Lam * M + K * ‖W1p.gradient U‖
  have hν' : (‖e‖ ^ 2)⁻¹ • e = e := by simp [he]
  have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hP : ∀ z, ⟪P z, e⟫_ℝ = 0 := fun z =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ z)
  have hPb : ∀ i, ‖P (b i)‖ ≤ 1 := fun i =>
    (Submodule.norm_starProjection_apply_le _ (b i)).trans_eq (hb i)
  have hgK : 0 ≤ (K : ℝ) * ‖W1p.gradient U‖ := by positivity
  -- The tangential terms `Gᵢⱼ = ∂_{P eᵢ} (aⁱʲ ∂ⱼu)`, each of norm at most `D`.
  choose G hGn hG using fun i j =>
    have h := htan (b j) (P (b i)) (hP (b i))
    exists_norm_le_hasWeakLineDerivOn_matrixBilinearForm_smul ha hK (b i) (b j) (C := M)
      (h.choose_spec.1.trans (by rw [hb, one_mul]; exact mul_le_of_le_one_left hM (hPb i)))
      h.choose_spec.2
  have hGD : ∀ i j, ‖G i j‖ ≤ D := fun i j => (hGn i j).trans (by
    simp only [hb, mul_one, one_mul, D]
    have := mul_le_mul_of_nonneg_left (hPb i) hgK
    linarith)
  -- The terms `Tⱼ = ∂_e (⟪e, a eⱼ⟫ ∂_{P eⱼ}u)`, each of norm at most `D`, where weak derivatives
  -- commute: `∂_e ∂_{P eⱼ}u = ∂_{P eⱼ} ∂_e u`.
  choose T hTn hT using fun j =>
    have h := htan e (P (b j)) (hP (b j))
    exists_norm_le_hasWeakLineDerivOn_matrixBilinearForm_smul ha hK ((‖e‖ ^ 2)⁻¹ • e) (b j)
      (h.choose_spec.1.trans_eq (by rw [he, one_mul]))
      (W1p.hasWeakLineDerivOn_inner_gradient_comm h.choose_spec.2)
  have hTD : ∀ j, ‖T j‖ ≤ D := fun j => (hTn j).trans (by
    simp only [hν']
    simp only [he, hb, mul_one, D]
    have h1 := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hM (hPb j)) ha.upper_nonneg
    have h2 := mul_le_mul_of_nonneg_left (hPb j) hgK
    linarith)
  -- The normal derivative of `W = ∑ⱼ ⟪e, a eⱼ⟫ ∂ⱼu`, from the equation.
  have hW := hasWeakLineDerivOn_sum_smul_inner_gradient
    (fun p q => (lipschitzOnWith_matrixBilinearForm_apply_apply hK p q).continuousOn)
    hU (G := fun i j => G i j) hG
  -- Subtracting the tangential parts leaves `⟪e, a e⟫ ∂_e u`, whose derivative is `R`.
  obtain ⟨R, hRn, hRae⟩ := exists_norm_le_ae_eq_neg_add_sum_sub_sum f G T hGD hTD
  have hR := ((hW.sub (HasWeakLineDerivOn.sum Finset.univ fun j _ => hT j)).congr_ae
    (Eventually.of_forall fun x => b.sum_smul_inner_sub_sum_smul_inner_proj
      (matrixBilinearForm (a x)) e (W1p.gradient U x))).congr_ae_deriv hRae.symm
  rw [hν'] at hR
  obtain ⟨G', hG'n, hG'⟩ :=
    exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_matrixBilinearForm_mul he ha hK hR
  exact ⟨G', hG'n.trans (add_le_add_left (div_le_div_of_nonneg_right hRn ha.pos.le) _), hG'⟩

omit [Fintype ι] [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The combination `t • G₁ + G₂` of elements of `L²(Ω)` has norm at most `‖t‖ ‖G₁‖ + ‖G₂‖`, and is
represented by the pointwise combination. -/
private theorem exists_norm_le_ae_eq_smul_add (t : ℝ) (G₁ G₂ : Lp ℝ 2 (mu.restrict Omega)) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖t‖ * ‖G₁‖ + ‖G₂‖ ∧
      (G : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] fun x => t • G₁ x + G₂ x := by
  refine ⟨t • G₁ + G₂, (norm_add_le _ _).trans_eq (by rw [norm_smul]), ?_⟩
  filter_upwards [Lp.coeFn_add (t • G₁) G₂, Lp.coeFn_smul t G₁] with x h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply]

omit [DecidableEq ι] in
/-- **Second derivatives from the normal and the tangential ones.** Let `‖e‖ = 1` and `0 ≤ M`.
Suppose that `∂_e u` has a weak derivative of `L²(Ω)` norm at most `C` in the direction `e`, and
that for all `y` and every `τ` orthogonal to `e` the derivative `∂_y u` has a weak derivative of
`L²(Ω)` norm at most `‖y‖ ‖τ‖ M` in the direction `τ`. Then for every `y` the derivative `∂_y u`
has a weak derivative of `L²(Ω)` norm at most `‖y‖ (C + M)` in the direction `e`. -/
private theorem exists_norm_le_hasWeakLineDerivOn_inner_gradient_normal_of_tangential
    {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1) {U : W1p mu Omega 2} {C M : ℝ} (hM : 0 ≤ M)
    {Gee : Lp ℝ 2 (mu.restrict Omega)} (hGeen : ‖Gee‖ ≤ C)
    (hGee : HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, e⟫_ℝ) Gee e)
    (htan : ∀ y τ, ⟪τ, e⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * ‖τ‖ * M ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G τ)
    (y : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * (C + M) ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G e := by
  set Py := (ℝ ∙ e)ᗮ.starProjection y
  have hdec : y = ⟪y, e⟫_ℝ • e + Py := by
    rw [real_inner_comm, ← Submodule.starProjection_unit_singleton ℝ he,
      Submodule.starProjection_add_starProjection_orthogonal]
  -- `∂_e ∂_y u = ⟪y, e⟫ ∂_e ∂_e u + ∂_{P y} ∂_e u`, where weak derivatives commute.
  have hPy : ⟪Py, e⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ y)
  have hPyn : ‖Py‖ ≤ ‖y‖ := Submodule.norm_starProjection_apply_le _ y
  obtain ⟨G₁, hG₁n, hG₁⟩ := htan e Py hPy
  have hsplit : ∀ x, ⟪y, e⟫_ℝ * ⟪W1p.gradient U x, e⟫_ℝ + ⟪W1p.gradient U x, Py⟫_ℝ =
      ⟪W1p.gradient U x, y⟫_ℝ := fun x => by
    conv_rhs => rw [hdec]
    rw [inner_add_right, real_inner_smul_right (W1p.gradient U x) e ⟪y, e⟫_ℝ]
  have hye : ‖⟪y, e⟫_ℝ‖ ≤ ‖y‖ := (norm_inner_le_norm y e).trans_eq (by rw [he, mul_one])
  have h1 : ‖G₁‖ ≤ ‖y‖ * M := hG₁n.trans (by
    rw [he, one_mul]
    exact mul_le_mul_of_nonneg_right hPyn hM)
  obtain ⟨G, hGn, hGae⟩ := exists_norm_le_ae_eq_smul_add ⟪y, e⟫_ℝ Gee G₁
  refine ⟨G, hGn.trans ?_, (((hGee.const_smul ⟪y, e⟫_ℝ).add
    (W1p.hasWeakLineDerivOn_inner_gradient_comm hG₁)).congr_ae
      (Eventually.of_forall hsplit)).congr_ae_deriv hGae.symm⟩
  calc ‖⟪y, e⟫_ℝ‖ * ‖Gee‖ + ‖G₁‖ ≤ ‖y‖ * C + ‖y‖ * M := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- **Second derivatives in every pair of directions.** Under the hypotheses of
`exists_norm_le_hasWeakLineDerivOn_inner_gradient_normal_of_tangential`, for all `y` and `w` the
derivative `∂_y u` has a weak derivative of `L²(Ω)` norm at most `‖y‖ ‖w‖ (C + 2 M)` in the
direction `w`: split `w` into its components along `e` and orthogonal to `e`. -/
private theorem exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_normal_of_tangential
    {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1) {U : W1p mu Omega 2} {C M : ℝ} (hM : 0 ≤ M)
    {Gee : Lp ℝ 2 (mu.restrict Omega)} (hGeen : ‖Gee‖ ≤ C)
    (hGee : HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, e⟫_ℝ) Gee e)
    (htan : ∀ y τ, ⟪τ, e⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * ‖τ‖ * M ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G τ)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * ‖w‖ * (C + 2 * M) ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w := by
  set Pw := (ℝ ∙ e)ᗮ.starProjection w
  have hdec : ⟪w, e⟫_ℝ • e + Pw = w := by
    rw [real_inner_comm, ← Submodule.starProjection_unit_singleton ℝ he,
      Submodule.starProjection_add_starProjection_orthogonal]
  obtain ⟨G₁, hG₁n, hG₁⟩ :=
    exists_norm_le_hasWeakLineDerivOn_inner_gradient_normal_of_tangential he hM hGeen hGee htan y
  have hPw : ⟪Pw, e⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ w)
  have hPwn : ‖Pw‖ ≤ ‖w‖ := Submodule.norm_starProjection_apply_le _ w
  obtain ⟨G₂, hG₂n, hG₂⟩ := htan y Pw hPw
  -- `∂_w = ⟪w, e⟫ ∂_e + ∂_{P w}`.
  have hw := (hG₁.smul_direction ⟪w, e⟫_ℝ).add_direction hG₂
  rw [hdec] at hw
  have hwe : ‖⟪w, e⟫_ℝ‖ ≤ ‖w‖ := (norm_inner_le_norm w e).trans_eq (by rw [he, mul_one])
  have h2 : ‖G₂‖ ≤ ‖y‖ * ‖w‖ * M :=
    hG₂n.trans (by gcongr)
  obtain ⟨G, hGn, hGae⟩ := exists_norm_le_ae_eq_smul_add ⟪w, e⟫_ℝ G₁ G₂
  refine ⟨G, hGn.trans ?_, hw.congr_ae_deriv hGae.symm⟩
  calc ‖⟪w, e⟫_ℝ‖ * ‖G₁‖ + ‖G₂‖ ≤ ‖w‖ * (‖y‖ * (C + M)) + ‖y‖ * ‖w‖ * M := by gcongr
    _ = _ := by ring

/-- The constant of the global `H²` estimate: with `M = (F + Kg) / λ`, the bound of the normal
second derivative plus `2 M` is at most `(n + 2)² (1 + Λ / λ) M`. -/
private theorem add_two_mul_le_sq_mul {N lam Lam F Kg : ℝ} (hN : 0 ≤ N) (hlam : 0 < lam)
    (hLam : 0 ≤ Lam) (hF : 0 ≤ F) (hKg : 0 ≤ Kg) :
    (F + N * (N + 1) * (Lam * ((F + Kg) / lam) + Kg)) / lam + Lam * Kg / lam ^ 2 +
        2 * ((F + Kg) / lam) ≤ (N + 2) ^ 2 * (1 + Lam / lam) * ((F + Kg) / lam) := by
  set M := (F + Kg) / lam
  set L := Lam / lam
  have hM : 0 ≤ M := by positivity
  have hL : 0 ≤ L := by positivity
  have hlM : lam * M = F + Kg := mul_div_cancel₀ _ hlam.ne'
  have hLl : L * lam = Lam := div_mul_cancel₀ _ hlam.ne'
  -- `F ≤ λ M` and `K g ≤ λ M`, so the first two terms are at most `M + n (n + 1) (L + 1) M` and
  -- `L M`.
  have h1 : (F + N * (N + 1) * (Lam * M + Kg)) / lam ≤ M + N * (N + 1) * (L + 1) * M := by
    rw [div_le_iff₀ hlam]
    have h3 : N * (N + 1) * (Lam * M + Kg) ≤ N * (N + 1) * (Lam * M + lam * M) := by
      gcongr
      linarith
    have h4 : (M + N * (N + 1) * (L + 1) * M) * lam =
        lam * M + N * (N + 1) * (Lam * M + lam * M) := by rw [← hLl]; ring
    rw [h4]
    linarith
  have h2 : Lam * Kg / lam ^ 2 ≤ L * M := by
    rw [div_le_iff₀ (by positivity)]
    calc Lam * Kg ≤ Lam * (lam * M) := by gcongr; linarith
      _ = L * M * lam ^ 2 := by rw [← hLl]; ring
  nlinarith [mul_nonneg (mul_nonneg hN hM) (_root_.add_nonneg hL zero_le_one)]

/-- **The global `H²` estimate up to the boundary.** Let `ν ≠ 0` and let `Ω` be mapped into
itself by every translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is.
Let `a` be uniformly elliptic and bounded on `Ω` with constants `λ` and `Λ`, with `x ↦ a(x)`
`K`-Lipschitz on `Ω` as a bilinear form, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`. Then for all `y` and `w` the derivative `∂_y u = ⟪∇u, y⟫` has
a weak derivative `∂_w ∂_y u` in the direction `w` that lies in `L²(Ω)`, with

`‖∂_w ∂_y u‖_{L²(Ω)} ≤ (n + 2)² (1 + Λ / λ) ‖y‖ ‖w‖ (‖f‖_{L²(Ω)} + K ‖∇u‖_{L²(Ω)}) / λ`,

where `n` is the dimension. The estimate is global on `Ω`, up to the boundary, and its constant
depends only on `n`, `λ` and `Λ`; no regularity of `∂Ω` is assumed. On the whole space it is
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith`,
with a better constant. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo (hν : ν ≠ 0)
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ (Fintype.card ι + 2) ^ 2 * (1 + Lam / lam) *
          (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) ∧
        HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w := by
  set U : W1p mu Omega 2 := (u : W1p mu Omega 2)
  set M : ℝ := (‖f‖ + K * ‖W1p.gradient U‖) / lam
  have hlam := ha.pos
  have hKg : 0 ≤ (K : ℝ) * ‖W1p.gradient U‖ := by positivity
  have hM : 0 ≤ M := by positivity
  -- The unit normal `e`; the directions orthogonal to `e` are those orthogonal to `ν`.
  set e : EuclideanSpace ℝ ι := ‖ν‖⁻¹ • ν
  have he : ‖e‖ = 1 := norm_smul_inv_norm hν
  have heν : ∀ τ, ⟪τ, e⟫_ℝ = 0 → ⟪τ, ν⟫_ℝ = 0 := fun τ hτ => by
    rw [real_inner_smul_right] at hτ
    exact (mul_eq_zero.1 hτ).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
  -- Tangential directions: the difference-quotient estimate.
  have htan : ∀ y τ, ⟪τ, e⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega), ‖G‖ ≤ ‖y‖ * ‖τ‖ * M ∧
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G τ := fun y τ hτ => by
    obtain ⟨G, hGn, hG⟩ :=
      ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo
        (hΩ τ (heν τ hτ)) hK hu y
    exact ⟨G, hGn.trans_eq (by simp only [M, U]; ring), hG⟩
  -- The normal direction: the equation and ellipticity.
  obtain ⟨Gee, hGeen, hGee⟩ := exists_norm_le_hasWeakLineDerivOn_inner_gradient_normal he ha hK
    hu.energyFormH1_ofTestFunctionₗ hM htan
  -- Every pair of directions.
  obtain ⟨G, hGn, hG⟩ :=
    exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_normal_of_tangential he hM hGeen hGee
      htan y w
  refine ⟨G, hGn.trans ?_, hG⟩
  have hC := add_two_mul_le_sq_mul (N := Fintype.card ι) (by positivity) hlam ha.upper_nonneg
    (norm_nonneg f) hKg
  calc ‖y‖ * ‖w‖ * (_ + 2 * M) ≤ ‖y‖ * ‖w‖ *
        ((Fintype.card ι + 2) ^ 2 * (1 + Lam / lam) * M) := by gcongr
    _ = _ := by simp only [M]; ring

/-- **`H²` regularity up to the boundary.** Let `ν ≠ 0` and let `Ω` be mapped into itself by every
translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is. Let `a` be
uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form, and
let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`, that is, of the
Dirichlet problem with zero boundary values. Then `u` is the first-order part of an element of
`W^{2,2}(Ω)`: its second weak derivatives lie in `L²(Ω)` up to the boundary. The quantitative
form is `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo (hν : ν ≠ 0)
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp mu Omega 2 2, Wkp.lowerOrder 1 U = (u : W1p mu Omega 2) :=
  W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun _ _ => by
      obtain ⟨G, -, hG⟩ := ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo hν hΩ hK hu _ _
      exact ⟨G, hG⟩

/-- **The global `H²` estimate up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}`
with `ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω` with constants `λ` and `Λ`, with
`x ↦ a(x)` `K`-Lipschitz on `Ω` as a bilinear form, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`. Then for all `y` and `w` the derivative `∂_y u = ⟪∇u, y⟫` has
a weak derivative `∂_w ∂_y u` in the direction `w` that lies in `L²(Ω)`, with

`‖∂_w ∂_y u‖_{L²(Ω)} ≤ (n + 2)² (1 + Λ / λ) ‖y‖ ‖w‖ (‖f‖_{L²(Ω)} + K ‖∇u‖_{L²(Ω)}) / λ`,

where `n` is the dimension. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ (Fintype.card ι + 2) ^ 2 * (1 + Lam / lam) *
          (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) ∧
        HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w :=
  ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo hν
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK hu y w

/-- **`H²` regularity up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a
bilinear form, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with
`f ∈ L²(Ω)`, that is, of the Dirichlet problem with zero boundary values. Then `u` is the
first-order part of an element of `W^{2,2}(Ω)`: its second weak derivatives lie in `L²(Ω)` up to
the boundary. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp mu Omega 2 2, Wkp.lowerOrder 1 U = (u : W1p mu Omega 2) :=
  ha.exists_lowerOrder_eq_of_mapsTo hν
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK hu

omit [DecidableEq ι] in
/-- The forcing term `g + ∑ᵢⱼ (∂ᵢ∂_τaⁱʲ ∂ⱼu + ∂_τaⁱʲ ∂ᵢ∂ⱼu)` of the equation differentiated along
`τ` lies in `L²(Ω)` when the first two derivatives of the coefficients are bounded on `Ω`, given
by the Lipschitz bounds on `a` and on the first derivatives of its entries. Here `∂ᵢ∂ⱼu` is
`⟪∇(D j), eᵢ⟫` for given `D j ∈ H¹(Ω)`. -/
private theorem memLp_add_sum_sum_fderiv_mul_inner_gradient
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    (g : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) (D : ι → W1p mu Omega 2)
    (τ : EuclideanSpace ℝ ι) :
    MemLp (fun x => g x + ∑ i, ∑ j,
      (fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (EuclideanSpace.basisFun ι ℝ i) *
          ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
        fderiv ℝ (fun y => a y i j) x τ * ⟪W1p.gradient (D j) x, EuclideanSpace.basisFun ι ℝ i⟫_ℝ))
      2 (mu.restrict Omega) := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- A coefficient continuous and bounded on `Ω` times an `L²(Ω)` function lies in `L²(Ω)`.
  have hmul : ∀ {c h : EuclideanSpace ℝ ι → ℝ} (M : ℝ), ContinuousOn c Omega →
      (∀ x ∈ Omega, ‖c x‖ ≤ M) → MemLp h 2 (mu.restrict Omega) →
      MemLp (fun x => c x * h x) 2 (mu.restrict Omega) := fun M hc hcM hh =>
    hh.of_le_mul ((hc.aestronglyMeasurable hΩm).mul hh.aestronglyMeasurable)
      ((ae_restrict_mem hΩm).mono fun x hx => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcM x hx) (norm_nonneg _))
  -- The entries of `a` are `K`-Lipschitz on `Ω`, and their first derivatives `K'`-Lipschitz.
  have hentry : ∀ i j, LipschitzOnWith K (fun x => a x i j) Omega := fun i j => by
    simpa [b, matrixBilinearForm_apply, b.orthonormal.1 i, b.orthonormal.1 j] using
      lipschitzOnWith_matrixBilinearForm_apply_apply hK (b i) (b j)
  have hd1 : ∀ i j, ∀ x ∈ Omega, ‖fderiv ℝ (fun y => a y i j) x τ‖ ≤ K * ‖τ‖ :=
    fun i j x hx => (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) (hentry i j))
      (norm_nonneg τ))
  have hd2 : ∀ i j, ∀ x ∈ Omega, ‖fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (b i)‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ τ‖₊ * K' := fun i j x hx => by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [b.orthonormal.1 i, mul_one]
    exact norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx)
      ((ContinuousLinearMap.apply ℝ ℝ τ).lipschitzWith.comp_lipschitzOnWith (hK' i j))
  -- The derivatives of the coefficients are continuous on `Ω`.
  have hc1 : ∀ i j, ContinuousOn (fun x => fderiv ℝ (fun y => a y i j) x τ) Omega := fun i j =>
    ((hsmooth i j).continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply
      continuousOn_const
  have hc2 : ∀ i j,
      ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (b i))
        Omega := fun i j =>
    ((((hsmooth i j).fderiv_of_isOpen (m := ∞) Omega.isOpen (by simp)).clm_apply
      contDiffOn_const).continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply
        continuousOn_const
  refine (Lp.memLp g).add (memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (hmul _ (hc2 i j) (hd2 i j) ((Lp.memLp _).inner_const _)).add
      (hmul _ (hc1 i j) (hd1 i j) ((Lp.memLp _).inner_const _)))

/-- **The tangential derivative solves the differentiated Dirichlet problem.** Let `ν ≠ 0` and let
`Ω` be convex and mapped into itself by every translation orthogonal to `ν`, as a half-space
`{x | c < ⟪x, ν⟫}` or a slab is. Let `a` be uniformly elliptic and bounded on `Ω`, with entries
smooth on `Ω`, `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form and the first derivatives of its
entries Lipschitz on `Ω`. Let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, and let `τ`
be orthogonal to `ν`, a tangential direction, along which `f ∈ L²(Ω)` has a weak derivative in
`L²(Ω)`. Then the weak derivative `∂_τ u` lies in `H¹₀(Ω)` and is itself a weak solution of a
Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = F` for some `F ∈ L²(Ω)`. No regularity of `∂Ω` is
assumed. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo
    (hν : ν ≠ 0) (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {f g : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0)
    (hf : HasWeakLineDerivOn mu Omega f g τ) :
    ∃ (w : W1p0 mu Omega 2) (F : Lp ℝ 2 (mu.restrict Omega)),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value (w : W1p mu Omega 2))
        τ ∧ IsWeakSolutionDirichlet a 0 0 F w := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- `u ∈ H²(Ω)`, so its first derivatives lie in `H¹(Ω)`.
  obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_mapsTo hν hΩ hK hu
  have hder : ∀ v, ∃ d : W1p mu Omega 2,
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value d) v := fun v => by
    obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 U v
    rw [Wkp.value_succ, hU, Wkp.value_one, Wkp.value_one (u : W1p mu Omega 2)] at hd
    exact ⟨d, hd⟩
  choose D hD using fun j => hder (b j)
  obtain ⟨d, hd⟩ := hder τ
  -- The tangential derivative has zero boundary values.
  have hmem : d ∈ w1p0Submodule mu Omega 2 :=
    W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (by simp) hΩc (hΩ τ hτ) b u.property hD hd
  -- The forcing term of the differentiated equation lies in `L²(Ω)`.
  set Fn : EuclideanSpace ℝ ι → ℝ := fun x => g x + ∑ i, ∑ j,
    (fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (b i) *
        ⟪W1p.gradient (u : W1p mu Omega 2) x, b j⟫_ℝ +
      fderiv ℝ (fun y => a y i j) x τ * ⟪W1p.gradient (D j) x, b i⟫_ℝ)
  have hFn : MemLp Fn 2 (mu.restrict Omega) :=
    memLp_add_sum_sum_fderiv_mul_inner_gradient hK hsmooth hK' g (u : W1p mu Omega 2) D τ
  refine ⟨⟨d, hmem⟩, hFn.toLp Fn, hd, ?_⟩
  -- Bounded coefficients make the energy form continuous, so testing against test functions
  -- suffices.
  have hcoeff := memLp_energyIntegrand_of_bounds (mu := mu) (Omega := Omega) (b := 0) (c := 0)
    (beta := 0) (gamma := 0) ha.upper_nonneg
    (ContinuousOn.aestronglyMeasurable (β := ι → ι → ℝ) (continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun j => (hsmooth i j).continuousOn) hΩm)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  refine (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2 fun φ => ?_
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn
    (fun i j => (hsmooth i j).of_le (by simp)) hu.energyFormH1_ofTestFunctionₗ hd hD hf φ]
  exact integral_congr_ae (hFn.coeFn_toLp.mono fun x hx => congrArg (· * φ x) hx.symm)

/-- **The tangential derivative solves the differentiated Dirichlet problem on a half-space.** Let
`Ω = {x | c < ⟪x, ν⟫}` with `ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with entries
smooth on `Ω`, `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form and the first derivatives of its
entries Lipschitz on `Ω`, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`. If `τ` is
parallel to the boundary hyperplane and `f ∈ L²(Ω)` has a weak derivative in `L²(Ω)` along `τ`,
then `∂_τ u ∈ H¹₀(Ω)` is a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = F` for some `F ∈ L²(Ω)`. This is
the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo`.
-/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_halfSpace
    (hν : ν ≠ 0) (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {f g : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0)
    (hf : HasWeakLineDerivOn mu Omega f g τ) :
    ∃ (w : W1p0 mu Omega 2) (F : Lp ℝ 2 (mu.restrict Omega)),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value (w : W1p mu Omega 2))
        τ ∧ IsWeakSolutionDirichlet a 0 0 F w :=
  ha.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo hν
    (TauCeti.convex_of_halfSpace hΩ) (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK
    hsmooth hK' hu hτ hf

/-- **Third derivatives with a tangential direction.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo`,
the weak derivative `∂_τ u ∈ H¹₀(Ω)` of the solution along a tangential direction `τ` has second
weak derivatives in `L²(Ω)` up to the boundary: for all `y` and `z`, `∂_y ∂_τ u = ⟪∇(∂_τ u), y⟫`
has a weak derivative in the direction `z` that lies in `L²(Ω)`. These are the third derivatives
of `u` with at least one tangential direction. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_mapsTo
    (hν : ν ≠ 0) (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {f g : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0)
    (hf : HasWeakLineDerivOn mu Omega f g τ) :
    ∃ w : W1p0 mu Omega 2,
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value (w : W1p mu Omega 2))
        τ ∧ ∀ y z : EuclideanSpace ℝ ι, ∃ G : Lp ℝ 2 (mu.restrict Omega),
          HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (w : W1p mu Omega 2) x, y⟫_ℝ)
            G z := by
  obtain ⟨w, _F, hw, hwsol⟩ := ha.exists_hasWeakLineDerivOn_and_isWeakSolutionDirichlet_of_mapsTo
    hν hΩc hΩ hK hsmooth hK' hu hτ hf
  exact ⟨w, hw, fun y z =>
    (ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo hν hΩ hK hwsol y z).imp
      fun _ h => h.2⟩

/-- **Third derivatives with a tangential direction up to the boundary of a half-space.** Let
`Ω = {x | c < ⟪x, ν⟫}` with `ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with entries
smooth on `Ω`, `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form and the first derivatives of its
entries Lipschitz on `Ω`, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`. If `τ` is
parallel to the boundary hyperplane and `f ∈ L²(Ω)` has a weak derivative `g ∈ L²(Ω)` along `τ`,
then `∂_τ u ∈ H¹₀(Ω)` and its second weak derivatives lie in `L²(Ω)`. This is the half-space
case of `UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_mapsTo`.
-/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_halfSpace
    (hν : ν ≠ 0) (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {f g : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0)
    (hf : HasWeakLineDerivOn mu Omega f g τ) :
    ∃ w : W1p0 mu Omega 2,
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value (w : W1p mu Omega 2))
        τ ∧ ∀ y z : EuclideanSpace ℝ ι, ∃ G : Lp ℝ 2 (mu.restrict Omega),
          HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (w : W1p mu Omega 2) x, y⟫_ℝ)
            G z :=
  ha.exists_hasWeakLineDerivOn_and_hasWeakLineDerivOn_gradient_of_mapsTo hν
    (TauCeti.convex_of_halfSpace hΩ) (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK
    hsmooth hK' hu hτ hf

end PDE

end TauCeti
