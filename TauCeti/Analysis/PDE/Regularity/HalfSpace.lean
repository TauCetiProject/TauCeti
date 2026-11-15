/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# `H²` regularity up to the boundary of a half-space

Let `Ω = {x | c < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, let `a` be a coefficient field that is
uniformly elliptic and bounded on `Ω` and Lipschitz there, and let `u ∈ H¹₀(Ω)` be the weak
solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`.

This file proves that `u ∈ H²(Ω)`: every second weak derivative of `u` exists and lies in
`L²(Ω)`, globally on `Ω` and not only on compactly contained subsets. The proof uses only that
every translation parallel to the hyperplane `⟪x, ν⟫ = 0` maps `Ω` into itself, so it also covers
slabs and the whole space.

This is the model of global `H²` regularity: flattening the boundary of a `C²` domain turns the
equation in each chart into one on a half-space with Lipschitz coefficients.

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

## Tangential derivatives

The first step towards higher regularity up to the boundary (Evans, §6.3.2, Theorem 5) is that
the tangential derivatives of the solution solve the same kind of problem. Let `a` also be smooth
on `Ω`, with first derivatives Lipschitz there, and let `f` have a weak derivative `g ∈ L²(Ω)` in a
direction `τ` orthogonal to `ν`. Then `∂_τ u ∈ H¹₀(Ω)`: the difference quotients of `u` in the
direction `τ` lie in `H¹₀(Ω)` and converge to `∂_τ u` in `H¹(Ω)`, since `u ∈ H²(Ω)`
(`TauCeti.W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn`). Differentiating the equation
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn`) shows that
`∂_τ u` solves `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = g + ∑ᵢⱼ (∂ᵢ∂_τ aⁱʲ ∂ⱼu + ∂_τ aⁱʲ ∂ᵢ∂ⱼu)` against test
functions; this right-hand side lies in `L²(Ω)` because `u ∈ H²(Ω)` and the first and second
derivatives of `a` are bounded on `Ω`. So `∂_τ u` is a weak solution of a Dirichlet problem with
zero boundary values and `L²` data. Applying `H²` regularity to `∂_τ u` puts every third
derivative of `u` with at least one tangential direction in `L²(Ω)`; the normal third derivative
`∂_ν ∂_ν ∂_ν u` is not treated here.

## Main declarations

All declarations below are in the namespace `TauCeti.PDE`.

* `UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_mapsTo`: on a domain
  mapped into itself by the translations parallel to a hyperplane, every first derivative of the
  solution has an `L²(Ω)` weak derivative in every direction.
* `UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`: on such a domain the solution
  lies in `W^{2,2}(Ω)`.
* `UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_halfSpace` and
  `UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace`: the case of a half-space.
* `UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo`
  and its half-space case
  `UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_halfSpace`:
  a tangential derivative of the solution lies in `H¹₀(Ω)` and solves the differentiated Dirichlet
  problem with `L²` data.
* `UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_mapsTo`
  and its half-space case
  `UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_halfSpace`:
  a tangential derivative of the solution lies in `H²(Ω)`.

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
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ} {K K' : ℝ≥0} {ν : EuclideanSpace ℝ ι}

omit [DecidableEq ι] in
/-- Splitting the gradient of a test function `φ` along `ν` and the hyperplane orthogonal to `ν`
(`P z = z - (⟪z, ν⟫ / ‖ν‖²) ν`) turns the energy form `a(u, φ)` into the sum of the normal term
`∫ (∂_ν φ) ∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu` and the tangential terms `∑ᵢⱼ ∫ (∂_{P eᵢ} φ) aⁱʲ ∂ⱼu`. -/
private theorem setIntegral_energyFormH1_split
    {P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hP : ∀ z, P z = z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν)
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
        (P (EuclideanSpace.basisFun ι ℝ i)) •
        (matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i)
          (EuclideanSpace.basisFun ι ℝ j) •
          ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) ∂mu =
      ∫ x in Omega, f x * φ x ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
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
      hP, ν']
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
Let `ν' = ν / ‖ν‖²` and let `P z = z - (⟪z, ν⟫ / ‖ν‖²) ν` be the projection onto the hyperplane
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
      (G i j) (EuclideanSpace.basisFun ι ℝ i -
        (⟪EuclideanSpace.basisFun ι ℝ i, ν⟫_ℝ / ‖ν‖ ^ 2) • ν)) :
    HasWeakLineDerivOn mu Omega (fun x => ∑ j, matrixBilinearForm (a x) ((‖ν‖ ^ 2)⁻¹ • ν)
        (EuclideanSpace.basisFun ι ℝ j) • ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
      (fun x => -(f x + ∑ i, ∑ j, G i j x)) ν := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  set P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun z => z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
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
  -- The weak equation, with the gradient of `φ` split along `ν` and the hyperplane.
  have heq := setIntegral_energyFormH1_split (P := P) (fun z => rfl) hloc hU φ
  -- Each tangential term moves its derivative onto the coefficient product.
  have htan : ∀ i j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
      (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) ∂mu =
        -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x ∂mu := fun i j =>
    (hG i j).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hIG : ∀ i j, Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x) mu :=
    fun i j => φ.integrable_smul (hG i j).locallyIntegrableOn_deriv
  have hR := TestFunction.neg_integral_smul_neg_add_eq φ hfloc hIG
  rw [hR, ← heq]
  simp only [b] at htan ⊢
  simp only [htan, Finset.sum_neg_distrib]
  ring

/-- **The normal second derivative.** Let `ν ≠ 0`, let `a` be uniformly elliptic and bounded on
`Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form, and let `u ∈ H¹(Ω)` satisfy
`a(u, φ) = ∫_Ω f φ` for every test function `φ`. If every first derivative `∂_y u` has an
`L²(Ω)` weak derivative in every direction orthogonal to `ν`, then `∂_ν u` has an `L²(Ω)` weak
derivative in the direction `ν`. -/
private theorem exists_hasWeakLineDerivOn_inner_gradient_normal (hν : ν ≠ 0)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {U : W1p mu Omega 2}
    (hU : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    (htan : ∀ y τ, ⟪τ, ν⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G τ) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, ν⟫_ℝ) G ν := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  set P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun z => z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
  have hN : 0 < ‖ν‖ ^ 2 := pow_pos (norm_pos_iff.2 hν) 2
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hP : ∀ z, ⟪P z, ν⟫_ℝ = 0 := fun z => real_inner_sub_div_norm_sq_smul_self_eq_zero z ν
  -- Weak derivatives commute, so a tangential derivative of `∂_ν u` is a derivative of the
  -- tangential first derivative in the direction `ν`.
  have hswap : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, τ⟫_ℝ) G ν := fun τ hτ => by
    obtain ⟨G, hG⟩ := htan ν τ hτ
    exact ⟨G, W1p.hasWeakLineDerivOn_inner_gradient_comm hG⟩
  -- The coefficients `β p q = ⟪p, a q⟫` are bounded and Lipschitz on `Ω`.
  set β : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ :=
    fun p q x => matrixBilinearForm (a x) p q
  have hβL := lipschitzOnWith_matrixBilinearForm_apply_apply hK
  have hgrad : ∀ z, MemLp (fun x => ⟪W1p.gradient U x, z⟫_ℝ) 2 (mu.restrict Omega) := fun z =>
    (Lp.memLp (W1p.gradient U)).inner_const z
  -- A coefficient times a first derivative with an `L²` weak derivative in a direction `v` has
  -- an `L²` weak derivative in that direction.
  have hprod : ∀ p q z v, (∃ G₀ : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, z⟫_ℝ) G₀ v) →
      ∃ G : Lp ℝ 2 (mu.restrict Omega),
        HasWeakLineDerivOn mu Omega (fun x => β p q x • ⟪W1p.gradient U x, z⟫_ℝ) G v := by
    rintro p q z v ⟨G₀, hG₀⟩
    exact hG₀.exists_lp_lipschitzOnWith_smul (hβL p q)
      (fun _ hx => ha.norm_point_matrixBilinearForm_le hx p q) (hgrad z) (Lp.memLp G₀)
  -- The normal derivative of `W = ∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu`, from the equation.
  choose G hG using fun i j => hprod (b i) (b j) (b j) (P (b i)) (htan (b j) (P (b i)) (hP (b i)))
  have hW := hasWeakLineDerivOn_sum_smul_inner_gradient (fun p q => (hβL p q).continuousOn)
    hU (G := fun i j => G i j) hG
  -- Subtracting the tangential parts leaves `⟪ν', a ν'⟫ ∂_ν u`.
  choose T hT using fun j => hprod ν' (b j) (P (b j)) ν (hswap (P (b j)) (hP (b j)))
  have hR := hW.sub (HasWeakLineDerivOn.sum Finset.univ fun j _ => hT j)
  have hRc : ∀ x, (∑ j, β ν' (b j) x • ⟪W1p.gradient U x, b j⟫_ℝ) -
      ∑ j, β ν' (b j) x • ⟪W1p.gradient U x, P (b j)⟫_ℝ =
        β ν' ν' x * ⟪W1p.gradient U x, ν⟫_ℝ := fun x =>
    b.sum_smul_inner_sub_sum_smul_inner_proj (matrixBilinearForm (a x)) ν (W1p.gradient U x)
  -- Ellipticity: `⟪ν', a ν'⟫ ≥ λ ‖ν'‖² > 0` on `Ω`, so its reciprocal is bounded and Lipschitz.
  obtain ⟨L, B, hrL, hrb, hne⟩ := exists_lipschitzOnWith_inv_matrixBilinearForm_self ha hK
    (smul_ne_zero (inv_ne_zero hN.ne') hν)
  set r : EuclideanSpace ℝ ι → ℝ := fun x => (β ν' ν' x)⁻¹
  -- Multiplying by `⟪ν', a ν'⟫⁻¹` gives the normal second derivative.
  have hRm : MemLp (fun x => (∑ j, β ν' (b j) x • ⟪W1p.gradient U x, b j⟫_ℝ) -
      ∑ j, β ν' (b j) x • ⟪W1p.gradient U x, P (b j)⟫_ℝ) 2 (mu.restrict Omega) := by
    simp only [hRc]
    exact (memLp_top_of_bound ((hβL ν' ν').continuousOn.aestronglyMeasurable hΩm)
      (Lam * ‖ν'‖ * ‖ν'‖) ((ae_restrict_mem hΩm).mono fun x hx =>
        ha.norm_point_matrixBilinearForm_le hx ν' ν')).mul (hgrad ν)
  have hR'm : MemLp (fun x => -(f x + ∑ i, ∑ j, G i j x) - ∑ j, T j x) 2
      (mu.restrict Omega) :=
    ((Lp.memLp f).add (memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
      Lp.memLp (G i j))).neg.sub (memLp_finsetSum _ fun j _ => Lp.memLp (T j))
  obtain ⟨G', hG'⟩ := hR.exists_lp_lipschitzOnWith_smul hrL hrb hRm hR'm
  refine ⟨G', hG'.congr_ae ?_⟩
  filter_upwards [ae_restrict_mem hΩm] with x hx
  refine (congrArg (fun t => (β ν' ν' x)⁻¹ • t) (hRc x)).trans ?_
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (hne x hx), one_mul]

/-- **Second derivatives up to the boundary.** Let `ν ≠ 0` and let `Ω` be mapped into itself by
every translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is. Let `a` be
uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form, and
let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`. Then for all `y` and
`w` the derivative `∂_y u = ⟪∇u, y⟫` has a weak derivative in the direction `w` that lies in
`L²(Ω)`. No regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_mapsTo (hν : ν ≠ 0)
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w := by
  set U : W1p mu Omega 2 := (u : W1p mu Omega 2)
  set P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun z => z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
  -- `D y w`: the derivative `∂_y u` has a weak derivative in the direction `w` in `L²(Ω)`.
  let D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop := fun y w =>
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w
  -- `D` is linear in each argument.
  have hadd_dir : ∀ {y w₁ w₂}, D y w₁ → D y w₂ → D y (w₁ + w₂) := by
    rintro y w₁ w₂ ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    exact ⟨G₁ + G₂, (h₁.add_direction h₂).congr_ae_deriv (Lp.coeFn_add G₁ G₂).symm⟩
  have hsmul_dir : ∀ {y w} (r : ℝ), D y w → D y (r • w) := by
    rintro y w r ⟨G, h⟩
    exact ⟨r • G, (h.smul_direction r).congr_ae_deriv (Lp.coeFn_smul r G).symm⟩
  have hadd : ∀ {y₁ y₂ w}, D y₁ w → D y₂ w → D (y₁ + y₂) w := by
    rintro y₁ y₂ w ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    refine ⟨G₁ + G₂, ((h₁.add h₂).congr_ae (Eventually.of_forall fun x => ?_))
      |>.congr_ae_deriv (Lp.coeFn_add G₁ G₂).symm⟩
    simp [inner_add_right]
  have hsmul : ∀ {y w} (r : ℝ), D y w → D (r • y) w := by
    rintro y w r ⟨G, h⟩
    refine ⟨r • G, ((h.const_smul r).congr_ae (Eventually.of_forall fun x => ?_))
      |>.congr_ae_deriv (Lp.coeFn_smul r G).symm⟩
    simp [real_inner_smul_right]
  -- The symmetry of `D` that comes from commuting weak derivatives.
  have hsymm : ∀ {y w}, D y w → D w y := by
    rintro y w ⟨G, hG⟩
    exact ⟨G, W1p.hasWeakLineDerivOn_inner_gradient_comm hG⟩
  -- Tangential directions: the difference-quotient estimate.
  have hP : ∀ z, ⟪P z, ν⟫_ℝ = 0 := fun z => real_inner_sub_div_norm_sq_smul_self_eq_zero z ν
  have htan : ∀ y {τ}, ⟪τ, ν⟫_ℝ = 0 → D y τ := by
    intro y τ hτ
    obtain ⟨G, -, hG⟩ :=
      ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo (hΩ τ hτ) hK hu y
    exact ⟨G, hG⟩
  -- The normal direction: the equation and ellipticity.
  have hνν : D ν ν := exists_hasWeakLineDerivOn_inner_gradient_normal hν ha hK
    hu.energyFormH1_ofTestFunctionₗ fun y _ hτ => htan y hτ
  -- Every first derivative has a normal derivative, and then a derivative in every direction.
  have hyν : ∀ y, D y ν := fun y => by
    have h := hadd (hsmul (⟪y, ν⟫_ℝ / ‖ν‖ ^ 2) hνν) (hsymm (htan ν (hP y)))
    simpa only [P, add_sub_cancel] using h
  have h := hadd_dir (hsmul_dir (⟪w, ν⟫_ℝ / ‖ν‖ ^ 2) (hyν y)) (htan y (hP w))
  simpa only [P, add_sub_cancel] using h

/-- **`H²` regularity up to the boundary.** Let `ν ≠ 0` and let `Ω` be mapped into itself by every
translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is. Let `a` be
uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a bilinear form, and
let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`, that is, of the
Dirichlet problem with zero boundary values. Then `u` is the first-order part of an element of
`W^{2,2}(Ω)`: its second weak derivatives lie in `L²(Ω)` up to the boundary. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo (hν : ν ≠ 0)
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp mu Omega 2 2, Wkp.lowerOrder 1 U = (u : W1p mu Omega 2) :=
  W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun _ _ => ha.exists_hasWeakLineDerivOn_gradient_of_mapsTo hν hΩ hK hu _ _

/-- **Second derivatives up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a
bilinear form, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with
`f ∈ L²(Ω)`. Then for all `y` and `w` the derivative `∂_y u = ⟪∇u, y⟫` has a weak derivative in
the direction `w` that lies in `L²(Ω)`. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w :=
  ha.exists_hasWeakLineDerivOn_gradient_of_mapsTo hν
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

/-! ### Tangential derivatives -/

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- A coefficient field whose bilinear forms are `K`-Lipschitz on `Ω` has entries whose
derivatives at points of `Ω` have norm at most `K`. -/
private theorem norm_fderiv_apply_le_of_lipschitzOnWith
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) (i j : ι)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι)))
    (τ : EuclideanSpace ℝ ι) : ‖fderiv ℝ (fun y => a y i j) x τ‖ ≤ K * ‖τ‖ := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  have hL := lipschitzOnWith_matrixBilinearForm_apply_apply hK (b i) (b j)
  have hentry : ∀ y, matrixBilinearForm (a y) (b i) (b j) = a y i j := fun y => by
    simp [b, Matrix.mulVec, dotProduct]
  have hb : ∀ k, ‖b k‖₊ = 1 := fun k => NNReal.eq (b.orthonormal.1 k)
  simp only [hentry, hb, mul_one] at hL
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  gcongr
  simpa using norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) hL

omit [DecidableEq ι] in
/-- The right-hand side `g + ∑ᵢⱼ (∂ᵢ∂_τ aⁱʲ ∂ⱼu + ∂_τ aⁱʲ ∂ᵢ∂ⱼu)` of the equation differentiated in
a direction `τ` is square integrable on `Ω`, for `g ∈ L²(Ω)`, `u ∈ H¹(Ω)` with `∂ⱼu = D j ∈ H¹(Ω)`,
and a smooth coefficient field whose bilinear forms and whose first derivatives are Lipschitz on
`Ω`. -/
private theorem memLp_add_sum_sum_fderiv_mul_inner_gradient
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    (hK' : ∀ i j, LipschitzOnWith K' (fderiv ℝ (fun x => a x i j)) Omega)
    (τ : EuclideanSpace ℝ ι) (g : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2)
    (D : ι → W1p mu Omega 2) :
    MemLp (fun x => g x + ∑ i, ∑ j,
      (fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (EuclideanSpace.basisFun ι ℝ i) *
          ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
        fderiv ℝ (fun y => a y i j) x τ *
          ⟪W1p.gradient (D j) x, EuclideanSpace.basisFun ι ℝ i⟫_ℝ)) 2 (mu.restrict Omega) := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- A bounded continuous function on `Ω` times an `L²(Ω)` function is in `L²(Ω)`.
  have hmul : ∀ {β h : EuclideanSpace ℝ ι → ℝ} {C : ℝ}, ContinuousOn β Omega →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖β x‖ ≤ C) → MemLp h 2 (mu.restrict Omega) →
        MemLp (fun x => β x * h x) 2 (mu.restrict Omega) := fun hβ hC hh =>
    (memLp_top_of_bound (hβ.aestronglyMeasurable hΩm) _ ((ae_restrict_mem hΩm).mono hC)).mul hh
  -- The first and second derivatives of the coefficients are continuous and bounded on `Ω`.
  have hfd : ∀ i j, ContinuousOn (fun x => fderiv ℝ (fun y => a y i j) x τ) Omega := fun i j =>
    ((hs i j).continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply continuousOn_const
  have hfdd : ∀ i j, ContinuousOn
      (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (b i)) Omega := fun i j =>
    ((((hs i j).fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply (contDiffOn_const (c := τ))
      (n := ∞)).continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).clm_apply continuousOn_const
  have hd2 : ∀ i j, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y τ) x (b i)‖ ≤ ‖τ‖ * K' * ‖b i‖ := by
    intro i j x hx
    have hL := (ContinuousLinearMap.lipschitzWith_apply τ).comp_lipschitzOnWith (hK' i j)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    simpa [Function.comp_def] using norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) hL
  exact (Lp.memLp g).add (memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (hmul (hfdd i j) (hd2 i j) ((Lp.memLp (W1p.gradient u)).inner_const (b j))).add
      (hmul (hfd i j) (fun x hx => norm_fderiv_apply_le_of_lipschitzOnWith hK i j hx τ)
        ((Lp.memLp (W1p.gradient (D j))).inner_const (b i))))

/-- **Tangential derivatives solve the differentiated Dirichlet problem.** Let `ν ≠ 0` and let `Ω`
be mapped into itself by every translation orthogonal to `ν`, as a half-space
`{x | c < ⟪x, ν⟫}` is. Let `a` be uniformly elliptic and bounded on `Ω`, smooth on `Ω`, with
`x ↦ a(x)` and the first derivatives of its entries Lipschitz on `Ω`, and let `u ∈ H¹₀(Ω)` be a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(Ω)`. If `τ` is orthogonal to `ν` and `f` has a weak
derivative `g ∈ L²(Ω)` in the direction `τ`, then the derivative `∂_τ u` lies in `H¹₀(Ω)` and is a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = F` with zero boundary values for some `F ∈ L²(Ω)`. -/
theorem UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo
    (hν : ν ≠ 0) (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    (hK' : ∀ i j, LipschitzOnWith K' (fderiv ℝ (fun x => a x i j)) Omega)
    {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0) {f g : Lp ℝ 2 (mu.restrict Omega)}
    (hf : HasWeakLineDerivOn mu Omega f g τ) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ (d : W1p0 mu Omega 2) (F : Lp ℝ 2 (mu.restrict Omega)),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2))
        (W1p.value (d : W1p mu Omega 2)) τ ∧ IsWeakSolutionDirichlet a 0 0 F d := by
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- `u ∈ H²(Ω)`: every first derivative `∂_y u` lies in `H¹(Ω)`.
  obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_mapsTo hν hΩ hK hu
  have hUv : Wkp.value 2 U = W1p.value (u : W1p mu Omega 2) := by
    rw [Wkp.value_succ, Wkp.value_one, hU]
  choose D hD using fun y => Wkp.exists_hasWeakLineDerivOn_value 1 U y
  simp only [hUv, Wkp.value_one] at hD
  -- The tangential derivative `∂_τ u` keeps zero boundary values.
  have hmem := W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (by simp) (hΩ τ hτ) u.2 (hD τ)
    fun y => ⟨D y, hD y⟩
  -- The right-hand side `F = g + ∑ᵢⱼ (∂ᵢ∂_τ aⁱʲ ∂ⱼu + ∂_τ aⁱʲ ∂ᵢ∂ⱼu)` is square integrable.
  have hF := memLp_add_sum_sum_fderiv_mul_inner_gradient hK hs hK' τ g (u : W1p mu Omega 2)
    fun j => D (EuclideanSpace.basisFun ι ℝ j)
  -- Testing against test functions suffices for bounded coefficients.
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℝ))
  have hcoeff : MemLp (fun x => energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) ha.upper_nonneg
      ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable hΩm)
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨⟨D τ, hmem⟩, hF.toLp _, hD τ,
    (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2 fun φ => ?_⟩
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn hs
    hu.energyFormH1_ofTestFunctionₗ (hD τ) (fun j => hD (EuclideanSpace.basisFun ι ℝ j)) hf φ]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

/-- **Third derivatives with a tangential direction.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo`,
the derivative `d = ∂_τ u ∈ H¹(Ω)` of the solution in a direction `τ` orthogonal to `ν` lies in
`H²(Ω)` up to the boundary: for all `y` and `w`, the derivative `∂_y d` has a weak derivative in the
direction `w` that lies in `L²(Ω)`. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_mapsTo
    (hν : ν ≠ 0) (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    (hK' : ∀ i j, LipschitzOnWith K' (fderiv ℝ (fun x => a x i j)) Omega)
    {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0) {f g : Lp ℝ 2 (mu.restrict Omega)}
    (hf : HasWeakLineDerivOn mu Omega f g τ) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {d : W1p mu Omega 2}
    (hd : HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value d) τ) (y w) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient d x, y⟫_ℝ) G w := by
  obtain ⟨d₀, F, hd₀, hdF⟩ :=
    ha.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo hν hΩ hK hs hK' hτ hf hu
  -- Weak derivatives are unique, so `d` is the solution `d₀` of the differentiated problem.
  obtain rfl : d = d₀ := W1p.ext_value (Lp.ext (hd.ae_eq hd₀))
  exact ha.exists_hasWeakLineDerivOn_gradient_of_mapsTo hν hΩ hK hdF y w

/-- **Tangential derivatives on a half-space solve the differentiated Dirichlet problem.** This is
the half-space case `Ω = {x | c < ⟪x, ν⟫}` of
`TauCeti.PDE.UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo`.
-/
theorem UniformlyEllipticOn.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_halfSpace
    (hν : ν ≠ 0) (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    (hK' : ∀ i j, LipschitzOnWith K' (fderiv ℝ (fun x => a x i j)) Omega)
    {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0) {f g : Lp ℝ 2 (mu.restrict Omega)}
    (hf : HasWeakLineDerivOn mu Omega f g τ) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ (d : W1p0 mu Omega 2) (F : Lp ℝ 2 (mu.restrict Omega)),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2))
        (W1p.value (d : W1p mu Omega 2)) τ ∧ IsWeakSolutionDirichlet a 0 0 F d :=
  ha.exists_isWeakSolutionDirichlet_of_hasWeakLineDerivOn_of_mapsTo hν
    (fun _ hτ' => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ') hK hs hK' hτ hf hu

/-- **Third derivatives with a tangential direction on a half-space.** This is the half-space case
`Ω = {x | c < ⟪x, ν⟫}` of
`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_mapsTo`
-/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_halfSpace
    (hν : ν ≠ 0) (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    (hK' : ∀ i j, LipschitzOnWith K' (fderiv ℝ (fun x => a x i j)) Omega)
    {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0) {f g : Lp ℝ 2 (mu.restrict Omega)}
    (hf : HasWeakLineDerivOn mu Omega f g τ) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) {d : W1p mu Omega 2}
    (hd : HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (W1p.value d) τ) (y w) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient d x, y⟫_ℝ) G w :=
  ha.exists_hasWeakLineDerivOn_gradient_of_hasWeakLineDerivOn_of_mapsTo hν
    (fun _ hτ' => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ') hK hs hK' hτ hf hu hd y w

end PDE

end TauCeti
