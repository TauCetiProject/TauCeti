/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Normed.Field.Lipschitz
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
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

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_mapsTo`: on a domain
  mapped into itself by the translations parallel to a hyperplane, every first derivative of the
  solution has an `L²(Ω)` weak derivative in every direction.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`: on such a domain the solution
  lies in `W^{2,2}(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_halfSpace` and
  `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace`: the case of a half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped Distributions InnerProductSpace Matrix NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι}

omit [Fintype ι] [DecidableEq ι] in
/-- Splitting a gradient along `ν` and the hyperplane orthogonal to it:
`B(g, w) = ⟪g, ν⟫ ∑ⱼ B(ν', eⱼ) ⟪w, eⱼ⟫ + ∑ᵢ ∑ⱼ ⟪g, P eᵢ⟫ B(eᵢ, eⱼ) ⟪w, eⱼ⟫`, where
`ν' = ν / ‖ν‖²` and `P z = z - (⟪z, ν⟫ / ‖ν‖²) ν`. -/
private theorem bilin_eq_inner_mul_sum_add_sum_sum [Fintype ι]
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) (g w : EuclideanSpace ℝ ι) :
    B g w = ⟪g, ν⟫_ℝ * ∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (EuclideanSpace.basisFun ι ℝ j) *
        ⟪w, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
      ∑ i, ∑ j, ⟪g, EuclideanSpace.basisFun ι ℝ i -
          (⟪EuclideanSpace.basisFun ι ℝ i, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ *
        (B (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) *
          ⟪w, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hw : ∀ p, B p w = ∑ j, B p (b j) * ⟪w, b j⟫_ℝ := fun p => by
    conv_lhs => rw [← b.sum_repr' w]
    simp only [map_sum, map_smul, smul_eq_mul, real_inner_comm, mul_comm]
  have hν : ∑ i, (⟪b i, ν⟫_ℝ / ‖ν‖ ^ 2 * ⟪g, ν⟫_ℝ) • b i = (⟪g, ν⟫_ℝ / ‖ν‖ ^ 2) • ν := by
    have h := congrArg (fun z => (⟪g, ν⟫_ℝ / ‖ν‖ ^ 2) • z) (b.sum_repr' ν)
    simp only [Finset.smul_sum, smul_smul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by congr 1; ring
  have hg : ⟪g, ν⟫_ℝ • (‖ν‖ ^ 2)⁻¹ • ν +
      ∑ i, ⟪g, b i - (⟪b i, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ • b i = g := by
    have hsum : ∑ i, ⟪g, b i⟫_ℝ • b i = g := by
      simpa only [real_inner_comm] using b.sum_repr' g
    simp only [inner_sub_right, real_inner_smul_right, sub_smul, Finset.sum_sub_distrib, hν]
    rw [hsum, smul_smul, div_eq_mul_inv]
    abel
  conv_lhs => rw [← hg]
  simp [hw, Finset.mul_sum, mul_assoc]

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
  have hφ : Differentiable ℝ (φ : EuclideanSpace ℝ ι → ℝ) := φ.contDiff.differentiable (by simp)
  have hI : ∀ (v p : EuclideanSpace ℝ ι) j, Integrable (fun x =>
      lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x v •
        (matrixBilinearForm (a x) p (b j) • ⟪W1p.gradient U x, b j⟫_ℝ)) mu :=
    fun v p j => integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc p j) φ v
  have hIW : Integrable (fun x => lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ∑ j, matrixBilinearForm (a x) ν' (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) mu :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn hW φ ν
  -- The weak equation, with the gradient of `φ` split along `ν` and the hyperplane.
  have heq : ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ∑ j, matrixBilinearForm (a x) ν' (b j) • ⟪W1p.gradient U x, b j⟫_ℝ ∂mu +
      ∑ i, ∑ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
        (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) ∂mu =
      ∫ x in Omega, f x * φ x ∂mu := by
    have hpt : ∫ x in Omega, matrixBilinearForm (a x)
          (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient U x) ∂mu =
        ∫ x in Omega, (lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
          ∑ j, matrixBilinearForm (a x) ν' (b j) • ⟪W1p.gradient U x, b j⟫_ℝ +
          ∑ i, ∑ j, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
            (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ)) ∂mu := by
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
      rw [W1p.gradient_ofTestFunctionₗ, hx,
        bilin_eq_inner_mul_sum_add_sum_sum (ν := ν) (matrixBilinearForm (a x))]
      simp only [inner_gradient_left, (hφ x).lineDeriv_eq_fderiv, smul_eq_mul, Finset.mul_sum,
        ν', P, b]
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
  -- Each tangential term moves its derivative onto the coefficient product.
  have htan : ∀ i j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (P (b i)) •
      (matrixBilinearForm (a x) (b i) (b j) • ⟪W1p.gradient U x, b j⟫_ℝ) ∂mu =
        -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x ∂mu := fun i j =>
    (hG i j).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hIG : ∀ i j, Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x) mu :=
    fun i j => integrable_smul_of_locallyIntegrableOn (hG i j).locallyIntegrableOn_deriv φ
  have hR : -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • -(f x + ∑ i, ∑ j, G i j x) ∂mu =
      (∫ x in Omega, f x * φ x ∂mu) +
        ∑ i, ∑ j, ∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G i j x ∂mu := by
    simp only [smul_neg, integral_neg, neg_neg, smul_add, Finset.smul_sum]
    rw [integral_add (integrable_smul_of_locallyIntegrableOn hfloc φ)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hIG i j),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hIG i j]
    congr 1
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [φ.zero_on_compl hx]]
      simp only [smul_eq_mul, mul_comm]
    · exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hIG i j
  rw [hR, ← heq]
  simp only [htan, Finset.sum_neg_distrib]
  ring

omit [DecidableEq ι] in
/-- **The normal part of the equation's leading term.** Subtracting the tangential parts
`∑ⱼ B(ν', eⱼ) ⟪g, P eⱼ⟫` from `∑ⱼ B(ν', eⱼ) ⟪g, eⱼ⟫` leaves `B(ν', ν') ⟪g, ν⟫`, where
`ν' = ν / ‖ν‖²` and `P z = z - (⟪z, ν⟫ / ‖ν‖²) ν`. -/
private theorem sum_smul_inner_sub_sum_smul_inner_proj
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) (g : EuclideanSpace ℝ ι) :
    (∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (EuclideanSpace.basisFun ι ℝ j) •
        ⟪g, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) -
      ∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (EuclideanSpace.basisFun ι ℝ j) •
        ⟪g, EuclideanSpace.basisFun ι ℝ j -
          (⟪EuclideanSpace.basisFun ι ℝ j, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ =
      B ((‖ν‖ ^ 2)⁻¹ • ν) ((‖ν‖ ^ 2)⁻¹ • ν) * ⟪g, ν⟫_ℝ := by
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  have hν'sum : ∑ j, (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) • b j = ν' := by
    simp only [ν', div_eq_inv_mul, ← smul_smul, ← Finset.smul_sum, b.sum_repr']
  have hν' : ∑ j, B ν' (b j) * (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) = B ν' ν' := by
    calc ∑ j, B ν' (b j) * (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2)
        = B ν' (∑ j, (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) • b j) := by
          simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = B ν' ν' := by rw [hν'sum]
  simp only [inner_sub_right, real_inner_smul_right, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← hν', Finset.sum_mul]
  simp only [sub_sub_cancel]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- **A bounded Lipschitz factor keeps an `L²` weak derivative.** If `g ∈ L²(Ω)` has a weak
derivative `g' ∈ L²(Ω)` in the direction `v` and `ψ` is bounded and Lipschitz on `Ω`, then `ψ g`
has a weak derivative in the direction `v` that lies in `L²(Ω)`, by the Leibniz rule
`TauCeti.HasWeakLineDerivOn.lipschitzOnWith_smul`. -/
private theorem exists_hasWeakLineDerivOn_lipschitzOnWith_smul
    {ψ g g' : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0} {M : ℝ} {v : EuclideanSpace ℝ ι}
    (hψ : LipschitzOnWith L ψ Omega) (hψb : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖ψ x‖ ≤ M)
    (hg : MemLp g 2 (mu.restrict Omega)) (hg' : MemLp g' 2 (mu.restrict Omega))
    (h : HasWeakLineDerivOn mu Omega g g' v) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega), HasWeakLineDerivOn mu Omega (fun x => ψ x • g x) G v := by
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hm := ((memLp_top_of_bound (hψ.continuousOn.aestronglyMeasurable hΩm) M
    ((ae_restrict_mem hΩm).mono hψb)).smul (r := 2) hg').add
    ((hψ.memLp_lineDeriv Omega.isOpen v).smul (r := 2) hg)
  exact ⟨hm.toLp _, (h.lipschitzOnWith_smul hψ).congr_ae_deriv hm.coeFn_toLp.symm⟩

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
  set b := EuclideanSpace.basisFun ι ℝ
  set ν' : EuclideanSpace ℝ ι := (‖ν‖ ^ 2)⁻¹ • ν
  set P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun z => z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
  have hN : 0 < ‖ν‖ ^ 2 := pow_pos (norm_pos_iff.2 hν) 2
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
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
  -- The first derivatives of `u`, and the symmetry of `D` that comes from commuting them.
  have hfd : ∀ z, HasWeakLineDerivOn mu Omega (W1p.value U)
      (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := fun z => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  have hsymm : ∀ {y w}, D y w → D w y := by
    rintro y w ⟨G, hG⟩
    exact ⟨G, (hfd y).comm hG (hfd w)⟩
  -- Tangential directions: the difference-quotient estimate.
  have hP : ∀ z, ⟪P z, ν⟫_ℝ = 0 := fun z => by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hN.ne', sub_self]
  have htan : ∀ y {τ}, ⟪τ, ν⟫_ℝ = 0 → D y τ := by
    intro y τ hτ
    obtain ⟨G, -, hG⟩ :=
      ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo (hΩ τ hτ) hK hu y
    exact ⟨G, hG⟩
  -- The coefficients `β p q = ⟪p, a q⟫` are bounded and Lipschitz on `Ω`.
  set β : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ :=
    fun p q x => matrixBilinearForm (a x) p q
  have hβL : ∀ p q, LipschitzOnWith (K * ‖p‖₊ * ‖q‖₊) (β p q) Omega := fun p q => by
    -- `β p q` is `x ↦ a x` followed by evaluation at `p` and then at `q`.
    have h := ((ContinuousLinearMap.lipschitzWith_apply q).comp
      (ContinuousLinearMap.lipschitzWith_apply p)).comp_lipschitzOnWith hK
    have hc : ‖q‖₊ * ‖p‖₊ * K = K * ‖p‖₊ * ‖q‖₊ := by ring
    rwa [hc] at h
  have hβb : ∀ p q, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖β p q x‖ ≤ Lam * ‖p‖ * ‖q‖ :=
    fun p q x hx => by
      simpa only [β, Real.norm_eq_abs, matrixBilinearForm_apply] using ha.upper_bound hx p q
  have hgrad : ∀ z, MemLp (fun x => ⟪W1p.gradient U x, z⟫_ℝ) 2 (mu.restrict Omega) := fun z =>
    (Lp.memLp (W1p.gradient U)).inner_const z
  -- A coefficient times a first derivative with an `L²` weak derivative in a direction `v` has
  -- an `L²` weak derivative in that direction.
  have hprod : ∀ p q z v, D z v → ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => β p q x • ⟪W1p.gradient U x, z⟫_ℝ) G v := by
    rintro p q z v ⟨G₀, hG₀⟩
    exact exists_hasWeakLineDerivOn_lipschitzOnWith_smul (hβL p q) (hβb p q) (hgrad z)
      (Lp.memLp G₀) hG₀
  -- The normal derivative of `W = ∑ⱼ ⟪ν', a eⱼ⟫ ∂ⱼu`, from the equation.
  choose G hG using fun i j => hprod (b i) (b j) (b j) (P (b i)) (htan (b j) (hP (b i)))
  have hUφ : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu := fun φ => by
    rw [(isWeakSolutionDirichlet_iff f u).1 hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]
  have hW := hasWeakLineDerivOn_sum_smul_inner_gradient (fun p q => (hβL p q).continuousOn)
    hUφ (G := fun i j => G i j) hG
  -- Subtracting the tangential parts leaves `⟪ν', a ν'⟫ ∂_ν u`.
  choose T hT using fun j => hprod ν' (b j) (P (b j)) ν (hsymm (htan ν (hP (b j))))
  have hR := hW.sub (HasWeakLineDerivOn.sum Finset.univ fun j _ => hT j)
  have hRc : ∀ x, (∑ j, β ν' (b j) x • ⟪W1p.gradient U x, b j⟫_ℝ) -
      ∑ j, β ν' (b j) x • ⟪W1p.gradient U x, P (b j)⟫_ℝ =
        β ν' ν' x * ⟪W1p.gradient U x, ν⟫_ℝ := fun x =>
    sum_smul_inner_sub_sum_smul_inner_proj (matrixBilinearForm (a x)) (W1p.gradient U x)
  -- Ellipticity: `⟪ν', a ν'⟫ ≥ λ ‖ν'‖² > 0` on `Ω`, so its reciprocal is bounded and Lipschitz.
  set m : ℝ := lam * ‖ν'‖ ^ 2
  have hm : 0 < m := mul_pos ha.pos (pow_pos (norm_pos_iff.2 (smul_ne_zero
    (inv_ne_zero hN.ne') hν)) 2)
  have hcm : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), m ≤ β ν' ν' x := fun x hx => by
    simpa only [m, β, matrixBilinearForm_self] using ha.lower_bound hx ν'
  set r : EuclideanSpace ℝ ι → ℝ := fun x => (β ν' ν' x)⁻¹
  have hrL : LipschitzOnWith (K * ‖ν'‖₊ * ‖ν'‖₊ / ⟨m, hm.le⟩ ^ 2) r Omega :=
    (hβL ν' ν').inv_of_le_norm hm fun x hx =>
      (hcm x hx).trans (Real.le_norm_self (β ν' ν' x))
  have hrb : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖r x‖ ≤ m⁻¹ := fun x hx => by
    have hx' := hm.trans_le (hcm x hx)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx']
    exact inv_anti₀ hm (hcm x hx)
  -- The normal second derivative.
  have hνν : D ν ν := by
    have hRm : MemLp (fun x => (∑ j, β ν' (b j) x • ⟪W1p.gradient U x, b j⟫_ℝ) -
        ∑ j, β ν' (b j) x • ⟪W1p.gradient U x, P (b j)⟫_ℝ) 2 (mu.restrict Omega) := by
      simp only [hRc]
      exact (memLp_top_of_bound ((hβL ν' ν').continuousOn.aestronglyMeasurable hΩm)
        (Lam * ‖ν'‖ * ‖ν'‖) ((ae_restrict_mem hΩm).mono fun x hx => hβb ν' ν' x hx)).mul
        (hgrad ν)
    have hR'm : MemLp (fun x => -(f x + ∑ i, ∑ j, G i j x) - ∑ j, T j x) 2
        (mu.restrict Omega) :=
      ((Lp.memLp f).add (memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
        Lp.memLp (G i j))).neg.sub (memLp_finsetSum _ fun j _ => Lp.memLp (T j))
    obtain ⟨G', hG'⟩ := exists_hasWeakLineDerivOn_lipschitzOnWith_smul hrL hrb hRm hR'm hR
    refine ⟨G', hG'.congr_ae ?_⟩
    filter_upwards [ae_restrict_mem hΩm] with x hx
    refine (congrArg (fun t => (β ν' ν' x)⁻¹ • t) (hRc x)).trans ?_
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (hm.trans_le (hcm x hx)).ne', one_mul]
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

end PDE

end TauCeti
