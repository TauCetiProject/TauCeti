/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.Wkp.Basic

import TauCeti.Analysis.Sobolev.W1p.Multiplication
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# The energy form against a flux with weak divergence

Let `a` be a matrix field on an open set `Ω` of Euclidean space with bounded energy density, and
let `u ∈ H¹(Ω)`. If every component `Fᵢ = ∑ⱼ aⁱʲ ∂ⱼu` of the flux of `u` has a weak derivative
`dᵢ ∈ L²(Ω)` along the `i`-th coordinate, then `u` is a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -∑ᵢ dᵢ` in `Ω`,

that is, `∫_Ω ⟨∇v, a ∇u⟩ = -∫_Ω (∑ᵢ dᵢ) v` for every `v ∈ H¹₀(Ω)`
(`TauCeti.PDE.energyFormH1_eq_setIntegral_neg_sum_of_hasWeakLineDerivOn`). This is integration
by parts against `H¹₀(Ω)`, proved on test functions from the definition of the weak derivative and
extended by density. No boundary condition on `u` is needed. When `u ∈ H¹₀(Ω)` and the energy
form is coercive on `H¹₀(Ω)`, it places `u` in the domain of `TauCeti.PDE.dirichletOperator`
via `TauCeti.PDE.mem_domain_dirichletOperator_iff` and computes the operator there.

For `u ∈ H²(Ω)` and `a` with `C¹` entries whose values and gradients are bounded on `Ω`, the
weak derivatives `dᵢ ∈ L²(Ω)` exist by the weak Leibniz rule, and the identity holds with them
(`TauCeti.PDE.exists_hasWeakLineDerivOn_flux_and_energyFormH1_eq_of_wkp_two`); in particular the
right-hand side is some `g ∈ L²(Ω)` (`TauCeti.PDE.exists_energyFormH1_eq_setIntegral_of_wkp_two`).
Under the same coercivity condition, this gives the inclusion `H²(Ω) ∩ H¹₀(Ω) ⊆ dom L`, with
the formula `L u = -∑ᵢ ∂ᵢ(∑ⱼ aⁱʲ ∂ⱼu)`.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- **Integration by parts against a flux with weak divergence.** Let the energy density of `a`
be essentially bounded on `Ω`, let `u ∈ H¹(Ω)`, and suppose that for every `i` the flux
component `Fᵢ = ∑ⱼ aⁱʲ ∂ⱼu` has the weak derivative `dᵢ ∈ L²(Ω)` along the `i`-th coordinate
vector `eᵢ`. Then for every `v ∈ H¹₀(Ω)`,

`∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω (-∑ᵢ dᵢ) v`. -/
theorem energyFormH1_eq_setIntegral_neg_sum_of_hasWeakLineDerivOn
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    {u : W1p mu Omega 2} {d : ι → Lp ℝ 2 (mu.restrict Omega)}
    (hd : ∀ i, HasWeakLineDerivOn mu Omega
      (fun x ↦ ∑ j, a x i j * ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) (d i)
      (EuclideanSpace.basisFun ι ℝ i))
    (v : W1p0 mu Omega 2) :
    energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, (-∑ i, d i x) * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  set e := EuclideanSpace.basisFun ι ℝ
  set g : Lp ℝ 2 (mu.restrict Omega) := -∑ i, d i
  have hg : ∀ᵐ x ∂mu.restrict Omega, g x = -∑ i, d i x :=
    Lp.coeFn_neg_ae_eq_of_ae_eq (Lp.coeFn_fun_finsetSum Finset.univ d)
  have key := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction (b := 0) (c := 0)
    hcoeff g u).2 fun φ ↦ ?_
  · rw [key v]
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Omega, matrixBilinearForm (a x)
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient u x) ∂mu
      = ∫ x in Omega, ∑ i, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (e i) •
          ∑ j, a x i j * ⟪W1p.gradient u x, e j⟫_ℝ ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
        rw [W1p.gradient_ofTestFunctionₗ, hx, ← sum_inner_mul_matrixBilinearForm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [smul_eq_mul, (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
          inner_gradient_left]
        congr 1
        exact matrixBilinearForm_basisFun_left i (W1p.gradient u x)
    _ = ∑ i, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (e i) •
          ∑ j, a x i j * ⟪W1p.gradient u x, e j⟫_ℝ ∂mu := by
        rw [integral_finsetSum _ fun i _ ↦
          (integrable_lineDeriv_smul_of_locallyIntegrableOn (hd i).locallyIntegrableOn φ
            (e i)).restrict]
        exact Finset.sum_congr rfl fun i _ ↦
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ (e i)
    _ = ∑ i, -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • d i x ∂mu :=
        Finset.sum_congr rfl fun i _ ↦ ((hasWeakLineDerivOn_iff_testFunction.1 (hd i)).2.2.2 φ)
    _ = ∑ i, ∫ x in Omega, -((φ : EuclideanSpace ℝ ι → ℝ) x • d i x) ∂mu :=
        Finset.sum_congr rfl fun i _ ↦ by rw [integral_neg, setIntegral_smul_eq_integral_smul φ]
    _ = ∫ x in Omega, ∑ i, -((φ : EuclideanSpace ℝ ι → ℝ) x • d i x) ∂mu :=
        (integral_finsetSum _ fun i _ ↦
          (φ.integrable_smul (hd i).locallyIntegrableOn_deriv).restrict.neg).symm
    _ = ∫ x in Omega, g x * φ x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hg] with x hx
        simp only [hx, smul_eq_mul, Finset.sum_neg_distrib, neg_mul, Finset.sum_mul, mul_comm]

/-- **The weak divergence of an `H²` flux.**
Let the entries of `a` be `C¹` on `Ω`, with values and gradients bounded by `M`, and let
`u ∈ H²(Ω)`. Then there are `dᵢ ∈ L²(Ω)` such that, for every `i`, the flux component
`Fᵢ = ∑ⱼ aⁱʲ ∂ⱼu` has the weak derivative `dᵢ` along the `i`-th coordinate vector `eᵢ`, and

`∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω (-∑ᵢ dᵢ) v` for every `v ∈ H¹₀(Ω)`.

Weak derivatives are unique almost everywhere (`TauCeti.HasWeakLineDerivOn.ae_eq`), so the
right-hand side is `-∑ᵢ ∂ᵢ(∑ⱼ aⁱʲ ∂ⱼu)`. If the energy form is coercive on `H¹₀(Ω)`, then
with `u ∈ H¹₀(Ω)` this gives `H² ∩ H¹₀ ⊆ dom L` for `L = TauCeti.PDE.dirichletOperator`, via
`TauCeti.PDE.mem_domain_dirichletOperator_iff`, with `L u = -∑ᵢ ∂ᵢ(∑ⱼ aⁱʲ ∂ⱼu)`. -/
theorem exists_hasWeakLineDerivOn_flux_and_energyFormH1_eq_of_wkp_two
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x ↦ a x i j) Omega) {M : ℝ}
    (haM : ∀ i j, ∀ x ∈ Omega, |a x i j| ≤ M ∧ ‖∇ (fun y ↦ a y i j) x‖ ≤ M)
    (U : Wkp mu Omega 2 2) :
    ∃ d : ι → Lp ℝ 2 (mu.restrict Omega),
      (∀ i, HasWeakLineDerivOn mu Omega
        (fun x ↦ ∑ j, a x i j *
          ⟪W1p.gradient (Wkp.lowerOrder 1 U) x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) (d i)
        (EuclideanSpace.basisFun ι ℝ i)) ∧
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a 0 0 (Wkp.lowerOrder 1 U) (v : W1p mu Omega 2) =
          ∫ x in Omega, (-∑ i, d i x) * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  set e := EuclideanSpace.basisFun ι ℝ
  choose D hD using fun j ↦ Wkp.exists_hasWeakLineDerivOn_value 1 U (e j)
  simp only [Wkp.value_succ 1, Wkp.value_one] at hD
  set u : W1p mu Omega 2 := Wkp.lowerOrder 1 U
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have haLp (i j : ι) : MemLp (fun x ↦ a x i j) ⊤ (mu.restrict Omega) :=
    memLp_top_of_bound ((ha i j).continuousOn.aestronglyMeasurable hΩ) M <|
      (ae_restrict_mem hΩ).mono fun x hx ↦ (haM i j x hx).1
  have hdaLp (i j : ι) :
      MemLp (fun x ↦ fderiv ℝ (fun y ↦ a y i j) x (e i)) ⊤ (mu.restrict Omega) := by
    have hc := ((ha i j).fderiv_of_isOpen Omega.isOpen (by simp : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn
    refine memLp_top_of_bound ((hc.clm_apply continuousOn_const).aestronglyMeasurable hΩ) M ?_
    filter_upwards [ae_restrict_mem hΩ] with x hx
    calc
      ‖fderiv ℝ (fun y ↦ a y i j) x (e i)‖ ≤ ‖fderiv ℝ (fun y ↦ a y i j) x‖ * ‖e i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ M := by
        rw [(e.orthonormal.norm_eq_one i), mul_one, ← norm_gradient_eq_norm_fderiv]
        exact (haM i j x hx).2
  let g (i j : ι) (x : EuclideanSpace ℝ ι) : ℝ :=
    a x i j * ⟪W1p.gradient (D j) x, e i⟫_ℝ +
      fderiv ℝ (fun y ↦ a y i j) x (e i) * ⟪W1p.gradient u x, e j⟫_ℝ
  have hterm (i j : ι) : MemLp (g i j) 2 (mu.restrict Omega) := by
    have hcomponent (w : W1p mu Omega 2) (k : ι) :
        MemLp (fun x ↦ ⟪W1p.gradient w x, e k⟫_ℝ) 2 (mu.restrict Omega) := by
      have h : MemLp (fun x ↦ (innerSL ℝ (e k)) (W1p.gradient w x)) 2 (mu.restrict Omega) :=
        (innerSL ℝ (e k)).comp_memLp (W1p.gradient w)
      simpa only [innerSL_apply_apply, real_inner_comm] using h
    exact ((haLp i j).fun_mul (hcomponent (D j) i)).add
      ((hdaLp i j).fun_mul (hcomponent u j))
  have hg (i : ι) : MemLp (fun x ↦ ∑ j, g i j x) 2 (mu.restrict Omega) :=
    memLp_finsetSum _ fun j _ ↦ hterm i j
  let d (i : ι) : Lp ℝ 2 (mu.restrict Omega) := (hg i).toLp _
  have hd (i : ι) : HasWeakLineDerivOn mu Omega
      (fun x ↦ ∑ j, a x i j * ⟪W1p.gradient u x, e j⟫_ℝ) (d i) (e i) := by
    refine (HasWeakLineDerivOn.sum Finset.univ fun j _ ↦ ?_).congr_ae_deriv
      (hg i).coeFn_toLp.symm
    simpa only [g, smul_eq_mul, innerSL_apply_apply] using
      W1p.hasWeakLineDerivOn_smul_inner_gradient (v := e i) (ha i j) (hD j)
  exact ⟨d, hd, energyFormH1_eq_setIntegral_neg_sum_of_hasWeakLineDerivOn
    (memLp_energyIntegrand_of_abs_apply_le (fun i j ↦ (ha i j).continuousOn)
      fun i j x hx ↦ (haM i j x hx).1) hd⟩

/-- **An `L²` representative for the energy pairing of an `H²` function.** Let the entries of
`a` be `C¹` on `Ω`, with values and gradients bounded by `M`. If `u ∈ H²(Ω)`, then there is
`g ∈ L²(Ω)` with

`∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω g v` for every `v ∈ H¹₀(Ω)`.

This is `TauCeti.PDE.exists_hasWeakLineDerivOn_flux_and_energyFormH1_eq_of_wkp_two` without the
formula `g = -∑ᵢ ∂ᵢ(∑ⱼ aⁱʲ ∂ⱼu)`. If the energy form is coercive on `H¹₀(Ω)`, then with
`u ∈ H¹₀(Ω)` it gives `H² ∩ H¹₀ ⊆ dom L` for `L = TauCeti.PDE.dirichletOperator`, via
`TauCeti.PDE.mem_domain_dirichletOperator_iff`. -/
theorem exists_energyFormH1_eq_setIntegral_of_wkp_two
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x ↦ a x i j) Omega) {M : ℝ}
    (haM : ∀ i j, ∀ x ∈ Omega, |a x i j| ≤ M ∧ ‖∇ (fun y ↦ a y i j) x‖ ≤ M)
    (U : Wkp mu Omega 2 2) :
    ∃ g : Lp ℝ 2 (mu.restrict Omega), ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 0 (Wkp.lowerOrder 1 U) (v : W1p mu Omega 2) =
        ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  obtain ⟨d, -, hd⟩ := exists_hasWeakLineDerivOn_flux_and_energyFormH1_eq_of_wkp_two ha haM U
  exact ⟨-∑ i, d i, fun v ↦ (hd v).trans (integral_congr_ae (by
    filter_upwards [Lp.coeFn_neg_ae_eq_of_ae_eq (Lp.coeFn_fun_finsetSum Finset.univ d)] with x hx
    rw [hx, Pi.neg_apply]))⟩

end TauCeti.PDE
