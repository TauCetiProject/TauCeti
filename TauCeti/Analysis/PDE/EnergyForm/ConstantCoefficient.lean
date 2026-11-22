/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.W1p.Symmetry

/-!
# Constant-coefficient energy forms against `H¹₀`

For a constant matrix `A`, `u ∈ H¹(Ω)` and `v ∈ H¹₀(Ω)`, the energy form `∫_Ω ∇vᵀ A ∇u` depends
only on the symmetric part `(A + Aᵀ) / 2` of `A`
(`TauCeti.PDE.energyFormH1_const_coefficientSymmetricPart`). Against a test function `ψ` the form
is `∑ᵢⱼ Aᵢⱼ ∫ (∂ᵢψ) ∂ⱼu`, and the pairings `∫ (∂ᵢψ) ∂ⱼu` are symmetric in `i` and `j`
(`TauCeti.W1p.integral_lineDeriv_smul_inner_gradient_comm`), so an antisymmetric part of `A`
contributes nothing; the identity extends to `H¹₀(Ω)` by density. Hence a weak solution of
`-div(A ∇u) = 0`, tested against `H¹₀(Ω)`, also solves the equation for the symmetric part of `A`,
which has the same ellipticity constants.

## Main declarations

* `TauCeti.PDE.energyFormH1_const_coefficientSymmetricPart`: a constant-coefficient energy form
  on `H¹(Ω) × H¹₀(Ω)` is unchanged by replacing the matrix by its symmetric part.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace Matrix

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

/-- Against a test function `ψ`, the constant-coefficient energy form of `u` is
`∑ᵢⱼ Aᵢⱼ ∫ (∂ᵢψ) ∂ⱼu`. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_sum_sum (A : Matrix ι ι ℝ) (u : W1p mu Omega 2)
    (ψ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 ψ) =
      ∑ j, ∑ i, A i j * ∫ x, lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) x
        (EuclideanSpace.basisFun ι ℝ i) •
          ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hloc : ∀ j, LocallyIntegrableOn (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) Omega mu := fun j =>
    (W1p.hasWeakLineDerivOn_inner_gradient u (b j)).locallyIntegrableOn_deriv
  rw [energyFormH1_ofTestFunctionₗ_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The `j`-th column of `A` is `∑ᵢ Aᵢⱼ bᵢ`.
  have hcol : WithLp.toLp 2 (Aᵀ j) = ∑ i, A i j • b i := by
    rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr (WithLp.toLp 2 (Aᵀ j))]
    simp [b]
  have hpt : ∀ x, lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) •
        innerSL ℝ (W1p.gradient u x) (b j) =
      ∑ i, A i j * (lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) x (b i) •
        ⟪W1p.gradient u x, b j⟫_ℝ) := fun x => by
    rw [hcol, TestFunction.lineDeriv_eq_fderiv, map_sum, smul_eq_mul, innerSL_apply_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, smul_eq_mul, TestFunction.lineDeriv_eq_fderiv, mul_assoc]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ fun i _ =>
    (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc j) ψ (b i)).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- **A constant-coefficient energy form against `H¹₀` sees only the symmetric part.** For a
constant matrix `A`, `u ∈ H¹(Ω)` and `v ∈ H¹₀(Ω)`,
`∫_Ω ∇vᵀ ((A + Aᵀ) / 2) ∇u = ∫_Ω ∇vᵀ A ∇u`. -/
theorem energyFormH1_const_coefficientSymmetricPart (A : Matrix ι ι ℝ) (u : W1p mu Omega 2)
    (v : W1p0 mu Omega 2) :
    energyFormH1 (fun _ => coefficientSymmetricPart A) 0 0 u (v : W1p mu Omega 2) =
      energyFormH1 (fun _ => A) 0 0 u v := by
  set S := coefficientSymmetricPart A
  have hS : MemLp (fun x => energyIntegrand ((fun _ => S) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega) := by
    simpa only [Pi.zero_apply] using memLp_top_const (energyIntegrand S 0 0)
  have hA : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega) := by
    simpa only [Pi.zero_apply] using memLp_top_const (energyIntegrand A 0 0)
  -- The identity is closed in `v`, so it suffices to check it on test functions.
  have hclosed : IsClosed {w : W1p mu Omega 2 |
      energyFormH1 (fun _ => S) 0 0 u w = energyFormH1 (fun _ => A) 0 0 u w} := by
    simp_rw [← energyFormH1L_apply hS, ← energyFormH1L_apply hA]
    exact isClosed_eq (energyFormH1L hS u).continuous (energyFormH1L hA u).continuous
  refine w1p0Submodule_subset_of_isClosed hclosed (fun ψ => ?_) v.property
  set J : ι → ι → ℝ := fun i j => ∫ x, lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) x
    (EuclideanSpace.basisFun ι ℝ i) • ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ ∂mu
  have hJ : ∀ i j, J i j = J j i := fun i j =>
    W1p.integral_lineDeriv_smul_inner_gradient_comm _ _ _ _
  have hsum : ∀ M : Matrix ι ι ℝ, energyFormH1 (fun _ => M) 0 0 u
      (W1p.ofTestFunctionₗ mu Omega 2 ψ) = ∑ j, ∑ i, M i j * J i j := fun M =>
    energyFormH1_ofTestFunctionₗ_eq_sum_sum M u ψ
  rw [Set.mem_ofPred_eq, hsum, hsum]
  -- The transposed half pairs `Aⱼᵢ` with `J i j = J j i`, which relabels to the `A` sum.
  have hT : ∑ j, ∑ i, A j i * J i j = ∑ j, ∑ i, A i j * J i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ]
  simp only [S, coefficientSymmetricPart_apply, add_div, add_mul, Finset.sum_add_distrib,
    div_mul_eq_mul_div, ← Finset.sum_div, hT]
  ring

end PDE

end TauCeti
