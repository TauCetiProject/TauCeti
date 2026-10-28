/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Smooth compactly supported fields are dense in vector-valued `W^{1,p}(ℝⁿ)`

For a finite-dimensional target `F` and `1 ≤ p < ∞`, every element of the first-order
weak-derivative graph over `Lᵖ(ℝⁿ, F)` is a limit of the graph elements of smooth compactly
supported fields `ℝⁿ → F`. A priori estimates proved for smooth compactly supported fields
therefore extend to the whole Sobolev space by continuity.

The proof is coordinatewise. A scalar Sobolev function `u` and a vector `b : F` give the field
`x ↦ u x • b` (`TauCeti.WeakDerivStep.smulRightW1pL`), with weak derivative `v ↦ ∂ᵥ u • b`.
Choosing a basis `bᵢ` of `F` with coordinate functionals `ℓᵢ`, a field `u` is the sum of the
fields `ℓᵢ ∘ u • bᵢ` built from its scalar projections `TauCeti.WeakDerivStep.toW1pL`. Each scalar
projection is a limit of test functions (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`), and a
test function `ψ` gives the smooth compactly supported field `x ↦ ψ x • bᵢ`.

## Main declarations

* `TauCeti.WeakDerivStep.smulRightW1pL`: the bounded linear map `u ↦ (x ↦ u x • b)` from scalar
  Sobolev functions to `F`-valued ones.
* `TauCeti.WeakDerivStep.prev_smulRightW1pL_ofTestFunctionₗ_ae_eq`: for a test function `ψ`, this
  field is represented by `x ↦ ψ x • b`.
* `TauCeti.WeakDerivStep.sum_smulRightW1pL_toW1pL`: a field is the sum of its coordinate fields.
* `TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`: the fields with a smooth
  compactly supported representative are dense.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2 (the scalar case, which is applied here
coordinatewise).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Distributions

namespace TauCeti.WeakDerivStep

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative `v ↦ ⟪g, v⟫ • b` of the field `x ↦ u x • b` at a point where the scalar
function `u` has gradient `g`. -/
def smulRightGradientL (b : F) : E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E ℝ F (ContinuousLinearMap.toSpanSingleton ℝ b)).comp
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation formula for `smulRightGradientL`. -/
@[simp]
theorem smulRightGradientL_apply (b : F) (g v : E) :
    smulRightGradientL b g v = inner ℝ g v • b := by
  simp [smulRightGradientL]

end Gradient

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The field `x ↦ u x • b` of a scalar Sobolev function has weak derivative
`v ↦ ⟪∇u x, v⟫ • b`. -/
theorem hasWeakFDerivOn_smulRight (b : F) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega
      ((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u))
      ((smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u)) := by
  refine ((W1p.hasWeakFDerivOn u).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ b)).congr_ae
    ((ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL (W1p.value u)).symm
    |>.congr_ae_deriv ?_
  filter_upwards [(smulRightGradientL b).coeFn_compLpL (W1p.gradient u)] with x hx
  rw [hx]
  ext v
  simp [real_inner_comm]

/-- The bounded linear map sending a scalar Sobolev function `u` to the `F`-valued Sobolev field
`x ↦ u x • b`. -/
def smulRightW1pL (b : F) :
    W1p mu Omega p →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      ((((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega)).comp
          W1p.valueL).prod
        (((smulRightGradientL b).compLpL p (mu.restrict Omega)).comp W1p.gradientL)))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr (by
      simpa using hasWeakFDerivOn_smulRight b u)

/-- The value of `smulRightW1pL b u` is the class of `x ↦ u x • b`. -/
@[simp]
theorem prev_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    prev _ (smulRightW1pL b u) =
      (ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u) := by
  simp [prev_coe, smulRightW1pL]

/-- The weak derivative of `smulRightW1pL b u` is the class of `x ↦ (v ↦ ⟪∇u x, v⟫ • b)`. -/
@[simp]
theorem weakFDeriv_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    weakFDeriv _ (smulRightW1pL b u) =
      (smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u) := by
  simp [weakFDeriv_coe, smulRightW1pL]

/-- The field `smulRightW1pL b φ` of a test function `φ` is represented by `x ↦ φ x • b`. -/
theorem prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (b : F) (φ : 𝓓(Omega, ℝ)) :
    ⇑(prev _ (smulRightW1pL b (W1p.ofTestFunctionₗ mu Omega p φ)))
      =ᵐ[mu.restrict Omega] fun x ↦ φ x • b := by
  rw [prev_smulRightW1pL, W1p.value_ofTestFunctionₗ]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL
    (testFunctionLp (mu := mu) p φ), testFunctionLp_apply_ae (mu := mu) p φ] with x hx hφ
  rw [hx, ContinuousLinearMap.toSpanSingleton_apply, hφ]

/-- **Coordinate reconstruction.** For a basis `b` of `F`, an `F`-valued Sobolev field is the sum
of the fields `ℓᵢ ∘ u • bᵢ` built from its scalar coordinate projections. -/
theorem sum_smulRightW1pL_toW1pL [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ∑ i, smulRightW1pL (b i) (toW1pL _ (b.coord i).toContinuousLinearMap u) = u := by
  apply ext
  rw [← prevL_apply, map_sum]
  simp only [prevL_apply, prev_smulRightW1pL, value_toW1pL, ContinuousLinearMap.id_apply]
  exact (eq_sum_basis_compLpL b (prev _ u)).symm

/-- **Density of smooth compactly supported fields.** For a finite-dimensional target and
`1 ≤ p < ∞`, the elements of the weak-derivative graph over `Lᵖ(ℝⁿ, F)` represented by a smooth
compactly supported field are dense. -/
theorem dense_setOf_exists_contDiff_hasCompactSupport [FiniteDimensional ℝ F] (hp : p ≠ ∞) :
    Dense {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ} := by
  classical
  -- The represented fields form a submodule.
  let S : Submodule ℝ (WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E))))) :=
    { carrier := {u | ∃ φ : E → F, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ⇑(prev _ u) =ᵐ[mu.restrict (⊤ : Opens E)] φ}
      add_mem' := by
        rintro u v ⟨φ, hφ, hφc, hu⟩ ⟨ψ, hψ, hψc, hv⟩
        refine ⟨φ + ψ, hφ.add hψ, hφc.add hψc, ?_⟩
        rw [← prevL_apply, map_add, prevL_apply, prevL_apply]
        filter_upwards [Lp.coeFn_add (prev _ u) (prev _ v), hu, hv] with x hx hux hvx
        rw [hx, Pi.add_apply, hux, hvx, Pi.add_apply]
      zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, by
        rw [← prevL_apply, map_zero]
        exact Lp.coeFn_zero _ _ _⟩
      smul_mem' := by
        rintro c u ⟨φ, hφ, hφc, hu⟩
        refine ⟨c • φ, hφ.const_smul c, hφc.smul_left, ?_⟩
        rw [← prevL_apply, map_smul, prevL_apply]
        filter_upwards [Lp.coeFn_smul c (prev _ u), hu] with x hx hux
        rw [hx, Pi.smul_apply, hux, Pi.smul_apply] }
  -- The field `x ↦ ψ x • bᵢ` of a test function `ψ` is represented.
  have htest (y : F) (ψ : 𝓓((⊤ : Opens E), ℝ)) :
      smulRightW1pL y (W1p.ofTestFunctionₗ mu ⊤ p ψ) ∈ S := by
    exact ⟨fun x ↦ ψ x • y, ψ.contDiff.smul contDiff_const,
      ψ.hasCompactSupport.smul_right, prev_smulRightW1pL_ofTestFunctionₗ_ae_eq y ψ⟩
  -- Each coordinate field is a limit of represented fields.
  have hcoord (y : F) (w : W1p mu ⊤ p) : smulRightW1pL y w ∈ closure (S : Set _) := by
    refine map_mem_closure (smulRightW1pL y).continuous
      (W1p.denseRange_ofTestFunctionₗ_top hp w) ?_
    rintro _ ⟨ψ, rfl⟩
    exact htest y ψ
  intro u
  let b := Module.finBasis ℝ F
  rw [← sum_smulRightW1pL_toW1pL b u]
  exact S.topologicalClosure.sum_mem fun i _ ↦ hcoord (b i) _

end TauCeti.WeakDerivStep
