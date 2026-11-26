/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Comp.Basic
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap

/-!
# Complex orientations and the determinant line of a composition

For complex-linear maps `f : M → N` and `g : N → P` with finite-dimensional kernels and
cokernels, the real determinant lines of `f`, `g` and `g ∘ f` carry complex orientations
(`LinearMap.IsComplexPositiveDetLine`), and the composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) identifies the first with the tensor
product of the other two. This file shows that the composition law respects these orientations:
it sends a complex positive element of `det (g ∘ f)` to the tensor product of complex positive
elements of `det f` and `det g`
(`LinearMap.IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul`). No sign corrections
enter, because complex vector spaces have even real dimension.

The composition law is the six-term isomorphism `TauCeti.detLineSixTermEquiv` of the exact
sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`, whose terms
are formed from the underlying real-linear maps. It is therefore an instance of the statement
about six-term exact sequences of real vector spaces isomorphic to the real restriction of an
exact sequence of complex vector spaces and complex-linear maps
(`TauCeti.exists_isComplexPositiveTMulDual_detLineSixTermEquiv_congr_eq_tmul`).
For the composition, the isomorphisms are those between the real and complex kernels and
cokernels (`LinearMap.kerRestrictScalarsEquiv`, `LinearMap.cokerRestrictScalarsEquiv`), which
commute with the maps of the two kernel–cokernel sequences
(`LinearMap.kerCompToKer_comp_kerRestrictScalarsEquiv` and its companions).

This is how complex orientations of determinant lines behave under composition of complex-linear
maps, such as Fredholm operators. For instance, a complex-linear operator `D` cut down by
complex-linear incidence conditions `ev` is the composite of `D.prod ev` with the projection onto
the target of `D`, so the complex orientations of `det (D.prod ev)` and of the determinant line of
the projection give that of `det D`.

## Main results

* `LinearMap.IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul`: the composition law of
  determinant lines respects complex orientations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences, and
  the canonical orientation of the determinant line of a complex-linear Fredholm operator).
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

open TauCeti

variable {M N P : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  [AddCommGroup P] [Module ℂ P] [Module ℝ P] [IsScalarTower ℝ ℂ P]

variable {f : M →ₗ[ℂ] N} {g : N →ₗ[ℂ] P} [FiniteDimensional ℝ (ker (f.restrictScalars ℝ))]
  [FiniteDimensional ℝ (ker (g.restrictScalars ℝ))]
  [FiniteDimensional ℝ (N ⧸ range (f.restrictScalars ℝ))]
  [FiniteDimensional ℝ (P ⧸ range (g.restrictScalars ℝ))]

/-- **The composition law of determinant lines respects complex orientations.** For complex-linear
maps `f` and `g` with finite-dimensional kernels and cokernels, the isomorphism
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) sends a complex positive element of
`det (g ∘ f)` to `x ⊗ y` for complex positive elements `x` of `det f` and `y` of `det g`. -/
theorem IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul
    {z : ((g ∘ₗ f).restrictScalars ℝ).detLine} (hz : (g ∘ₗ f).IsComplexPositiveDetLine z) :
    ∃ x y, f.IsComplexPositiveDetLine x ∧ g.IsComplexPositiveDetLine y ∧
      (f.restrictScalars ℝ).detLineCompEquiv (g.restrictScalars ℝ) z = x ⊗ₜ y := by
  have : FiniteDimensional ℝ (P ⧸ range (g.restrictScalars ℝ ∘ₗ f.restrictScalars ℝ)) :=
    Module.Finite.quotient_range_comp (f.restrictScalars ℝ) (g.restrictScalars ℝ)
  -- The kernel–cokernel sequence of the real composite is isomorphic to that of the complex
  -- composite, through the identifications of the real and complex kernels and cokernels.
  obtain ⟨s₁, s₂, hs₁, hs₂, h⟩ := exists_isComplexPositiveTMulDual_detLineSixTermEquiv_congr_eq_tmul
    (Submodule.inclusion_injective _)
    ((f.restrictScalars ℝ).exact_inclusion_kerCompToKer (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_kerCompToKer_kerToCoker (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_kerToCoker_cokerToCokerComp (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_cokerToCokerComp_factor (g.restrictScalars ℝ))
    (Submodule.factor_surjective _) _ _ _ _ _ _ (inclusion_comp_kerRestrictScalarsEquiv ℝ f g)
    (kerCompToKer_comp_kerRestrictScalarsEquiv ℝ f g)
    (kerToCoker_comp_kerRestrictScalarsEquiv ℝ f g)
    (cokerToCokerComp_comp_cokerRestrictScalarsEquiv_symm ℝ f g)
    (factor_comp_cokerRestrictScalarsEquiv_symm ℝ f g)
    (isComplexPositiveDetLine_iff.1 hz)
  have hz' : TensorProduct.congr ((g ∘ₗ f).kerRestrictScalarsEquiv ℝ).detLineCongr
      ((g ∘ₗ f).cokerRestrictScalarsEquiv ℝ).symm.detLineCongr.symm.dualMap
        ((g ∘ₗ f).detLineRestrictScalarsEquiv z) = z :=
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr (g ∘ₗ f)) _).symm.trans
      (LinearEquiv.symm_apply_apply _ z)
  refine ⟨f.detLineRestrictScalarsEquiv.symm s₁, g.detLineRestrictScalarsEquiv.symm s₂,
    by rwa [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply],
    by rwa [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply], ?_⟩
  -- `(g ∘ₗ f).restrictScalars ℝ` is `g.restrictScalars ℝ ∘ₗ f.restrictScalars ℝ` by definition
  -- (`LinearMap.restrictScalars_comp` is `rfl`), but not syntactically, so the two determinant
  -- lines are matched by `Eq.trans`, which checks definitional equality, rather than by rewriting.
  rw [detLineCompEquiv_def]
  exact ((congrArg _ hz').symm.trans h).trans (congrArg₂ (· ⊗ₜ ·)
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr f) s₁).symm
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr g) s₂).symm)

end LinearMap
