/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact.RestrictedRadius
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeightedSubst

/-!
# Matrices of weighted substitution operators

Let `R` be a complete ultrametric normed commutative ring. At unit radii, the coefficient
isometry `TauCeti.MvPowerSeries.restrictedCoeffLinearIsometryEquiv` identifies restricted series
with null coefficient families, and so turns the weighted substitution operator
`f ↦ g · f(h)` (`TauCeti.MvPowerSeries.restrictedWeightedSubstCLM`) into a map between model
spaces `C₀(Fin k →₀ ℕ, R) → C₀(τ →₀ ℕ, R)`
(`TauCeti.MvPowerSeries.restrictedWeightedSubstCoeffCLM`). Its matrix entry in row `e` and
column `t` is the coefficient of `Yᵉ` in `g hᵗ`
(`TauCeti.MvPowerSeries.matrixCoeff_restrictedWeightedSubstCoeffCLM`).

In one variable, after identifying the exponents with `ℕ`, these are the entries
`coeff i (g hʲ)`, which characterise the coefficient kernel `g(X) / (1 - h(X) Y)` by
`ContinuousLinearMap.coefficientKernel_mul_one_sub_eq_C_iff`.

Suppose that the weight and the substituted series are the unit-radius restrictions of series
`G` and `Hᵢ` restricted at polyradii `c`, with `‖Hᵢ‖_c ≤ 1`. Then the operator factors through
series restricted at `c`, and row `e` of its matrix is bounded by `‖G‖_c ‖1‖ c⁻ᵉ`
(`TauCeti.MvPowerSeries.norm_matrixCoeff_restrictedWeightedSubstCoeffCLM_le`). If every
`cⱼ > 1`, these bounds tend to zero, so the operator is row compact
(`TauCeti.MvPowerSeries.isRowCompact_restrictedWeightedSubstCoeffCLM`), and the weighted
substitution operator on unit-radius restricted series is completely continuous
(`TauCeti.MvPowerSeries.isCompletelyContinuous_restrictedWeightedSubstCLM`). This is the
mechanism behind the compactness of Dwork's operators and of the `U_p`-operator on
overconvergent functions. Without the larger radius it fails: substituting the variables with
weight one is the identity, which is not completely continuous
(`TauCeti.MvPowerSeries.not_isCompletelyContinuous_id_isRestrictedSubring`).

## Main definitions

* `TauCeti.MvPowerSeries.restrictedWeightedSubstCoeffCLM`: the weighted substitution operator in
  coefficient coordinates.

## Main results

* `TauCeti.MvPowerSeries.matrixCoeff_restrictedWeightedSubstCoeffCLM`: the matrix entries are the
  coefficients of `g hᵗ`.
* `TauCeti.MvPowerSeries.isRowCompact_restrictedWeightedSubstCoeffCLM`: overconvergent weight
  and substitution give a row-compact operator.
* `TauCeti.MvPowerSeries.isCompletelyContinuous_restrictedWeightedSubstCLM`: the corresponding
  operator on unit-radius restricted series is completely continuous.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open scoped ZeroAtInfty

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

/-- The unit radius is positive. -/
local instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

variable {k : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- The weighted substitution operator `f ↦ g · f(h)` between unit-radius restricted series,
written in coefficient coordinates as a map between model spaces of null coefficient families. -/
noncomputable def restrictedWeightedSubstCoeffCLM
    (g : IsRestricted.subring (R := R) (fun _ : τ ↦ 1))
    (h : Fin k → IsRestricted.subring (R := R) (fun _ : τ ↦ 1)) (hh : ∀ i, ‖h i‖ ≤ 1) :
    C₀(WithDiscreteTopology (Fin k →₀ ℕ), R) →L[R] C₀(WithDiscreteTopology (τ →₀ ℕ), R) :=
  ((restrictedCoeffLinearIsometryEquiv (σ := τ) (R := R)).toContinuousLinearEquiv :
      _ →L[R] _).comp <| (restrictedWeightedSubstCLM (r := fun _ ↦ 1) g h hh).comp
    ((restrictedCoeffLinearIsometryEquiv (σ := Fin k) (R := R)).symm.toContinuousLinearEquiv :
      _ →L[R] _)

section Matrix

variable (g : IsRestricted.subring (R := R) (fun _ : τ ↦ 1))
  (h : Fin k → IsRestricted.subring (R := R) (fun _ : τ ↦ 1)) (hh : ∀ i, ‖h i‖ ≤ 1)

/-- The coefficients of the image of a null family `x` are those of `g · f(h)`, where `f` is the
restricted series with coefficient family `x`. -/
@[simp]
theorem restrictedWeightedSubstCoeffCLM_apply (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R))
    (e : τ →₀ ℕ) :
    restrictedWeightedSubstCoeffCLM g h hh x (.toTopology ⊥ e) =
      coeff e (restrictedWeightedSubstCLM (r := fun _ ↦ 1) g h hh
        (restrictedCoeffLinearIsometryEquiv.symm x) : _root_.MvPowerSeries τ R) := by
  simp [restrictedWeightedSubstCoeffCLM]

/-- Conjugating the coefficient form by the coefficient isometry recovers the weighted
substitution operator on unit-radius restricted series. -/
theorem restrictedWeightedSubstCLM_eq_comp_restrictedWeightedSubstCoeffCLM :
    restrictedWeightedSubstCLM (r := fun _ ↦ 1) g h hh =
      ((restrictedCoeffLinearIsometryEquiv (σ := τ) (R := R)).symm.toContinuousLinearEquiv :
        _ →L[R] _).comp ((restrictedWeightedSubstCoeffCLM g h hh).comp
          ((restrictedCoeffLinearIsometryEquiv (σ := Fin k) (R := R)).toContinuousLinearEquiv :
            _ →L[R] _)) := by
  ext1 f
  simp [restrictedWeightedSubstCoeffCLM]

variable [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))]

/-- **The matrix of a weighted substitution.** The entry in row `e` and column `t` is the
coefficient of `Yᵉ` in `g hᵗ`. -/
theorem matrixCoeff_restrictedWeightedSubstCoeffCLM (e : τ →₀ ℕ) (t : Fin k →₀ ℕ) :
    (restrictedWeightedSubstCoeffCLM g h hh).matrixCoeff (.toTopology ⊥ e) (.toTopology ⊥ t) =
      coeff e ((g : _root_.MvPowerSeries τ R) * ∏ i, (h i : _root_.MvPowerSeries τ R) ^ t i) := by
  have hsingle : restrictedCoeffLinearIsometryEquiv.symm
      (ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) (1 : R)) =
        (⟨monomial t 1, isRestricted_monomial _ t 1⟩ :
          IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    convert (restrictedCoeffLinearIsometryEquiv_monomial t (1 : R)).symm
  rw [ContinuousLinearMap.matrixCoeff_apply, restrictedWeightedSubstCoeffCLM_apply, hsingle,
    restrictedWeightedSubstCLM_monomial]
  simp

end Matrix

section RowCompact

variable [Finite τ] {c : τ → ℝ} [∀ j, Fact (0 < c j)] (hc : ∀ j, 1 < c j)
  (G : IsRestricted.subring (R := R) c) (H : Fin k → IsRestricted.subring (R := R) c)
  {g : IsRestricted.subring (R := R) (fun _ : τ ↦ 1)}
  {h : Fin k → IsRestricted.subring (R := R) (fun _ : τ ↦ 1)} (hh : ∀ i, ‖h i‖ ≤ 1)
  (hg : (g : _root_.MvPowerSeries τ R) = G) (hH : ∀ i, (h i : _root_.MvPowerSeries τ R) = H i)
  (hHc : ∀ i, ‖H i‖ ≤ 1)

omit [Finite τ] in
include hg hH in
/-- If `g` and the `hᵢ` are the unit-radius restrictions of `G` and `Hᵢ`, the coefficient form of
`f ↦ g · f(h)` takes the coefficients of `f ↦ G · f(H)`. -/
private theorem restrictedWeightedSubstCoeffCLM_apply_eq_coeff
    (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R)) (e : τ →₀ ℕ) :
    restrictedWeightedSubstCoeffCLM g h hh x (.toTopology ⊥ e) =
      coeff e (restrictedWeightedSubstCLM (r := fun _ ↦ 1) G H hHc
        (restrictedCoeffLinearIsometryEquiv.symm x) : _root_.MvPowerSeries τ R) := by
  rw [restrictedWeightedSubstCoeffCLM_apply]
  simp only [restrictedWeightedSubstCLM_apply, Subring.coe_mul, hg]
  congr 2
  ext e'
  simp [coeff_restrictedAnalyticSubst, hH]

variable [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))]

omit [Finite τ] in
include hg hH hHc in
/-- **Row bound for an overconvergent weighted substitution.** If `g` and the `hᵢ` are the
unit-radius restrictions of series `G` and `Hᵢ` restricted at positive polyradii `c`, with
`‖Hᵢ‖_c ≤ 1`, the entries of row `e` of the matrix of `f ↦ g · f(h)` are bounded by
`‖G‖_c ‖1‖ c⁻ᵉ`. -/
theorem norm_matrixCoeff_restrictedWeightedSubstCoeffCLM_le (e : τ →₀ ℕ)
    (j : WithDiscreteTopology (Fin k →₀ ℕ)) :
    ‖(restrictedWeightedSubstCoeffCLM g h hh).matrixCoeff (.toTopology ⊥ e) j‖ ≤
      ‖G‖ * ‖(1 : R)‖ * (e.prod (c · ^ ·))⁻¹ := by
  refine norm_matrixCoeff_le_of_apply_eq_coeff
    (fun x ↦ restrictedWeightedSubstCLM (r := fun _ ↦ 1) G H hHc
      (restrictedCoeffLinearIsometryEquiv.symm x))
    (restrictedWeightedSubstCoeffCLM_apply_eq_coeff G H hh hg hH hHc) (fun x ↦ ?_) e j
  simpa using norm_restrictedWeightedSubstCLM_apply_le G H hHc
    (restrictedCoeffLinearIsometryEquiv.symm x)

include hc hg hH hHc in
/-- **Overconvergent weighted substitutions are row compact.** If `g` and the `hᵢ` are the
unit-radius restrictions of series `G` and `Hᵢ` restricted at polyradii `c`, with every `cⱼ > 1`
and `‖Hᵢ‖_c ≤ 1`, then `f ↦ g · f(h)` at unit radius, in coefficient coordinates, is row
compact. -/
theorem isRowCompact_restrictedWeightedSubstCoeffCLM :
    (restrictedWeightedSubstCoeffCLM g h hh).IsRowCompact := by
  refine isRowCompact_of_apply_eq_coeff hc (C := ‖G‖)
    (fun x ↦ restrictedWeightedSubstCLM (r := fun _ ↦ 1) G H hHc
      (restrictedCoeffLinearIsometryEquiv.symm x))
    (restrictedWeightedSubstCoeffCLM_apply_eq_coeff G H hh hg hH hHc) (fun x ↦ ?_)
  simpa using norm_restrictedWeightedSubstCLM_apply_le G H hHc
    (restrictedCoeffLinearIsometryEquiv.symm x)

omit [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))] in
include hc hg hH hHc in
/-- **Overconvergent weighted substitutions are completely continuous.** If `g` and the `hᵢ` are
the unit-radius restrictions of series `G` and `Hᵢ` restricted at polyradii `c`, with every
`cⱼ > 1` and `‖Hᵢ‖_c ≤ 1`, then `f ↦ g · f(h)` is a completely continuous operator between
unit-radius restricted series. -/
theorem isCompletelyContinuous_restrictedWeightedSubstCLM :
    (restrictedWeightedSubstCLM (r := fun _ ↦ 1) g h hh).IsCompletelyContinuous := by
  classical
  rw [restrictedWeightedSubstCLM_eq_comp_restrictedWeightedSubstCoeffCLM]
  refine (((isRowCompact_restrictedWeightedSubstCoeffCLM hc G H hh hg hH hHc
    ).isCompletelyContinuous).comp_clm_of_bound _ one_pos fun x ↦ ?_).clm_comp_of_bound _
      one_pos fun x ↦ ?_ <;>
  simp

end RowCompact

end TauCeti.MvPowerSeries
