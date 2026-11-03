/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact.RestrictedRadius
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeightedSubst

/-!
# Row compactness of weighted substitution operators

Let `R` be a complete ultrametric normed commutative ring. Over finitely many variables `Y`, let
`g` and series `h₁, …, h_k` converge on a strictly larger polydisc of polyradii `c`, with
`cⱼ > 1` and `‖hᵢ‖_c ≤ 1`. Then the weighted substitution `f ↦ g · f(h)` on the unit-radius
coefficient model (`TauCeti.MvPowerSeries.weightedSubstCLM`) factors through series restricted
at `c`. Its row `e` is then bounded by `‖g‖_c ‖1‖ c⁻ᵉ`, so it is row compact
(`TauCeti.MvPowerSeries.isRowCompact_weightedSubstCLM`), and in particular completely
continuous. Without the larger radius this fails: the identity is a weighted substitution.

## Main results

* `TauCeti.MvPowerSeries.norm_matrixCoeff_weightedSubstCLM_le`,
  `TauCeti.MvPowerSeries.isRowCompact_weightedSubstCLM`: the row bound and row compactness
  from convergence on a larger polydisc.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
* B. Dwork, *On the zeta function of a hypersurface*, Publ. Math. IHÉS **12** (1962), 5–68.
-/

public section

open scoped ZeroAtInfty

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {k : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

section RowCompact

variable {c : τ → ℝ} [∀ j, Fact (0 < c j)] (g : IsRestricted.subring (R := R) c)
  (h : Fin k → IsRestricted.subring (R := R) c) (hh : ∀ i, ‖h i‖ ≤ 1)

/-- The weighted substitution by the unit-radius restrictions of series restricted at polyradii
`c ≥ 1` reads off the coefficients of the weighted substitution at `c`. -/
private theorem weightedSubstCLM_restrictedRadiusHom_apply (hc : ∀ j, 1 ≤ c j)
    (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R)) (e : τ →₀ ℕ) :
    weightedSubstCLM (restrictedRadiusHom (fun _ ↦ zero_le_one) hc g)
        (fun i ↦ restrictedRadiusHom (fun _ ↦ zero_le_one) hc (h i))
        (fun i ↦ (norm_restrictedRadiusHom_le _ hc (h i)).trans (hh i)) x (.toTopology ⊥ e) =
      coeff e (restrictedWeightedSubstCLM g h hh (restrictedCoeffLinearIsometryEquiv.symm x) :
        MvPowerSeries τ R) := by
  rw [weightedSubstCLM_apply_toTopology, restrictedWeightedSubstCLM_apply, Subring.coe_mul,
    coe_restrictedRadiusHom]
  -- Both substitutions have the same coefficient sums; only the radius of the target differs.
  congr 2
  ext e'
  simp only [coeff_restrictedAnalyticSubst, coe_restrictedRadiusHom]

/-- **Row bound from a larger polydisc.** Let `g` and the `hᵢ` be restricted at polyradii
`c ≥ 1`, with `‖hᵢ‖_c ≤ 1`. Then row `e` of the matrix of the weighted substitution by their
unit-radius restrictions is bounded by `‖g‖_c ‖1‖ c⁻ᵉ`. -/
theorem norm_matrixCoeff_weightedSubstCLM_le [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))]
    (hc : ∀ j, 1 ≤ c j) (e : τ →₀ ℕ) (t : Fin k →₀ ℕ) :
    ‖(weightedSubstCLM (restrictedRadiusHom (fun _ ↦ zero_le_one) hc g)
        (fun i ↦ restrictedRadiusHom (fun _ ↦ zero_le_one) hc (h i))
        (fun i ↦ (norm_restrictedRadiusHom_le _ hc (h i)).trans (hh i))).matrixCoeff
        (.toTopology ⊥ e) (.toTopology ⊥ t)‖ ≤ ‖g‖ * ‖(1 : R)‖ * (e.prod (c · ^ ·))⁻¹ :=
  norm_matrixCoeff_le_of_apply_eq_coeff (C := ‖g‖)
    (fun x ↦ restrictedWeightedSubstCLM g h hh (restrictedCoeffLinearIsometryEquiv.symm x))
    (weightedSubstCLM_restrictedRadiusHom_apply g h hh hc)
    (fun x ↦ (norm_restrictedWeightedSubstCLM_apply_le g h hh _).trans_eq
      (by rw [LinearIsometryEquiv.norm_map])) e (.toTopology ⊥ t)

/-- **Weighted substitutions converging on a larger polydisc are row compact.** Over finitely
many variables `Y`, let `g` and the `hᵢ` be restricted at polyradii `c` with every `cⱼ > 1`, and
`‖hᵢ‖_c ≤ 1`. Then the weighted substitution `f ↦ g · f(h)` by their unit-radius restrictions is
row compact on the coefficient model. -/
theorem isRowCompact_weightedSubstCLM [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))]
    [Finite τ] (hc : ∀ j, 1 < c j) :
    (weightedSubstCLM (restrictedRadiusHom (fun _ ↦ zero_le_one) (fun j ↦ (hc j).le) g)
      (fun i ↦ restrictedRadiusHom (fun _ ↦ zero_le_one) (fun j ↦ (hc j).le) (h i))
      (fun i ↦ (norm_restrictedRadiusHom_le _ _ (h i)).trans (hh i))).IsRowCompact :=
  isRowCompact_of_apply_eq_coeff hc (C := ‖g‖)
    (fun x ↦ restrictedWeightedSubstCLM g h hh (restrictedCoeffLinearIsometryEquiv.symm x))
    (weightedSubstCLM_restrictedRadiusHom_apply g h hh fun j ↦ (hc j).le)
    (fun x ↦ (norm_restrictedWeightedSubstCLM_apply_le g h hh _).trans_eq
      (by rw [LinearIsometryEquiv.norm_map]))

end RowCompact

end TauCeti.MvPowerSeries
