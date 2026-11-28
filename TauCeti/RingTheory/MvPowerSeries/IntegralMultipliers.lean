/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Integral multipliers for rescaled products

If a product of one-variable rescalings has an inverse expressed integrally in a formal
coordinate, the product along a family of linear forms has an inverse expressed integrally
in the substituted coordinates. One can put that inverse, and a prescribed integral series
in one of those coordinates, into just one factor of the rescaled product. The resulting
product identity allows coefficient bounds for the prescribed series to be transferred to
products of theta jets.

This is the cancellation step in `New.CMLattice.leastValLE_of_unit_coefficients` in
[lsernau/grh-lean, `New/Derivatives/Sharpness/LeastValuation.lean`][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Derivatives/Sharpness/LeastValuation.lean
-/

public section

open Finset

namespace MvPowerSeries

/-- Transport a one-variable inverse for the product of the rescalings of `θ` through each
linear form `μ j`, with multiplicity `m j`. Multiplying the resulting product by the inverse
and by `g` in coordinate `j₀` requires changing only one factor, the one indexed by `i₀`.
The preimages `H i` have coefficients in `O`; their images are evaluated at the family
of formal parameters `y ∘ μ j`. -/
theorem exists_integral_multipliers_prod_rescale {O R J I σ : Type*}
    [CommRing O] [CommRing R] [Algebra O R] [Fintype J] [Fintype I]
    (θ y : PowerSeries R) (u g : PowerSeries O) (hy : PowerSeries.HasSubst y)
    (δ : I → R) (μ : J → MvPowerSeries σ R) (m : J → ℕ) (i₀ : I) (j₀ : J)
    (hμ : ∀ j, ∀ d ∈ Function.support (μ j), d.degree = 1)
    (hu : PowerSeries.substAlgHom hy u * (∏ i, θ.rescale (δ i)) = 1) :
    ∃ H : I → MvPowerSeries J O, (∀ i ≠ i₀, H i = 1) ∧
      (∏ i, subst (fun j ↦ y.subst (μ j)) (H i) *
          rescale (Function.const σ (δ i)) (∏ j, (θ.subst (μ j)) ^ m j)) =
        g.subst (y.subst (μ j₀)) := by
  classical
  have hs (j : J) : PowerSeries.HasSubst (μ j) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_apply]
    by_contra hz
    simpa using hμ j 0 hz
  let P : J → MvPowerSeries σ R := fun j ↦ y.subst (μ j)
  have hP : HasSubst P := by
    refine ⟨fun j ↦ ?_, fun _ ↦ Set.toFinite _⟩
    have hj : PowerSeries.HasSubst (P j) := by
      simpa only [P, PowerSeries.coe_substAlgHom] using hy.comp (hs j)
    exact (PowerSeries.hasSubst_iff.mp hj).const_coeff ()
  let V : MvPowerSeries J O := ∏ j, (u.subst (X j)) ^ m j
  let G : MvPowerSeries J O := g.subst (X j₀)
  refine ⟨fun i ↦ if i = i₀ then G * V else 1, fun i hi ↦ ite_eq_right hi, ?_⟩
  have heval (f : PowerSeries O) (j : J) :
      subst P (f.subst (X j : MvPowerSeries J O)) = f.subst (P j) := by
    rw [subst_powerSeriesSubst hP (PowerSeries.HasSubst.X j), subst_X hP]
  -- Commute the two products after moving each scalar rescaling through each linear form.
  have hprod :
      (∏ i, rescale (Function.const σ (δ i)) (∏ j, (θ.subst (μ j)) ^ m j)) =
        ∏ j, (∏ i, (θ.rescale (δ i)).subst (μ j)) ^ m j := by
    have h (i : I) (j : J) :=
      PowerSeries.subst_rescale_of_degree_eq_one (δ i) (μ j) (hμ j) θ
    simp_rw [← Finset.prod_pow]
    rw [← Finset.prod_comm]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [← rescaleAlgHom_apply, map_prod]
    simp only [map_pow, rescaleAlgHom_apply, ← h]
  rw [prod_mul_distrib, hprod]
  have hsingle : (∏ i, subst P (if i = i₀ then G * V else 1)) = subst P (G * V) := by
    have hone : subst P (1 : MvPowerSeries J O) = 1 := by
      rw [← substAlgHom_apply hP, map_one]
    rw [prod_eq_single i₀ (fun i _ hi ↦ by simp [hi, hone]) (by simp)]
    simp
  have hcancel (j : J) : u.subst (P j) * ∏ i, (θ.rescale (δ i)).subst (μ j) = 1 := by
    simpa only [map_mul, map_prod, map_one, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hy (hs j), P] using
      congrArg (PowerSeries.substAlgHom (hs j)) hu
  rw [hsingle, ← substAlgHom_apply hP, map_mul, mul_assoc]
  simp only [G, V, map_prod, map_pow, substAlgHom_apply, heval, ← prod_mul_distrib,
    ← mul_pow, hcancel, one_pow, prod_const_one, mul_one, P]

end MvPowerSeries
