/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Theta series in rank twenty-four

The theta series of an even unimodular lattice of rank `24` is determined by its number of
roots, that is, its vectors of squared norm `2`. It is
`E₄³ + (r_L(2) - 720) Δ`: the constant coefficient is `1`, and the linear coefficient is
`r_L(2)`. The level-one Sturm bound in weight `12` makes these two coefficients sufficient.

We give the identity as a bundled modular form, as a function, and on `q`-expansions. Reading
its quadratic coefficient gives `r_L(4) + 24 r_L(2) = 196560`. In particular every rootless
even unimodular lattice of rank `24` has `196560` vectors of squared norm `4`; no vector count
is needed as input.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §§3 and 6.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

open UpperHalfPlane ModularForm EisensteinSeries
open scoped MatrixGroups

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- The theta form of an even unimodular lattice of rank `24` is
`E₄³ + (r_L(2) - 720) Δ`. -/
theorem thetaForm_eq_E₄_cube_add_smul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) :
    thetaForm hL hU (k := 12) hr =
      ModularForm.mcast (by norm_num : (3 : ℤ) * 4 = 12) (E₄.pow 3) +
        ((representationNumber L 2 : ℂ) - 720) •
          CuspForm.toModularFormₗ CuspForm.discriminant := by
  have hΔ : ⇑(CuspForm.toModularFormₗ CuspForm.discriminant) =
      ModularForm.discriminant := (funext (CuspForm.toModularFormₗ_apply _)).trans
        CuspForm.coe_discriminant
  have hq : qExpansion 1
      (thetaForm hL hU (k := 12) hr -
        (ModularForm.mcast (by norm_num : (3 : ℤ) * 4 = 12) (E₄.pow 3) +
          ((representationNumber L 2 : ℂ) - 720) •
            CuspForm.toModularFormₗ CuspForm.discriminant) : ModularForm 𝒮ℒ 12) =
      qExpansion 1 (thetaSeries L) - (qExpansion 1 E₄ ^ 3 +
        ((representationNumber L 2 : ℂ) - 720) • qExpansion 1 ModularForm.discriminant) := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp only [coe_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ZLattice.coe_thetaForm (k := 12) hL hU hr, hΔ]
  apply sub_eq_zero.mp
  apply ModularForm.sturm_bound_levelOne_nat (k := 12)
  refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 2 ?_)
  intro n hn
  rw [hq]
  interval_cases n
  · simp [-PowerSeries.coeff_zero_eq_constantCoeff, hL.qExpansion_thetaSeries_coeff_zero,
      pow_succ, PowerSeries.coeff_mul, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_zero]
  · simp [hL.qExpansion_thetaSeries_coeff, pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
      E_qExpansion_coeff_zero _ ⟨2, rfl⟩, discriminant_qExpansion_coeff_one]
    ring

/-- As functions on the upper half-plane, `Θ_L = E₄³ + (r_L(2) - 720) Δ` in rank `24`. -/
theorem thetaSeries_eq_E₄_cube_add_mul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) (τ : ℍ) :
    thetaSeries L τ = E₄ τ ^ 3 +
      ((representationNumber L 2 : ℂ) - 720) * ModularForm.discriminant τ := by
  have h := congrFun (congrArg DFunLike.coe
    (hL.thetaForm_eq_E₄_cube_add_smul_discriminant hU hr)) τ
  simpa only [coe_thetaForm, FunLike.coe_add, FunLike.coe_smul, coe_mcast, coe_pow,
    Pi.add_apply, Pi.smul_apply, Pi.pow_apply, CuspForm.toModularFormₗ_apply,
    CuspForm.coe_discriminant, smul_eq_mul, congrFun (coe_pow E₄ 3) τ] using h

/-- The power series identity for a rank-`24` even unimodular lattice. Its coefficients
express every representation number in terms of `E₄³`, Ramanujan's tau function, and `r_L(2)`. -/
theorem qExpansion_thetaSeries_eq_E₄_cube_add_smul_discriminant (hL : IsEven L)
    (hU : IsUnimodular L) (hr : Module.finrank ℝ E = 24) :
    qExpansion 1 (thetaSeries L) = qExpansion 1 E₄ ^ 3 +
      ((representationNumber L 2 : ℂ) - 720) • qExpansion 1 ModularForm.discriminant := by
  have hΔ : ⇑(CuspForm.toModularFormₗ CuspForm.discriminant) =
      ModularForm.discriminant := (funext (CuspForm.toModularFormₗ_apply _)).trans
        CuspForm.coe_discriminant
  have h := congrArg (fun f : ModularForm 𝒮ℒ 12 ↦ qExpansion 1 f)
    (hL.thetaForm_eq_E₄_cube_add_smul_discriminant hU hr)
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL] at h
  simpa only [ZLattice.coe_thetaForm (k := 12) hL hU hr, coe_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hΔ] using h

/-- In rank `24`, the numbers of vectors of squared norms `2` and `4` satisfy
`r_L(4) + 24 r_L(2) = 196560`. -/
theorem representationNumber_four_add_twenty_four_mul (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) :
    representationNumber L 4 + 24 * representationNumber L 2 = 196560 := by
  have h := congrArg (PowerSeries.coeff 2)
    (hL.qExpansion_thetaSeries_eq_E₄_cube_add_smul_discriminant hU hr)
  norm_num [hL.qExpansion_thetaSeries_coeff, pow_succ, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    TauCeti.ModularForm.E₄_qExpansion_coeff_two, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    TauCeti.ModularForm.discriminant_qExpansion_coeff_two] at h
  have hc : (representationNumber L 4 : ℂ) + 24 * representationNumber L 2 = 196560 := by
    linear_combination h
  exact_mod_cast hc

/-- Every rootless even unimodular lattice of rank `24` has `196560` vectors of squared
norm `4`. -/
theorem representationNumber_four_of_rootless (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) (hroot : representationNumber L 2 = 0) :
    representationNumber L 4 = 196560 := by
  simpa [hroot] using hL.representationNumber_four_add_twenty_four_mul hU hr

end ZLattice.IsEven
