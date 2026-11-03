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

The same two coefficients identify `Θ_L` against the normalized Eisenstein series `E₁₂` of weight
`12`, whose `q`-expansion is `1 + (65520/691) ∑ σ₁₁(m) qᵐ` (`B₁₂ = -691/2730`):
`Θ_L = E₁₂ + (r_L(2) - 65520/691) Δ`. Reading off the coefficient of `qᵐ` gives the closed form
`r_L(2m) = (65520/691) σ₁₁(m) + (r_L(2) - 65520/691) τ(m)` for `m ≥ 1`, where `τ(m)` is the
`m`-th `q`-coefficient of `Δ` (Ramanujan's function).

## Main statements

* `ZLattice.IsEven.thetaForm_eq_add_smul_discriminant`: `Θ_L = f + (r_L(2) - a₁(f)) Δ` for every
  level-one form `f` of weight `12` with constant term `1`.
* `ZLattice.IsEven.thetaForm_eq_E₄_cube_add_smul_discriminant`,
  `ZLattice.IsEven.thetaSeries_eq_E₄_cube_add_mul_discriminant`: `Θ_L = E₄³ + (r_L(2) - 720) Δ`.
* `ZLattice.IsEven.representationNumber_four_add_twenty_four_mul`:
  `r_L(4) + 24 r_L(2) = 196560`.
* `ZLattice.IsEven.thetaForm_eq_E_twelve_add_smul_discriminant`,
  `ZLattice.IsEven.thetaSeries_eq_E_twelve_add_mul_discriminant`:
  `Θ_L = E₁₂ + (r_L(2) - 65520/691) Δ`.
* `ZLattice.IsEven.representationNumber_two_mul_of_finrank_eq_twenty_four`:
  `r_L(2m) = (65520/691) σ₁₁(m) + (r_L(2) - 65520/691) τ(m)` for `m ≥ 1`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §§3 and 6.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

open UpperHalfPlane ModularForm EisensteinSeries
open scoped ArithmeticFunction.sigma MatrixGroups

namespace ZLattice.IsEven

-- The natural-weight APIs `thetaForm` and `sturm_bound_levelOne_nat` use `k = 12`:
-- `2 * 12 = 24` and `((12 : ℕ) : ℤ) = 12` hold by definitional equality.

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The theta form in rank `24` is determined by `r_L(2)`**: if `f` is a level-one modular form
of weight `12` with constant term `1` and linear coefficient `a₁`, then the theta form of an even
unimodular lattice of rank `24` is `f + (r_L(2) - a₁) Δ`. -/
theorem thetaForm_eq_add_smul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) {f : ModularForm 𝒮ℒ 12} (hf : (qExpansion 1 f).coeff 0 = 1) :
    thetaForm hL hU (k := 12) hr =
      f + ((representationNumber L 2 : ℂ) - (qExpansion 1 f).coeff 1) •
        CuspForm.toModularFormₗ CuspForm.discriminant := by
  have hq : qExpansion 1
      (thetaForm hL hU (k := 12) hr -
        (f + ((representationNumber L 2 : ℂ) - (qExpansion 1 f).coeff 1) •
          CuspForm.toModularFormₗ CuspForm.discriminant) : ModularForm 𝒮ℒ 12) =
      qExpansion 1 (thetaSeries L) - (qExpansion 1 f +
        ((representationNumber L 2 : ℂ) - (qExpansion 1 f).coeff 1) •
          qExpansion 1 ModularForm.discriminant) := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_add_smul_discriminant,
      ZLattice.coe_thetaForm (k := 12) hL hU hr]
  apply sub_eq_zero.mp
  apply ModularForm.sturm_bound_levelOne_nat (k := 12)
  -- The Sturm bound in weight `12` asks for the vanishing of the coefficients of `1` and `q`.
  refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 2 ?_)
  intro n hn
  rw [hq]
  interval_cases n
  · simp only [map_sub, map_add, PowerSeries.coeff_smul, hL.qExpansion_thetaSeries_coeff_zero, hf,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_zero, smul_zero, add_zero, sub_self]
  · simp [hL.qExpansion_thetaSeries_coeff, discriminant_qExpansion_coeff_one]

/-- The theta form of an even unimodular lattice of rank `24` is
`E₄³ + (r_L(2) - 720) Δ`. -/
theorem thetaForm_eq_E₄_cube_add_smul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) :
    thetaForm hL hU (k := 12) hr =
      ModularForm.mcast (by norm_num) (E₄.pow 3) +
        ((representationNumber L 2 : ℂ) - 720) •
          CuspForm.toModularFormₗ CuspForm.discriminant := by
  have hE : qExpansion 1 (ModularForm.mcast (by norm_num) (E₄.pow 3) : ModularForm 𝒮ℒ 12) =
      qExpansion 1 E₄ ^ 3 := by
    rw [coe_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [hL.thetaForm_eq_add_smul_discriminant hU hr
      (by rw [hE, TauCeti.ModularForm.E₄_cube_qExpansion_coeff_zero]),
    hE, TauCeti.ModularForm.E₄_cube_qExpansion_coeff_one]

/-- As functions on the upper half-plane, `Θ_L = E₄³ + (r_L(2) - 720) Δ` in rank `24`. -/
theorem thetaSeries_eq_E₄_cube_add_mul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) (τ : ℍ) :
    thetaSeries L τ = E₄ τ ^ 3 +
      ((representationNumber L 2 : ℂ) - 720) * ModularForm.discriminant τ := by
  have h := congrFun (congrArg DFunLike.coe
    (hL.thetaForm_eq_E₄_cube_add_smul_discriminant hU hr)) τ
  -- At a point, coercions reduce to evaluation before `coe_pow` can match the function;
  -- its pointwise instance rewrites the bundled power without unfolding its definition.
  simpa only [coe_thetaForm, FunLike.coe_add, FunLike.coe_smul, coe_mcast,
    Pi.add_apply, Pi.smul_apply, CuspForm.toModularFormₗ_apply,
    CuspForm.coe_discriminant, smul_eq_mul, congrFun (coe_pow E₄ 3) τ, Pi.pow_apply] using h

/-- The power series identity for a rank-`24` even unimodular lattice. Its coefficients
express every representation number in terms of `E₄³`, Ramanujan's tau function, and `r_L(2)`. -/
theorem qExpansion_thetaSeries_eq_E₄_cube_add_smul_discriminant (hL : IsEven L)
    (hU : IsUnimodular L) (hr : Module.finrank ℝ E = 24) :
    qExpansion 1 (thetaSeries L) = qExpansion 1 E₄ ^ 3 +
      ((representationNumber L 2 : ℂ) - 720) • qExpansion 1 ModularForm.discriminant := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 12 ↦ qExpansion 1 f)
    (hL.thetaForm_eq_E₄_cube_add_smul_discriminant hU hr)
  rw [TauCeti.ModularForm.qExpansion_E₄_cube_add_smul_discriminant,
    ZLattice.coe_thetaForm (k := 12) hL hU hr] at h
  exact h

/-- In rank `24`, the numbers of vectors of squared norms `2` and `4` satisfy
`r_L(4) + 24 r_L(2) = 196560`. -/
theorem representationNumber_four_add_twenty_four_mul (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) :
    representationNumber L 4 + 24 * representationNumber L 2 = 196560 := by
  have h := congrArg (PowerSeries.coeff 2)
    (hL.qExpansion_thetaSeries_eq_E₄_cube_add_smul_discriminant hU hr)
  norm_num [hL.qExpansion_thetaSeries_coeff, PowerSeries.coeff_smul,
    TauCeti.ModularForm.E₄_cube_qExpansion_coeff_two,
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

/-! ### The Eisenstein form -/

/-- The theta form of an even unimodular lattice of rank `24` is
`E₁₂ + (r_L(2) - 65520/691) Δ`, where `E₁₂` is the normalized Eisenstein series of weight
`12`. -/
theorem thetaForm_eq_E_twelve_add_smul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) :
    thetaForm hL hU (k := 12) hr =
      ModularForm.E (by norm_num : 3 ≤ 12) +
        ((representationNumber L 2 : ℂ) - 65520 / 691) •
          CuspForm.toModularFormₗ CuspForm.discriminant := by
  rw [hL.thetaForm_eq_add_smul_discriminant hU hr
      (by rw [TauCeti.ModularForm.E_twelve_qExpansion_coeff, ite_eq_left rfl]),
    TauCeti.ModularForm.E_twelve_qExpansion_coeff]
  simp

/-- As functions on the upper half-plane, `Θ_L = E₁₂ + (r_L(2) - 65520/691) Δ` in rank `24`. -/
theorem thetaSeries_eq_E_twelve_add_mul_discriminant (hL : IsEven L) (hU : IsUnimodular L)
    (hr : Module.finrank ℝ E = 24) (τ : ℍ) :
    thetaSeries L τ = ModularForm.E (by norm_num : 3 ≤ 12) τ +
      ((representationNumber L 2 : ℂ) - 65520 / 691) * ModularForm.discriminant τ := by
  have h := congrFun (congrArg DFunLike.coe
    (hL.thetaForm_eq_E_twelve_add_smul_discriminant hU hr)) τ
  simpa only [coe_thetaForm, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    CuspForm.toModularFormₗ_apply, CuspForm.coe_discriminant, smul_eq_mul] using h

/-- **Representation numbers in rank `24`**: an even unimodular lattice of rank `24` has
`(65520/691) σ₁₁(m) + (r_L(2) - 65520/691) τ(m)` vectors of squared norm `2m`, for every `m ≥ 1`,
where `τ(m)` is the `m`-th `q`-coefficient of `Δ`. -/
theorem representationNumber_two_mul_of_finrank_eq_twenty_four (hL : IsEven L)
    (hU : IsUnimodular L) (hr : Module.finrank ℝ E = 24) {m : ℕ} (hm : m ≠ 0) :
    (representationNumber L (2 * m : ℝ) : ℂ) = 65520 / 691 * σ 11 m +
      ((representationNumber L 2 : ℂ) - 65520 / 691) *
        (qExpansion 1 ModularForm.discriminant).coeff m := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 12 ↦ (qExpansion 1 f).coeff m)
    (hL.thetaForm_eq_E_twelve_add_smul_discriminant hU hr)
  rw [ModularForm.qExpansion_add_smul_discriminant,
    ZLattice.coe_thetaForm (k := 12) hL hU hr, hL.qExpansion_thetaSeries_coeff, map_add,
    PowerSeries.coeff_smul, TauCeti.ModularForm.E_twelve_qExpansion_coeff, ite_eq_right hm,
    smul_eq_mul] at h
  exact_mod_cast h

end ZLattice.IsEven
