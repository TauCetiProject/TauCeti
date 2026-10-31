/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Theta series of even unimodular lattices of rank `8` and `16`

Let `L` be an even unimodular lattice in a real inner product space `E` of dimension `n = 2k`.
Its theta series is a level-one modular form of weight `k` (`ZLattice.thetaForm`) whose
`q`-expansion has constant term `r_L(0) = 1`. When `k < 12`, the level-one Sturm bound
(`ModularForm.sturm_bound_levelOne_nat`) says that a modular form of weight `k` for `SL(2, ℤ)` is
determined by its constant term, so `Θ_L` is the unique level-one form of weight `k` with constant
term `1`. No representation number other than `r_L(0)` enters.

Since `8 ∣ n`, this applies in ranks `8` and `16`, and identifies the theta series with
Eisenstein series:

* in rank `8`, `Θ_L = E₄` for **every** even unimodular `L`;
* in rank `16`, `Θ_L = E₄²` for **every** even unimodular `L`, and this is also the normalized
  Eisenstein series `E 8` of weight `8`.

Reading off the `q`-expansion coefficients of the normalized Eisenstein series
(`EisensteinSeries.E_qExpansion_coeff`, with `B₄ = B₈ = -1/30`) gives the classical
representation numbers: for `m ≥ 1`, an even unimodular lattice has `r_L(2m) = 240 σ₃(m)`
vectors of half-norm `m` in rank `8`, and `r_L(2m) = 480 σ₇(m)` in rank `16`. In particular the
kissing number of an even unimodular lattice of rank `8` is `240`.

## Main statements

* `ZLattice.IsEven.thetaForm_eq_of_qExpansion_coeff_zero`: for an even unimodular lattice of rank
  `2k < 24`, `Θ_L` is the level-one form of weight `k` with constant term `1`.
* `ZLattice.IsEven.thetaForm_eq_E₄`, `ZLattice.IsEven.thetaSeries_eq_E₄`: `Θ_L = E₄` in rank `8`.
* `ZLattice.IsEven.representationNumber_two_mul_of_finrank_eq_eight`: `r_L(2m) = 240 σ₃(m)` for
  `m ≥ 1` in rank `8`.
* `ZLattice.IsEven.thetaForm_eq_E₄_mul_E₄`, `ZLattice.IsEven.thetaSeries_eq_E₄_sq`,
  `ZLattice.IsEven.thetaForm_eq_E_eight`: `Θ_L = E₄²` and `Θ_L = E 8` in rank `16`.
* `ZLattice.IsEven.representationNumber_two_mul_of_finrank_eq_sixteen`: `r_L(2m) = 480 σ₇(m)` for
  `m ≥ 1` in rank `16`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, §3.2.
-/

public section

open Module ModularForm EisensteinSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma MatrixGroups

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

namespace IsEven

/-- **The theta series of an even unimodular lattice of rank `2k < 24` is determined by its
constant term**: if `L` is even unimodular with `dim E = 2k` and `k < 12`, then `Θ_L` is the
unique level-one modular form of weight `k` whose `q`-expansion has constant term `1`. -/
theorem thetaForm_eq_of_qExpansion_coeff_zero {k : ℕ} (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) (hk12 : k < 12) {f : ModularForm 𝒮ℒ k}
    (hf : (qExpansion 1 f).coeff 0 = 1) : thetaForm hL hU hk = f := by
  rw [← sub_eq_zero]
  refine sturm_bound_levelOne_nat ?_
  -- Since `k < 12`, the Sturm bound asks only that the constant term of `Θ_L - f` vanish.
  rw [Nat.div_eq_of_lt hk12, Nat.cast_zero, pos_iff_ne_zero,
    PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub, coe_thetaForm,
    hL.qExpansion_thetaSeries_coeff_zero, hf, sub_self]

omit [IsZLattice ℝ L] in
/-- If the theta series of an even lattice is the normalized Eisenstein series of weight `k`, then
for `m ≥ 1` the lattice has `-(2k / B_k) σ_{k-1}(m)` vectors of squared norm `2m`. -/
private theorem representationNumber_two_mul_of_thetaSeries_eq_E (hL : IsEven L) {k : ℕ}
    (hk : 3 ≤ k) (hk2 : Even k) (hθ : thetaSeries L = ModularForm.E hk) {m : ℕ} (hm : m ≠ 0) :
    (representationNumber L (2 * m) : ℂ) = -(2 * k / bernoulli k : ℂ) * σ (k - 1) m := by
  simp [← hL.qExpansion_thetaSeries_coeff, hθ, E_qExpansion_coeff hk hk2, hm]

/-! ### Rank `8` -/

/-- **The theta series of an even unimodular lattice of rank `8` is `E₄`.** -/
theorem thetaForm_eq_E₄ (hL : IsEven L) (hU : IsUnimodular L) (h8 : finrank ℝ E = 8) :
    thetaForm hL hU (k := 4) h8 = E₄ :=
  hL.thetaForm_eq_of_qExpansion_coeff_zero hU h8 (by norm_num) (E_qExpansion_coeff_zero _ ⟨2, rfl⟩)

/-- The theta series of an even unimodular lattice of rank `8` is the Eisenstein series `E₄`, as
a function on the upper half-plane. -/
theorem thetaSeries_eq_E₄ (hL : IsEven L) (hU : IsUnimodular L) (h8 : finrank ℝ E = 8) :
    thetaSeries L = E₄ := by
  rw [← coe_thetaForm hL hU (k := 4) h8, hL.thetaForm_eq_E₄ hU h8]

/-- **Representation numbers in rank `8`**: an even unimodular lattice of rank `8` has
`240 σ₃(m)` vectors of squared norm `2m`, for every `m ≥ 1`. -/
theorem representationNumber_two_mul_of_finrank_eq_eight (hL : IsEven L) (hU : IsUnimodular L)
    (h8 : finrank ℝ E = 8) {m : ℕ} (hm : m ≠ 0) :
    representationNumber L (2 * m : ℝ) = 240 * σ 3 m := by
  have h := hL.representationNumber_two_mul_of_thetaSeries_eq_E _ ⟨2, rfl⟩
    (hL.thetaSeries_eq_E₄ hU h8) hm
  rw [show bernoulli 4 = -1 / 30 by decide +kernel] at h
  exact_mod_cast h.trans (by norm_num : _ = ((240 * σ 3 m : ℕ) : ℂ))

/-- The **kissing number** of an even unimodular lattice of rank `8` is `240`: it has `240`
vectors of squared norm `2`. -/
theorem representationNumber_two_of_finrank_eq_eight (hL : IsEven L) (hU : IsUnimodular L)
    (h8 : finrank ℝ E = 8) : representationNumber L 2 = 240 := by
  simpa using hL.representationNumber_two_mul_of_finrank_eq_eight hU h8 one_ne_zero

/-! ### Rank `16` -/

/-- **The theta series of an even unimodular lattice of rank `16` is `E₄²`**, as a modular form
of weight `8`. -/
theorem thetaForm_eq_E₄_mul_E₄ (hL : IsEven L) (hU : IsUnimodular L) (h16 : finrank ℝ E = 16) :
    thetaForm hL hU (k := 8) h16 = mcast (by norm_num) (E₄.mul E₄) :=
  hL.thetaForm_eq_of_qExpansion_coeff_zero hU h16 (by norm_num) <| by
    rw [coe_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, mul_one]

/-- The theta series of an even unimodular lattice of rank `16` is `E₄²`, as a function on the
upper half-plane. -/
theorem thetaSeries_eq_E₄_sq (hL : IsEven L) (hU : IsUnimodular L) (h16 : finrank ℝ E = 16) :
    thetaSeries L = E₄ ^ 2 := by
  rw [← coe_thetaForm hL hU (k := 8) h16, hL.thetaForm_eq_E₄_mul_E₄ hU h16, coe_mcast, coe_mul,
    sq]

/-- **The theta series of an even unimodular lattice of rank `16` is the normalized Eisenstein
series of weight `8`.** -/
theorem thetaForm_eq_E_eight (hL : IsEven L) (hU : IsUnimodular L) (h16 : finrank ℝ E = 16) :
    thetaForm hL hU (k := 8) h16 = ModularForm.E (by norm_num : 3 ≤ 8) :=
  hL.thetaForm_eq_of_qExpansion_coeff_zero hU h16 (by norm_num) (E_qExpansion_coeff_zero _ ⟨4, rfl⟩)

/-- **Representation numbers in rank `16`**: an even unimodular lattice of rank `16` has
`480 σ₇(m)` vectors of squared norm `2m`, for every `m ≥ 1`. -/
theorem representationNumber_two_mul_of_finrank_eq_sixteen (hL : IsEven L) (hU : IsUnimodular L)
    (h16 : finrank ℝ E = 16) {m : ℕ} (hm : m ≠ 0) :
    representationNumber L (2 * m : ℝ) = 480 * σ 7 m := by
  have h := hL.representationNumber_two_mul_of_thetaSeries_eq_E _ ⟨4, rfl⟩
    (by rw [← coe_thetaForm hL hU (k := 8) h16, hL.thetaForm_eq_E_eight hU h16]) hm
  rw [show bernoulli 8 = -1 / 30 by decide +kernel] at h
  exact_mod_cast h.trans (by norm_num : _ = ((480 * σ 7 m : ℕ) : ℂ))

end IsEven

end ZLattice
