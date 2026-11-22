/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Basic
public import TauCeti.Algebra.Lie.Weights.IsSimple
public import TauCeti.LinearAlgebra.RootSystem.DualCoxeterNumber

/-!
# Affine normalisations and the dual Coxeter number for Segal--Sugawara operators

This file specialises the Segal--Sugawara Virasoro modes `sugawaraVirasoro` and central charge
`sugawaraCentralCharge` to invariant bilinear forms `κ₀` satisfying `κ_L = (2 d) • κ₀` with `d ≠ 0`
at the affine level `Φ = -(k • κ₀)` and central value `a = 1`. In particular, for a simple Lie
algebra over a field of characteristic zero with Killing-form normalisation `κ_L = 2 h^∨ κ₀` in
terms of the dual Coxeter number `h^∨` (`RootPairing.Base.dualCoxeterNumber`), this yields:

* `Lₘ = (2 (k + h^∨))⁻¹ ∑ᵢ :bᵢ b^i:_m` in every `κ₀`-dual basis;
* `c_{Vir} = k · dim L / (k + h^∨)`.

## Main results

* `TauCeti.CurrentAlgebra.eq_neg_div_two_mul_smul_killingForm`: `Φ = -(k • κ₀)` equals
  `(-k / (2 d)) • κ_L` when `κ_L = (2 d) • κ₀`.
* `TauCeti.CurrentAlgebra.one_sub_two_mul_neg_div_two_mul_ne_zero_iff`: noncriticality
  `1 - 2 · 1 · (-k / (2 d)) ≠ 0 ↔ k + d ≠ 0`.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_eq_sum_dualBasis`: `κ₀`-dual-basis formula for `Lₘ`.
* `TauCeti.CurrentAlgebra.sugawaraCentralCharge_neg_div_two_mul`: central charge
  `k · dim L / (k + d)`.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_eq_sum_dualBasis_of_dualCoxeterNumber`,
  `TauCeti.CurrentAlgebra.sugawaraCentralCharge_of_dualCoxeterNumber`: the `κ₀`-dual-basis formula
  and central charge `k · dim L / (k + h^∨)` in terms of the dual Coxeter number.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §§3.1.1--3.1.4.
* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 6.
-/

public section

noncomputable section

open LieAlgebra

namespace TauCeti.CurrentAlgebra

section Normalization

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm}

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem one_sub_two_mul_neg_div_two_mul [NeZero (2 : K)] {d : K} (hd : d ≠ 0) (k : K) :
    1 - 2 * (1 : K) * (-k / (2 * d)) = (k + d) / d := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  field_simp
  ring

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- **For a form `κ₀` with `κ_L = (2 d) • κ₀`, the affine level `Φ = -(k • κ₀)` at `a = 1` is
`(-k / (2 d)) • κ_L`.** -/
theorem eq_neg_div_two_mul_smul_killingForm [NeZero (2 : K)] {κ₀ : LinearMap.BilinForm K L}
    {d : K} (hd : d ≠ 0) (hκ₀ : killingForm K L = (2 * d) • κ₀) (k : K)
    (hΦk : Φ = -(k • κ₀)) :
    Φ = (-k / (2 * d)) • killingForm K L := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  ext x y
  simp only [hΦk, hκ₀, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- **Noncriticality in the affine normalisation**: `1 - 2 · 1 · (-k / (2 d)) ≠ 0` if and only if
`k + d ≠ 0`. -/
theorem one_sub_two_mul_neg_div_two_mul_ne_zero_iff [NeZero (2 : K)] {d : K} (hd : d ≠ 0)
    (k : K) :
    1 - 2 * (1 : K) * (-k / (2 * d)) ≠ 0 ↔ k + d ≠ 0 := by
  rw [one_sub_two_mul_neg_div_two_mul hd, div_ne_zero_iff]
  exact and_iff_left hd

/-- **The `κ₀`-dual-basis formula for the Segal--Sugawara Virasoro modes.** If
`κ_L = (2 d) • κ₀`, then at `a = 1` and `c = -k / (2 d)`,

`Lₘ = (2 (k + d))⁻¹ • ∑ᵢ :bᵢ b^i:_m`

for every basis `b` of `L` and its `κ₀`-dual basis `b^i`. -/
theorem sugawaraVirasoro_eq_sum_dualBasis [NeZero (2 : K)] {κ₀ : LinearMap.BilinForm K L}
    (hκ₀nd : κ₀.Nondegenerate) {d : K} (hd : d ≠ 0) (hκ₀ : killingForm K L = (2 * d) • κ₀)
    (k : K) {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs 1 (-k / (2 * d)) m =
      (2 * (k + d))⁻¹ • ∑ i, normalOrderedMode Φ hΦ hΦs 1 m (b i) (κ₀.dualBasis hκ₀nd b i) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  rw [sugawaraVirasoro_def, one_sub_two_mul_neg_div_two_mul hd,
    sugawaraMode_eq_inv_smul_sum_dualBasis hκ₀nd (mul_ne_zero h2 hd) hκ₀ b m, smul_smul]
  congr 1
  field_simp

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- **The Sugawara central charge in the `κ₀`-normalisation** is `k · dim L / (k + d)`. -/
theorem sugawaraCentralCharge_neg_div_two_mul [NeZero (2 : K)] {d : K} (hd : d ≠ 0) (k : K) :
    sugawaraCentralCharge K L 1 (-k / (2 * d)) = k * (Module.finrank K L : K) / (k + d) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have hnum : -(2 * (1 : K) * (-k / (2 * d))) = k / d := by
    field_simp
  rw [sugawaraCentralCharge_def, hnum, one_sub_two_mul_neg_div_two_mul hd,
    div_div_div_cancel_right₀ hd, div_mul_eq_mul_div]

section Simple

variable [CharZero K] [LieAlgebra.IsSimple K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (bp : (LieAlgebra.IsKilling.rootSystem H).Base)

/-- **For a simple Lie algebra in characteristic zero, the Segal--Sugawara Virasoro modes in any
`κ₀`-dual basis are `(2 (k + h^∨))⁻¹ • ∑ᵢ :bᵢ b^i:_m`**, where `h^∨` is the dual Coxeter number
and `κ_L = 2 h^∨ κ₀`. -/
theorem sugawaraVirasoro_eq_sum_dualBasis_of_dualCoxeterNumber {κ₀ : LinearMap.BilinForm K L}
    (hκ₀nd : κ₀.Nondegenerate)
    (hκ₀ : killingForm K L = (2 * (bp.dualCoxeterNumber : K)) • κ₀) (k : K)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs 1 (-k / (2 * (bp.dualCoxeterNumber : K))) m =
      (2 * (k + (bp.dualCoxeterNumber : K)))⁻¹ •
        ∑ i, normalOrderedMode Φ hΦ hΦs 1 m (b i) (κ₀.dualBasis hκ₀nd b i) :=
  sugawaraVirasoro_eq_sum_dualBasis hκ₀nd bp.cast_dualCoxeterNumber_ne_zero hκ₀ k b m

/-- **For a simple Lie algebra in characteristic zero, the Sugawara central charge at level `k` is
`k · dim L / (k + h^∨)`**, where `h^∨` is the dual Coxeter number. -/
theorem sugawaraCentralCharge_of_dualCoxeterNumber (k : K) :
    sugawaraCentralCharge K L 1 (-k / (2 * (bp.dualCoxeterNumber : K))) =
      k * (Module.finrank K L : K) / (k + (bp.dualCoxeterNumber : K)) :=
  sugawaraCentralCharge_neg_div_two_mul bp.cast_dualCoxeterNumber_ne_zero k

end Simple

end Normalization

end TauCeti.CurrentAlgebra
