/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The translation law of theta series

Let `L` be a lattice in a real inner product space `E`, with dual lattice `L^∨`. The term of index
`v ∈ L` of the coset theta series `θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)` is multiplied by
`exp (π i ‖γ + v‖² t)` when `τ` is translated by a real number `t`. This file shows that this
factor is independent of `v` in the two arithmetic situations of interest, and deduces the
behaviour of theta series under the translations `T ^ n : τ ↦ τ + n` of the modular group.

* If `L` is **even** and `γ ∈ L^∨`, then `‖γ + v‖² ≡ ‖γ‖² (mod 2)`, so for every integer `n`
  `θ_{γ+L}(τ + n) = exp (π i n ‖γ‖²) θ_{γ+L}(τ)`. In the notation `e(x) = exp (2 π i x)` and
  `q_L(γ) = ‖γ‖² / 2 mod ℤ`, this is `θ_{γ+L}(τ + 1) = e(q_L(γ)) θ_{γ+L}(τ)`. In particular
  `Θ_L(τ + 1) = Θ_L(τ)`, that is `Θ_L ∣[k] T = Θ_L` in every weight `k`, and `θ_{γ+L}` is invariant
  under `T ^ N` as soon as `N ‖γ‖² / 2 ∈ ℤ`; the least such `N > 0` for all `γ ∈ L^∨` is the level
  of `L`.
* If `L` is only **integral** and `γ ∈ L^∨`, then `‖γ + v‖² ≡ ‖γ‖² (mod 1)`, which gives the same
  statements for even translations: `θ_{γ+L}(τ + 2) = exp (2 π i ‖γ‖²) θ_{γ+L}(τ)` and
  `Θ_L ∣[k] T ^ 2 = Θ_L`. Integrality does not give period `1`: the theta series of `ℤ ⊆ ℝ` is
  the Jacobi theta function, of period `2` only (`jacobiTheta_T_sq_smul`).

The rank of `L` is arbitrary, and no discreteness or finite dimensionality is needed: the
identities hold termwise.

## Main statements

* `ZLattice.thetaCoset_vadd_eq_mul`: if `(‖γ + v‖² - ‖γ‖²) t ∈ 2ℤ` for every `v ∈ L`, then
  `θ_{γ+L}(τ + t) = exp (π i ‖γ‖² t) θ_{γ+L}(τ)`.
* `ZLattice.IsEven.cexp_pi_mul_I_mul_norm_add_sq`: for even `L`, the factor `e(q_L(γ))` depends
  only on the coset `γ + L`.
* `ZLattice.IsEven.thetaCoset_slash_T_zpow`, `ZLattice.IsEven.thetaSeries_slash_T`: the
  translation law for even lattices.
* `ZLattice.IsEven.thetaCoset_slash_T_zpow_eq_self`: invariance of `θ_{γ+L}` under `T ^ N` when
  `N ‖γ‖² / 2 ∈ ℤ`.
* `ZLattice.IsIntegral.thetaCoset_slash_T_zpow_two_mul`,
  `ZLattice.IsIntegral.thetaSeries_slash_T_sq`: the translation law for integral lattices.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, §3.2.
-/

public section

open Complex
open UpperHalfPlane (coe_vadd)
open scoped Real ModularForm UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E]

/-- If `(‖γ + v‖² - ‖γ‖²) t` is an even integer for every `v ∈ L`, then translating `τ` by `t`
multiplies the theta series of `γ + L` by `exp (π i ‖γ‖² t)`. -/
theorem thetaCoset_vadd_eq_mul (L : Submodule ℤ E) (γ : E) {t : ℝ}
    (h : ∀ v ∈ L, ∃ m : ℤ, (‖γ + v‖ ^ 2 - ‖γ‖ ^ 2) * t = 2 * m) (τ : ℍ) :
    thetaCoset L γ (t +ᵥ τ) = cexp (π * I * (‖γ‖ ^ 2 : ℝ) * t) * thetaCoset L γ τ := by
  rw [thetaCoset_apply, thetaCoset_apply, ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  obtain ⟨m, hm⟩ := h v v.2
  have hm' : ((‖γ + (v : E)‖ ^ 2 : ℝ) : ℂ) * t = ((‖γ‖ ^ 2 : ℝ) : ℂ) * t + 2 * m := by
    rw [← sub_eq_iff_eq_add', ← sub_mul]
    exact_mod_cast hm
  have he : π * I * ((‖γ + (v : E)‖ ^ 2 : ℝ) : ℂ) * (t + τ) =
      π * I * ((‖γ‖ ^ 2 : ℝ) : ℂ) * t + π * I * ((‖γ + (v : E)‖ ^ 2 : ℝ) : ℂ) * τ +
        m * (2 * π * I) := by
    linear_combination (π * I) * hm'
  rw [coe_vadd, he, exp_add, exp_int_mul_two_pi_mul_I, mul_one, exp_add]

variable [InnerProductSpace ℝ E] {L : Submodule ℤ E} {γ : E}

/-! ### Even lattices -/

namespace IsEven

/-- For an even lattice `L` and `γ ∈ L^∨`, the factor `e(q_L(γ)) = exp (π i ‖γ‖²)` of the
translation law depends only on the coset `γ + L`. -/
theorem cexp_pi_mul_I_mul_norm_add_sq (hL : IsEven L) (hγ : γ ∈ dual L) {v : E} (hv : v ∈ L) :
    cexp (π * I * (‖γ + v‖ ^ 2 : ℝ)) = cexp (π * I * (‖γ‖ ^ 2 : ℝ)) := by
  obtain ⟨m, hm⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
  have hm' : ((‖γ + v‖ ^ 2 : ℝ) : ℂ) = ((‖γ‖ ^ 2 : ℝ) : ℂ) + 2 * m := by
    rw [← sub_eq_iff_eq_add']
    exact_mod_cast hm
  have he : π * I * ((‖γ + v‖ ^ 2 : ℝ) : ℂ) = π * I * ((‖γ‖ ^ 2 : ℝ) : ℂ) + m * (2 * π * I) := by
    linear_combination (π * I) * hm'
  rw [he, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- The translation law of the theta series of a coset of an even lattice: for `γ ∈ L^∨` and an
integer `n`, `θ_{γ+L}(τ + n) = exp (π i n ‖γ‖²) θ_{γ+L}(τ)`. -/
theorem thetaCoset_intCast_vadd (hL : IsEven L) (hγ : γ ∈ dual L) (n : ℤ) (τ : ℍ) :
    thetaCoset L γ ((n : ℝ) +ᵥ τ) = cexp (π * I * (‖γ‖ ^ 2 : ℝ) * n) * thetaCoset L γ τ := by
  refine mod_cast thetaCoset_vadd_eq_mul L γ (fun v hv ↦ ?_) τ
  obtain ⟨m, hm⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
  exact ⟨m * n, by rw [hm]; push_cast; ring⟩

/-- The translation law of the theta series of a coset of an even lattice: for `γ ∈ L^∨`,
`θ_{γ+L}(τ + 1) = e(q_L(γ)) θ_{γ+L}(τ)` with `e(q_L(γ)) = exp (π i ‖γ‖²)`. -/
theorem thetaCoset_one_vadd (hL : IsEven L) (hγ : γ ∈ dual L) (τ : ℍ) :
    thetaCoset L γ ((1 : ℝ) +ᵥ τ) = cexp (π * I * (‖γ‖ ^ 2 : ℝ)) * thetaCoset L γ τ := by
  simpa using hL.thetaCoset_intCast_vadd hγ 1 τ

/-- The theta series of an even lattice has period `1`. -/
theorem thetaSeries_intCast_vadd (hL : IsEven L) (n : ℤ) (τ : ℍ) :
    thetaSeries L ((n : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaCoset_intCast_vadd (zero_mem (dual L)) n τ

/-- The theta series of an even lattice has period `1`: `Θ_L(τ + 1) = Θ_L(τ)`. -/
theorem thetaSeries_one_vadd (hL : IsEven L) (τ : ℍ) :
    thetaSeries L ((1 : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaSeries_intCast_vadd 1 τ

/-- The translation law of the theta series of a coset of an even lattice, in slash form: for
`γ ∈ L^∨`, every weight `k` and every integer `n`,
`θ_{γ+L} ∣[k] T ^ n = exp (π i n ‖γ‖²) θ_{γ+L}`. -/
theorem thetaCoset_slash_T_zpow (hL : IsEven L) (hγ : γ ∈ dual L) (k n : ℤ) :
    thetaCoset L γ ∣[k] (ModularGroup.T ^ n) =
      cexp (π * I * (‖γ‖ ^ 2 : ℝ) * n) • thetaCoset L γ := by
  ext τ
  rw [TauCeti.ModularForm.slash_T_zpow_apply, hL.thetaCoset_intCast_vadd hγ, Pi.smul_apply,
    smul_eq_mul]

/-- The translation law of the theta series of a coset of an even lattice, in slash form: for
`γ ∈ L^∨` and every weight `k`, `θ_{γ+L} ∣[k] T = e(q_L(γ)) θ_{γ+L}`. -/
theorem thetaCoset_slash_T (hL : IsEven L) (hγ : γ ∈ dual L) (k : ℤ) :
    thetaCoset L γ ∣[k] ModularGroup.T = cexp (π * I * (‖γ‖ ^ 2 : ℝ)) • thetaCoset L γ := by
  simpa using hL.thetaCoset_slash_T_zpow hγ k 1

/-- For an even lattice `L` and `γ ∈ L^∨`, the theta series of `γ + L` is invariant under `T ^ N`
as soon as `N ‖γ‖² / 2` is an integer. When `L` is even of level `N`, this holds for every
`γ ∈ L^∨`. -/
theorem thetaCoset_slash_T_zpow_eq_self (hL : IsEven L) (hγ : γ ∈ dual L) (k : ℤ) {N : ℤ}
    (hN : ∃ m : ℤ, N * ‖γ‖ ^ 2 = 2 * m) :
    thetaCoset L γ ∣[k] (ModularGroup.T ^ N) = thetaCoset L γ := by
  obtain ⟨m, hm⟩ := hN
  have hm' : π * I * ((‖γ‖ ^ 2 : ℝ) : ℂ) * N = m * (2 * π * I) := by
    have : (N : ℂ) * ((‖γ‖ ^ 2 : ℝ) : ℂ) = 2 * m := by exact_mod_cast hm
    linear_combination (π * I) * this
  rw [hL.thetaCoset_slash_T_zpow hγ, hm', exp_int_mul_two_pi_mul_I, one_smul]

/-- The theta series of an even lattice is invariant under every power of `T`, in every
weight. -/
theorem thetaSeries_slash_T_zpow (hL : IsEven L) (k n : ℤ) :
    thetaSeries L ∣[k] (ModularGroup.T ^ n) = thetaSeries L := by
  simpa using hL.thetaCoset_slash_T_zpow (zero_mem (dual L)) k n

/-- The theta series of an even lattice is invariant under `T`, in every weight:
`Θ_L ∣[k] T = Θ_L`. -/
theorem thetaSeries_slash_T (hL : IsEven L) (k : ℤ) :
    thetaSeries L ∣[k] ModularGroup.T = thetaSeries L := by
  simpa using hL.thetaSeries_slash_T_zpow k 1

end IsEven

/-! ### Integral lattices -/

namespace IsIntegral

/-- The translation law of the theta series of a coset of an integral lattice: for `γ ∈ L^∨` and
an integer `n`, `θ_{γ+L}(τ + 2n) = exp (2 π i n ‖γ‖²) θ_{γ+L}(τ)`. -/
theorem thetaCoset_two_mul_intCast_vadd (hL : IsIntegral L) (hγ : γ ∈ dual L) (n : ℤ)
    (τ : ℍ) :
    thetaCoset L γ ((2 * n : ℝ) +ᵥ τ) =
      cexp (2 * π * I * (‖γ‖ ^ 2 : ℝ) * n) * thetaCoset L γ τ := by
  rw [thetaCoset_vadd_eq_mul L γ (fun v hv ↦ ?_) τ]
  · push_cast
    ring_nf
  · obtain ⟨m, hm⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
    exact ⟨m * n, by rw [hm]; push_cast; ring⟩

/-- The theta series of an integral lattice has period `2`. -/
theorem thetaSeries_two_mul_intCast_vadd (hL : IsIntegral L) (n : ℤ) (τ : ℍ) :
    thetaSeries L ((2 * n : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaCoset_two_mul_intCast_vadd (zero_mem (dual L)) n τ

/-- The translation law of the theta series of a coset of an integral lattice, in slash form: for
`γ ∈ L^∨`, every weight `k` and every integer `n`,
`θ_{γ+L} ∣[k] T ^ (2n) = exp (2 π i n ‖γ‖²) θ_{γ+L}`. -/
theorem thetaCoset_slash_T_zpow_two_mul (hL : IsIntegral L) (hγ : γ ∈ dual L) (k n : ℤ) :
    thetaCoset L γ ∣[k] (ModularGroup.T ^ (2 * n)) =
      cexp (2 * π * I * (‖γ‖ ^ 2 : ℝ) * n) • thetaCoset L γ := by
  ext τ
  rw [TauCeti.ModularForm.slash_T_zpow_apply, Pi.smul_apply, smul_eq_mul,
    ← hL.thetaCoset_two_mul_intCast_vadd hγ]
  push_cast
  rfl

/-- The theta series of an integral lattice is invariant under `T ^ 2`, in every weight:
`Θ_L ∣[k] T ^ 2 = Θ_L`. -/
theorem thetaSeries_slash_T_sq (hL : IsIntegral L) (k : ℤ) :
    thetaSeries L ∣[k] (ModularGroup.T ^ 2) = thetaSeries L := by
  ext τ
  rw [← zpow_natCast, TauCeti.ModularForm.slash_T_zpow_apply]
  simpa using hL.thetaSeries_two_mul_intCast_vadd 1 τ

end IsIntegral

end ZLattice
