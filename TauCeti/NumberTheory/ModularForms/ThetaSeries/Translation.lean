/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
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
  under `T ^ N` as soon as `N ‖γ‖² / 2 ∈ ℤ`; when some `N > 0` works for every `γ ∈ L^∨` (for
  instance when `L` is a full lattice in a finite-dimensional space), the least one is the level
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
* `ZLattice.thetaCoset_vadd_eq_self`: if `h ‖γ + v‖² ∈ 2ℤ` for every `v ∈ L`, then `θ_{γ+L}` has
  period `h`.
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
  have ht : cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * t) = cexp (π * I * (‖γ‖ ^ 2 : ℝ) * t) := by
    simpa only [mul_assoc] using exp_pi_mul_I_mul_eq_of_sub_eq
      (a := ((‖γ + (v : E)‖ ^ 2 : ℝ) : ℂ) * t) (b := ((‖γ‖ ^ 2 : ℝ) : ℂ) * t)
      (by rw [← sub_mul]; exact_mod_cast hm)
  rw [coe_vadd, mul_add, exp_add, ht]

/-- If `h ‖γ + v‖²` is an even integer for every `v ∈ L`, then the theta series of `γ + L` has
period `h`. -/
theorem thetaCoset_vadd_eq_self (L : Submodule ℤ E) (γ : E) {h : ℝ}
    (hnorm : ∀ v ∈ L, ∃ m : ℤ, h * ‖γ + v‖ ^ 2 = 2 * m) (τ : ℍ) :
    thetaCoset L γ (h +ᵥ τ) = thetaCoset L γ τ := by
  obtain ⟨n, hn⟩ := hnorm 0 (zero_mem L)
  rw [add_zero] at hn
  rw [thetaCoset_vadd_eq_mul L γ (fun v hv ↦ ?_) τ]
  · have h1 : cexp (π * I * (‖γ‖ ^ 2 : ℝ) * h) = 1 := by
      simpa only [mul_zero, exp_zero, mul_assoc] using exp_pi_mul_I_mul_eq_of_sub_eq
        (a := ((‖γ‖ ^ 2 : ℝ) : ℂ) * h) (b := 0) (by rw [sub_zero, mul_comm]; exact_mod_cast hn)
    rw [h1, one_mul]
  · obtain ⟨m, hm⟩ := hnorm v hv
    exact ⟨m - n, by push_cast; linarith⟩

variable {L : Submodule ℤ E}

/-! ### Even lattices -/

namespace IsEven

/-- The theta series of an even lattice has period `1`. -/
@[simp]
theorem thetaSeries_intCast_vadd (hL : IsEven L) (n : ℤ) (τ : ℍ) :
    thetaSeries L ((n : ℝ) +ᵥ τ) = thetaSeries L τ := by
  rw [← thetaCoset_zero, thetaCoset_vadd_eq_mul L 0 (fun v hv ↦ ?_) τ]
  · simp
  · obtain ⟨m, hm⟩ := isEven_iff.mp hL v hv
    exact ⟨m * n, by rw [zero_add, hm, norm_zero]; push_cast; ring⟩

/-- The theta series of an even lattice has period `1`: `Θ_L(τ + 1) = Θ_L(τ)`. -/
@[simp]
theorem thetaSeries_one_vadd (hL : IsEven L) (τ : ℍ) :
    thetaSeries L ((1 : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaSeries_intCast_vadd 1 τ

/-- The theta series of an even lattice is invariant under every power of `T`, in every
weight. -/
@[simp]
theorem thetaSeries_slash_T_zpow (hL : IsEven L) (k n : ℤ) :
    thetaSeries L ∣[k] (ModularGroup.T ^ n) = thetaSeries L := by
  ext τ
  rw [TauCeti.ModularForm.slash_T_zpow_apply, hL.thetaSeries_intCast_vadd]

/-- The theta series of an even lattice is invariant under `T`, in every weight:
`Θ_L ∣[k] T = Θ_L`. -/
@[simp]
theorem thetaSeries_slash_T (hL : IsEven L) (k : ℤ) :
    thetaSeries L ∣[k] ModularGroup.T = thetaSeries L := by
  simpa using hL.thetaSeries_slash_T_zpow k 1

end IsEven

variable [InnerProductSpace ℝ E] {γ : E}

namespace IsEven

/-- For an even lattice `L` and `γ ∈ L^∨`, the factor `e(q_L(γ)) = exp (π i ‖γ‖²)` of the
translation law depends only on the coset `γ + L`. -/
theorem cexp_pi_mul_I_mul_norm_add_sq (hL : IsEven L) (hγ : γ ∈ dual L) {v : E} (hv : v ∈ L) :
    cexp (π * I * (‖γ + v‖ ^ 2 : ℝ)) = cexp (π * I * (‖γ‖ ^ 2 : ℝ)) := by
  obtain ⟨m, hm⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
  exact exp_pi_mul_I_mul_eq_of_sub_eq (by exact_mod_cast hm)

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
  have h1 : cexp (π * I * (‖γ‖ ^ 2 : ℝ) * N) = 1 := by
    simpa only [mul_zero, exp_zero, mul_assoc] using exp_pi_mul_I_mul_eq_of_sub_eq
      (a := ((‖γ‖ ^ 2 : ℝ) : ℂ) * N) (b := 0) (by rw [sub_zero, mul_comm]; exact_mod_cast hm)
  rw [hL.thetaCoset_slash_T_zpow hγ, h1, one_smul]

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

/-- The translation law of the theta series of a coset of an integral lattice: for `γ ∈ L^∨`,
`θ_{γ+L}(τ + 2) = exp (2 π i ‖γ‖²) θ_{γ+L}(τ)`. -/
theorem thetaCoset_two_vadd (hL : IsIntegral L) (hγ : γ ∈ dual L) (τ : ℍ) :
    thetaCoset L γ ((2 : ℝ) +ᵥ τ) = cexp (2 * π * I * (‖γ‖ ^ 2 : ℝ)) * thetaCoset L γ τ := by
  simpa using hL.thetaCoset_two_mul_intCast_vadd hγ 1 τ

/-- The theta series of an integral lattice has period `2`. -/
@[simp]
theorem thetaSeries_two_mul_intCast_vadd (hL : IsIntegral L) (n : ℤ) (τ : ℍ) :
    thetaSeries L ((2 * n : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaCoset_two_mul_intCast_vadd (zero_mem (dual L)) n τ

/-- The theta series of an integral lattice has period `2`: `Θ_L(τ + 2) = Θ_L(τ)`. -/
@[simp]
theorem thetaSeries_two_vadd (hL : IsIntegral L) (τ : ℍ) :
    thetaSeries L ((2 : ℝ) +ᵥ τ) = thetaSeries L τ := by
  simpa using hL.thetaSeries_two_mul_intCast_vadd 1 τ

/-- The translation law of the theta series of a coset of an integral lattice, in slash form: for
`γ ∈ L^∨`, every weight `k` and every integer `n`,
`θ_{γ+L} ∣[k] T ^ (2n) = exp (2 π i n ‖γ‖²) θ_{γ+L}`. -/
theorem thetaCoset_slash_T_zpow_two_mul (hL : IsIntegral L) (hγ : γ ∈ dual L) (k n : ℤ) :
    thetaCoset L γ ∣[k] (ModularGroup.T ^ (2 * n)) =
      cexp (2 * π * I * (‖γ‖ ^ 2 : ℝ) * n) • thetaCoset L γ := by
  ext τ
  rw [TauCeti.ModularForm.slash_T_zpow_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_ofNat, hL.thetaCoset_two_mul_intCast_vadd hγ]

/-- The theta series of an integral lattice is invariant under `T ^ 2`, in every weight:
`Θ_L ∣[k] T ^ 2 = Θ_L`. -/
@[simp]
theorem thetaSeries_slash_T_sq (hL : IsIntegral L) (k : ℤ) :
    thetaSeries L ∣[k] (ModularGroup.T ^ 2) = thetaSeries L := by
  ext τ
  rw [← zpow_natCast, TauCeti.ModularForm.slash_T_zpow_apply]
  simpa using hL.thetaSeries_two_mul_intCast_vadd 1 τ

end IsIntegral

end ZLattice
