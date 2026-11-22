/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Fuchsian
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cusp multipliers of `Γ₀(N)` with a Dirichlet character

Let `χ` be a Dirichlet character modulo `N` and `γ = [a,b;c,d] ∈ SL₂(ℤ)`. The stabilizer of the
cusp `γ ∞` in `Γ₀(N)` is generated, up to sign, by `TauCeti.cuspGenerator N γ = γ T^w γ⁻¹`, whose
lower-right entry is `1 + wac` for `w = TauCeti.cuspWidth N γ`. Its value under `χ` is the
*multiplier* `ζ = χ(1 + wac)` of the cusp: a function `f` with `f (δ z) = χ(d_δ) f z` for
`δ ∈ Γ₀(N)` satisfies `f (γ (z + w)) = ζ f (γ z)`. The cusp is *regular* for `χ` when `ζ = 1`, so
that `z ↦ f (γ z)` is periodic, and *irregular* otherwise.

The multiplier is an `N / w`-th root of unity, since the `N / w`-th power of the generator is
`γ T^N γ⁻¹`, which has lower-right entry `1` modulo `N`. It depends only on the cusp orbit. The
cusp `∞` is regular for every character, and every cusp is regular for the trivial character.
At level `9`, the cusp `1/3` has width `1` and multiplier `χ(4)`; it is irregular for every
character with `χ(4) ≠ 1`, such as the even characters of order `3`, and such characters exist.

## Main declarations

* `TauCeti.cuspMultiplier`: the multiplier `χ(1 + wac)` of the cusp `γ ∞`.
* `TauCeti.IsRegularCusp`: the multiplier is `1`.
* `TauCeti.cuspMultiplier_pow_div_cuspWidth`: the multiplier is an `N / w`-th root of unity.
* `TauCeti.cuspMultiplier_eq_of_cuspOrbitOfSL2Z_eq`: it depends only on the cusp orbit.
* `TauCeti.exists_not_isRegularCusp_nine`: some character modulo `9` has an irregular cusp.

## References

* Henryk Iwaniec, *Spectral Methods of Automorphic Forms*, §2.4 and §3.4.
* Andrew R. Booker, Min Lee and Andreas Strömbergsson, *Twist-minimal trace formulas and the
  Selberg eigenvalue conjecture*, arXiv:1803.06016, §1.1.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ}

/-- **The multiplier of the cusp `γ ∞` for the character `χ`**: the value `χ(1 + wac)` of `χ` at
the lower-right entry of the generator `cuspGenerator N γ = γ T^w γ⁻¹` of the stabilizer, where
`γ = [a,b;c,d]` and `w = cuspWidth N γ`. -/
def cuspMultiplier (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) : R :=
  χ (Gamma0Map N (cuspGenerator N γ))

theorem cuspMultiplier_def (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) :
    cuspMultiplier χ γ = χ (Gamma0Map N (cuspGenerator N γ)) := (rfl)

/-- The multiplier of `γ ∞ = a / c` is `χ(1 + wac)` for `w = cuspWidth N γ`. -/
theorem cuspMultiplier_eq (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) :
    cuspMultiplier χ γ = χ ((1 + cuspWidth N γ * γ 0 0 * γ 1 0 : ℤ) : ZMod N) := by
  rw [cuspMultiplier, Gamma0Map_cuspGenerator]

/-- The multiplier of the cusp `∞` is `1`. -/
@[simp]
theorem cuspMultiplier_one_right (χ : DirichletCharacter R N) : cuspMultiplier χ 1 = 1 := by
  rw [cuspMultiplier, Gamma0Map_cuspGenerator_one, map_one]

/-- For the trivial character every multiplier is `1`, since `1 + wac` is a unit modulo `N`. -/
@[simp]
theorem cuspMultiplier_one_left (γ : SL(2, ℤ)) :
    cuspMultiplier (1 : DirichletCharacter R N) γ = 1 := by
  rw [cuspMultiplier, ← MonoidHom.coe_toHomUnits, MulChar.one_apply_coe]

/-- **The multiplier is an `N / w`-th root of unity**, for `w = cuspWidth N γ`: the `N / w`-th
power of the generator is `γ T^N γ⁻¹`, whose lower-right entry `1 + Nac` is `1` modulo `N`. -/
theorem cuspMultiplier_pow_div_cuspWidth (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) :
    cuspMultiplier χ γ ^ (N / cuspWidth N γ) = 1 := by
  have hpow : ((cuspGenerator N γ ^ (N / cuspWidth N γ) : Gamma0 N) : SL(2, ℤ)) =
      γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ := by
    rw [Subgroup.coe_pow, coe_cuspGenerator, conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      ← Nat.cast_mul, Nat.mul_div_cancel' (cuspWidth_dvd N γ)]
  rw [cuspMultiplier, ← map_pow, ← map_pow, Gamma0Map_apply, hpow, γ.coe_conj_T_zpow]
  simp

/-- The multiplier depends only on the cusp orbit. -/
theorem cuspMultiplier_eq_of_cuspOrbitOfSL2Z_eq [NeZero N] (χ : DirichletCharacter R N)
    {γ γ' : SL(2, ℤ)} (h : (Gamma0 N).cuspOrbitOfSL2Z γ = (Gamma0 N).cuspOrbitOfSL2Z γ') :
    cuspMultiplier χ γ' = cuspMultiplier χ γ := by
  rw [cuspMultiplier, Gamma0Map_cuspGenerator_eq_of_cuspOrbitOfSL2Z_eq N h, cuspMultiplier]

/-- **A regular cusp for `χ`**: the cusp `γ ∞` whose multiplier `χ(1 + wac)` is `1`, so that
`z ↦ f (γ z)` is `w`-periodic for every `f` transforming under `Γ₀(N)` by `χ`. -/
def IsRegularCusp (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) : Prop :=
  cuspMultiplier χ γ = 1

theorem isRegularCusp_iff (χ : DirichletCharacter R N) (γ : SL(2, ℤ)) :
    IsRegularCusp χ γ ↔ cuspMultiplier χ γ = 1 := Iff.rfl

/-- The cusp `∞` is regular for every character. -/
@[simp]
theorem isRegularCusp_one_right (χ : DirichletCharacter R N) : IsRegularCusp χ 1 :=
  cuspMultiplier_one_right χ

/-- Every cusp is regular for the trivial character. -/
@[simp]
theorem isRegularCusp_one_left (γ : SL(2, ℤ)) : IsRegularCusp (1 : DirichletCharacter R N) γ :=
  cuspMultiplier_one_left γ

/-- Regularity depends only on the cusp orbit. -/
theorem isRegularCusp_iff_of_cuspOrbitOfSL2Z_eq [NeZero N] (χ : DirichletCharacter R N)
    {γ γ' : SL(2, ℤ)} (h : (Gamma0 N).cuspOrbitOfSL2Z γ = (Gamma0 N).cuspOrbitOfSL2Z γ') :
    IsRegularCusp χ γ' ↔ IsRegularCusp χ γ := by
  rw [isRegularCusp_iff, isRegularCusp_iff, cuspMultiplier_eq_of_cuspOrbitOfSL2Z_eq χ h]

/-- At level `9` the cusp `1/3`, represented by any `γ = [1,b;3,d]`, has width `1` and multiplier
`χ(1 + 1 · 1 · 3) = χ(4)`. -/
theorem cuspMultiplier_nine (χ : DirichletCharacter R 9) {γ : SL(2, ℤ)} (h₀₀ : γ 0 0 = 1)
    (h₁₀ : γ 1 0 = 3) : cuspMultiplier χ γ = χ 4 := by
  have hw : cuspWidth 9 γ = 1 := by
    rw [cuspWidth_def, h₁₀]
    rfl
  rw [cuspMultiplier_eq, hw, h₀₀, h₁₀]
  norm_num

/-- **An irregular cusp**: some Dirichlet character modulo `9` has the cusp `1/3` irregular,
namely any character with `χ(4) ≠ 1`, which exists because `4 ≠ 1` modulo `9`. -/
theorem exists_not_isRegularCusp_nine :
    ∃ χ : DirichletCharacter ℂ 9, ∀ γ : SL(2, ℤ), γ 0 0 = 1 → γ 1 0 = 3 → ¬IsRegularCusp χ γ := by
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (n := 9) (a := 4) (by decide)
  exact ⟨χ, fun γ h₀₀ h₁₀ ↦ by rwa [isRegularCusp_iff, cuspMultiplier_nine χ h₀₀ h₁₀]⟩

end TauCeti
