/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Reflection of the zeros of Dirichlet L-functions in the critical strip

In the open strip `0 < re s < 1` the functional equation carries the zeros of the continued
Dirichlet L-function `χ.LFunction`, with their multiplicities, to those of `χ⁻¹.LFunction`
under `s ↦ 1 - s`. Both the reflection and the order form of the conjugation identity
`L(χ⁻¹, conj s) = conj L(χ, s)` (`DirichletCharacter.meromorphicOrderAt_LFunction_inv_conj`) are
simp lemmas, so `simp` rewrites the order of `χ.LFunction` at `1 - conj s`, for `0 < re s < 1`, to
its order at `s`: the zeros in the open strip are invariant under `s ↦ 1 - conj s`. Orders are read
with `meromorphicOrderAt`, so the pole at `1` of the principal character, which lies outside the
open strip, needs no exception; for the character modulo `1` the statements are about
`riemannZeta`.

For a primitive character the reflection is read off Mathlib's functional equation
`DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, whose factor `N ^ (s - 1 / 2)` times
the root number is analytic and nonzero, together with
`DirichletCharacter.meromorphicOrderAt_completedLFunction`: on `0 < re s` the
completed function and `χ.LFunction` have the same order. An arbitrary character has, in the open
strip, the orders of its primitive character, since the deleted Euler factors vanish only on
`re s = 0` (`DirichletCharacter.meromorphicOrderAt_LFunction_changeLevel`); so the reflection holds
for every character.

The same reflection for the entire completion of a primitive character is
`TauCeti.LFunctions.analyticOrderAt_dirichletData_entireCompletion_one_sub`. Its comparison with
`χ.LFunction` on `re s > 0`,
`TauCeti.LFunctions.analyticOrderAt_dirichletData_entireCompletion_eq_LFunction`, needs `χ ≠ 1`,
so it does not cover `riemannZeta`; the order form here is read off Mathlib's functional
equation directly, uniformly in `χ`.

The half-plane predicate `TauCeti.ZeroFreeRightOf σ χ.LFunction` excludes points of positive
meromorphic order only, so it allows the pole `1` of the principal character even when `σ < 1`.
It holds for `χ⁻¹` exactly when it holds for `χ`, for every `σ`
(`DirichletCharacter.zeroFreeRightOf_LFunction_inv_iff`). The reflection turns it into a
statement about the zeros in the open strip: for `σ ≥ 0` it holds exactly when every zero `ρ` with
`0 < re ρ < 1` has `1 - σ ≤ re ρ ≤ σ`. At `σ = 1 / 2` this is the critical-line form of
the generalized Riemann hypothesis for `χ`; its form with the zeros in the half-plane `0 < re s`
reads pointwise values there, and so excludes the pole `1` of the principal character explicitly.

## Main results

* `DirichletCharacter.meromorphicOrderAt_LFunction_one_sub`: for `0 < re s < 1`, the order of
  `χ.LFunction` at `1 - s` is that of `χ⁻¹.LFunction` at `s`.
* `DirichletCharacter.LFunction_one_sub_eq_zero_iff`: the value form of the reflection.
* `DirichletCharacter.zeroFreeRightOf_LFunction_iff`: for `σ ≥ 0`, the strip form of
  `ZeroFreeRightOf σ χ.LFunction`.
* `DirichletCharacter.zeroFreeRightOf_one_half_LFunction_iff_re_eq_one_half`,
  `DirichletCharacter.zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos`: the two forms at
  `σ = 1 / 2`, with the zeros in the open strip and with the zeros in `re s > 0` off the pole.

## References

* The statements follow `Claim.prim_reflect` and `Claim.strip`
  (`Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`), `Deduction.LFunction_conj`
  (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LFunctionConj.lean`) and
  `Deduction.Gchi_conj_LFunction`
  (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/GchiConj.lean`) of the Lean
  formalization of the Riemann hypothesis for Dirichlet L-functions,
  https://github.com/leanprover-community/riemann-hypothesis.
* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`, for the
  functional equation.
-/

public section

open Complex Filter TauCeti
open scoped Topology ComplexConjugate

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The reflection of orders in the open strip, for a primitive character, read off the orders of
the completed L-functions. -/
private theorem IsPrimitive.meromorphicOrderAt_LFunction_one_sub {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    meromorphicOrderAt χ.LFunction (1 - s) = meromorphicOrderAt χ⁻¹.LFunction s := by
  set g : ℂ → ℂ := fun z ↦ (N : ℂ) ^ (z - 1 / 2) * χ.rootNumber with hg_def
  have heq : (χ.completedLFunction ∘ fun z ↦ 1 - z) = g * χ⁻¹.completedLFunction :=
    funext fun z ↦ by
      simpa only [Function.comp_apply, Pi.mul_apply, hg_def] using hχ.completedLFunction_one_sub z
  have hg : AnalyticAt ℂ g s :=
    (analyticAt_const.cpow (by fun_prop) (by simp [NeZero.ne N])).mul analyticAt_const
  have hg0 : g s ≠ 0 :=
    mul_ne_zero (by simp [NeZero.ne N]) (rootNumber_ne_zero hχ)
  rw [← χ.meromorphicOrderAt_completedLFunction (by simpa using hs1),
    ← χ⁻¹.meromorphicOrderAt_completedLFunction hs0,
    ← meromorphicOrderAt_comp_of_deriv_ne_zero (f := χ.completedLFunction) (g := fun z ↦ 1 - z)
      (by fun_prop) (by simp), heq, meromorphicOrderAt_mul_of_ne_zero hg hg0]

/-- **Reflection of zeros in the critical strip.** For `0 < re s < 1`, the order of
`χ.LFunction` at `1 - s` is the order of `χ⁻¹.LFunction` at `s`. Primitivity is not needed: in the
open strip a character has the orders of its primitive character. -/
@[simp]
theorem meromorphicOrderAt_LFunction_one_sub {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    meromorphicOrderAt χ.LFunction (1 - s) = meromorphicOrderAt χ⁻¹.LFunction s := by
  have hdvd := χ.conductor_dvd_level
  calc meromorphicOrderAt χ.LFunction (1 - s)
      = meromorphicOrderAt χ.primitiveCharacter.LFunction (1 - s) := by
        conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
        exact meromorphicOrderAt_LFunction_changeLevel _ hdvd (by simpa using hs1)
    _ = meromorphicOrderAt χ.primitiveCharacter⁻¹.LFunction s :=
        χ.primitiveCharacter_isPrimitive.meromorphicOrderAt_LFunction_one_sub hs0 hs1
    _ = meromorphicOrderAt χ⁻¹.LFunction s := by
        rw [← meromorphicOrderAt_LFunction_changeLevel _ hdvd hs0, map_inv,
          changeLevel_primitiveCharacter]

/-- For `0 < re s < 1`, `χ.LFunction` vanishes at `1 - s` exactly when `χ⁻¹.LFunction` vanishes
at `s`. -/
@[simp]
theorem LFunction_one_sub_eq_zero_iff {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    χ.LFunction (1 - s) = 0 ↔ χ⁻¹.LFunction s = 0 := by
  have hs : s ≠ 1 := fun h ↦ by simp [h] at hs1
  have hs' : 1 - s ≠ 1 := fun h ↦ by simp [sub_eq_self.1 h] at hs0
  have h := congrArg (0 < ·) (χ.meromorphicOrderAt_LFunction_one_sub hs0 hs1)
  simpa [hs, hs'] using h

/-- **Strip form of a zero-free half-plane.** For `σ ≥ 0`, `χ.LFunction` is zero-free right of `σ`
exactly when every zero `ρ` in the open strip `0 < re ρ < 1` has `1 - σ ≤ re ρ ≤ σ`. For
`σ < 1 / 2` both sides say that there is no zero in the open strip, and for `σ ≥ 1` both hold.
The hypothesis `0 ≤ σ` excludes the zeros with `re ρ ≤ 0`, which the right side does not see.
`ZeroFreeRightOf` rules out points of positive meromorphic order only, so the pole `1` of the
principal character is allowed on the left even when `σ < 1`; the right side reads values only in
the open strip, which does not contain the pole. -/
theorem zeroFreeRightOf_LFunction_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ χ.LFunction ↔ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 →
      1 - σ ≤ ρ.re ∧ ρ.re ≤ σ := by
  rw [zeroFreeRightOf_iff]
  refine ⟨fun h ρ hρ0 hρ1 hρ ↦ ?_, fun h s hs ↦ ?_⟩
  · have hpos : 0 < meromorphicOrderAt χ.LFunction ρ :=
      (χ.meromorphicOrderAt_LFunction_pos_iff).2 ⟨hρ, .inl fun h1 ↦ by simp [h1] at hρ1⟩
    have hle (z : ℂ) (hz : 0 < meromorphicOrderAt χ.LFunction z) : z.re ≤ σ :=
      not_lt.1 fun hσz ↦ (h z hσz).not_gt hz
    have hconj := hle (1 - conj ρ)
      (by simpa [hρ0, hρ1] using hpos)
    have hre : (1 - conj ρ).re = 1 - ρ.re := by simp
    exact ⟨by linarith, hle ρ hpos⟩
  · refine not_lt.1 fun hpos ↦ ?_
    obtain ⟨h0, h1⟩ := (χ.meromorphicOrderAt_LFunction_pos_iff).1 hpos
    exact hs.not_ge (h s (hσ.trans_lt hs) (χ.re_lt_one_of_LFunction_eq_zero h1 h0) h0).2

/-- **Critical-line form.** `χ.LFunction` is zero-free right of `1 / 2` exactly when every zero
in the open strip `0 < re ρ < 1` lies on the critical line `re ρ = 1 / 2`. As in
`zeroFreeRightOf_LFunction_iff`, the left side excludes only points of positive order, so the pole
`1` of the principal character does not contradict it; the right side never reads the pole. -/
theorem zeroFreeRightOf_one_half_LFunction_iff_re_eq_one_half :
    ZeroFreeRightOf (1 / 2) χ.LFunction ↔
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1 / 2 := by
  rw [χ.zeroFreeRightOf_LFunction_iff (by norm_num)]
  refine forall₄_congr fun ρ _ _ _ ↦ ?_
  constructor
  · rintro ⟨h1, h2⟩
    linarith
  · intro h
    constructor <;> linarith

/-- **Critical-line form, without the strip.** `χ.LFunction` is zero-free right of `1 / 2` exactly
when every zero `s` with `0 < re s`, other than the pole `1` of the principal character, lies on
the critical line `re s = 1 / 2`. Unlike the left side, which reads orders, the right side reads
pointwise values on the half-plane `0 < re s`, which contains the pole; the guard `χ ≠ 1 ∨ s ≠ 1`
excludes the value Mathlib assigns at the pole. -/
theorem zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos :
    ZeroFreeRightOf (1 / 2) χ.LFunction ↔
      ∀ s : ℂ, 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s = 0 → s.re = 1 / 2 := by
  rw [χ.zeroFreeRightOf_one_half_LFunction_iff_re_eq_one_half]
  refine ⟨fun h s hs0 h1 hs ↦ h s hs0 (χ.re_lt_one_of_LFunction_eq_zero h1.symm hs) hs,
    fun h ρ hρ0 hρ1 hρ ↦ h ρ hρ0 (.inr fun h1 ↦ by simp [h1] at hρ1) hρ⟩

end DirichletCharacter
