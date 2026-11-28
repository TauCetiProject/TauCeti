/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.GRH
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Reduction

/-!
# From parameter-modulus nonvanishing to GRH and the Riemann hypothesis

`TauCeti.OneSidedBound.forall_zeroFreeRightOf_LFunction_iff_forall_parameters` reduces the
meromorphic half-plane condition `ZeroFreeRightOf (1 / 2) χ.LFunction` for all Dirichlet
characters to pointwise nonvanishing away from `s = 1` on `Re s > β` (`β > 1 / 2`) at the
parameter moduli `P.q₀`. Combining this reduction with the critical-line equivalences in
`TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection` and `GRH` yields the end
theorems: `TauCeti.GRH`, the open-strip critical-line form for every character, nonvanishing of
`riemannZeta` on `Re s > 1 / 2`, and Mathlib's `RiemannHypothesis`.

## Main results

* `TauCeti.OneSidedBound.grh_iff_forall_parameters`: equivalence between `TauCeti.GRH` and
  pointwise nonvanishing off `s = 1` on `Re s > β` (`β > 1 / 2`) at every parameter modulus.
* `TauCeti.OneSidedBound.re_eq_one_half_of_forall_parameters`: strip form `Re s = 1 / 2` for
  every zero of `χ.LFunction` in `0 < Re s < 1`.
* `TauCeti.OneSidedBound.riemannZeta_ne_zero_of_forall_parameters`: `riemannZeta s ≠ 0` for
  every `s` with `1 / 2 < Re s` (including `s = 1`).
* `TauCeti.OneSidedBound.riemannHypothesis_of_forall_parameters`: Mathlib's `RiemannHypothesis`.

## Provenance

Adapted from `New.zeros_on_line` and `New.zeta_zeros_on_line` in `grh/src/New/Main.lean` and
`New.grh` in `grh/src/New/Reduction/OneSidedBound.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open DirichletCharacter

namespace TauCeti.OneSidedBound

/-- `GRH` holds for all Dirichlet characters if and only if, for every `Parameters` and every
`β > 1 / 2`, no Dirichlet L-function modulo `P.q₀` vanishes at any `s ≠ 1` with `Re s > β`. -/
theorem grh_iff_forall_parameters :
    GRH ↔ ∀ (P : Parameters) (β : ℝ), 1 / 2 < β → ∀ (χ : DirichletCharacter ℂ P.q₀) {s : ℂ},
      β < s.re → s ≠ 1 → χ.LFunction s ≠ 0 := by
  rw [← forall_zeroFreeRightOf_LFunction_iff_forall_parameters, grh_def]
  refine forall_congr' fun N ↦ forall_congr' fun _ ↦ forall_congr' fun χ ↦ ?_
  rw [χ.zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos, dirichletGRH_def]

/-- Strip form: nonvanishing off `s = 1` on `Re s > β` (`β > 1 / 2`) at every parameter modulus
implies that every zero of every Dirichlet L-function in `0 < Re s < 1` lies on `Re s = 1 / 2`. -/
theorem re_eq_one_half_of_forall_parameters
    (h : ∀ (P : Parameters) (β : ℝ), 1 / 2 < β → ∀ (χ : DirichletCharacter ℂ P.q₀) {s : ℂ},
      β < s.re → s ≠ 1 → χ.LFunction s ≠ 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : χ.LFunction s = 0) : s.re = 1 / 2 :=
  ((χ.dirichletGRH_iff_mem_Ioo).mp ((grh_iff_forall_parameters.mpr h).dirichletGRH χ))
    s hz ⟨hs0, hs1⟩

/-- Nonvanishing of `riemannZeta` on the entire open half-plane `1 / 2 < Re s` (including `s = 1`)
from parameter-modulus nonvanishing. -/
theorem riemannZeta_ne_zero_of_forall_parameters
    (h : ∀ (P : Parameters) (β : ℝ), 1 / 2 < β → ∀ (χ : DirichletCharacter ℂ P.q₀) {s : ℂ},
      β < s.re → s ≠ 1 → χ.LFunction s ≠ 0)
    {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · simpa [hs1] using riemannZeta_one_ne_zero
  · have hgrh := (grh_iff_forall_parameters.mpr h).dirichletGRH (1 : DirichletCharacter ℂ 1)
    intro hz
    have hre := hgrh.re_eq (by linarith) (.inr hs1) (by simpa [LFunction_modOne_eq] using hz)
    linarith

/-- Mathlib's `RiemannHypothesis` follows from parameter-modulus nonvanishing off `s = 1` on
every half-plane `Re s > β` with `β > 1 / 2`. -/
theorem riemannHypothesis_of_forall_parameters
    (h : ∀ (P : Parameters) (β : ℝ), 1 / 2 < β → ∀ (χ : DirichletCharacter ℂ P.q₀) {s : ℂ},
      β < s.re → s ≠ 1 → χ.LFunction s ≠ 0) : RiemannHypothesis :=
  (grh_iff_forall_parameters.mpr h).riemannHypothesis

end TauCeti.OneSidedBound
