/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing.Continuation

/-!
# Nonvanishing and Landau criteria for presented Hecke L-functions

Given series agreement `hLL` on `Re z > 1` for the canonical function
`TauCeti.LFunctions.heckeLFunctionC χ` (obtained from a whole-plane meromorphic normal-form
continuation via `TauCeti.meromorphicContinuation_eqOn`), this file lifts
`TauCeti.GlobalNumberFields.RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re` to
`heckeLFunctionC χ` on `Re s ≥ 1`:

* since `heckeLFunctionC χ` is already meromorphic in normal form on `ℂ`, boundary meromorphy is
  automatic, and comparison with the analytic nonvanishing model yields `meromorphicOrderAt = 0`
  and nonvanishing away from `χ ^ 2 = 1 ∧ s = 1`;
* only at `χ ^ 2 = 1 ∧ s = 1` does Landau's theorem require holomorphy of `heckeLFunctionC χ` on
  `{z | 1 / 2 < z.re}` together with the sharp boundary condition that
  `(dedekindZetaC K σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`
  (supplying `dedekindZetaC K` internally).

For the cancellation comparison `heckeLFunctionC_eqOn_continuedLFunctionOfWeight`, see
`TauCeti.NumberTheory.LFunctions.Hecke.Cancellation`. For unconditional results without supplying
series agreement for `heckeLFunctionC χ`, see `TauCeti.NumberTheory.LFunctions.Hecke.Rat.Basic`
(identifying `heckeLFunctionC χ` over `ℚ` with the meromorphic normal form of Mathlib's
`DirichletCharacter.LFunction`), `TauCeti.NumberTheory.LFunctions.Hecke.Rat.Nonvanishing`
(giving unconditional nonvanishing and meromorphic order zero on `Re s ≥ 1` over `ℚ` whenever
`χ ≠ 1 ∨ s ≠ 1`), `TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing.Basic` (unitary character
families and away-from-exception nonvanishing of `continuedLFunctionOfWeight`), and
`TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing.DegreeOne` (full `Re s ≥ 1` nonvanishing of
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` for nontrivial `χ ≠ 1`, requiring
`[K : ℚ] = 1` only at `χ ^ 2 = 1 ∧ s = 1`).

## Main results

* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re`: meromorphic order
  zero on `Re s ≥ 1` for `heckeLFunctionC χ` given series agreement on `Re z > 1`, reserving
  Landau half-plane hypotheses on `heckeLFunctionC χ` solely for `χ ^ 2 = 1 ∧ s = 1`.
* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re`: nonvanishing on `Re s ≥ 1` for
  `heckeLFunctionC χ` under the same hypotheses.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao), which also supplies the unconditional nonvanishing over `ℚ` in
  `TauCeti.NumberTheory.LFunctions.Hecke.Rat.Nonvanishing`.
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Meromorphic order zero on `Re s ≥ 1` for presented Hecke L-functions.**
Suppose `heckeLFunctionC χ` agrees with the defining `L`-series on `{z | 1 < z.re}` (for
instance via `meromorphicContinuation_eqOn` from a whole-plane meromorphic normal-form
continuation). Then `meromorphicOrderAt (heckeLFunctionC χ) s = 0` for any `s` with `1 ≤ s.re`
unconditionally away from `χ ^ 2 = 1 ∧ s = 1`, and at `χ ^ 2 = 1 ∧ s = 1` given holomorphy of
`heckeLFunctionC χ` on `{z | 1 / 2 < z.re}` together with the sharp boundary condition that
`(dedekindZetaC K σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.

For an arbitrary continuation `L` with branch-specific hypotheses, see
`TauCeti.GlobalNumberFields.RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  χ.meromorphicOrderAt_eq_zero_of_one_le_re hLL hs
    (fun _ _ ↦ (meromorphicNFOn_heckeLFunctionC χ (Set.mem_univ s)).meromorphicAt) hlandau

/-- **Nonvanishing criterion on `Re s ≥ 1` for presented Hecke L-functions.**
Under the series-agreement and Landau hypotheses of
`meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re`, `heckeLFunctionC χ s ≠ 0`.

For an arbitrary continuation `L` with branch-specific hypotheses, use
`TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    heckeLFunctionC χ s ≠ 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mp
    (meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re hLL hs hlandau)

end TauCeti.LFunctions
