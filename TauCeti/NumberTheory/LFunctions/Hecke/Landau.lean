/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Nonvanishing

/-!
# Nonvanishing and Landau criteria for presented Hecke L-functions

The canonical function `TauCeti.LFunctions.heckeLFunctionC χ` is defined via
`TauCeti.meromorphicContinuation 1`, so it agrees with the `L`-series of `χ` on `Re s > 1` only
once a **whole-plane** meromorphic normal-form continuation `g` exists
(`TauCeti.meromorphicContinuation_eqOn`). Given that explicit whole-plane prerequisite, this file
lifts `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re` and
`TauCeti.GlobalNumberFields.RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re` to
`heckeLFunctionC χ` on `Re s ≥ 1`:

* on `Re s > 1`, series agreement alone suffices via the Euler product;
* on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, `3-4-1` requires only complex differentiability
  of `heckeLFunctionC χ` at `s` (together with a continuous continuation of `L(χ ^ 2, ·)` at
  `2 * s - 1` when `χ ^ 2 ≠ 1`);
* only at `χ ^ 2 = 1 ∧ s = 1` does Landau's theorem require half-plane continuations of **both**
  `heckeLFunctionC χ` (holomorphic on `{z | 1 / 2 < z.re}`) and `ζ_K` (`Z` holomorphic on
  `{z | 1 / 2 < z.re} \ {1}`), together with the sharp boundary condition that
  `(Z σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.

For unconditional results without supplying a whole-plane continuation of `heckeLFunctionC χ`, see
`TauCeti.NumberTheory.LFunctions.Hecke.Rat` (which identifies `heckeLFunctionC χ` over `ℚ` with
Mathlib's `DirichletCharacter.LFunction`) and
`TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Nonvanishing` (which proves `Re s ≥ 1`
nonvanishing of `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` for nontrivial `χ ≠ 1`,
requiring `[K : ℚ] = 1` only at `χ ^ 2 = 1 ∧ s = 1`).

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re`: nonvanishing on `Re s ≥ 1` for
  `heckeLFunctionC χ` given the whole-plane series-agreement witness, reserving `3-4-1` and Landau
  half-plane hypotheses on `heckeLFunctionC χ` and `ζ_K` for their respective branches.
* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re`: meromorphic order
  zero on `Re s ≥ 1` for `heckeLFunctionC χ` under the same hypotheses.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao), which also supplies the unconditional nonvanishing over `ℚ` in
  `TauCeti.NumberTheory.LFunctions.Hecke.Rat`.
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Nonvanishing criterion on `Re s ≥ 1` for presented Hecke L-functions.**
Suppose the `L`-series of `χ` admits a whole-plane meromorphic normal-form continuation `g` (making
`heckeLFunctionC χ` agree with the `L`-series on `{z | 1 < z.re}`). Then `heckeLFunctionC χ s ≠ 0`
for any `s` with `1 ≤ s.re` under branch-minimal analytic hypotheses:
* on `1 < s.re`, nothing further is needed;
* on `s.re = 1` with `χ ^ 2 = 1` and `s ≠ 1`, differentiability of `heckeLFunctionC χ` at `s`
  suffices;
* on `s.re = 1` with `χ ^ 2 ≠ 1`, differentiability at `s` and a continuation of `L(χ ^ 2, ·)`
  continuous at `2 * s - 1` suffice;
* at `χ ^ 2 = 1 ∧ s = 1`, Landau's theorem applies given continuations of both `ζ_K` (`Z`
  holomorphic on `{z | 1 / 2 < z.re} \ {1}`) and `heckeLFunctionC χ` (holomorphic on
  `{z | 1 / 2 < z.re}`) such that `(Z σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as
  real `σ → (1 / 2)⁺`.

For an arbitrary continuation `L` with branch-specific hypotheses in place of the whole-plane
witness `hcont` (series agreement on `Re z > 1`, differentiability on `Re s = 1` away from
`χ ^ 2 = 1 ∧ s = 1`, a continuous continuation of `L(χ ^ 2, ·)` when `χ ^ 2 ≠ 1`, and half-plane
holomorphy of `ζ_K` and `L` together with the boundary limit condition at `χ ^ 2 = 1 ∧ s = 1`),
use `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hcont : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      EqOn g (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → DifferentiableAt ℂ (heckeLFunctionC χ) s)
    (hsq_ne : s.re = 1 → χ ^ 2 ≠ 1 → ∃ L₂ : ℂ → ℂ, ContinuousAt L₂ (2 * s - 1) ∧
      EqOn L₂
        (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    heckeLFunctionC χ s ≠ 0 := by
  have hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re} := by
    rw [heckeLFunctionC_def]
    exact meromorphicContinuation_eqOn hcont
  exact χ.ne_zero_of_one_le_re hLL hs hLs hsq_ne hlandau

/-- **Meromorphic order zero on `Re s ≥ 1` for presented Hecke L-functions.** Under the
whole-plane series-agreement witness and branch-minimal hypotheses of
`heckeLFunctionC_ne_zero_of_one_le_re`, `meromorphicOrderAt (heckeLFunctionC χ) s = 0`.

For an arbitrary continuation `L` with branch-specific hypotheses in place of `hcont` (including
half-plane holomorphy and the boundary limit condition at `χ ^ 2 = 1 ∧ s = 1`, together with
meromorphic normal form on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`),
see `TauCeti.GlobalNumberFields.RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hcont : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      EqOn g (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → DifferentiableAt ℂ (heckeLFunctionC χ) s)
    (hsq_ne : s.re = 1 → χ ^ 2 ≠ 1 → ∃ L₂ : ℂ → ℂ, ContinuousAt L₂ (2 * s - 1) ∧
      EqOn L₂
        (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re hcont hs hLs hsq_ne hlandau)

end TauCeti.LFunctions
