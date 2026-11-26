/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Presented Hecke L-functions over `ℚ`

Over `ℚ`, `TauCeti.GlobalNumberFields.RayClassCharacter.toDirichletCharacter` identifies any ray
class character `χ` of a modulus `𝔪` with a Dirichlet character `ψ = χ.toDirichletCharacter` modulo
`Ideal.absNorm 𝔪.finitePart` (`TauCeti.GlobalNumberFields.LSeries_rayClassCharacter_rat_eq`). Since
`DirichletCharacter.LFunction` is meromorphic on `ℂ` (entire when `ψ ≠ 1`, and agreeing with a
finite Euler product times `riemannZeta` when `ψ = 1`), the canonical meromorphic continuation
`TauCeti.LFunctions.heckeLFunctionC χ` equals
`toMeromorphicNFOn (DirichletCharacter.LFunction χ.toDirichletCharacter) Set.univ` for every `χ`
(including the principal character), yielding unconditional series agreement on `Re s > 1`, entire
continuation when `χ ≠ 1`, and nonvanishing (meromorphic order `0`) on `Re s ≥ 1` whenever
`χ ≠ 1 ∨ s ≠ 1`.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat`: identification of
  `heckeLFunctionC χ` with the meromorphic normal form of Mathlib's `DirichletCharacter.LFunction`
  for every `χ`.
* `TauCeti.LFunctions.differentiable_heckeLFunctionC_rat`: entireness of `heckeLFunctionC χ` when
  `χ ≠ 1`.
* `TauCeti.LFunctions.heckeLFunctionC_eq_LSeries_rat`: agreement with the defining `L`-series on
  `Re s > 1`.
* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_rat` and
  `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat`: unconditional
  nonvanishing and meromorphic order zero on `Re s ≥ 1` whenever `χ ≠ 1 ∨ s ≠ 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* The Dirichlet-character continuation is `DirichletCharacter.LFunction` in
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` (David Loeffler and Michael Stoll).
* Nonvanishing on `Re s ≥ 1` comes from `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

open Filter NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

/-- **Over `ℚ`, the presented Hecke L-function of any ray class character is the meromorphic normal
form of the corresponding Dirichlet L-function.** -/
theorem heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat {𝔪 : Modulus ℚ}
    (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ =
      toMeromorphicNFOn (DirichletCharacter.LFunction χ.toDirichletCharacter) Set.univ := by
  rw [heckeLFunctionC_def, LSeries_rayClassCharacter_rat_eq χ]
  exact meromorphicContinuation_eq_toMeromorphicNFOn
    χ.toDirichletCharacter.meromorphic_LFunction
    (fun s (hs : 1 < s.re) ↦
      χ.toDirichletCharacter.analyticAt_LFunction (.inl fun h ↦ by simp [h] at hs))
    fun _ hs ↦ DirichletCharacter.LFunction_eq_LSeries _ hs

/-- **Entire continuation over `ℚ`.** For any modulus `𝔪` of `ℚ` and any nontrivial ray class
character `χ ≠ 1`, `heckeLFunctionC χ` is entire. -/
theorem differentiable_heckeLFunctionC_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) : Differentiable ℂ (heckeLFunctionC χ) := by
  have hψ : χ.toDirichletCharacter ≠ 1 :=
    RayClassCharacter.toDirichletCharacter_eq_one_iff.not.mpr hχ
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ.toDirichletCharacter) :=
    DirichletCharacter.differentiable_LFunction hψ
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat χ,
    toMeromorphicNFOn_eq_self.mpr
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hLdiff).meromorphicNFOn]
  exact hLdiff

/-- **Dirichlet series agreement over `ℚ`.** For any modulus `𝔪` of `ℚ` and any ray class
character `χ`, `heckeLFunctionC χ` agrees with its defining `L`-series on `Re s > 1`. -/
theorem heckeLFunctionC_eq_LSeries_rat {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC χ s =
      LSeries (normCoeff ℚ χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat χ,
    toMeromorphicNFOn_apply_of_analyticAt χ.toDirichletCharacter.meromorphic_LFunction
      (χ.toDirichletCharacter.analyticAt_LFunction (.inl fun h ↦ by simp [h] at hs)),
    LSeries_rayClassCharacter_rat_eq χ,
    DirichletCharacter.LFunction_eq_LSeries _ hs]

/-- **Unconditional nonvanishing on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ`, any ray
class character `χ`, and any `s` with `1 ≤ s.re` such that `χ ≠ 1 ∨ s ≠ 1`,
`heckeLFunctionC χ s ≠ 0`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : heckeLFunctionC χ s ≠ 0 := by
  have hψs : χ.toDirichletCharacter ≠ 1 ∨ s ≠ 1 :=
    h.imp_left RayClassCharacter.toDirichletCharacter_eq_one_iff.not.mpr
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat χ,
    toMeromorphicNFOn_apply_of_analyticAt χ.toDirichletCharacter.meromorphic_LFunction
      (χ.toDirichletCharacter.analyticAt_LFunction hψs.symm)]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hψs hs

/-- **Meromorphic order zero on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ`, any ray class
character `χ`, and any `s` with `1 ≤ s.re` such that `χ ≠ 1 ∨ s ≠ 1` (excluding the pole of the
principal character `χ = 1` at `s = 1`), `meromorphicOrderAt (heckeLFunctionC χ) s = 0`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat {𝔪 : Modulus ℚ}
    {χ : RayClassCharacter 𝔪} {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re_rat h hs)

end TauCeti.LFunctions
