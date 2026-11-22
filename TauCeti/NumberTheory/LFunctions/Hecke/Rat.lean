/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Presented Hecke L-functions over `ℚ`

Over `ℚ`, `TauCeti.GlobalNumberFields.ratDirichletEquiv` identifies any ray class character `χ`
of a modulus `𝔪` with a Dirichlet character `ψ` modulo `n = Ideal.absNorm 𝔪.finitePart`
(`TauCeti.GlobalNumberFields.lSeries_rayClassCharacter_rat_eq`). Since
`DirichletCharacter.LFunction` is meromorphic on `ℂ` (entire when `ψ ≠ 1`, and agreeing with a
finite Euler product times `riemannZeta` when `ψ = 1`), the canonical meromorphic continuation
`TauCeti.LFunctions.heckeLFunctionC χ` equals
`toMeromorphicNFOn (DirichletCharacter.LFunction ψ) Set.univ` for every `χ` (including the
principal character), yielding unconditional series agreement on `Re s > 1`, entire continuation
when `χ ≠ 1`, and nonvanishing (meromorphic order `0`) on `Re s ≥ 1` whenever `χ ≠ 1 ∨ s ≠ 1`.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_eq_LFunction_rat`: identification of `heckeLFunctionC χ`
  with the meromorphic normal form of Mathlib's `DirichletCharacter.LFunction` for every `χ`.
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

/-- Associated Dirichlet character modulo `Ideal.absNorm 𝔪.finitePart` for a ray class character
over `ℚ`. -/
private noncomputable def ratDirichletCharacter {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪) :
    DirichletCharacter ℂ (Ideal.absNorm 𝔪.finitePart) :=
  ratDirichletEquiv (Ideal.absNorm 𝔪.finitePart)
    (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
    (χ.induced (dvd_ratModulus_absNorm 𝔪))

private theorem ratDirichletCharacter_ne_one {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) : ratDirichletCharacter χ ≠ 1 := by
  intro h
  apply hχ
  rw [← RayClassCharacter.induced_eq_one_iff (dvd_ratModulus_absNorm 𝔪)]
  exact (ratDirichletEquiv _ _).injective (by simpa [ratDirichletCharacter] using h)

private theorem ne_one_or_ne_one_of_rayClass {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) : ratDirichletCharacter χ ≠ 1 ∨ s ≠ 1 :=
  h.imp_left ratDirichletCharacter_ne_one

private theorem analyticAt_LFunction_of_ne_one_or_ne_one {n : ℕ} [NeZero n]
    (ψ : DirichletCharacter ℂ n) {s : ℂ} (hs : ψ ≠ 1 ∨ s ≠ 1) :
    AnalyticAt ℂ (DirichletCharacter.LFunction ψ) s := by
  rcases hs with hψ | hs1
  · exact Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (DirichletCharacter.differentiable_LFunction hψ) s (mem_univ s)
  · have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction ψ) ({1}ᶜ : Set ℂ) := fun z hz ↦
      (DirichletCharacter.differentiableAt_LFunction ψ z (.inl hz)).differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_compl_singleton) s hs1

private theorem meromorphic_LFunction {n : ℕ} [NeZero n] (ψ : DirichletCharacter ℂ n) :
    Meromorphic (DirichletCharacter.LFunction ψ) := by
  intro s
  by_cases hs : ψ ≠ 1 ∨ s ≠ 1
  · exact (analyticAt_LFunction_of_ne_one_or_ne_one ψ hs).meromorphicAt
  push Not at hs
  rcases hs with ⟨rfl, rfl⟩
  have hprod : Differentiable ℂ
      (fun z : ℂ ↦ ∏ p ∈ n.primeFactors, (1 - (p : ℂ) ^ (-z))) :=
    Differentiable.fun_finsetProd fun p hp ↦ by
      have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
      fun_prop
  refine ((hprod.analyticAt 1).meromorphicAt.mul (TauCeti.meromorphic_riemannZeta 1)).congr ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 1)
  exact (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz).symm

private theorem analyticOnNhd_LFunction_one_lt_re {n : ℕ} [NeZero n]
    (ψ : DirichletCharacter ℂ n) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) {s | 1 < s.re} := fun s hs ↦
  analyticAt_LFunction_of_ne_one_or_ne_one ψ (.inr fun h ↦ by simp [h] at hs)

private theorem heckeLFunctionC_eq_toMeromorphicNFOn {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ =
      toMeromorphicNFOn
        (have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
          ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
        DirichletCharacter.LFunction (ratDirichletCharacter χ))
        Set.univ := by
  have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
    ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
  rw [heckeLFunctionC_def, lSeries_rayClassCharacter_rat_eq χ]
  exact meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_LFunction (ratDirichletCharacter χ))
    (analyticOnNhd_LFunction_one_lt_re (ratDirichletCharacter χ))
    fun _ hs ↦ DirichletCharacter.LFunction_eq_LSeries _ hs

/-- **Over `ℚ`, the presented Hecke L-function of any ray class character is the meromorphic normal
form of the corresponding Dirichlet L-function.** -/
theorem heckeLFunctionC_eq_LFunction_rat {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ =
      toMeromorphicNFOn
        (@DirichletCharacter.LFunction (Ideal.absNorm 𝔪.finitePart)
          ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
          (ratDirichletEquiv (Ideal.absNorm 𝔪.finitePart)
            (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
            (χ.induced (dvd_ratModulus_absNorm 𝔪))))
        Set.univ :=
  heckeLFunctionC_eq_toMeromorphicNFOn χ

/-- **Entire continuation over `ℚ`.** For any modulus `𝔪` of `ℚ` and any nontrivial ray class
character `χ ≠ 1`, `heckeLFunctionC χ` is entire. -/
theorem differentiable_heckeLFunctionC_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) : Differentiable ℂ (heckeLFunctionC χ) := by
  have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
    ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
  have hψ : ratDirichletCharacter χ ≠ 1 := ratDirichletCharacter_ne_one hχ
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction (ratDirichletCharacter χ)) :=
    DirichletCharacter.differentiable_LFunction hψ
  rw [heckeLFunctionC_eq_toMeromorphicNFOn χ,
    toMeromorphicNFOn_eq_self.mpr
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hLdiff).meromorphicNFOn]
  exact hLdiff

/-- **Dirichlet series agreement over `ℚ`.** For any modulus `𝔪` of `ℚ` and any ray class
character `χ`, `heckeLFunctionC χ` agrees with its defining `L`-series on `Re s > 1`. -/
theorem heckeLFunctionC_eq_LSeries_rat {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC χ s =
      LSeries (normCoeff ℚ χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
    ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
  rw [heckeLFunctionC_eq_toMeromorphicNFOn χ,
    toMeromorphicNFOn_apply_of_analyticAt (meromorphic_LFunction (ratDirichletCharacter χ))
      (analyticOnNhd_LFunction_one_lt_re (ratDirichletCharacter χ) s hs),
    lSeries_rayClassCharacter_rat_eq χ,
    DirichletCharacter.LFunction_eq_LSeries _ hs]
  rfl

/-- **Unconditional nonvanishing on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ`, any ray
class character `χ`, and any `s` with `1 ≤ s.re` such that `χ ≠ 1 ∨ s ≠ 1`,
`heckeLFunctionC χ s ≠ 0`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : heckeLFunctionC χ s ≠ 0 := by
  have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
    ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
  have hψs : ratDirichletCharacter χ ≠ 1 ∨ s ≠ 1 := ne_one_or_ne_one_of_rayClass h
  rw [heckeLFunctionC_eq_toMeromorphicNFOn χ,
    toMeromorphicNFOn_apply_of_analyticAt (meromorphic_LFunction (ratDirichletCharacter χ))
      (analyticAt_LFunction_of_ne_one_or_ne_one (ratDirichletCharacter χ) hψs)]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hψs hs

/-- **Meromorphic order zero on `Re s ≥ 1` over `ℚ`.** -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat {𝔪 : Modulus ℚ}
    {χ : RayClassCharacter 𝔪} {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 := by
  have : NeZero (Ideal.absNorm 𝔪.finitePart) :=
    ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
  have hmer : Meromorphic (DirichletCharacter.LFunction (ratDirichletCharacter χ)) :=
    meromorphic_LFunction (ratDirichletCharacter χ)
  have hanaψ : AnalyticAt ℂ (DirichletCharacter.LFunction (ratDirichletCharacter χ)) s :=
    analyticAt_LFunction_of_ne_one_or_ne_one (ratDirichletCharacter χ)
      (ne_one_or_ne_one_of_rayClass h)
  have hana : AnalyticAt ℂ (heckeLFunctionC χ) s := by
    rw [heckeLFunctionC_eq_toMeromorphicNFOn χ]
    refine hanaψ.congr ?_
    filter_upwards [hanaψ.eventually_analyticAt] with z hz
    exact (toMeromorphicNFOn_apply_of_analyticAt hmer hz).symm
  exact hana.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re_rat h hs)

end TauCeti.LFunctions
