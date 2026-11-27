/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight.Rat
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive

/-!
# The rational Hecke-to-Dirichlet L-function dictionary

Over `ℚ`, attaching `η.toDirichletCharacter : DirichletCharacter ℂ N`
(`N = Ideal.absNorm 𝔪.finitePart`) to a ray class character `η : RayClassCharacter 𝔪` identifies
their continued `L`-functions, meromorphic orders, divisors, and zero counts:

* On `ℂ`, `heckeLFunctionC η` is the meromorphic normal form of `η.toDirichletCharacter.LFunction`.
  Its punctured germ at every `s : ℂ` is that of `η.toDirichletCharacter.LFunction`; for `η ≠ 1` the
  two functions are equal on the whole plane, while for `η = 1` they agree at every `s ≠ 1` (at the
  pole `s = 1`, `heckeLFunctionC` takes its normal-form value `0` whereas `LFunction` is an
  unnormalized Hurwitz combination). Punctured-germ agreement transports `meromorphicOrderAt`,
  `MeromorphicOn.divisor`, `divisorCount`, and `zeroCount` on arbitrary sets without excluding `1`.
* At `(N)·∞`, the `@[simp]` rewrite `LFunction_toDirichletCharacter_ratDirichletEquiv_symm`
  identifies `((ratDirichletEquiv N _).symm χ).toDirichletCharacter.LFunction` with `χ.LFunction`.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_eventuallyEq_LFunction` and
  `TauCeti.LFunctions.heckeLFunctionC_eq_LFunction`: comparison of `heckeLFunctionC` over
  `ℚ` with `DirichletCharacter.LFunction`.
* `TauCeti.LFunctions.LFunction_toDirichletCharacter_ratDirichletEquiv_symm`,
  `TauCeti.LFunctions.heckeLFunctionC_ratDirichletEquiv_symm_eventuallyEq`, and
  `TauCeti.LFunctions.heckeLFunctionC_ratDirichletEquiv_symm`: identifications with
  `DirichletCharacter.LFunction` at `(N)·∞`.
* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_LFunction`,
  `TauCeti.LFunctions.divisor_heckeLFunctionC_eq_LFunction`,
  `TauCeti.LFunctions.divisorCount_heckeLFunctionC_eq_LFunction`, and
  `TauCeti.LFunctions.zeroCount_heckeLFunctionC_eq_LFunction`: order, divisor, and zero-count
  transport.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 4–5 and 12.
-/

public section
noncomputable section

open DirichletCharacter Filter NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

/-! ### Presented Hecke L-functions over `ℚ` and `DirichletCharacter.LFunction` -/

section HeckeLFunction

variable {𝔪 : Modulus ℚ}

/-- **Over `ℚ`, the presented Hecke L-function of `η` is the meromorphic normal form of
`η.toDirichletCharacter.LFunction`.** -/
theorem heckeLFunctionC_eq_toMeromorphicNFOn_LFunction (η : RayClassCharacter 𝔪) :
    heckeLFunctionC η = toMeromorphicNFOn η.toDirichletCharacter.LFunction univ := by
  rw [heckeLFunctionC_def]
  exact meromorphicContinuation_eq_toMeromorphicNFOn
    η.toDirichletCharacter.meromorphic_LFunction
    (fun _ hs ↦ η.toDirichletCharacter.analyticAt_LFunction
      (.inl (by rintro rfl; simp at hs)))
    fun s hs ↦ (η.toDirichletCharacter.LFunction_eq_LSeries hs).trans
      (η.LSeries_toUnitaryIdealWeight_eq s).symm

/-- **At every complex point `s`, `heckeLFunctionC η` has the same punctured germ as
`η.toDirichletCharacter.LFunction`.** -/
theorem heckeLFunctionC_eventuallyEq_LFunction (η : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC η =ᶠ[𝓝[≠] s] η.toDirichletCharacter.LFunction := by
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction]
  exact η.toDirichletCharacter.meromorphic_LFunction.meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- **Away from the pole at `1` of the trivial character, `heckeLFunctionC η` agrees pointwise with
`η.toDirichletCharacter.LFunction`.** -/
theorem heckeLFunctionC_eq_LFunction (η : RayClassCharacter 𝔪) {s : ℂ} (hs : s ≠ 1 ∨ η ≠ 1) :
    heckeLFunctionC η s = η.toDirichletCharacter.LFunction s := by
  have hs' : s ≠ 1 ∨ η.toDirichletCharacter ≠ 1 :=
    hs.imp_right (mt (RayClassCharacter.toDirichletCharacter_eq_one_iff η).mp)
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction,
    toMeromorphicNFOn_apply_of_analyticAt η.toDirichletCharacter.meromorphic_LFunction
      (η.toDirichletCharacter.analyticAt_LFunction hs')]

/-- On `Re s > 1`, a rational presented Hecke L-function agrees with its defining `LSeries`. -/
theorem heckeLFunctionC_rat_eq_LSeries (η : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC η s =
      LSeries (normCoeff ℚ η.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  rw [heckeLFunctionC_eq_LFunction η (.inl fun h ↦ by simp [h] at hs),
    η.toDirichletCharacter.LFunction_eq_LSeries hs, η.LSeries_toUnitaryIdealWeight_eq]

/-- Away from `s = 1`, the presented Hecke L-function of the trivial character of `𝔪 : Modulus ℚ`
is `riemannZeta s` times the Euler factors at the prime factors of `Ideal.absNorm 𝔪.finitePart`. -/
theorem heckeLFunctionC_one_rat_eq_mul_riemannZeta (𝔪 : Modulus ℚ) {s : ℂ} (hs : s ≠ 1) :
    heckeLFunctionC (1 : RayClassCharacter 𝔪) s =
      (∏ p ∈ (Ideal.absNorm 𝔪.finitePart).primeFactors, (1 - (p : ℂ) ^ (-s))) *
        riemannZeta s := by
  rw [heckeLFunctionC_eq_LFunction 1 (.inl hs), map_one]
  exact LFunctionTrivChar_eq_mul_riemannZeta hs

/-- At `(N)·∞`, the Dirichlet `L`-function attached to `(ratDirichletEquiv N _).symm χ` is
`χ.LFunction`. -/
@[simp]
theorem LFunction_toDirichletCharacter_ratDirichletEquiv_symm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ((ratDirichletEquiv N (NeZero.ne N)).symm χ).toDirichletCharacter.LFunction = χ.LFunction :=
  LFunction_eq_of_changeLevel_eq (absNorm_ratModulus_finitePart N (NeZero.ne N))
    (by rw [RayClassCharacter.changeLevel_toDirichletCharacter_ratModulus,
      MulEquiv.apply_symm_apply])

/-- **At every complex point `s`, `heckeLFunctionC ((ratDirichletEquiv N _).symm χ)` has the same
punctured germ as `χ.LFunction`.** -/
theorem heckeLFunctionC_ratDirichletEquiv_symm_eventuallyEq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    heckeLFunctionC ((ratDirichletEquiv N (NeZero.ne N)).symm χ) =ᶠ[𝓝[≠] s] χ.LFunction := by
  simpa only [LFunction_toDirichletCharacter_ratDirichletEquiv_symm] using
    heckeLFunctionC_eventuallyEq_LFunction ((ratDirichletEquiv N (NeZero.ne N)).symm χ) s

/-- **Away from the pole at `1` of the principal character, `heckeLFunctionC` of
`(ratDirichletEquiv N _).symm χ` agrees pointwise with `χ.LFunction`.** -/
theorem heckeLFunctionC_ratDirichletEquiv_symm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    heckeLFunctionC ((ratDirichletEquiv N (NeZero.ne N)).symm χ) s = χ.LFunction s := by
  have hs' : s ≠ 1 ∨ (ratDirichletEquiv N (NeZero.ne N)).symm χ ≠ 1 :=
    hs.imp_right fun hχ h ↦ hχ (by simpa using congrArg (ratDirichletEquiv N (NeZero.ne N)) h)
  rw [heckeLFunctionC_eq_LFunction _ hs', LFunction_toDirichletCharacter_ratDirichletEquiv_symm]

end HeckeLFunction

/-! ### Meromorphic order, divisor, and zero-count transport -/

section ZeroCounting

variable {𝔪 : Modulus ℚ}

@[simp]
theorem meromorphicOrderAt_heckeLFunctionC_eq_LFunction (η : RayClassCharacter 𝔪) (s : ℂ) :
    meromorphicOrderAt (heckeLFunctionC η) s =
      meromorphicOrderAt η.toDirichletCharacter.LFunction s :=
  meromorphicOrderAt_congr (heckeLFunctionC_eventuallyEq_LFunction η s)

@[simp]
theorem divisor_heckeLFunctionC_eq_LFunction (η : RayClassCharacter 𝔪) (U : Set ℂ) :
    MeromorphicOn.divisor (heckeLFunctionC η) U =
      MeromorphicOn.divisor η.toDirichletCharacter.LFunction U :=
  MeromorphicOn.divisor_congr_nhdsNE fun z _ ↦ heckeLFunctionC_eventuallyEq_LFunction η z

@[simp]
theorem divisorCount_heckeLFunctionC_eq_LFunction (η : RayClassCharacter 𝔪) (U R : Set ℂ) :
    divisorCount (heckeLFunctionC η) U R =
      divisorCount η.toDirichletCharacter.LFunction U R :=
  divisorCount_congr_nhdsNE fun z _ ↦ heckeLFunctionC_eventuallyEq_LFunction η z

@[simp]
theorem zeroCount_heckeLFunctionC_eq_LFunction (η : RayClassCharacter 𝔪) (U R : Set ℂ) :
    zeroCount (heckeLFunctionC η) U R =
      zeroCount η.toDirichletCharacter.LFunction U R :=
  zeroCount_congr_nhdsNE fun z _ ↦ heckeLFunctionC_eventuallyEq_LFunction η z

end ZeroCounting

end TauCeti.LFunctions
