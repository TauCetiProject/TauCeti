/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits
public import TauCeti.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Euler coefficients and the ideal character of a character of the finite ideles

Let `R` be a Dedekind domain with fraction field `K` and `ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ` a character of the
finite ideles. Given a unit `ϖ_v` of every completion `K_v`, typically a uniformizer, the *Euler
coefficient* of `ψ` at a place `v` is the value `ψ(ι_v(ϖ_v))` of `ψ` at the finite idele with
component `ϖ_v` at `v` and `1` elsewhere (`MonoidHom.heckeCoeff`). Where `ψ` is trivial on the local
units it depends only on the valuation of `ϖ_v`.

Away from a set `S` of places these values assemble into the *ideal character* of `ψ`
(`MonoidHom.heckeIdealCharacter`): the completely multiplicative function on the integral ideals
that sends an ideal `𝔞` prime to `S` to `ψ(ϖ ^ 𝔞)`, with `ϖ ^ 𝔞 = ∏_v ϖ_v ^ ord_v(𝔞)` the finite
idele `IsDedekindDomain.FiniteAdeleRing.uniformizerPow`, and every other ideal to `0`. At a prime
`v` it takes the Euler coefficient at `v` if `v ∉ S` and `0` otherwise, so its Dirichlet series is
the Euler product of the Euler coefficients outside `S`. This is how Tate's integral at the finite
places of a number field produces partial `L`-functions.

## Main definitions

* `MonoidHom.heckeCoeff`: the Euler coefficient `ψ(ι_v(ϖ_v))` of a character of the finite ideles.
* `MonoidHom.heckeIdealCharacter`: the completely multiplicative function `𝔞 ↦ ψ(ϖ ^ 𝔞)` on the
  ideals prime to `S`, extended by zero.

## Main results

* `MonoidHom.heckeCoeff_eq_of_valued_eq`: where `ψ` is trivial on the local units, the Euler
  coefficient does not depend on the choice of the uniformizer.
* `MonoidHom.heckeIdealCharacter_apply_asIdeal`: at a prime `v` the ideal character is the Euler
  coefficient if `v ∉ S` and `0` if `v ∈ S`.
* `MonoidHom.norm_heckeIdealCharacter_le_one`: if the Euler coefficients outside `S` have modulus
  at most one, so do all values of the ideal character.

## Provenance

The ideal character corresponds to `New.IsHeckeOfType.exists_monoidHom_asIdeal_eq_heckeCoeff` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), file
`src/Lib/ClassField/HeckeL/ContinuationAtOne.lean`; here it is a definition for a character of the
finite ideles of any Dedekind domain.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors

namespace MonoidHom

section IdealCharacter

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The **Euler coefficient** at a place `v` of a character `ψ` of the finite ideles, for a choice
`ϖ` of units of the completions: the value `ψ(ι_v(ϖ_v))` of `ψ` at the finite idele with component
`ϖ_v` at `v` and `1` elsewhere. When `ϖ_v` is a uniformizer and `ψ` is trivial on the local units at
`v`, it does not depend on the choice of `ϖ_v` (`MonoidHom.heckeCoeff_eq_of_valued_eq`). -/
def heckeCoeff (ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ) (ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (v : HeightOneSpectrum R) : ℂ :=
  ψ (unitsOfAdicCompletion K v (ϖ v))

variable {ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ} {ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ}
  {S : Set (HeightOneSpectrum R)}

/-- The defining formula of `MonoidHom.heckeCoeff`. -/
theorem heckeCoeff_def (v : HeightOneSpectrum R) :
    ψ.heckeCoeff ϖ v = ψ (unitsOfAdicCompletion K v (ϖ v)) :=
  (rfl)

/-- **The Euler coefficient does not depend on the uniformizer** at a place `v` where `ψ` is
trivial on the local units: `ψ.heckeCoeff ϖ v = ψ(ι_v(π))` for every `π ∈ K_vˣ` with the valuation
of `ϖ_v`, for instance for every uniformizer `π` if `ϖ_v` is one. -/
theorem heckeCoeff_eq_of_valued_eq {v : HeightOneSpectrum R}
    (hψ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ψ (unitsOfAdicCompletion K v u) = 1)
    {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = Valued.v (ϖ v : v.adicCompletion K)) :
    ψ.heckeCoeff ϖ v = ψ (unitsOfAdicCompletion K v π) := by
  -- `π = ϖ_v · (ϖ_v⁻¹ π)`, and `ϖ_v⁻¹ π` is a local unit
  rw [heckeCoeff_def, ← mul_inv_cancel_left (ϖ v) π, map_mul, map_mul, hψ ((ϖ v)⁻¹ * π), mul_one]
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπ,
    inv_mul_cancel₀ (Valued.v.ne_zero_iff.mpr (ϖ v).ne_zero)]

open scoped Classical in
/-- The **ideal character** of a character `ψ` of the finite ideles away from a set `S` of places,
for a choice `ϖ` of units of the completions: the completely multiplicative function on the
integral ideals sending an ideal `𝔞` prime to `S` to `ψ(ϖ ^ 𝔞)`, where
`ϖ ^ 𝔞 = ∏_v ϖ_v ^ ord_v(𝔞)` (`IsDedekindDomain.FiniteAdeleRing.uniformizerPow`), and every other
ideal to `0`. At a prime `v` it is the Euler coefficient `ψ.heckeCoeff ϖ v` if `v ∉ S` and `0` if
`v ∈ S` (`MonoidHom.heckeIdealCharacter_apply_asIdeal`). -/
def heckeIdealCharacter (ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ) (S : Set (HeightOneSpectrum R)) :
    Ideal R →*₀ ℂ where
  toFun I := if h : I.IsPrimeTo S then
      (ψ (uniformizerPow ϖ (FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.ne_bot⟩)) :
        ℂ)
    else 0
  map_zero' := dite_eq_right Ideal.not_isPrimeTo_bot
  map_one' := by
    rw [dite_eq_left (Ideal.one_eq_top (R := R) ▸ Ideal.isPrimeTo_top)]
    -- the unit of `(Ideal R)⁰` is the unit ideal
    have h1 : (⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ : (Ideal R)⁰) = 1 := rfl
    simp only [h1, map_one, Units.val_one]
  map_mul' I J := by
    by_cases h : (I * J).IsPrimeTo S
    · obtain ⟨hI, hJ⟩ := Ideal.isPrimeTo_mul_iff.mp h
      rw [dite_eq_left h, dite_eq_left hI, dite_eq_left hJ, ← Units.val_mul, ← map_mul,
        ← map_mul, ← map_mul]
      -- products in `(Ideal R)⁰` are computed on the underlying ideals
      rfl
    · rcases not_and_or.mp (fun hc ↦ h (Ideal.isPrimeTo_mul_iff.mpr hc)) with h' | h' <;>
        simp [h, h']

/-- On an ideal `𝔞` prime to `S`, the ideal character is `ψ(ϖ ^ 𝔞)`. -/
@[simp]
theorem heckeIdealCharacter_apply_of_isPrimeTo {I : Ideal R} (hI : I.IsPrimeTo S) :
    ψ.heckeIdealCharacter ϖ S I =
      ψ (uniformizerPow ϖ
        (FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hI.ne_bot⟩)) :=
  dite_eq_left hI

/-- On an ideal not prime to `S`, the ideal character vanishes. -/
@[simp]
theorem heckeIdealCharacter_apply_of_not_isPrimeTo {I : Ideal R} (hI : ¬ I.IsPrimeTo S) :
    ψ.heckeIdealCharacter ϖ S I = 0 :=
  dite_eq_right hI

/-- **The ideal character at a prime** `v` is the Euler coefficient `ψ.heckeCoeff ϖ v` if `v ∉ S`
and `0` if `v ∈ S`. -/
@[simp]
theorem heckeIdealCharacter_apply_asIdeal (v : HeightOneSpectrum R) :
    ψ.heckeIdealCharacter ϖ S v.asIdeal = Sᶜ.indicator (ψ.heckeCoeff ϖ) v := by
  by_cases hv : v ∈ S
  · rw [heckeIdealCharacter_apply_of_not_isPrimeTo (Ideal.isPrimeTo_asIdeal_iff.not.mpr
      (not_not.mpr hv)), Set.indicator_of_notMem (not_not.mpr hv)]
  · rw [heckeIdealCharacter_apply_of_isPrimeTo (Ideal.isPrimeTo_asIdeal_iff.mpr hv),
      Set.indicator_of_mem (Set.mem_compl hv), heckeCoeff_def, ← uniformizerPow_unitOfPrime]
    congr 3
    exact Units.ext (by rw [FractionalIdeal.coe_mk0, HeightOneSpectrum.coe_unitOfPrime])

/-- If the Euler coefficients outside `S` have modulus at most one, so do all values of the ideal
character. -/
theorem norm_heckeIdealCharacter_le_one (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (I : Ideal R) :
    ‖ψ.heckeIdealCharacter ϖ S I‖ ≤ 1 := by
  by_cases hI : I.IsPrimeTo S
  · refine hI.induction_on (by rw [← Ideal.one_eq_top, map_one, norm_one]) fun v J hv _ hJ ↦ ?_
    rw [map_mul, norm_mul, heckeIdealCharacter_apply_asIdeal,
      Set.indicator_of_mem (Set.mem_compl hv)]
    simpa using mul_le_mul (hψ v hv) hJ (norm_nonneg _) zero_le_one
  · rw [heckeIdealCharacter_apply_of_not_isPrimeTo hI, norm_zero]
    exact zero_le_one

end IdealCharacter

end MonoidHom
