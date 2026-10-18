/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Minuscule
public import TauCeti.Algebra.Lie.HighestWeight.RacahSpeiser

/-!
# The minuscule Pieri rule

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, `H` a Cartan subalgebra, and `b` a base of its root system.
The Racah–Speiser formula is proved in
`TauCeti/Algebra/Lie/HighestWeight/RacahSpeiser.lean`.

When `μ` is **minuscule** (`TauCeti.IsMinuscule b μ`), no folding occurs: every `w ≠ 1` term in the
Racah–Speiser sum vanishes
(`TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`).
Indeed, if `τ = ν - w ⬝ λ` is a weight of `L(μ)`, then `τ` pairs with every simple coroot `αᵢ^∨`
to an integer `z ≤ 1` (`TauCeti.IsMinuscule.le_one_of_apply_coroot_eq_intCast`). Because `ν` is
dominant integral, `ν + ρ` pairs with `αᵢ^∨` in `1 + ℕ`, so the difference
`w(λ + ρ) = w ⬝ λ + ρ = (ν + ρ) - τ` still takes a natural value on every simple coroot. Since
`λ + ρ` is strictly dominant integral,
`TauCeti.eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one`
forces `w = 1`.

Only the `w = 1` term therefore survives, and since every weight of a minuscule module has
multiplicity one (`TauCeti.formalCharacter_coeff_irreducibleQuotient_eq_ite_of_isMinuscule`), the
tensor multiplicity is `1` when `ν - λ` is a weight of `L(μ)` and `0` otherwise
(`TauCeti.minuscule_pieri`). Dominance of `ν` is essential: for `sl₂` with `λ = 0` and `μ = ω` the
fundamental weight, `ν = -ω` satisfies `-ω - 0 = -ω` being a weight of `L(ω)`, whereas
`L(0) ⊗ L(ω) ≅ L(ω)` contains no copy of `L(-ω)`.

## Main results

* `TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`:
  for dominant integral `λ`, `ν` and minuscule `μ`, `ν - w ⬝ λ` is not a weight of `L(μ)` when
  `w ≠ 1`, so every `w ≠ 1` term of the Racah–Speiser sum vanishes.
* `TauCeti.tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule`: for dominant integral
  `λ`, `ν` and minuscule `μ`, the tensor multiplicity `c^ν_{λμ}` is the weight multiplicity of
  `ν - λ` in `L(μ)`.
* `TauCeti.minuscule_pieri`: **the minuscule Pieri rule**, together with
  `TauCeti.tensorMultiplicity_le_one_of_isMinuscule`,
  `TauCeti.tensorMultiplicity_eq_one_iff_of_isMinuscule`, and
  `TauCeti.tensorMultiplicity_eq_zero_iff_of_isMinuscule`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VIII, §9, Exercise 2 (the Brauer–Klimyk formula
  and its specialization to minuscule weights).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24,
  Exercise 9.
-/

public section

namespace TauCeti

open LieAlgebra _root_.LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

section MinusculePieri

variable (b : (IsKilling.rootSystem H).Base)

/-- **No nontrivial Weyl-group element contributes to the Racah–Speiser sum when `mu` is
minuscule**: for dominant integral `lam` and `nu`, a minuscule weight `mu`, and `w ≠ 1`, the weight
`nu - w ⬝ lam` is not a weight of `L(mu)`.

If `τ = nu - w ⬝ lam` were a weight of `L(mu)`, it would pair with every simple coroot `αᵢ^∨` to an
integer `z ≤ 1` (`TauCeti.IsMinuscule.le_one_of_apply_coroot_eq_intCast`). Since `nu` is dominant
integral, `nu + ρ` pairs with `αᵢ^∨` to `n + 1` with `n : ℕ`, so
`w • (lam + ρ) = w ⬝ lam + ρ = (nu + ρ) - τ` takes the natural value `n + 1 - z ≥ 0` on every
simple coroot. Because `lam + ρ` is strictly dominant integral,
`TauCeti.eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one` then forces
`w = 1`. -/
theorem genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu)
    (hnu : IsDominantIntegral b nu) {w : (IsKilling.rootSystem H).weylGroup} (hw : w ≠ 1) :
    genWeightSpace (irreducibleQuotient b mu)
      ((nu - dotAction (IsKilling.rootSystem H) b w lam : Dual K H) : H → K) = ⊥ := by
  by_contra htau
  set ρ := weylVector (IsKilling.rootSystem H) b
  -- `lam + ρ` is strictly dominant integral
  have hlamρ : ∀ i ∈ b.support, ∃ n : ℕ,
      (IsKilling.rootSystem H).coroot' i (lam + ρ) = (n : K) + 1 := by
    intro i hi
    obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hlam i hi
    exact ⟨n, by rw [coroot'_add_weylVector (IsKilling.rootSystem H) b hi,
      rootSystem_coroot'_apply, hn]⟩
  -- `w • (lam + ρ) = (nu + ρ) - (nu - w ⬝ lam)` is dominant integral
  have hwlamρ : ∀ i ∈ b.support, ∃ n : ℕ,
      (IsKilling.rootSystem H).coroot' i (w • (lam + ρ)) = (n : K) := by
    intro i hi
    obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hnu i hi
    obtain ⟨z, ⟨-, hzle⟩, hz⟩ := hmu.exists_int_abs_le_one_apply_coroot htau i
    have hrel : w • (lam + ρ) =
        (nu + ρ) - (nu - dotAction (IsKilling.rootSystem H) b w lam) := by
      rw [← dotAction_add_weylVector]
      abel
    have hval : (IsKilling.rootSystem H).coroot' i (w • (lam + ρ)) =
        (((n : ℤ) + 1 - z : ℤ) : K) := by
      rw [hrel, map_sub, coroot'_add_weylVector (IsKilling.rootSystem H) b hi,
        rootSystem_coroot'_apply, rootSystem_coroot'_apply, hn, hz]
      push_cast
      ring
    refine ⟨((n : ℤ) + 1 - z).toNat, ?_⟩
    rw [hval, ← Int.cast_natCast (R := K), Int.toNat_of_nonneg (by omega)]
  exact hw (eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one
    hlamρ hwlamρ)

/-- **For a minuscule weight `mu`, the tensor multiplicity `c^nu_{lam mu}` at dominant integral
`lam` and `nu` is the weight multiplicity of `nu - lam` in `L(mu)`.** All `w ≠ 1` terms in the
Racah–Speiser formula vanish by
`TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`,
leaving only the `w = 1` term. -/
theorem tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
    (tensorMultiplicity b lam mu nu : ℤ) =
      (formalCharacter K H (irreducibleQuotient b mu)).coeff (nu - lam) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
  have _ : Finite (IsKilling.rootSystem H).weylGroup :=
    RootPairing.finite_weylGroup (IsKilling.rootSystem H)
  let _ : Fintype (IsKilling.rootSystem H).weylGroup :=
    Fintype.ofFinite (IsKilling.rootSystem H).weylGroup
  rw [tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff
    b hlam hmu.isDominantIntegral hnu, Finset.sum_eq_single 1]
  · simp
  · intro w _ hw
    rw [formalCharacter_coeff_eq_zero_iff.mpr
      (genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one
        b hlam hmu hnu hw), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ 1) h

attribute [local instance] Classical.propDecidable

/-- **The minuscule Pieri rule**: for dominant integral `lam`, minuscule `mu`, and dominant integral
`nu`, the tensor multiplicity of `L(nu)` in `L(lam) ⊗ L(mu)` is `1` when `nu - lam` is a weight of
`L(mu)` and `0` otherwise.

In particular `L(lam) ⊗ L(mu)` is multiplicity-free, decomposing into the direct sum of those
`L(lam + τ)` for which `τ` is a weight of `L(mu)` and `lam + τ` is dominant integral. -/
theorem minuscule_pieri {lam mu : Dual K H} (hlam : IsDominantIntegral b lam)
    (hmu : IsMinuscule b mu) (nu : Dual K H) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu =
      if genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) ≠ ⊥ then 1 else 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
  have h := tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule b hlam hmu hnu
  rw [formalCharacter_coeff_irreducibleQuotient_eq_ite_of_isMinuscule hmu (nu - lam),
    ← genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
      (isHighestWeightVector_irreducibleQuotientGenerator b mu)
      (lieSpan_irreducibleQuotientGenerator_eq_top b mu)
      (fun _ ↦ hmu.exists_weylGroup_smul_eq) (nu - lam)] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- **A tensor product with a minuscule module is multiplicity-free**: for dominant integral `lam`
and minuscule `mu`, every irreducible `L(nu)` occurs with multiplicity at most `1` in
`L(lam) ⊗ L(mu)`. -/
theorem tensorMultiplicity_le_one_of_isMinuscule {lam mu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (nu : Dual K H) :
    tensorMultiplicity b lam mu nu ≤ 1 := by
  by_cases hnu : IsDominantIntegral b nu
  · rw [minuscule_pieri b hlam hmu nu hnu]
    split_ifs <;> omega
  · have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
    rw [tensorMultiplicity_def,
      isotypicMultiplicity_irreducibleQuotient_eq_zero_of_not_isDominantIntegral hnu]
    omega

/-- For dominant integral `lam` and `nu` and minuscule `mu`, `L(nu)` occurs in `L(lam) ⊗ L(mu)`
with multiplicity `1` exactly when `nu - lam` is a weight of `L(mu)`. -/
theorem tensorMultiplicity_eq_one_iff_of_isMinuscule {lam mu nu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu = 1 ↔
      genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) ≠ ⊥ := by
  rw [minuscule_pieri b hlam hmu nu hnu]
  split_ifs with h <;> simp [h]

/-- For dominant integral `lam` and `nu` and minuscule `mu`, `L(nu)` does not occur in
`L(lam) ⊗ L(mu)` exactly when `nu - lam` is not a weight of `L(mu)`. -/
theorem tensorMultiplicity_eq_zero_iff_of_isMinuscule {lam mu nu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu = 0 ↔
      genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) = ⊥ := by
  rw [minuscule_pieri b hlam hmu nu hnu]
  by_cases h : genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) = ⊥ <;> simp [h]

end MinusculePieri

end TauCeti
