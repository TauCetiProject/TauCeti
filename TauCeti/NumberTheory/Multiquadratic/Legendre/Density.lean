/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Primes with prescribed quadratic residue symbols

Let `d₁, …, dₙ` be integers that are independent in `ℚ^× / ℚ^{×2}`: no nonempty product of them
is a square. For every choice of signs `εᵢ ∈ {±1}`, the rational primes `p` with `(dᵢ/p) = εᵢ` for
all `i` have Dirichlet density `2^{-n}`.

The route is Chebotarev for the multiquadratic field `M = ℚ(√d₁, …, √dₙ)`. Its Galois group is
`(ℤ/2)ⁿ` (`TauCeti.Multiquadratic.galoisGroupEquiv`), so the signs `ε` pick out one automorphism
`σ`, whose conjugacy class is `{σ}`. An odd prime `p ∤ d₁ ⋯ dₙ` is unramified in `M`, and the
arithmetic Frobenius at `p` sends `√dᵢ` to `(dᵢ/p) √dᵢ` (`NumberField.signPattern_frobenius`), so
`p` lies in the Frobenius fibre of `σ` exactly when `(dᵢ/p) = εᵢ` for all `i`
(`NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_signPattern_eq`). The two sets of primes
therefore differ in finitely many primes, and the fibre has density `1 / [M : ℚ] = 2^{-n}`
(`NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet`).

Primes are height-one primes `𝔭` of `𝓞 ℚ`, with rational prime `p = Ideal.absNorm 𝔭`, and the
symbol is written `jacobiSym (dᵢ) p`, which is the Legendre symbol for a prime `p`.

## Main results

* `TauCeti.Multiquadratic.hasDirichletDensity_setOf_jacobiSym_eq`: for square-class independent
  `d₁, …, dₙ` and signs `ε`, the primes with `(dᵢ/p) = εᵢ` for all `i` have Dirichlet density
  `1 / 2 ^ n`.
* `TauCeti.Multiquadratic.infinite_setOf_jacobiSym_eq`: in particular there are infinitely many
  of them.
-/

public section

open NumberField IsDedekindDomain IntermediateField

open scoped NumberField symmDiff

namespace TauCeti.Multiquadratic

variable {ι : Type*}

/-- For a height-one prime `𝔭` of `𝓞 ℚ` not containing `a`, the symbol `(a/p)` equals a sign `e`
exactly when its `ℤ/2` encoding is that of `e`. -/
private theorem jacobiSym_eq_iff (𝔭 : HeightOneSpectrum (𝓞 ℚ)) {a : ℤ}
    (ha : (a : 𝓞 ℚ) ∉ 𝔭.asIdeal) (e : ℤˣ) :
    jacobiSym a (Ideal.absNorm 𝔭.asIdeal) = e ↔
      additiveIntUnitsAddEquiv (Additive.ofMul e) =
        if jacobiSym a (Ideal.absNorm 𝔭.asIdeal) = 1 then 0 else 1 := by
  have : Fact (Ideal.absNorm 𝔭.asIdeal).Prime := ⟨Rat.HeightOneSpectrum.prime_absNorm_asIdeal 𝔭⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hl := legendreSym.eq_one_or_neg_one (Ideal.absNorm 𝔭.asIdeal) (a := a) (by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h ↦ ha ((Rat.HeightOneSpectrum.intCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mpr h))
  rcases Int.units_eq_one_or e with he | he <;> rcases hl with hl | hl <;>
    simp only [he, hl, additiveIntUnitsAddEquiv_apply, toMul_ofMul, Units.val_one,
      Units.val_neg] <;> decide

variable [Finite ι]

/-- **Primes with prescribed quadratic residue symbols.** Let `d₁, …, dₙ` be integers no nonempty
product of which is a square in `ℚ`, and let `ε₁, …, εₙ` be signs. Then the primes `p` with
`(dᵢ/p) = εᵢ` for all `i` have Dirichlet density `1 / 2 ^ n`. -/
theorem hasDirichletDensity_setOf_jacobiSym_eq (d : ι → ℤ)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ))) (ε : ι → ℤˣ) :
    NumberField.Set.HasDirichletDensity
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | ∀ i, jacobiSym (d i) (Ideal.absNorm 𝔭.asIdeal) = ε i}
      (1 / 2 ^ Nat.card ι) := by
  classical
  let := Fintype.ofFinite ι
  -- The multiquadratic field `M = ℚ(√d₁, …, √dₙ)` inside an algebraic closure of `ℚ`.
  have hex (i : ι) : ∃ r : AlgebraicClosure ℚ, r ^ 2 = algebraMap ℤ _ (d i) :=
    IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose root hroot using hex
  have hroot' : ∀ i, root i ^ 2 = algebraMap ℚ _ (d i) := fun i ↦ by rw [hroot i]; simp
  have : FiniteDimensional ℚ (adjoin ℚ (Set.range root)) := finiteDimensional_adjoin_range hroot'
  have : NumberField (adjoin ℚ (Set.range root)) := ⟨⟩
  have : IsGalois ℚ (adjoin ℚ (Set.range root)) := isGalois hroot'
  -- The automorphism `σ` with sign pattern `ε`.
  let s : ι → ZMod 2 := fun i ↦ additiveIntUnitsAddEquiv (Additive.ofMul (ε i))
  let σ := (galoisGroupEquiv hroot' hindep).symm (Multiplicative.ofAdd s)
  have hσ : signPattern root σ = s := by
    have := (galoisGroupEquiv hroot' hindep).apply_symm_apply (Multiplicative.ofAdd s)
    rw [galoisGroupEquiv_apply] at this
    exact Multiplicative.ofAdd.injective this
  -- The class of `σ` is `{σ}`, and `Gal(M/ℚ)` has `2 ^ n` elements.
  rw [NumberField.Chebotarev.hasDirichletDensity_iff_of_finite_symmDiff_frobeniusPrimeSet
    (C := ConjClasses.mk σ), Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center
    (Submonoid.mem_center_iff.mpr fun c ↦ aut_commute hroot' c σ),
    card_aut_adjoin_range hroot' hindep]
  · simp
  -- The two sets agree away from the primes dividing `2 d₁ ⋯ dₙ`.
  have hd0 (i : ι) : d i ≠ 0 := by
    intro h
    exact hindep {i} (Finset.singleton_nonempty i) (by simp [h])
  have hN : Ideal.span {(((2 * ∏ i, d i : ℤ)) : 𝓞 ℚ)} ≠ ⊥ := by
    simp [Finset.prod_eq_zero_iff, hd0]
  refine (Ideal.finite_factors hN).subset fun 𝔭 h𝔭 ↦ ?_
  by_contra hN𝔭
  simp only [Set.mem_ofPred_eq, Ideal.dvd_span_singleton] at hN𝔭
  have h2 : ((2 : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal := fun h ↦ hN𝔭 (by
    rw [Int.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hd (i : ι) : ((d i : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal := fun h ↦ hN𝔭 (by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j ↦ ((d j : ℤ) : 𝓞 ℚ)) (Finset.mem_univ i)
    rw [Int.cast_mul, Int.cast_prod, hc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h))
  have hiff : 𝔭 ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ (adjoin ℚ (Set.range root))
      (ConjClasses.mk σ) ↔ ∀ i, jacobiSym (d i) (Ideal.absNorm 𝔭.asIdeal) = ε i :=
    (NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_signPattern_eq hroot σ h2 hd).trans
      (forall_congr' fun i ↦ by rw [hσ]; exact (jacobiSym_eq_iff 𝔭 (hd i) (ε i)).symm)
  rw [Set.mem_symmDiff] at h𝔭
  rcases h𝔭 with ⟨hmem, hnot⟩ | ⟨hmem, hnot⟩
  · exact hnot (hiff.mpr hmem)
  · exact hnot (hiff.mp hmem)

/-- **Infinitely many primes with prescribed quadratic residue symbols.** For square-class
independent integers `d₁, …, dₙ` and any signs `εᵢ`, infinitely many primes `p` have
`(dᵢ/p) = εᵢ` for all `i`. -/
theorem infinite_setOf_jacobiSym_eq (d : ι → ℤ)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ))) (ε : ι → ℤˣ) :
    {𝔭 : HeightOneSpectrum (𝓞 ℚ) |
      ∀ i, jacobiSym (d i) (Ideal.absNorm 𝔭.asIdeal) = ε i}.Infinite :=
  (hasDirichletDensity_setOf_jacobiSym_eq d hindep ε).infinite (by positivity)

end TauCeti.Multiquadratic
