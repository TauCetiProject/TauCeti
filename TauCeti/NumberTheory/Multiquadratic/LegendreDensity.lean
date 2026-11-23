/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
import TauCeti.NumberTheory.Multiquadratic.Frobenius
import TauCeti.NumberTheory.NumberField.ArtinSymbol
import TauCeti.NumberTheory.NumberField.Frobenius.Tower
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Primes with prescribed quadratic residue symbols

Let `d₁, …, dₙ` be integers that are independent in `ℚ^× / ℚ^{×2}`: no nonempty product of them
is a square. For every choice of signs `εᵢ ∈ {±1}`, the rational primes `p` with `(dᵢ/p) = εᵢ` for
all `i` have Dirichlet density `2^{-n}`.

The route is Chebotarev for the multiquadratic field `M = ℚ(√d₁, …, √dₙ)`. Its Galois group is
`(ℤ/2)ⁿ` (`TauCeti.Multiquadratic.galoisGroupEquiv`), so the signs `ε` pick out one automorphism
`σ`, whose conjugacy class is `{σ}`. For an odd prime `p ∤ d₁ ⋯ dₙ`, unramified in `M`, the
arithmetic Frobenius at `p` sends `√dᵢ` to `(dᵢ/p) √dᵢ` (`NumberField.signPattern_frobenius`), so
`p` lies in the Frobenius fibre of `σ` exactly when `(dᵢ/p) = εᵢ` for all `i`. The two sets of
primes therefore differ in finitely many primes, and the fibre has density `1 / [M : ℚ] = 2^{-n}`
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

/-- For a nonzero integer `a` and a height-one prime `𝔭` of `𝓞 ℚ` with `a ∉ 𝔭`, the rational
prime of `𝔭` does not divide `a`. -/
private theorem not_dvd_of_intCast_notMem (𝔭 : HeightOneSpectrum (𝓞 ℚ)) {a : ℤ}
    (ha : (a : 𝓞 ℚ) ∉ 𝔭.asIdeal) : ¬ ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) ∣ a := by
  rintro ⟨c, rfl⟩
  apply ha
  rw [Int.cast_mul]
  refine Ideal.mul_mem_right _ _ ?_
  rw [Int.cast_natCast]
  exact (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mpr dvd_rfl

/-- For a height-one prime `𝔭` of `𝓞 ℚ` not containing `a`, the symbol `(a/p)` equals a sign `e`
exactly when both have the same encoding in `ℤ/2`. -/
private theorem jacobiSym_eq_iff (𝔭 : HeightOneSpectrum (𝓞 ℚ)) {a : ℤ}
    (ha : (a : 𝓞 ℚ) ∉ 𝔭.asIdeal) (e : ℤˣ) :
    jacobiSym a (Ideal.absNorm 𝔭.asIdeal) = e ↔
      (if (e : ℤ) = 1 then (0 : ZMod 2) else 1) =
        if jacobiSym a (Ideal.absNorm 𝔭.asIdeal) = 1 then 0 else 1 := by
  have : Fact (Ideal.absNorm 𝔭.asIdeal).Prime :=
    ⟨by simpa using Rat.HeightOneSpectrum.prime_natGenerator 𝔭⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hl := legendreSym.eq_one_or_neg_one (Ideal.absNorm 𝔭.asIdeal) (a := a) (by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact not_dvd_of_intCast_notMem 𝔭 ha)
  rcases Int.units_eq_one_or e with he | he <;> rcases hl with hl | hl <;>
    simp only [he, hl, Units.val_one, Units.val_neg] <;> decide

section Fibre

variable {d : ι → ℤ} {L : Type*} [Field L] [CharZero L] {root : ι → L}

/-- Away from `2 d₁ ⋯ dₙ` and the ramified primes, a prime of `𝓞 ℚ` lies in the Frobenius fibre
of the automorphism `σ` of `M = ℚ(√d₁, …, √dₙ)` exactly when its Legendre symbols at the `dᵢ`
give the sign pattern of `σ`. -/
private theorem mem_frobeniusPrimeSet_iff [NumberField (adjoin ℚ (Set.range root))]
    [IsGalois ℚ (adjoin ℚ (Set.range root))]
    (hroot : ∀ i, root i ^ 2 = algebraMap ℤ L (d i))
    (σ : adjoin ℚ (Set.range root) ≃ₐ[ℚ] adjoin ℚ (Set.range root))
    {𝔭 : HeightOneSpectrum (𝓞 ℚ)} (h2 : ((2 : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal)
    (hd : ∀ i, ((d i : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal)
    (hur : ∀ (Q : Ideal (𝓞 (adjoin ℚ (Set.range root)))) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 ℚ) Q) :
    𝔭 ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ (adjoin ℚ (Set.range root))
        (ConjClasses.mk σ) ↔
      ∀ i, signPattern root σ i =
        if jacobiSym (d i) (Ideal.absNorm 𝔭.asIdeal) = 1 then 0 else 1 := by
  set p := Ideal.absNorm 𝔭.asIdeal
  have : Fact p.Prime := ⟨by simpa [p] using Rat.HeightOneSpectrum.prime_natGenerator 𝔭⟩
  have hodd : p ≠ 2 := fun h ↦ not_dvd_of_intCast_notMem 𝔭 h2 (by simp [p, h])
  have hcop (i : ι) : ¬ (p : ℤ) ∣ d i := not_dvd_of_intCast_notMem 𝔭 (hd i)
  rw [NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq hur]
  -- A Frobenius `τ` at a prime `Q` over `𝔭` represents the Artin symbol.
  obtain ⟨Q, hQp, hQo⟩ :=
    (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (adjoin ℚ (Set.range root)))))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt ℚ Q hQ
  rw [artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q τ hτ, ConjClasses.mk_eq_mk_iff_isConj]
  have : 𝔭.asIdeal.LiesOver 𝔭.asIdeal := ⟨by simp [Ideal.under_def]⟩
  have : 𝔭.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Rat.HeightOneSpectrum.liesOver_span_absNorm 𝔭 𝔭.asIdeal
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q 𝔭.asIdeal _
  have hτℤ : IsArithFrobAt ℤ τ Q :=
    NumberField.isArithFrobAt_int_of_absNorm_eq 𝔭.asIdeal rfl Q hτ
  have hsign := NumberField.signPattern_frobenius hroot p hodd hcop Q hτℤ
  -- In the abelian group `Gal(M/ℚ)`, conjugate automorphisms are equal, and an automorphism is
  -- determined by its sign pattern.
  have hroot' : ∀ i, root i ^ 2 = algebraMap ℚ L (d i) := fun i ↦ by rw [hroot i]; simp
  constructor
  · rintro ⟨c, hc⟩ i
    have hτσ : τ = σ := mul_right_cancel ((aut_commute hroot' c τ).symm.trans hc)
    rw [← hτσ, hsign, jacobiSym.legendreSym.to_jacobiSym]
  · intro h
    suffices τ = σ from this ▸ IsConj.refl σ
    refine signHom_injective hroot' ?_
    simp only [signHom_apply]
    congr 1
    funext i
    rw [hsign, h, jacobiSym.legendreSym.to_jacobiSym]

omit [CharZero L] in
/-- The conjugacy class of an automorphism of a multiquadratic field is a singleton. -/
private theorem card_carrier_mk {K : Type*} [Field K] {e : ι → K} [Algebra K L] {r : ι → L}
    (hr : ∀ i, r i ^ 2 = algebraMap K L (e i))
    (σ : adjoin K (Set.range r) ≃ₐ[K] adjoin K (Set.range r)) :
    Nat.card (ConjClasses.mk σ).carrier = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨σ, ConjClasses.mem_carrier_mk⟩, fun ⟨τ, hτ⟩ ↦ Subtype.ext ?_⟩
  obtain ⟨c, hc⟩ := ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hτ)
  exact mul_right_cancel ((aut_commute hr c τ).symm.trans hc)

end Fibre

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
  let σ := (galoisGroupEquiv hroot' hindep).symm
    (Multiplicative.ofAdd fun i ↦ if (ε i : ℤ) = 1 then 0 else 1)
  have hσ : signPattern root σ = fun i ↦ if (ε i : ℤ) = 1 then 0 else 1 := by
    have := (galoisGroupEquiv hroot' hindep).apply_symm_apply
      (Multiplicative.ofAdd fun i ↦ if (ε i : ℤ) = 1 then 0 else 1)
    rw [galoisGroupEquiv_apply] at this
    exact Multiplicative.ofAdd.injective this
  -- The class of `σ` is `{σ}`, and `Gal(M/ℚ)` has `2 ^ n` elements.
  rw [NumberField.Chebotarev.hasDirichletDensity_iff_of_finite_symmDiff_frobeniusPrimeSet
    (C := ConjClasses.mk σ), card_carrier_mk hroot' σ, card_aut_adjoin_range hroot' hindep]
  · simp
  -- The two sets agree away from the primes dividing `2 d₁ ⋯ dₙ` and the ramified primes.
  have hd0 (i : ι) : d i ≠ 0 := by
    intro h
    exact hindep {i} (Finset.singleton_nonempty i) (by simp [h])
  have hN : Ideal.span {(((2 * ∏ i, d i : ℤ)) : 𝓞 ℚ)} ≠ ⊥ := by
    simp [Finset.prod_eq_zero_iff, hd0]
  refine ((Ideal.finite_factors hN).union
    (NumberField.Chebotarev.ramifiedPrimes ℚ (adjoin ℚ (Set.range root))).finite_toSet).subset ?_
  intro 𝔭 h𝔭
  by_contra hout
  simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or,
    NumberField.Chebotarev.mem_ramifiedPrimes_iff, not_not, Ideal.dvd_span_singleton] at hout
  obtain ⟨hN𝔭, hur⟩ := hout
  have h2 : ((2 : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal := fun h ↦ hN𝔭 (by
    rw [Int.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hd (i : ι) : ((d i : ℤ) : 𝓞 ℚ) ∉ 𝔭.asIdeal := fun h ↦ hN𝔭 (by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j ↦ ((d j : ℤ) : 𝓞 ℚ)) (Finset.mem_univ i)
    rw [Int.cast_mul, Int.cast_prod, hc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h))
  have hiff : 𝔭 ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ (adjoin ℚ (Set.range root))
      (ConjClasses.mk σ) ↔ ∀ i, jacobiSym (d i) (Ideal.absNorm 𝔭.asIdeal) = ε i :=
    (mem_frobeniusPrimeSet_iff hroot σ h2 hd hur).trans
      (forall_congr' fun i ↦ by rw [hσ]; exact (jacobiSym_eq_iff 𝔭 (hd i) (ε i)).symm)
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
