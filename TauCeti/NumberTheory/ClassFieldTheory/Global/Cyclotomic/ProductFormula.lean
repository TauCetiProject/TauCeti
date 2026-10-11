/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.ArtinNorm
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ProductFormula
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The product formula for the cyclotomic characters of local Artin symbols

Let `K` be a number field, `p` a prime and `x ∈ Kˣ`. At every place `v` of `K` the local Artin
symbol `Art_v(x)` of the image of `x` in the completion `K_v` acts on the roots of unity of
`p`-power order through the `p`-adic cyclotomic character
`χ_p = TauCeti.abelianizedLocalCyclotomicCharacter p K_v`. This file proves the product formula

```text
∏_v χ_p(Art_v(x)) = 1,
```

the product running over the finite and the infinite places
(`finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one`). Reading each `Art_v(x)`
through its action on the roots of unity of `p`-power order, which is what `χ_p` records, this is
the reciprocity law `∏_v Art_v(x) = 1` for the cyclotomic extensions `K(μ_{pⁿ})/K`, and so, as `p`
varies, for every `K(μ_m)/K`. That reciprocity law is the input from which the sum of the local
invariants of a Brauer class of `K` split by a cyclic cyclotomic extension is shown to vanish.

The local factors are explicit over `ℚ`. At a prime `ℓ ≠ p` the Artin symbol of `a ∈ ℚˣ` has
cyclotomic character `ℓ ^ v_ℓ(a)` (`abelianizedLocalCyclotomicCharacter_artinMap`, the residue
field of `ℚ_ℓ` having `ℓ` elements), at `p` it is `u⁻¹` for `a = pᵏ u` with `u ∈ ℤ_pˣ`
(`abelianizedLocalCyclotomicCharacter_artinMap_padic`), and at the real place it is the sign of
`a` (`abelianizedLocalCyclotomicCharacter_infiniteArtinAt_eq_neg_one_of_neg`). The finite
places of `ℚ` are read in `ℚ_ℓ` through `Padic.adicCompletionEquiv` and the naturality of the
cyclotomic character of Artin symbols (`abelianizedLocalCyclotomicCharacter_artinMap_congr`).
Modulo `pⁿ` the local factors are exactly the explicit cyclotomic symbols `cyclotomicSymbol (pⁿ) ℓ`
and `realCyclotomicSymbol (pⁿ)` of `ℚ(μ_{pⁿ})/ℚ`, so the product formula over `ℚ` is, level by
level, the product formula for the explicit symbols (`prod_cyclotomicSymbol_of_subset`). The norm
functoriality of the local Artin symbols
(`finprod_abelianizedLocalCyclotomicCharacter_artinMap_normUnits` and
`prod_abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits`) then carries the formula
for `N_{K/ℚ}(x)` over `ℚ` to the formula for `x` over `K`.

## Main results

* `TauCeti.ClassFieldTheory.finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one`:
  the product over all places of `K` of the `p`-adic cyclotomic characters of the local Artin
  symbols of `x ∈ Kˣ` is `1`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Example 8.2 and Lemma 8.4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField NumberField.InfinitePlace

variable (p : ℕ) [Fact p.Prime]

/-! ### Over `ℚ` -/

section Rat

open Rat.HeightOneSpectrum

local instance (ℓ : Nat.Primes) : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩

/-- The `p`-adic cyclotomic character of the local Artin symbol of `a ∈ ℚˣ` at the prime `ℓ`. -/
private abbrev ratLocalFactor (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚˣ) : ℤ_[p]ˣ :=
  abelianizedLocalCyclotomicCharacter p ℚ_[ℓ] (artinMap ℚ_[ℓ] (Units.map (algebraMap ℚ ℚ_[ℓ]) a))

/-- At a prime `ℓ ≠ p`, the factor is `ℓ ^ v_ℓ(a)`, with `ℓ` a unit of `ℤ_p`. -/
private theorem ratLocalFactor_of_ne {ℓ : ℕ} [Fact ℓ.Prime] {u : ℤ_[p]ˣ}
    (hu : (u : ℤ_[p]) = ℓ) (a : ℚˣ) : ratLocalFactor p ℓ a = u ^ padicValRat ℓ a := by
  rw [ratLocalFactor, abelianizedLocalCyclotomicCharacter_artinMap ℚ_[ℓ] (u := u)
    (by rw [hu, Padic.natCard_residueField]), Padic.toAdd_normalizedValuation_eq_valuation]
  simp

/-- At `p`, the factor of `a = pᵏ u` with `u ∈ ℤ_pˣ` is `u⁻¹`. -/
private theorem ratLocalFactor_self {a : ℚˣ} {k : ℤ} {u : ℤ_[p]ˣ}
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ k * (u : ℤ_[p])) : ratLocalFactor p p a = u⁻¹ :=
  abelianizedLocalCyclotomicCharacter_artinMap_padic p (by simpa using ha)

/-- Modulo `p ^ n`, the factor at `ℓ` is the explicit cyclotomic symbol
`cyclotomicSymbol (p ^ n) ℓ`: `u⁻¹` at `ℓ = p` and `ℓ ^ v_ℓ(a)` at `ℓ ≠ p`. -/
private theorem unitsMap_toZModPow_ratLocalFactor (n ℓ : ℕ) [Fact ℓ.Prime] (a : ℚˣ) :
    Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom (ratLocalFactor p ℓ a) =
      cyclotomicSymbol (p ^ n) ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a) := by
  set x := Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a
  have hx : (x : ℚ_[ℓ]) = (a : ℚ) := by simp [x]
  have hx0 : (x : ℚ_[ℓ]) ≠ 0 := hx ▸ Rat.cast_ne_zero.2 a.ne_zero
  obtain rfl | hℓ := eq_or_ne ℓ p
  · obtain ⟨w, hw⟩ := Padic.exists_eq_zpow_valuation_mul hx0
    have h := unitsMap_cyclotomicSymbol_primePow (ℓ ^ n) ℓ dvd_rfl x _ w hw
    rw [ZMod.unitsMap_self, MonoidHom.id_apply] at h
    rw [h, ratLocalFactor_self ℓ (hx ▸ hw), map_inv]
  · obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := p)
      ((Nat.coprime_primes Fact.out Fact.out).2 hℓ.symm)
    have hcop : ℓ.Coprime (p ^ n) := ((Nat.coprime_primes Fact.out Fact.out).2 hℓ).pow_right n
    rw [ratLocalFactor_of_ne p hu, cyclotomicSymbol_of_coprime _ _ hcop, hx,
      Padic.valuation_ratCast, map_zpow]
    congr 1
    ext
    simp [hu]

/-- The factor at a prime `ℓ ≠ p` dividing neither the numerator nor the denominator of `a` is
trivial. -/
private theorem ratLocalFactor_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ p) {a : ℚˣ}
    (hnum : ¬ ℓ ∣ (a : ℚ).num.natAbs) (hden : ¬ ℓ ∣ (a : ℚ).den) : ratLocalFactor p ℓ a = 1 := by
  obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := p)
    ((Nat.coprime_primes Fact.out Fact.out).2 hℓ.symm)
  rw [ratLocalFactor_of_ne p hu, padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnum,
    padicValNat.eq_zero_of_not_dvd hden]
  simp

/-- The archimedean factor of `a ∈ ℚˣ`, read in the completion `x`, is the sign of `a`. -/
private theorem abelianizedLocalCyclotomicCharacter_infiniteArtinAt_rat (w : InfinitePlace ℚ)
    (a : ℚˣ) (x : w.Completionˣ) (hx : (x : w.Completion) = (a : ℚ)) :
    abelianizedLocalCyclotomicCharacter p w.Completion (infiniteArtinAt w x) =
      if 0 < (a : ℚ) then 1 else -1 := by
  have hw : w.IsReal := Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace
  have he : Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) = (a : ℚ) := by
    rw [hx, map_ratCast]
  split_ifs with ha
  · rw [(infiniteArtinAt_eq_one_iff_of_isReal w hw _).2 (by rw [he]; exact_mod_cast ha), map_one]
  · refine abelianizedLocalCyclotomicCharacter_infiniteArtinAt_eq_neg_one_of_neg w hw p ?_
    rw [he]
    exact_mod_cast lt_of_le_of_ne (not_lt.1 ha) a.ne_zero

/-- The local factor at a finite place of `ℚ` is the one computed in `ℚ_ℓ`. -/
private theorem abelianizedLocalCyclotomicCharacter_artinMap_adicCompletion_rat (ℓ : Nat.Primes)
    (a : ℚˣ) (x : (((primesEquiv (R := 𝓞 ℚ)).symm ℓ).adicCompletion ℚ)ˣ)
    (hx : (x : ((primesEquiv (R := 𝓞 ℚ)).symm ℓ).adicCompletion ℚ) = (a : ℚ)) :
    abelianizedLocalCyclotomicCharacter p (((primesEquiv (R := 𝓞 ℚ)).symm ℓ).adicCompletion ℚ)
        (artinMap _ x) = ratLocalFactor p ℓ a := by
  -- `Padic.adicCompletionEquiv` is stated for the `ℚ`-algebra structure of the completion, not for
  -- the one every field of characteristic zero carries, which instance search finds first.
  let _ : Algebra ℚ (((primesEquiv (R := 𝓞 ℚ)).symm ℓ).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  let e := (Padic.adicCompletionEquiv (𝓞 ℚ) ℓ).symm
  rw [abelianizedLocalCyclotomicCharacter_artinMap_congr _ p e.toAlgEquiv.toRingEquiv
    e.continuous]
  refine congrArg _ (congrArg _ (Units.ext ?_))
  simp [hx]

/-- **The product formula over `ℚ`**, with the finite places indexed by the primes. Only the
primes dividing `p · a` contribute, and modulo every `p ^ n` the factors are the explicit
cyclotomic symbols, so this is the product formula `prod_cyclotomicSymbol_of_subset`. -/
private theorem finprod_ratLocalFactor_mul_eq_one (a : ℚˣ) :
    (∏ᶠ ℓ : Nat.Primes, ratLocalFactor p ℓ a) * (if 0 < (a : ℚ) then 1 else -1) = 1 := by
  set T := (p * (a : ℚ).num.natAbs * (a : ℚ).den).primeFactors
  have hS : p * (a : ℚ).num.natAbs * (a : ℚ).den ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Fact.out : p.Prime).ne_zero
      (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 a.ne_zero))) (a : ℚ).den_ne_zero
  have hT (ℓ : ℕ) (hℓ : ℓ ∈ T) : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  let ι : T ↪ Nat.Primes := ⟨fun ℓ ↦ ⟨ℓ, hT ℓ ℓ.2⟩, fun _ _ h ↦
    Subtype.ext (congrArg (fun q : Nat.Primes ↦ (q : ℕ)) h)⟩
  rw [finprod_eq_prod_of_mulSupport_subset (s := T.attach.map ι) _ fun ℓ hℓ ↦ ?_,
    Finset.prod_map]
  · refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n ↦ ?_)
    have h := prod_cyclotomicSymbol_of_subset (p ^ n) T hT
      (fun q hq ↦ Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hq,
        ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq)).trans
          ((dvd_mul_right _ _).mul_right _), hS⟩) a
      (Nat.primeFactors_mono ((dvd_mul_left _ _).mul_right _) hS)
      (Nat.primeFactors_mono (dvd_mul_left _ _) hS)
    have hsign : Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom
        (if 0 < (a : ℚ) then 1 else -1) =
          realCyclotomicSymbol (p ^ n) (Units.map (algebraMap ℚ ℝ).toMonoidHom a) := by
      split_ifs with ha
      · rw [map_one, realCyclotomicSymbol_of_pos _ _ (by simpa using ha)]
      · rw [RingHom.toMonoidHom_eq_coe, Units.map_neg_one, realCyclotomicSymbol_of_neg _ _ (by
          simpa using lt_of_le_of_ne (not_lt.1 ha) a.ne_zero)]
    have hunits : Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom
        ((∏ ℓ ∈ T.attach, ratLocalFactor p (ι ℓ) a) * (if 0 < (a : ℚ) then 1 else -1)) = 1 := by
      rw [map_mul, map_prod, hsign, mul_comm, ← h]
      exact congrArg _ (Finset.prod_congr rfl fun ℓ _ ↦
        unitsMap_toZModPow_ratLocalFactor p n (ι ℓ) a)
    simpa using congrArg Units.val hunits
  · by_contra h
    have hℓT : ¬ (ℓ : ℕ) ∣ p * (a : ℚ).num.natAbs * (a : ℚ).den := fun hd ↦
      h (Finset.mem_coe.2 (Finset.mem_map.2
        ⟨⟨ℓ, Nat.mem_primeFactors.2 ⟨ℓ.2, hd, hS⟩⟩, Finset.mem_attach _ _, rfl⟩))
    refine hℓ (ratLocalFactor_eq_one p (fun he ↦ hℓT ?_) (fun hd ↦ hℓT ?_) fun hd ↦ hℓT ?_)
    · rw [he]
      exact (dvd_mul_right _ _).mul_right _
    · exact (hd.mul_left _).mul_right _
    · exact hd.mul_left _

end Rat

variable {K : Type} [Field K] [NumberField K]

/-- **The product formula for the cyclotomic characters of local Artin symbols.** For `x ∈ Kˣ`,
the product over all places `v` of the number field `K`, finite and infinite, of the `p`-adic
cyclotomic characters of the local Artin symbols `Art_v(x)` is `1`:

```text
∏_v χ_p(Art_v(x)) = 1.
```

The factors at the finite places are `1` for all but finitely many `v`
(`hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap`). -/
theorem finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one (x : Kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
        (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) x))) *
      ∏ w : InfinitePlace K, abelianizedLocalCyclotomicCharacter p w.Completion
        (infiniteArtinAt w (Units.map (algebraMap K w.Completion) x)) = 1 := by
  rw [← finprod_abelianizedLocalCyclotomicCharacter_artinMap_normUnits (K := ℚ) p x,
    ← prod_abelianizedLocalCyclotomicCharacter_infiniteArtinAt_normUnits (K := ℚ) p x,
    ← finprod_comp_equiv (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm,
    Fintype.prod_unique]
  rw [finprod_congr fun ℓ ↦ abelianizedLocalCyclotomicCharacter_artinMap_adicCompletion_rat p ℓ
      (Algebra.normUnits ℚ x) _ (by rw [Units.coe_map, MonoidHom.coe_ofClass, eq_ratCast]),
    abelianizedLocalCyclotomicCharacter_infiniteArtinAt_rat p _ (Algebra.normUnits ℚ x) _
      (by rw [Units.coe_map, MonoidHom.coe_ofClass, eq_ratCast])]
  exact finprod_ratLocalFactor_mul_eq_one p _

end TauCeti.ClassFieldTheory
