/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.ArtinNorm
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.Data.Rat.Units
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
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
`a` (`abelianizedLocalCyclotomicCharacter_infiniteArtinAt_of_neg`). The finite places of `ℚ` are
read in `ℚ_ℓ` through `Padic.adicCompletionEquiv` and the naturality of the cyclotomic character
of Artin symbols (`abelianizedLocalCyclotomicCharacter_artinMap_congr`). The product of the local
factors is a character of `ℚˣ`, so it suffices to evaluate it at the generators `-1` and the primes
`q` (`MonoidHom.ext_units_rat`): at `-1` the factors at `p` and at the real place are both `-1`,
at `p` every factor is trivial, and at a prime `q ≠ p` the factors at `q` and at `p` are `q` and
`q⁻¹`. The norm functoriality of the local Artin symbols
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

/-- The local factors of `-1` multiply to `-1`: only the factor at `p` is nontrivial. -/
private theorem finprod_ratLocalFactor_neg_one :
    ∏ᶠ ℓ : Nat.Primes, ratLocalFactor p ℓ (-1) = -1 := by
  let P : Nat.Primes := ⟨p, Fact.out⟩
  rw [finprod_eq_single _ P fun ℓ hℓ ↦ ?_]
  · exact (ratLocalFactor_self p (k := 0) (u := -1) (by simp)).trans inv_neg_one
  · obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := p)
      ((Nat.coprime_primes Fact.out ℓ.2).2 fun h ↦ hℓ (Subtype.ext h.symm))
    rw [ratLocalFactor_of_ne p hu]
    simp

/-- The local factors of a prime `q` multiply to `1`: for `q ≠ p` the factors at `q` and at `p`
are `q` and `q⁻¹`, and all others are trivial. -/
private theorem finprod_ratLocalFactor_prime {q : ℕ} (hq : q.Prime) :
    ∏ᶠ ℓ : Nat.Primes, ratLocalFactor p ℓ (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) =
      1 := by
  let P : Nat.Primes := ⟨p, Fact.out⟩
  let Q : Nat.Primes := ⟨q, hq⟩
  have hval (ℓ : Nat.Primes) (hℓ : ℓ ≠ Q) : padicValRat ℓ q = 0 := by
    rw [padicValRat.of_nat, Nat.cast_eq_zero, padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr fun h ↦ hℓ (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hq).1 h)))
  have hne (ℓ : Nat.Primes) (hℓ : ℓ ≠ P) (hℓQ : ℓ ≠ Q) :
      ratLocalFactor p ℓ (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := p)
      ((Nat.coprime_primes Fact.out ℓ.2).2 fun h ↦ hℓ (Subtype.ext h.symm))
    rw [ratLocalFactor_of_ne p hu, Units.val_mk0, hval ℓ hℓQ, zpow_zero]
  obtain hqp | hqp := eq_or_ne q p
  · subst hqp
    refine finprod_eq_one_of_forall_eq_one fun ℓ ↦ ?_
    obtain rfl | hℓ := eq_or_ne ℓ P
    · exact (ratLocalFactor_self q (k := 1) (u := 1) (by simp)).trans inv_one
    · exact hne ℓ hℓ hℓ
  · have : Fact q.Prime := ⟨hq⟩
    obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := p)
      ((Nat.coprime_primes Fact.out hq).2 hqp.symm)
    have hPQ : P ≠ Q := fun h ↦ hqp (congrArg Subtype.val h).symm
    rw [finprod_eq_prod_of_mulSupport_subset (s := {P, Q}) _ fun ℓ hℓ ↦ ?_,
      Finset.prod_pair hPQ, ratLocalFactor_self p (k := 0) (u := u) (by simp [hu]),
      ratLocalFactor_of_ne p (ℓ := q) hu, Units.val_mk0, padicValRat.self hq.one_lt, zpow_one,
      inv_mul_cancel]
    by_contra h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at h
    exact hℓ (hne ℓ h.1 h.2)

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
  · refine abelianizedLocalCyclotomicCharacter_infiniteArtinAt_of_neg w hw p ?_
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

/-- Only finitely many of the factors at the primes are nontrivial. -/
private theorem hasFiniteMulSupport_ratLocalFactor (a : ℚˣ) :
    Function.HasFiniteMulSupport fun ℓ : Nat.Primes ↦ ratLocalFactor p ℓ a := by
  have h := (hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap (K := ℚ) p a).preimage
    ((primesEquiv (R := 𝓞 ℚ)).symm.injective.injOn)
  refine h.subset fun ℓ hℓ ↦ ?_
  rwa [Set.mem_preimage, Function.mem_mulSupport,
    abelianizedLocalCyclotomicCharacter_artinMap_adicCompletion_rat p ℓ a _
      (by rw [Units.coe_map, MonoidHom.coe_ofClass, eq_ratCast])]

/-- The product of the `p`-adic cyclotomic characters of the local Artin symbols of `a ∈ ℚˣ` at
all places of `ℚ`, as a character of `ℚˣ`. -/
private def ratProduct : ℚˣ →* ℤ_[p]ˣ where
  toFun a := (∏ᶠ ℓ : Nat.Primes, ratLocalFactor p ℓ a) *
    ∏ w : InfinitePlace ℚ, abelianizedLocalCyclotomicCharacter p w.Completion
      (infiniteArtinAt w (Units.map (algebraMap ℚ w.Completion : ℚ →* w.Completion) a))
  map_one' := by simp [ratLocalFactor]
  map_mul' a b := by
    simp only [ratLocalFactor, map_mul, finprod_mul_distrib (hasFiniteMulSupport_ratLocalFactor p a)
      (hasFiniteMulSupport_ratLocalFactor p b), Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

/-- The archimedean factor of `a ∈ ℚˣ` is the sign of `a`. -/
private theorem prod_infiniteArtinAt_rat (a : ℚˣ) :
    ∏ w : InfinitePlace ℚ, abelianizedLocalCyclotomicCharacter p w.Completion
      (infiniteArtinAt w (Units.map (algebraMap ℚ w.Completion : ℚ →* w.Completion) a)) =
      if 0 < (a : ℚ) then 1 else -1 := by
  rw [Fintype.prod_unique]
  exact abelianizedLocalCyclotomicCharacter_infiniteArtinAt_rat p _ a _
    (by rw [Units.coe_map, MonoidHom.coe_ofClass, eq_ratCast])

/-- **The product formula over `ℚ`**, with the finite places indexed by the primes. -/
private theorem finprod_ratLocalFactor_mul_eq_one (a : ℚˣ) :
    (∏ᶠ ℓ : Nat.Primes, ratLocalFactor p ℓ a) * (if 0 < (a : ℚ) then 1 else -1) = 1 := by
  rw [← prod_infiniteArtinAt_rat]
  refine DFunLike.congr_fun (MonoidHom.ext_units_rat (f := ratProduct p) (g := 1) ?_ fun q hq ↦ ?_)
    a
  · rw [ratProduct, MonoidHom.coe_mk, OneHom.coe_mk, finprod_ratLocalFactor_neg_one,
      prod_infiniteArtinAt_rat]
    simp
  · rw [ratProduct, MonoidHom.coe_mk, OneHom.coe_mk, finprod_ratLocalFactor_prime p hq,
      prod_infiniteArtinAt_rat]
    simp [hq.pos]

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
