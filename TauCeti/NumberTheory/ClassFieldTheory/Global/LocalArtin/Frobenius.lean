/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Compatibility
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap

/-!
# The global Artin symbol of a prime idele is arithmetic Frobenius

Let `L/K` be a finite Galois extension of number fields and `v` a finite place of `K`. The
**prime idele class** `primeIdeleClass K v ∈ C_K` is the class of the idele with a uniformizer of
`K_v` at `v` and `1` at every other place. It is the idelic counterpart of the prime ideal `v`.

If `v` is unramified in `L` and `σ ∈ Gal(L/K)` is an arithmetic Frobenius at a prime `Q` of `L`
above `v`, then the global Artin symbol of the class of the idele concentrated at `v` with
component `x ∈ K_vˣ` is the class of `σ` raised to the normalized valuation of `x`
(`globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt`). This combines the local–global
compatibility `globalArtinMap_local` with the unramified local computation
`localArtinAt_eq_of_isArithFrobAt`. In particular the Artin symbol of the prime idele class is
the class of Frobenius, whichever uniformizer represents it
(`globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt`).

For `L/K` abelian, `Gal(L/K)` is its own abelianization, so this pins the Artin symbol down as an
automorphism: an automorphism whose class is the Artin symbol of the prime idele class at `v` is
an arithmetic Frobenius at every prime of `L` above `v` (`globalArtinMap_isArithFrobAt`). This is
the arithmetic, rather than geometric, normalization of the global Artin map.

Consequently the global Artin map agrees with the ideal-theoretic Artin map
`TauCeti.NumberFieldArithmetic.artinHomAway` on the primes outside a finite set `S` containing
the ramified ones: for an abelian `L/K` and `v ∉ S`, the Artin symbol of the prime idele class at
`v` is the class of the value of `artinHomAway` at the prime `v` (`globalArtinMap_ideal`). Since
a homomorphism on the ideals prime to `S` is determined by its values on primes, every such
homomorphism whose prime values are the global Artin symbols of the prime idele classes is
`artinHomAway` itself (`eq_artinHomAway_of_globalArtinMap`).

## Main definitions

* `TauCeti.ClassFieldTheory.primeIdeleClass K v`: the idele class of a uniformizer at `v`.

## Main results

* `TauCeti.ClassFieldTheory.globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt`: at an
  unramified place, the global Artin symbol of `x ∈ K_vˣ` is Frobenius to the power `v(x)`.
* `TauCeti.ClassFieldTheory.globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt`: the global Artin
  symbol of the prime idele class at an unramified place is the class of Frobenius.
* `TauCeti.ClassFieldTheory.globalArtinMap_isArithFrobAt`: for `L/K` abelian, an automorphism
  representing the Artin symbol of the prime idele class at an unramified `v` is an arithmetic
  Frobenius at every prime of `L` above `v`.
* `TauCeti.ClassFieldTheory.globalArtinMap_ideal`: for `L/K` abelian, the global Artin symbol of
  the prime idele class at `v ∉ S` is the class of the ideal-theoretic Artin symbol of `v`.
* `TauCeti.ClassFieldTheory.eq_artinHomAway_of_globalArtinMap`: a homomorphism on the ideals
  prime to `S` taking the global Artin symbols of the prime idele classes at the primes outside
  `S` is the ideal-theoretic Artin map.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5 and §7 (the idelic and the
  ideal-theoretic Artin symbols).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3 and Chapter VII.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- **The prime idele class at a finite place** `v` of a number field `K`: the class in the idele
class group of the idele whose component at `v` is a chosen uniformizer of `K_v` and whose other
components are `1`. At a place unramified in a finite Galois extension its global Artin symbol does
not depend on the choice (`globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt`). -/
def primeIdeleClass (v : HeightOneSpectrum (𝓞 K)) : IdeleClassGroup (𝓞 K) K :=
  IdeleClassGroup.ofAdicCompletion (𝓞 K) K v (exists_isUniformizer (v.adicCompletion K)).choose

/-- The prime idele class at `v` is the class of the idele concentrated at `v` with a uniformizer
of `K_v` as component. -/
theorem exists_isUniformizer_primeIdeleClass_eq (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, IsUniformizer (v.adicCompletion K) π ∧
      primeIdeleClass K v = IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π :=
  ⟨_, (exists_isUniformizer (v.adicCompletion K)).choose_spec, rfl⟩

variable {K} (L : Type) [Field L] [NumberField L] [Algebra K L]

section Unramified

variable [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K) (v : HeightOneSpectrum (𝓞 K))
  (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] [Algebra.IsUnramifiedAt (𝓞 K) Q]

/-- **The global Artin symbol at an unramified place.** If `v` is unramified at a prime `Q` of `L`
above it and `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, then the global Artin symbol of the
class of the idele concentrated at `v` with component `x ∈ K_vˣ` is the class of `σ` raised to the
normalized valuation of `x`. -/
theorem globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt {σ : Gal(L/K)}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) (x : (v.adicCompletion K)ˣ) :
    globalArtinMap K L ι (.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x)) =
      .ofMul (Abelianization.of σ ^ (normalizedValuation (v.adicCompletion K) x).toAdd) := by
  -- The prime `Q` is a finite place of `L` above `v`.
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := ‹Q.LiesOver v.asIdeal›
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := ‹Algebra.IsUnramifiedAt (𝓞 K) Q›
  rw [IdeleClassGroup.ofAdicCompletion_apply, globalArtinMap_local,
    localArtinAt_eq_of_isArithFrobAt v w hσ]

/-- **The global Artin symbol of a prime idele class is Frobenius.** If `v` is unramified at a prime
`Q` of `L` above it and `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, then the global Artin
symbol of the prime idele class at `v` is the class of `σ` in `Gal(L/K)^ab`. -/
theorem globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt {σ : Gal(L/K)}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    globalArtinMap K L ι (.ofMul (primeIdeleClass K v)) = .ofMul (Abelianization.of σ) := by
  obtain ⟨π, hπ, h⟩ := exists_isUniformizer_primeIdeleClass_eq K v
  rw [h, globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L ι v Q hσ, (isUniformizer_def π).1 hπ,
    toAdd_ofAdd, zpow_one]

/-- **Arithmetic Frobenius normalization of the global Artin map.** For a finite abelian extension
`L/K` of number fields and a finite place `v` of `K` unramified at a prime `Q` of `L` above it, an
automorphism `σ ∈ Gal(L/K)` whose class is the global Artin symbol of the prime idele class at `v`
is an arithmetic Frobenius at `Q`. -/
theorem globalArtinMap_isArithFrobAt [IsMulCommutative Gal(L/K)] {σ : Gal(L/K)}
    (hσ : globalArtinMap K L ι (.ofMul (primeIdeleClass K v)) = .ofMul (Abelianization.of σ)) :
    IsArithFrobAt (𝓞 K) σ Q := by
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt K Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  -- `Gal(L/K)` is commutative, so `Abelianization.of` is injective on it.
  have hof : Function.Injective (Abelianization.of (G := Gal(L/K))) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [Abelianization.ker_of, commutator_eq_bot])
  rw [globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt L ι v Q hτ] at hσ
  rwa [← hof (Additive.ofMul.injective hσ)]

end Unramified

section Ideal

variable [IsAbelianGalois K L] (ι : L →ₐ[K] SeparableClosure K)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **Comparison with the ideal-theoretic Artin map.** For a finite abelian extension `L/K` of
number fields, unramified outside a finite set `S` of finite places of `K`, and a finite place
`v ∉ S`, the global Artin symbol of the prime idele class at `v` is the class of the value of
`NumberFieldArithmetic.artinHomAway` at the prime `v`, that is, of the arithmetic Frobenius at
`v`. -/
theorem globalArtinMap_ideal (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (I : NumberFieldArithmetic.idealsAway K S)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) :
    globalArtinMap K L ι (.ofMul (primeIdeleClass K v)) =
      .ofMul (Abelianization.of
        (NumberFieldArithmetic.artinHomAway algEquiv_commute_of_isAbelianGalois S hur I)) := by
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  have := hur v hv Q
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  rw [globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt L ι v Q hσ,
    NumberFieldArithmetic.artinHomAway_apply_prime _ S hur I v hv hI Q σ hσ]

/-- **The global Artin symbols of the prime idele classes determine the ideal-theoretic Artin
map.** For a finite abelian extension `L/K` of number fields, unramified outside a finite set `S`
of finite places of `K`, a homomorphism `φ` on the ideals prime to `S` whose value at each prime
`v ∉ S` represents the global Artin symbol of the prime idele class at `v` is
`NumberFieldArithmetic.artinHomAway`. -/
theorem eq_artinHomAway_of_globalArtinMap
    (φ : NumberFieldArithmetic.idealsAway K S →* (L ≃ₐ[K] L))
    (hφ : ∀ (I : NumberFieldArithmetic.idealsAway K S) (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
      ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) →
      globalArtinMap K L ι (.ofMul (primeIdeleClass K v)) = .ofMul (Abelianization.of (φ I))) :
    φ = NumberFieldArithmetic.artinHomAway algEquiv_commute_of_isAbelianGalois S hur := by
  refine NumberFieldArithmetic.artinHomAway_eq_of_apply_prime _ S hur φ ?_
  intro I v hv hI Q _ _ σ hσ
  have := hur v hv Q
  exact isArithFrobAt_eq_of_isUnramifiedAt
    (globalArtinMap_isArithFrobAt L ι v Q (hφ I v hv hI)) hσ

end Ideal

end TauCeti.ClassFieldTheory
