/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Order and cyclicity of a cyclotomic Galois group, and embeddings of cyclotomic extensions

For an `n`-th cyclotomic extension `L / K` whose cyclotomic polynomial `Φ_n` is irreducible over
`K`, the Galois group has exactly `φ n` elements. Over any base, the Galois group embeds in the unit
group `(ZMod n)ˣ` through the action on a primitive `n`-th root of unity, so it is cyclic whenever
`(ZMod n)ˣ` is — for instance whenever `n` is a power of an odd prime. When `Φ_n` is irreducible, a
primitive `n`-th root of unity in `L` is sent to any primitive `n`-th root of unity in a domain
containing `K` by exactly one `K`-algebra map.

## Main results

* `IsCyclotomicExtension.card_aut_eq_totient`: `#Gal(L / K) = φ n` when `Φ_n` is irreducible.
* `IsCyclotomicExtension.isCyclic_aut`: the group is cyclic when `(ZMod n)ˣ` is.
* `IsCyclotomicExtension.neZero_of_nontrivial_aut`: a nontrivial Galois group forces `n ≠ 0`.
* `IsPrimitiveRoot.existsUnique_algHom_apply_eq`: exactly one `K`-algebra map sends a given
  primitive root to any other when `Φ_n` is irreducible.

## Implementation notes

`Nat.card` is used rather than `Fintype.card` so that no finiteness instance is demanded of the
caller; the finiteness is supplied locally (irreducibility of `Φ_n` forces `n ≠ 0`).

## References

The Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0),
performs the `φ n` count inline over `ℚ` on branch `development` at commit
`8575c9df1ae0a61120ab5c964c7911414254bec7`. In `CebotarevDensity/Main.lean` it sets
`E := IsCyclotomicExtension.autEquivPow L hirr` and rewrites with `Nat.card_congr E.toEquiv`,
`Nat.card_eq_fintype_card` and `ZMod.card_units_eq_totient`, as a step inside the consumer of
`chebotarev_cyclotomic` rather than as a named result. `card_aut_eq_totient` is that step named and
stated over an arbitrary base field. `isCyclic_aut` does not appear in the source.
-/

public section

open Polynomial

namespace IsCyclotomicExtension

/-- **A nontrivial cyclotomic Galois group has nonzero level.** At level `0` the algebra map
`A → B` is surjective, so the identity is the only `A`-algebra automorphism of `B`. -/
theorem neZero_of_nontrivial_aut {n : ℕ} (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsCyclotomicExtension {n} A B] [Nontrivial (B ≃ₐ[A] B)] : NeZero n := by
  refine ⟨?_⟩
  rintro rfl
  have : Subsingleton (Subalgebra A B) := subsingleton_of_bot_eq_top <|
    (Algebra.surjective_algebraMap_iff.mp
      (isCyclotomicExtension_zero_iff.mp ‹_›)).symm
  exact not_nontrivial (B ≃ₐ[A] B) ‹_›

variable {n : ℕ} [NeZero n] (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L]

omit [NeZero n] in
/-- **The order of a cyclotomic Galois group.** If `Φ_n` is irreducible over `K` then the Galois
group of an `n`-th cyclotomic extension of `K` has exactly `φ n` elements.

At a prime `q` this reads `q - 1`, via `Nat.totient_prime`. -/
theorem card_aut_eq_totient (h : Irreducible (cyclotomic n K)) :
    Nat.card Gal(L/K) = n.totient := by
  have : NeZero n := ⟨by rintro rfl; simp at h⟩
  rw [Nat.card_congr (autEquivPow L h).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

omit [NeZero n] in
/-- **A cyclotomic Galois group is cyclic when the unit group is.** The hypothesis holds at every
power of an odd prime, where it is `ZMod.isCyclic_units_of_prime_pow`. -/
theorem isCyclic_aut [IsCyclic (ZMod n)ˣ] : IsCyclic Gal(L/K) := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- `L` is generated over `K` by `K` itself, so the Galois group is trivial
    have hsurj := isCyclotomicExtension_zero_iff.1 ‹IsCyclotomicExtension {0} K L›
    have : Subsingleton (Subalgebra K L) :=
      subsingleton_of_bot_eq_top (Algebra.surjective_algebraMap_iff.1 hsurj).symm
    infer_instance
  · have : NeZero n := ⟨hn⟩
    exact isCyclic_of_injective _ ((zeta_spec n K L).autToPow_injective K)

end IsCyclotomicExtension

namespace IsPrimitiveRoot

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] {L : Type*} [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L] {ζ : L}

omit [NeZero n] in
/-- If `Φ_n` is irreducible over `K`, a primitive `n`-th root of unity in an `n`-th cyclotomic
extension of `K` is sent to any given primitive `n`-th root of unity in a domain containing `K` by
exactly one `K`-algebra map. -/
theorem existsUnique_algHom_apply_eq (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (cyclotomic n K)) {C : Type*} [CommRing C] [IsDomain C] [Algebra K C]
    {ω : C} (hω : IsPrimitiveRoot ω n) : ∃! ι : L →ₐ[K] C, ι ζ = ω := by
  have : NeZero n := ⟨by rintro rfl; simp at hirr⟩
  simpa only [Subtype.ext_iff, embeddingsEquivPrimitiveRoots_apply_coe] using
    (hζ.embeddingsEquivPrimitiveRoots C hirr).bijective.existsUnique
      ⟨ω, (mem_primitiveRoots (NeZero.pos n)).mpr hω⟩

end IsPrimitiveRoot
