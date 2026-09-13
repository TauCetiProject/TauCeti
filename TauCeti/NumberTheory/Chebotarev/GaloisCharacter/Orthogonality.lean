/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Character orthogonality for the ideal weight of a Galois character

For a finite **abelian** Galois extension `L / K` of number fields, summing `(χ σ)⁻¹` against the
ideal weight `MonoidHom.galoisCharacterWeight χ` over all characters `χ : Gal(L/K) →* ℂˣ` selects
one Frobenius fibre: at a height-one prime `𝔭` unramified in `L` the sum is `#Gal(L/K)` when the
Frobenius at `𝔭` is `σ`, and `0` otherwise. At a ramified prime it is `0`, because every summand is.

What the identity buys is a change of index: an indicator of the single condition `Frob 𝔭 = σ`
becomes a sum over the character group, in which each character contributes an ideal weight that is
completely multiplicative, and so is open to Euler-product and Dirichlet-series methods.

## Main results

* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_of_unramified`: the orthogonality identity at
  an unramified height-one prime, selecting the fibre of a chosen `σ`.
* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes`: the sum
  vanishes at a ramified prime, for the trivial reason that every summand does.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Without it the sum is
`∑ χ, χ (σ * Frob 𝔭)`, the indicator of `Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is
not an involution.

Commutativity enters as `[IsMulCommutative (L ≃ₐ[K] L)]`, a `Prop`-class, rather than as a
`CommGroup` instance argument: `L ≃ₐ[K] L` already carries a `Group` instance, and a second
bundled group structure on the same type would be a diamond. Mathlib supplies the bundled form
from the mixin as a `scoped instance` in the `IsMulCommutative` namespace, deliberately kept out of
global synthesis, so the proofs open that scope. The abelian hypothesis is what
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` requires; `Gal(K(ζ_m)/K)` satisfies it by
`IsCyclotomicExtension.Aut.commGroup`.

The sum ranges over the full character group, whose cardinality equals `Nat.card (L ≃ₐ[K] L)` by
Mathlib's duality for finite abelian groups; that equality is what puts `Nat.card (L ≃ₐ[K] L)` on
the right rather than the cardinality of the dual.

## References

The orthogonality relation and its use to select a Frobenius fibre are adapted from
`sum_galoisCharacter_mul_inv_eq` and the pair `character_orthogonality_cyclotomic_eq` /
`character_orthogonality_cyclotomic_ne` in `CebotarevDensity/Cyclotomic.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, which attributes the
argument to Sharifi, *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The statements here are
in `if`-normal form rather than split into matching and non-matching cases, are taken at the level
of the ideal weight rather than of `χ (Frob 𝔭)` directly, and hold for a general abelian extension
rather than a cyclotomic one.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open NumberField NumberField.Chebotarev

namespace AlgEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Orthogonality at a ramified prime.** Every character's weight vanishes there, so any
character sum against it does too. No commutativity is needed. -/
theorem sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes (σ : L ≃ₐ[K] L)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ ramifiedPrimes K L) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal = 0 :=
  Finset.sum_eq_zero fun χ _ ↦ by
    rw [(MonoidHom.galoisCharacterWeight_apply_eq_zero_iff χ 𝔭).mpr h𝔭, mul_zero]

open scoped Classical IsMulCommutative in
/-- **Character orthogonality for the Galois character weight.** For `L / K` abelian, `σ` a chosen
element of `Gal(L/K)` and `𝔭` a height-one prime unramified in `L`, summing `(χ σ)⁻¹` against the
weight over every character gives `#Gal(L/K)` when the Frobenius at `𝔭` is `σ`, and `0` otherwise.
This is the identity that selects one Frobenius fibre.

The inverse sits on the tag `σ`, never on the Frobenius argument: dropping it would leave
`∑ χ, χ (σ * Frob 𝔭)`, the indicator of `Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is
not an involution.

`artinSymbol` returns a conjugacy class and `.out` picks a representative, but the value does not
depend on that choice for any group: a character lands in `ℂˣ`, which is abelian, so it kills
commutators and is constant on conjugacy classes. What commutativity is needed for is the count on
the right — over a nonabelian group the character sum detects the image of the class in the
abelianization, not the condition `Frob 𝔭 = σ`. -/
theorem sum_inv_mul_galoisCharacterWeight_apply_of_unramified [IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal =
      if (artinSymbol (L := L) 𝔭.asIdeal hur).out = σ then (Nat.card (L ≃ₐ[K] L) : ℂ) else 0 := by
  have hexp : Monoid.exponent (L ≃ₐ[K] L) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero ((Monoid.exponent (L ≃ₐ[K] L) : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hexp⟩
  calc ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal
      = ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * ((χ (artinSymbol (L := L) 𝔭.asIdeal hur).out : ℂˣ) : ℂ) :=
        Finset.sum_congr rfl fun χ _ ↦ by
          rw [MonoidHom.galoisCharacterWeight_apply_of_unramified χ 𝔭 hur]
    _ = _ := CommGroup.sum_inv_mul_monoidHom_apply_eq_ite _ _

end AlgEquiv
