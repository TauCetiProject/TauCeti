/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.FieldTheory.IsAlgClosed.Embedding
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of unity and automorphisms in closed fields

Mathlib's `IsSepClosed.hasEnoughRootsOfUnity` provides primitive `n`-th roots of unity in a
separably closed field `E` in which `n` is nonzero. If `n` is nonzero in some algebra over a
commutative semiring `K`, then it is nonzero in `K`, hence in every algebra over `K` in which `K`
embeds. Hence a separably closed field `E` into which `K` embeds contains a primitive `n`-th root of
unity as soon as some domain over `K` does. For instance, the separable closure of a field `K`
contains every primitive root of unity found in an algebraic closure of `K`, and a separably closed
field of characteristic zero (take `K = ℕ`) contains every primitive root of unity found in a domain
of characteristic zero.

When `Φ_n` is irreducible over a field `K`, coprime powers of a primitive root are conjugate
over `K`. In an algebraically closed ambient field these conjugates are realized by
automorphisms, even if the ambient extension is transcendental.

## Main results

* `IsPrimitiveRoot.exists_algEquiv_apply_eq_pow_of_coprime_of_isAlgClosed`: coprime powers
  of primitive roots are realized by automorphisms when the cyclotomic polynomial is irreducible.
* `IsPrimitiveRoot.exists_isPrimitiveRoot_of_isSepClosed`: a separably closed field into which `K`
  embeds contains a primitive `n`-th root of unity as soon as some domain over `K` does.
-/

public section

namespace IsPrimitiveRoot

/-- A separably closed field `E` that is a faithful algebra over a commutative semiring `K` (for
instance any field extension of a field `K`) contains a primitive `n`-th root of unity as soon as
some domain `M` over `K` does. -/
theorem exists_isPrimitiveRoot_of_isSepClosed (K : Type*) {E M : Type*}
    [CommSemiring K] [Field E] [IsSepClosed E] [Algebra K E] [FaithfulSMul K E]
    [CommRing M] [IsDomain M] [Algebra K M]
    {n : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ξ : E, IsPrimitiveRoot ξ n := by
  obtain rfl | hn := eq_or_ne n 0
  · exact ⟨0, .zero⟩
  -- For `n ≠ 0`, `n` is nonzero in `M`, hence in `K` and in `E`.
  have := NeZero.mk hn
  have := hζ.neZero'
  have : NeZero (n : K) := .of_map (algebraMap K M) (neZero := by rwa [map_natCast])
  have : NeZero (n : E) := .nat_of_injective (FaithfulSMul.algebraMap_injective K E)
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot E n

end IsPrimitiveRoot

/-- If `Φ_n` is irreducible over `K`, every coprime power of a primitive `n`th root in an
algebraically closed field is its image under a `K`-automorphism. For `K = ℚ`, `Ω = ℂ` and
`n > 0`, every unit modulo `n` is realized by an automorphism of `ℂ`. -/
theorem IsPrimitiveRoot.exists_algEquiv_apply_eq_pow_of_coprime_of_isAlgClosed
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {n j : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (hj : n.Coprime j)
    (hirr : Irreducible (Polynomial.cyclotomic n K)) :
    ∃ τ : Ω ≃ₐ[K] Ω, τ ζ = ζ ^ j := by
  have : NeZero n :=
    ⟨by rintro rfl; exact not_irreducible_one (Polynomial.cyclotomic_zero K ▸ hirr)⟩
  have := hζ.neZero'
  have : NeZero (n : K) := ⟨fun hn ↦
    (NeZero.ne (n : Ω)) (by simpa using congrArg (algebraMap K Ω) hn)⟩
  apply IsConjRoot.exists_algEquiv_of_isAlgClosed
  rw [isConjRoot_def, (hζ.minpoly_eq_cyclotomic_of_irreducible hirr).symm,
    ((hζ.pow_of_coprime j hj.symm).minpoly_eq_cyclotomic_of_irreducible hirr).symm]
