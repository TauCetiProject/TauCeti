/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.Idempotents.Corner.Local

/-!
# Algebra homomorphisms to the base field at an idempotent

Let `A` be a commutative `k`-algebra over a field `k` and `e` an idempotent of `A`. This file
studies the `k`-algebra homomorphisms `φ : A → k` with `φ(e) = 1`.

When `A` is Artinian and `e` is primitive there is at most one
(`TauCeti.IsPrimitiveIdempotent.algHom_ext`): if two differed at `x`, a rescaling `w` of
`x - φ(x)` would have `φ(w) = 0` and `ψ(w) = 1`, but the corner `eA` is a local ring, so one of
`w e` and `(1 - w) e` is invertible there (`TauCeti.IsPrimitiveIdempotent.exists_mul_mul_eq_or`),
and both homomorphisms send `e` to `1`.

When `A` is of finite type over `k` and `k` is algebraically closed there is one for every
nonzero idempotent (`IsIdempotentElem.exists_algHom_apply_eq_one`, which more generally allows
values in any algebraically closed extension `K` of `k`): `e` is not nilpotent, so by the weak
Nullstellensatz
(`TauCeti.exists_algHom_apply_ne_zero_of_not_isNilpotent`) some `φ` has `φ(e) ≠ 0`, and the
idempotent `φ(e)` of a field is then `1`.

## Main results

* `TauCeti.IsPrimitiveIdempotent.algHom_ext`: two `k`-algebra homomorphisms `A → k` taking the
  value `1` at a primitive idempotent of the Artinian ring `A` are equal.
* `IsIdempotentElem.exists_algHom_apply_eq_one`: a nonzero idempotent of a commutative
  `k`-algebra of finite type takes the value `1` under some `k`-algebra homomorphism `A → K` to an
  algebraically closed extension `K` of `k`.

## References

* A. Martínez, *Modular representation theory of finite groups*, pp. 9–10, for `A` the centre of
  a group algebra.
-/

public section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {e : A}

/-- **Existence of a character at an idempotent.** For an algebraically closed extension `K` of
`k`, some `k`-algebra homomorphism `A → K` takes the value `1` at a nonzero idempotent `e` of a
commutative `k`-algebra `A` of finite type. -/
theorem IsIdempotentElem.exists_algHom_apply_eq_one {K : Type*} [Field K] [Algebra k K]
    [IsAlgClosed K] [Algebra.FiniteType k A] (he : IsIdempotentElem e) (hne : e ≠ 0) :
    ∃ φ : A →ₐ[k] K, φ e = 1 := by
  obtain ⟨φ, hφ⟩ := TauCeti.exists_algHom_apply_ne_zero_of_not_isNilpotent (k := k) (K := K)
    (mt he.eq_zero_of_isNilpotent hne)
  exact ⟨φ, (IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ)).resolve_left hφ⟩

namespace TauCeti

/-- **Uniqueness of a character at a primitive idempotent.** Two `k`-algebra homomorphisms
`A → k` taking the value `1` at a primitive idempotent `e` of a commutative Artinian `k`-algebra
`A` are equal. -/
theorem IsPrimitiveIdempotent.algHom_ext [IsArtinianRing A] (he : IsPrimitiveIdempotent e)
    {φ ψ : A →ₐ[k] k} (hφ : φ e = 1) (hψ : ψ e = 1) : φ = ψ := by
  ext x
  by_contra hne
  -- `w` rescales `x - φ(x)` so that `φ(w) = 0` and `ψ(w) = 1`.
  set w := algebraMap k A (ψ x - φ x)⁻¹ * (x - algebraMap k A (φ x))
  have hd : ψ x - φ x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hφw : φ w = 0 := by simp [w]
  have hψw : ψ w = 1 := by simp [w, inv_mul_cancel₀ hd]
  rcases he.exists_mul_mul_eq_or w with ⟨z, hz⟩ | ⟨z, hz⟩
  · have := congrArg φ hz
    rw [map_mul, map_mul, hφw, hφ] at this
    simp at this
  · have := congrArg ψ hz
    rw [map_mul, map_mul, map_sub, map_one, hψw, hψ] at this
    simp at this

end TauCeti
