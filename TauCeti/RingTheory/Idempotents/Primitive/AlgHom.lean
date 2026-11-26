/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Local

/-!
# Algebra homomorphisms to the base field at a primitive idempotent

Let `A` be a commutative Artinian `k`-algebra over a field `k` and `e` a primitive idempotent of
`A`. There is at most one `k`-algebra homomorphism `φ : A → k` with `φ(e) = 1`
(`TauCeti.IsPrimitiveIdempotent.algHom_ext`): if two differed at `x`, a rescaling `w` of
`x - φ(x)` would have `φ(w) = 0` and `ψ(w) = 1`, but the corner `eA` is a local ring, so one of
`w e` and `(1 - w) e` is invertible there (`TauCeti.IsPrimitiveIdempotent.exists_mul_mul_eq_or`),
and both homomorphisms send `e` to `1`.

Over an algebraically closed field such a homomorphism exists when `A` is of finite type, by the
weak Nullstellensatz (`IsIdempotentElem.exists_algHom_apply_eq_one`, in
`TauCeti.RingTheory.FiniteType.PointSeparation`).

## Main results

* `TauCeti.IsPrimitiveIdempotent.algHom_ext`: two `k`-algebra homomorphisms `A → k` taking the
  value `1` at a primitive idempotent of the Artinian ring `A` are equal.
* `TauCeti.IsPrimitiveIdempotent.exists_mul_mul_eq_of_apply_ne_zero`: if `φ(e) = 1` and
  `φ(w) ≠ 0`, then `w e` is invertible in the corner `eA`.

## References

* A. Martínez, *Modular representation theory of finite groups*, pp. 9–10, for `A` the centre of
  a group algebra.
-/

public section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {e : A}

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

/-- **Elements with nonzero character value are invertible at a primitive idempotent.** Let `e` be
a primitive idempotent of a commutative Artinian `k`-algebra `A` and `φ : A → k` a `k`-algebra
homomorphism with `φ(e) = 1`. If `φ(w) ≠ 0`, then `w e` is invertible in the local ring `eA`:
there is a `z` with `w z e = e`. -/
theorem IsPrimitiveIdempotent.exists_mul_mul_eq_of_apply_ne_zero [IsArtinianRing A]
    (he : IsPrimitiveIdempotent e) {φ : A →ₐ[k] k} (hφ : φ e = 1) {w : A} (hw : φ w ≠ 0) :
    ∃ z, w * z * e = e := by
  -- Rescale `w` to `w'` with `φ(w') = 1`; then `(1 - w') e` is not invertible in `eA`.
  set w' := algebraMap k A (φ w)⁻¹ * w
  have hw' : φ w' = 1 := by simp [w', inv_mul_cancel₀ hw]
  rcases he.exists_mul_mul_eq_or w' with ⟨z, hz⟩ | ⟨z, hz⟩
  · exact ⟨algebraMap k A (φ w)⁻¹ * z, Eq.trans (by simp only [w']; ring) hz⟩
  · have := congrArg φ hz
    rw [map_mul, map_mul, map_sub, map_one, hw', hφ] at this
    simp at this

end TauCeti
