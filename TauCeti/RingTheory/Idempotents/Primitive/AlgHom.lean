/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

When `A` is finite-dimensional and `k` is algebraically closed there is one for every nonzero
idempotent (`IsIdempotentElem.exists_algHom_apply_eq_one`): `e` is not nilpotent, so it lies
outside some prime ideal `𝔪` of the Artinian ring `A`, which is maximal with residue field finite
over `k`, hence `k`.

## Main results

* `TauCeti.IsPrimitiveIdempotent.algHom_ext`: two `k`-algebra homomorphisms `A → k` taking the
  value `1` at a primitive idempotent of the Artinian ring `A` are equal.
* `IsIdempotentElem.exists_algHom_apply_eq_one`: over an algebraically closed field, a nonzero
  idempotent of a finite-dimensional commutative algebra takes the value `1` under some
  `k`-algebra homomorphism `A → k`.

## References

* A. Martínez, *Modular representation theory of finite groups*, pp. 9–10, for `A` the centre of
  a group algebra.
-/

public section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {e : A}

/-- **Existence of a character at an idempotent.** Over an algebraically closed field `k`, some
`k`-algebra homomorphism `A → k` takes the value `1` at a nonzero idempotent `e` of a
finite-dimensional commutative `k`-algebra `A`. -/
theorem IsIdempotentElem.exists_algHom_apply_eq_one [IsAlgClosed k] [Module.Finite k A]
    (he : IsIdempotentElem e) (hne : e ≠ 0) : ∃ φ : A →ₐ[k] k, φ e = 1 := by
  have := IsArtinianRing.of_finite k A
  -- `e` is not nilpotent, so it lies outside some prime ideal `𝔪`, which is maximal.
  have hnil : e ∉ nilradical A := by
    rw [mem_nilradical]
    rintro ⟨n, hn⟩
    have h := he.pow_succ_eq n
    rw [pow_succ, hn, zero_mul] at h
    exact hne h.symm
  rw [nilradical_eq_sInf, Submodule.mem_sInf] at hnil
  simp only [not_forall] at hnil
  obtain ⟨𝔪, h𝔪, he𝔪⟩ := hnil
  have : Ideal.IsPrime 𝔪 := h𝔪
  have : Ideal.IsMaximal 𝔪 := IsArtinianRing.isMaximal_of_isPrime 𝔪
  let := Ideal.Quotient.field 𝔪
  let ι : k ≃ₐ[k] A ⧸ 𝔪 :=
    AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨ι.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  have hidem : IsIdempotentElem (ι.symm (Ideal.Quotient.mkₐ k 𝔪 e)) :=
    he.map (ι.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k 𝔪))
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 hidem).resolve_left fun h ↦ he𝔪 ?_
  have h' := ι.symm.injective (h.trans (map_zero ι.symm).symm)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h'

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
