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

Such a homomorphism `φ` describes the local ring `eA` completely: its maximal ideal, the elements
`x e` with `φ(x) = 0`, consists of nilpotent elements
(`TauCeti.IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero`), so `eA = k e + (nilpotents)`.
This survives any ring homomorphism `F : A → A'` compatible with a field homomorphism `k → k'`
whose image spans `A'` over `k'`: every element of `F(e) A'` is then `c F(e) + m` with `m`
nilpotent, and an idempotent of this form is `0` or `F(e)`
(`IsIdempotentElem.eq_zero_or_eq_of_eq_algebraMap_mul_add`), so `F(e)` stays primitive provided
`F(e) ≠ 0`.

## Main results

* `TauCeti.IsPrimitiveIdempotent.algHom_ext`: two `k`-algebra homomorphisms `A → k` taking the
  value `1` at a primitive idempotent of the Artinian ring `A` are equal.
* `TauCeti.IsPrimitiveIdempotent.exists_mul_mul_eq_of_apply_ne_zero`: if `φ(e) = 1` and
  `φ(w) ≠ 0`, then `w e` is invertible in the corner `eA`.
* `TauCeti.IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero`: for a primitive idempotent
  `e` of a commutative Artinian `k`-algebra and a `k`-algebra homomorphism `φ` with `φ(e) = 1`,
  `x e` is nilpotent whenever `φ(x) = 0`.
* `IsIdempotentElem.eq_zero_or_eq_of_eq_algebraMap_mul_add`: an idempotent `c β + m`, with `β`
  idempotent and `m` nilpotent with `m β = m`, is `0` or `β`.
* `TauCeti.IsPrimitiveIdempotent.map_of_span_eq_top`: such an `e` stays
  primitive under a ring homomorphism `F`, compatible with a field homomorphism `k → k'`, whose
  image spans the target over `k'`, provided `F e ≠ 0`.

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

/-- **The maximal ideal of a local corner is nil.** Let `e` be a primitive idempotent of a
commutative Artinian `k`-algebra `A` and `φ : A → k` a `k`-algebra homomorphism with `φ(e) = 1`.
If `φ(x) = 0`, then `x e` is nilpotent. -/
theorem IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero [IsArtinianRing A]
    (he : IsPrimitiveIdempotent e) {φ : A →ₐ[k] k} (hφ : φ e = 1) {x : A} (hx : φ x = 0) :
    IsNilpotent (x * e) := by
  -- By the Artinian property `x^n = x^(n+1) y`, and `(1 - x y) e` is invertible in the local
  -- ring `eA`, so `x^n e = 0`.
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  obtain ⟨z, hz⟩ := (he.exists_mul_mul_eq_or (x * y)).resolve_left fun ⟨z, hz⟩ => by
    simpa [hx, hφ] using congrArg φ hz
  have hxn : x ^ n * e = 0 := by
    calc x ^ n * e = x ^ n * ((1 - x * y) * z * e) := by rw [hz]
      _ = (x ^ n - x ^ (n + 1) * y) * z * e := by ring
      _ = 0 := by rw [hy, sub_self, zero_mul, zero_mul]
  refine ⟨n + 1, ?_⟩
  rw [mul_pow, he.isIdempotentElem.pow_succ_eq, pow_succ', mul_assoc, hxn, mul_zero]

/-- **Idempotents of a corner with nilpotent radical.** In a commutative `K`-algebra `A`, let `β`
be an idempotent and `e` an idempotent of the form `e = c β + m` with `c ∈ K`, `m`
nilpotent and `m β = m`. Then `e` is `0` or `β`. -/
theorem _root_.IsIdempotentElem.eq_zero_or_eq_of_eq_algebraMap_mul_add {K : Type*} [Field K]
    [Algebra K A] {β e m : A} (hβ : IsIdempotentElem β) (he : IsIdempotentElem e)
    {c : K} (hm : IsNilpotent m) (hmβ : m * β = m) (he' : e = algebraMap K A c * β + m) :
    e = 0 ∨ e = β := by
  -- If `β = 0`, then `m = m β = 0`, so `e = 0`.
  obtain rfl | hβ0 := eq_or_ne β 0
  · left
    rw [he', ← hmβ]
    simp
  -- `(c² - c) β = m (1 - 2c - m)` is nilpotent, so `c² = c`, and idempotents differing by a
  -- nilpotent element are equal.
  have hcβ : IsNilpotent (algebraMap K A (c * c - c) * β) := by
    have hsq : algebraMap K A (c * c - c) * β = m * (1 - 2 * algebraMap K A c - m) := by
      have := he.eq
      rw [he'] at this
      rw [map_sub, map_mul]
      linear_combination this - (algebraMap K A c) ^ 2 * hβ.eq - 2 * algebraMap K A c * hmβ
    rw [hsq]
    exact (Commute.all _ _).isNilpotent_mul_right hm
  have hc : c * c - c = 0 := by
    by_contra hc
    refine hβ0 (hβ.eq_zero_of_isNilpotent ?_)
    have hβ' : β = algebraMap K A (c * c - c)⁻¹ * (algebraMap K A (c * c - c) * β) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [hβ']
    exact (Commute.all _ _).isNilpotent_mul_left hcβ
  have hc' : c * (c - 1) = 0 := by linear_combination hc
  rcases mul_eq_zero.1 hc' with h0 | h1
  · -- `c = 0`: `e = m` is nilpotent.
    left
    refine he.eq_zero_of_isNilpotent ?_
    rwa [he', h0, map_zero, zero_mul, zero_add]
  · -- `c = 1`: `e - β = m` is nilpotent.
    right
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he hβ ?_ (Commute.all _ _)
    rwa [he', sub_eq_zero.1 h1, map_one, one_mul, add_sub_cancel_left]

/-- **Primitivity survives a map whose image spans.** Let `e` be a primitive idempotent of a
commutative Artinian `k`-algebra `A` with a `k`-algebra homomorphism `φ : A → k`, `φ(e) = 1`, and
`F : A → A'` a ring homomorphism to a commutative `k'`-algebra, compatible with a field
homomorphism `f : k → k'`, whose image spans `A'` over `k'`. If `F e ≠ 0`, then `F e` is
primitive. -/
theorem IsPrimitiveIdempotent.map_of_span_eq_top [IsArtinianRing A]
    {k' A' : Type*} [Field k'] [CommRing A'] [Algebra k' A'] (he : IsPrimitiveIdempotent e)
    {φ : A →ₐ[k] k} (hφ : φ e = 1) (f : k →+* k') (F : A →+* A')
    (hF : ∀ r, F (algebraMap k A r) = algebraMap k' A' (f r))
    (hspan : Submodule.span k' (Set.range F) = ⊤) (h0 : F e ≠ 0) :
    IsPrimitiveIdempotent (F e) := by
  have hβ : IsIdempotentElem (F e) := he.isIdempotentElem.map F
  -- Every element of `F(e) A'` is `c F(e) + m` with `m` nilpotent, since
  -- `F(e) F(a) = f(φ(a)) F(e) + F(a e - φ(a) e)` and `a e - φ(a) e` is nilpotent.
  have key (y : A') : ∃ (c : k') (m : A'), IsNilpotent m ∧ m * F e = m ∧
      F e * y = algebraMap k' A' c * F e + m := by
    have hy : y ∈ Submodule.span k' (Set.range F) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine ⟨f (φ a), F (a * e - algebraMap k A (φ a) * e), ?_, ?_, ?_⟩
      · have := he.isNilpotent_mul_of_apply_eq_zero hφ (x := a - algebraMap k A (φ a)) (by simp)
        rw [sub_mul] at this
        exact this.map F
      · rw [← map_mul, sub_mul, mul_assoc, mul_assoc, he.isIdempotentElem.eq]
      · rw [map_sub, map_mul, map_mul, hF]
        ring
    | zero => exact ⟨0, 0, IsNilpotent.zero, zero_mul _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, m, hm, hmβ, hy⟩ := hy
      obtain ⟨d, n, hn, hnβ, hz⟩ := hz
      refine ⟨c + d, m + n, (Commute.all _ _).isNilpotent_add hm hn, by rw [add_mul, hmβ, hnβ], ?_⟩
      rw [mul_add, hy, hz, map_add]
      ring
    | smul r y _ hy =>
      obtain ⟨c, m, hm, hmβ, hy⟩ := hy
      refine ⟨r * c, r • m, hm.smul r, by rw [smul_mul_assoc, hmβ], ?_⟩
      rw [mul_smul_comm, hy, smul_add, map_mul, Algebra.smul_def, Algebra.smul_def]
      ring
  refine isPrimitiveIdempotent_of_eq_zero_or_eq hβ h0 fun x hx hβx _ => ?_
  obtain ⟨c, m, hm, hmβ, hxc⟩ := key x
  rw [hβx] at hxc
  exact hβ.eq_zero_or_eq_of_eq_algebraMap_mul_add hx hm hmβ hxc

end TauCeti
